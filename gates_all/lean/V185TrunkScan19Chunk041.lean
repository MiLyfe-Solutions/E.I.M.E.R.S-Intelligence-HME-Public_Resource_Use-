import V185TrunkScan19Chunk040

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_411543 : List Nat := [1, 1, 3, 3, 1, 10]
def baseStart_411543 : Nat := 118140960795 + 411543 * 2 ^ 59
def prefixEnd_411543 : Nat := 4983230072969 + 3 ^ 40 * 411543 * 2
def baseEnd_411543 : Nat := 13914032526313650687727

theorem tailTrace_411543 : CollatzResearch.WordTrace tailWord_411543 prefixEnd_411543 13914032526313650687727 := by
  unfold tailWord_411543
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010206348057471793759283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10006804232038314529172855 15010206348057471793759283)
  ·
    refine ⟨22515309522086207690638925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15010206348057471793759283 22515309522086207690638925)
    ·
      refine ⟨8443241070782327883989597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22515309522086207690638925 8443241070782327883989597)
      ·
        refine ⟨3166215401543372956496099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8443241070782327883989597 3166215401543372956496099)
        ·
          refine ⟨4749323102315059434744149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166215401543372956496099 4749323102315059434744149)
          ·
            refine ⟨13914032526313650687727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4749323102315059434744149 13914032526313650687727)
            ·
              rfl

theorem cell19_411543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_411543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411543 prefixEnd_411543 := by exact prefixLift 411543
  have htrace : WordTrace (prefixWord ++ tailWord_411543) baseStart_411543 baseEnd_411543 := by
    simpa [prefixWord, tailWord_411543, baseEnd_411543] using wordTrace_append hprefix tailTrace_411543
  have hstable : (prefixWord ++ tailWord_411543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411543).length < 2 ^ (prefixWord ++ tailWord_411543).sum := by decide
  have hdescent : baseEnd_411543 < baseStart_411543 := by decide
  rcases family_descends (prefixWord ++ tailWord_411543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411655 : List Nat := [1, 1, 4, 3, 1, 4, 5]
def baseStart_411655 : Nat := 118140960795 + 411655 * 2 ^ 59
def prefixEnd_411655 : Nat := 4983230072969 + 3 ^ 40 * 411655 * 2
def baseEnd_411655 : Nat := 41753457546013260566783

theorem tailTrace_411655 : CollatzResearch.WordTrace tailWord_411655 prefixEnd_411655 41753457546013260566783 := by
  unfold tailWord_411655
  simp only [CollatzResearch.WordTrace]
  refine ⟨15014291323651714921836419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10009527549101143281224279 15014291323651714921836419)
  ·
    refine ⟨22521436985477572382754629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15014291323651714921836419 22521436985477572382754629)
    ·
      refine ⟨4222769434777044821766493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22521436985477572382754629 4222769434777044821766493)
      ·
        refine ⟨1583538538041391808162435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4222769434777044821766493 1583538538041391808162435)
        ·
          refine ⟨2375307807062087712243653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583538538041391808162435 2375307807062087712243653)
          ·
            refine ⟨445370213824141446045685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2375307807062087712243653 445370213824141446045685)
            ·
              refine ⟨41753457546013260566783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 445370213824141446045685 41753457546013260566783)
              ·
                rfl

theorem cell19_411655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_411655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411655 prefixEnd_411655 := by exact prefixLift 411655
  have htrace : WordTrace (prefixWord ++ tailWord_411655) baseStart_411655 baseEnd_411655 := by
    simpa [prefixWord, tailWord_411655, baseEnd_411655] using wordTrace_append hprefix tailTrace_411655
  have hstable : (prefixWord ++ tailWord_411655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411655).length < 2 ^ (prefixWord ++ tailWord_411655).sum := by decide
  have hdescent : baseEnd_411655 < baseStart_411655 := by decide
  rcases family_descends (prefixWord ++ tailWord_411655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411674 : List Nat := [3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_411674 : Nat := 118140960795 + 411674 * 2 ^ 59
def prefixEnd_411674 : Nat := 4983230072969 + 3 ^ 40 * 411674 * 2
def baseEnd_411674 : Nat := 125266154049853367278075

theorem tailTrace_411674 : CollatzResearch.WordTrace tailWord_411674 prefixEnd_411674 125266154049853367278075 := by
  unfold tailWord_411674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753746077645720291694519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10009989540388587444518717 3753746077645720291694519)
  ·
    refine ⟨5630619116468580437541779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3753746077645720291694519 5630619116468580437541779)
    ·
      refine ⟨8445928674702870656312669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5630619116468580437541779 8445928674702870656312669)
      ·
        refine ⟨3167223253013576496117251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8445928674702870656312669 3167223253013576496117251)
        ·
          refine ⟨4750834879520364744175877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167223253013576496117251 4750834879520364744175877)
          ·
            refine ⟨890781539910068389532977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4750834879520364744175877 890781539910068389532977)
            ·
              refine ⟨668086154932551292149733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890781539910068389532977 668086154932551292149733)
              ·
                refine ⟨125266154049853367278075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668086154932551292149733 125266154049853367278075)
                ·
                  rfl

theorem cell19_411674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_411674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411674 prefixEnd_411674 := by exact prefixLift 411674
  have htrace : WordTrace (prefixWord ++ tailWord_411674) baseStart_411674 baseEnd_411674 := by
    simpa [prefixWord, tailWord_411674, baseEnd_411674] using wordTrace_append hprefix tailTrace_411674
  have hstable : (prefixWord ++ tailWord_411674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411674).length < 2 ^ (prefixWord ++ tailWord_411674).sum := by decide
  have hdescent : baseEnd_411674 < baseStart_411674 := by decide
  rcases family_descends (prefixWord ++ tailWord_411674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411710 : List Nat := [4, 2, 1, 3, 3, 6]
def baseStart_411710 : Nat := 118140960795 + 411710 * 2 ^ 59
def prefixEnd_411710 : Nat := 4983230072969 + 3 ^ 40 * 411710 * 2
def baseEnd_411710 : Nat := 13919678700423994497553

theorem tailTrace_411710 : CollatzResearch.WordTrace tailWord_411710 prefixEnd_411710 13919678700423994497553 := by
  unfold tailWord_411710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877037167306557414386073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10010864892301639543392389 1877037167306557414386073)
  ·
    refine ⟨1407777875479918060789555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1877037167306557414386073 1407777875479918060789555)
    ·
      refine ⟨2111666813219877091184333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407777875479918060789555 2111666813219877091184333)
      ·
        refine ⟨791875054957453909194125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2111666813219877091184333 791875054957453909194125)
        ·
          refine ⟨296953145609045215947797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791875054957453909194125 296953145609045215947797)
          ·
            refine ⟨13919678700423994497553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 296953145609045215947797 13919678700423994497553)
            ·
              rfl

theorem cell19_411710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_411710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411710 prefixEnd_411710 := by exact prefixLift 411710
  have htrace : WordTrace (prefixWord ++ tailWord_411710) baseStart_411710 baseEnd_411710 := by
    simpa [prefixWord, tailWord_411710, baseEnd_411710] using wordTrace_append hprefix tailTrace_411710
  have hstable : (prefixWord ++ tailWord_411710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411710).length < 2 ^ (prefixWord ++ tailWord_411710).sum := by decide
  have hdescent : baseEnd_411710 < baseStart_411710 := by decide
  rcases family_descends (prefixWord ++ tailWord_411710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411746 : List Nat := [3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_411746 : Nat := 118140960795 + 411746 * 2 ^ 59
def prefixEnd_411746 : Nat := 4983230072969 + 3 ^ 40 * 411746 * 2
def baseEnd_411746 : Nat := 125288062557778533677879

theorem tailTrace_411746 : CollatzResearch.WordTrace tailWord_411746 prefixEnd_411746 125288062557778533677879 := by
  unfold tailWord_411746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754402591580509365849773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10011740244214691642266061 3754402591580509365849773)
  ·
    refine ⟨1407900971842691012193665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3754402591580509365849773 1407900971842691012193665)
    ·
      refine ⟨1055925728882018259145249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1407900971842691012193665 1055925728882018259145249)
      ·
        refine ⟨791944296661513694358937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055925728882018259145249 791944296661513694358937)
        ·
          refine ⟨593958222496135270769203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791944296661513694358937 593958222496135270769203)
          ·
            refine ⟨890937333744202906153805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593958222496135270769203 890937333744202906153805)
            ·
              refine ⟨334101500154076089807677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890937333744202906153805 334101500154076089807677)
              ·
                refine ⟨125288062557778533677879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334101500154076089807677 125288062557778533677879)
                ·
                  rfl

theorem cell19_411746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_411746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411746 prefixEnd_411746 := by exact prefixLift 411746
  have htrace : WordTrace (prefixWord ++ tailWord_411746) baseStart_411746 baseEnd_411746 := by
    simpa [prefixWord, tailWord_411746, baseEnd_411746] using wordTrace_append hprefix tailTrace_411746
  have hstable : (prefixWord ++ tailWord_411746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411746).length < 2 ^ (prefixWord ++ tailWord_411746).sum := by decide
  have hdescent : baseEnd_411746 < baseStart_411746 := by decide
  rcases family_descends (prefixWord ++ tailWord_411746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411805 : List Nat := [1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_411805 : Nat := 118140960795 + 411805 * 2 ^ 59
def prefixEnd_411805 : Nat := 4983230072969 + 3 ^ 40 * 411805 * 2
def baseEnd_411805 : Nat := 125306015362883878366607

theorem tailTrace_411805 : CollatzResearch.WordTrace tailWord_411805 prefixEnd_411805 125306015362883878366607 := by
  unfold tailWord_411805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019762273108290539796869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10013174848738860359864579 15019762273108290539796869)
  ·
    refine ⟨2816205426207804476211913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15019762273108290539796869 2816205426207804476211913)
    ·
      refine ⟨2112154069655853357158935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2816205426207804476211913 2112154069655853357158935)
      ·
        refine ⟨3168231104483780035738403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112154069655853357158935 3168231104483780035738403)
        ·
          refine ⟨4752346656725670053607605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168231104483780035738403 4752346656725670053607605)
          ·
            refine ⟨445532499068031567525713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4752346656725670053607605 445532499068031567525713)
            ·
              refine ⟨334149374301023675644285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445532499068031567525713 334149374301023675644285)
              ·
                refine ⟨125306015362883878366607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334149374301023675644285 125306015362883878366607)
                ·
                  rfl

theorem cell19_411805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_411805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411805 prefixEnd_411805 := by exact prefixLift 411805
  have htrace : WordTrace (prefixWord ++ tailWord_411805) baseStart_411805 baseEnd_411805 := by
    simpa [prefixWord, tailWord_411805, baseEnd_411805] using wordTrace_append hprefix tailTrace_411805
  have hstable : (prefixWord ++ tailWord_411805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411805).length < 2 ^ (prefixWord ++ tailWord_411805).sum := by decide
  have hdescent : baseEnd_411805 < baseStart_411805 := by decide
  rcases family_descends (prefixWord ++ tailWord_411805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411807 : List Nat := [1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_411807 : Nat := 118140960795 + 411807 * 2 ^ 59
def prefixEnd_411807 : Nat := 4983230072969 + 3 ^ 40 * 411807 * 2
def baseEnd_411807 : Nat := 125306623932548466322157

theorem tailTrace_411807 : CollatzResearch.WordTrace tailWord_411807 prefixEnd_411807 125306623932548466322157 := by
  unfold tailWord_411807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019835219101044881369675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10013223479400696587579783 15019835219101044881369675)
  ·
    refine ⟨22529752828651567322054513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15019835219101044881369675 22529752828651567322054513)
    ·
      refine ⟨16897314621488675491540885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22529752828651567322054513 16897314621488675491540885)
      ·
        refine ⟨792061622882281663665979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16897314621488675491540885 792061622882281663665979)
        ·
          refine ⟨1188092434323422495498969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792061622882281663665979 1188092434323422495498969)
          ·
            refine ⟨891069325742566871624227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188092434323422495498969 891069325742566871624227)
            ·
              refine ⟨1336603988613850307436341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891069325742566871624227 1336603988613850307436341)
              ·
                refine ⟨125306623932548466322157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1336603988613850307436341 125306623932548466322157)
                ·
                  rfl

theorem cell19_411807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_411807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411807 prefixEnd_411807 := by exact prefixLift 411807
  have htrace : WordTrace (prefixWord ++ tailWord_411807) baseStart_411807 baseEnd_411807 := by
    simpa [prefixWord, tailWord_411807, baseEnd_411807] using wordTrace_append hprefix tailTrace_411807
  have hstable : (prefixWord ++ tailWord_411807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411807).length < 2 ^ (prefixWord ++ tailWord_411807).sum := by decide
  have hdescent : baseEnd_411807 < baseStart_411807 := by decide
  rcases family_descends (prefixWord ++ tailWord_411807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411822 : List Nat := [4, 1, 4, 2, 1, 2, 5]
def baseStart_411822 : Nat := 118140960795 + 411822 * 2 ^ 59
def prefixEnd_411822 : Nat := 4983230072969 + 3 ^ 40 * 411822 * 2
def baseEnd_411822 : Nat := 41770396068344291996261

theorem tailTrace_411822 : CollatzResearch.WordTrace tailWord_411822 prefixEnd_411822 41770396068344291996261 := by
  unfold tailWord_411822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877547789255837805395715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10013588209364468295443813 1877547789255837805395715)
  ·
    refine ⟨2816321683883756708093573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877547789255837805395715 2816321683883756708093573)
    ·
      refine ⟨528060315728204382767545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2816321683883756708093573 528060315728204382767545)
      ·
        refine ⟨396045236796153287075659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528060315728204382767545 396045236796153287075659)
        ·
          refine ⟨594067855194229930613489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396045236796153287075659 594067855194229930613489)
          ·
            refine ⟨445550891395672447960117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594067855194229930613489 445550891395672447960117)
            ·
              refine ⟨41770396068344291996261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 445550891395672447960117 41770396068344291996261)
              ·
                rfl

theorem cell19_411822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_411822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411822 prefixEnd_411822 := by exact prefixLift 411822
  have htrace : WordTrace (prefixWord ++ tailWord_411822) baseStart_411822 baseEnd_411822 := by
    simpa [prefixWord, tailWord_411822, baseEnd_411822] using wordTrace_append hprefix tailTrace_411822
  have hstable : (prefixWord ++ tailWord_411822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411822).length < 2 ^ (prefixWord ++ tailWord_411822).sum := by decide
  have hdescent : baseEnd_411822 < baseStart_411822 := by decide
  rcases family_descends (prefixWord ++ tailWord_411822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411862 : List Nat := [5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_411862 : Nat := 118140960795 + 411862 * 2 ^ 59
def prefixEnd_411862 : Nat := 4983230072969 + 3 ^ 40 * 411862 * 2
def baseEnd_411862 : Nat := 125323359598324635099785

theorem tailTrace_411862 : CollatzResearch.WordTrace tailWord_411862 prefixEnd_411862 125323359598324635099785 := by
  unfold tailWord_411862
  simp only [CollatzResearch.WordTrace]
  refine ⟨938865077118861829663865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10014560822601192849747893 938865077118861829663865)
  ·
    refine ⟨704148807839146372247899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 938865077118861829663865 704148807839146372247899)
    ·
      refine ⟨1056223211758719558371849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704148807839146372247899 1056223211758719558371849)
      ·
        refine ⟨792167408819039668778887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056223211758719558371849 792167408819039668778887)
        ·
          refine ⟨1188251113228559503168331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792167408819039668778887 1188251113228559503168331)
          ·
            refine ⟨1782376669842839254752497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188251113228559503168331 1782376669842839254752497)
            ·
              refine ⟨1336782502382129441064373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1782376669842839254752497 1336782502382129441064373)
              ·
                refine ⟨125323359598324635099785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1336782502382129441064373 125323359598324635099785)
                ·
                  rfl

theorem cell19_411862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_411862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411862 prefixEnd_411862 := by exact prefixLift 411862
  have htrace : WordTrace (prefixWord ++ tailWord_411862) baseStart_411862 baseEnd_411862 := by
    simpa [prefixWord, tailWord_411862, baseEnd_411862] using wordTrace_append hprefix tailTrace_411862
  have hstable : (prefixWord ++ tailWord_411862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411862).length < 2 ^ (prefixWord ++ tailWord_411862).sum := by decide
  have hdescent : baseEnd_411862 < baseStart_411862 := by decide
  rcases family_descends (prefixWord ++ tailWord_411862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411866 : List Nat := [3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_411866 : Nat := 118140960795 + 411866 * 2 ^ 59
def prefixEnd_411866 : Nat := 4983230072969 + 3 ^ 40 * 411866 * 2
def baseEnd_411866 : Nat := 125324576737653811010885

theorem tailTrace_411866 : CollatzResearch.WordTrace tailWord_411866 prefixEnd_411866 125324576737653811010885 := by
  unfold tailWord_411866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755496781471824489441863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10014658083924865305178301 3755496781471824489441863)
  ·
    refine ⟨5633245172207736734162795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3755496781471824489441863 5633245172207736734162795)
    ·
      refine ⟨8449867758311605101244193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5633245172207736734162795 8449867758311605101244193)
      ·
        refine ⟨6337400818733703825933145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8449867758311605101244193 6337400818733703825933145)
        ·
          refine ⟨4753050614050277869449859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6337400818733703825933145 4753050614050277869449859)
          ·
            refine ⟨7129575921075416804174789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753050614050277869449859 7129575921075416804174789)
            ·
              refine ⟨1336795485201640650782773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7129575921075416804174789 1336795485201640650782773)
              ·
                refine ⟨125324576737653811010885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1336795485201640650782773 125324576737653811010885)
                ·
                  rfl

theorem cell19_411866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_411866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411866 prefixEnd_411866 := by exact prefixLift 411866
  have htrace : WordTrace (prefixWord ++ tailWord_411866) baseStart_411866 baseEnd_411866 := by
    simpa [prefixWord, tailWord_411866, baseEnd_411866] using wordTrace_append hprefix tailTrace_411866
  have hstable : (prefixWord ++ tailWord_411866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411866).length < 2 ^ (prefixWord ++ tailWord_411866).sum := by decide
  have hdescent : baseEnd_411866 < baseStart_411866 := by decide
  rcases family_descends (prefixWord ++ tailWord_411866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411885 : List Nat := [1, 5, 1, 2, 10]
def baseStart_411885 : Nat := 118140960795 + 411885 * 2 ^ 59
def prefixEnd_411885 : Nat := 4983230072969 + 3 ^ 40 * 411885 * 2
def baseEnd_411885 : Nat := 4641865116646940614393

theorem tailTrace_411885 : CollatzResearch.WordTrace tailWord_411885 prefixEnd_411885 4641865116646940614393 := by
  unfold tailWord_411885
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022680112818464202709109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10015120075212309468472739 15022680112818464202709109)
  ·
    refine ⟨1408376260576731019003979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15022680112818464202709109 1408376260576731019003979)
    ·
      refine ⟨2112564390865096528505969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408376260576731019003979 2112564390865096528505969)
      ·
        refine ⟨1584423293148822396379477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2112564390865096528505969 1584423293148822396379477)
        ·
          refine ⟨4641865116646940614393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1584423293148822396379477 4641865116646940614393)
          ·
            rfl

theorem cell19_411885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 10].length) (baseStart_411885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411885 prefixEnd_411885 := by exact prefixLift 411885
  have htrace : WordTrace (prefixWord ++ tailWord_411885) baseStart_411885 baseEnd_411885 := by
    simpa [prefixWord, tailWord_411885, baseEnd_411885] using wordTrace_append hprefix tailTrace_411885
  have hstable : (prefixWord ++ tailWord_411885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411885).length < 2 ^ (prefixWord ++ tailWord_411885).sum := by decide
  have hdescent : baseEnd_411885 < baseStart_411885 := by decide
  rcases family_descends (prefixWord ++ tailWord_411885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411904 : List Nat := [2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_411904 : Nat := 118140960795 + 411904 * 2 ^ 59
def prefixEnd_411904 : Nat := 4983230072969 + 3 ^ 40 * 411904 * 2
def baseEnd_411904 : Nat := 125336139561280982166337

theorem tailTrace_411904 : CollatzResearch.WordTrace tailWord_411904 prefixEnd_411904 125336139561280982166337 := by
  unfold tailWord_411904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511686549874815223825383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10015582066499753631767177 7511686549874815223825383)
  ·
    refine ⟨11267529824812222835738075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7511686549874815223825383 11267529824812222835738075)
    ·
      refine ⟨16901294737218334253607113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11267529824812222835738075 16901294737218334253607113)
      ·
        refine ⟨12675971052913750690205335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16901294737218334253607113 12675971052913750690205335)
        ·
          refine ⟨19013956579370626035308003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12675971052913750690205335 19013956579370626035308003)
          ·
            refine ⟨28520934869055939052962005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19013956579370626035308003 28520934869055939052962005)
            ·
              refine ⟨668459410993498571553797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28520934869055939052962005 668459410993498571553797)
              ·
                refine ⟨125336139561280982166337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668459410993498571553797 125336139561280982166337)
                ·
                  rfl

theorem cell19_411904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_411904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411904 prefixEnd_411904 := by exact prefixLift 411904
  have htrace : WordTrace (prefixWord ++ tailWord_411904) baseStart_411904 baseEnd_411904 := by
    simpa [prefixWord, tailWord_411904, baseEnd_411904] using wordTrace_append hprefix tailTrace_411904
  have hstable : (prefixWord ++ tailWord_411904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411904).length < 2 ^ (prefixWord ++ tailWord_411904).sum := by decide
  have hdescent : baseEnd_411904 < baseStart_411904 := by decide
  rcases family_descends (prefixWord ++ tailWord_411904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411921 : List Nat := [1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_411921 : Nat := 118140960795 + 411921 * 2 ^ 59
def prefixEnd_411921 : Nat := 4983230072969 + 3 ^ 40 * 411921 * 2
def baseEnd_411921 : Nat := 125341312403429979788513

theorem tailTrace_411921 : CollatzResearch.WordTrace tailWord_411921 prefixEnd_411921 125341312403429979788513 := by
  unfold tailWord_411921
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023993140688042351019617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10015995427125361567346411 15023993140688042351019617)
  ·
    refine ⟨11267994855516031763264713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15023993140688042351019617 11267994855516031763264713)
    ·
      refine ⟨8450996141637023822448535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11267994855516031763264713 8450996141637023822448535)
      ·
        refine ⟨12676494212455535733672803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8450996141637023822448535 12676494212455535733672803)
        ·
          refine ⟨19014741318683303600509205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12676494212455535733672803 19014741318683303600509205)
          ·
            refine ⟨891315999313279856273869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19014741318683303600509205 891315999313279856273869)
            ·
              refine ⟨334243499742479946102701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891315999313279856273869 334243499742479946102701)
              ·
                refine ⟨125341312403429979788513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334243499742479946102701 125341312403429979788513)
                ·
                  rfl

theorem cell19_411921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_411921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411921 prefixEnd_411921 := by exact prefixLift 411921
  have htrace : WordTrace (prefixWord ++ tailWord_411921) baseStart_411921 baseEnd_411921 := by
    simpa [prefixWord, tailWord_411921, baseEnd_411921] using wordTrace_append hprefix tailTrace_411921
  have hstable : (prefixWord ++ tailWord_411921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411921).length < 2 ^ (prefixWord ++ tailWord_411921).sum := by decide
  have hdescent : baseEnd_411921 < baseStart_411921 := by decide
  rcases family_descends (prefixWord ++ tailWord_411921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411972 : List Nat := [2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_411972 : Nat := 118140960795 + 411972 * 2 ^ 59
def prefixEnd_411972 : Nat := 4983230072969 + 3 ^ 40 * 411972 * 2
def baseEnd_411972 : Nat := 125356830929876972655041

theorem tailTrace_411972 : CollatzResearch.WordTrace tailWord_411972 prefixEnd_411972 125356830929876972655041 := by
  unfold tailWord_411972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512926631751639030563085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10017235509002185374084113 7512926631751639030563085)
  ·
    refine ⟨2817347486906864636461157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7512926631751639030563085 2817347486906864636461157)
    ·
      refine ⟨528252653795037119336467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2817347486906864636461157 528252653795037119336467)
      ·
        refine ⟨792378980692555679004701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528252653795037119336467 792378980692555679004701)
        ·
          refine ⟨297142117759708379626763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 792378980692555679004701 297142117759708379626763)
          ·
            refine ⟨445713176639562569440145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297142117759708379626763 445713176639562569440145)
            ·
              refine ⟨334284882479671927080109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445713176639562569440145 334284882479671927080109)
              ·
                refine ⟨125356830929876972655041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334284882479671927080109 125356830929876972655041)
                ·
                  rfl

theorem cell19_411972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_411972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411972 prefixEnd_411972 := by exact prefixLift 411972
  have htrace : WordTrace (prefixWord ++ tailWord_411972) baseStart_411972 baseEnd_411972 := by
    simpa [prefixWord, tailWord_411972, baseEnd_411972] using wordTrace_append hprefix tailTrace_411972
  have hstable : (prefixWord ++ tailWord_411972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411972).length < 2 ^ (prefixWord ++ tailWord_411972).sum := by decide
  have hdescent : baseEnd_411972 < baseStart_411972 := by decide
  rcases family_descends (prefixWord ++ tailWord_411972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411980 : List Nat := [2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_411980 : Nat := 118140960795 + 411980 * 2 ^ 59
def prefixEnd_411980 : Nat := 4983230072969 + 3 ^ 40 * 411980 * 2
def baseEnd_411980 : Nat := 125359265208535324477241

theorem tailTrace_411980 : CollatzResearch.WordTrace tailWord_411980 prefixEnd_411980 125359265208535324477241 := by
  unfold tailWord_411980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513072523737147713708697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10017430031649530284944929 7513072523737147713708697)
  ·
    refine ⟨5634804392802860785281523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7513072523737147713708697 5634804392802860785281523)
    ·
      refine ⟨8452206589204291177922285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634804392802860785281523 8452206589204291177922285)
      ·
        refine ⟨3169577470951609191720857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8452206589204291177922285 3169577470951609191720857)
        ·
          refine ⟨2377183103213706893790643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3169577470951609191720857 2377183103213706893790643)
          ·
            refine ⟨3565774654820560340685965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377183103213706893790643 3565774654820560340685965)
            ·
              refine ⟨1337165495557710127757237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3565774654820560340685965 1337165495557710127757237)
              ·
                refine ⟨125359265208535324477241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1337165495557710127757237 125359265208535324477241)
                ·
                  rfl

theorem cell19_411980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_411980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411980 prefixEnd_411980 := by exact prefixLift 411980
  have htrace : WordTrace (prefixWord ++ tailWord_411980) baseStart_411980 baseEnd_411980 := by
    simpa [prefixWord, tailWord_411980, baseEnd_411980] using wordTrace_append hprefix tailTrace_411980
  have hstable : (prefixWord ++ tailWord_411980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411980).length < 2 ^ (prefixWord ++ tailWord_411980).sum := by decide
  have hdescent : baseEnd_411980 < baseStart_411980 := by decide
  rcases family_descends (prefixWord ++ tailWord_411980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412018 : List Nat := [3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_412018 : Nat := 118140960795 + 412018 * 2 ^ 59
def prefixEnd_412018 : Nat := 4983230072969 + 3 ^ 40 * 412018 * 2
def baseEnd_412018 : Nat := 125370828032162495632693

theorem tailTrace_412018 : CollatzResearch.WordTrace tailWord_412018 prefixEnd_412018 125370828032162495632693 := by
  unfold tailWord_412018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756882755334156979325177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10018354014224418611533805 3756882755334156979325177)
  ·
    refine ⟨2817662066500617734493883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3756882755334156979325177 2817662066500617734493883)
    ·
      refine ⟨4226493099750926601740825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817662066500617734493883 4226493099750926601740825)
      ·
        refine ⟨3169869824813194951305619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4226493099750926601740825 3169869824813194951305619)
        ·
          refine ⟨4754804737219792426958429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169869824813194951305619 4754804737219792426958429)
          ·
            refine ⟨1783051776457422160109411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4754804737219792426958429 1783051776457422160109411)
            ·
              refine ⟨2674577664686133240164117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783051776457422160109411 2674577664686133240164117)
              ·
                refine ⟨125370828032162495632693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2674577664686133240164117 125370828032162495632693)
                ·
                  rfl

theorem cell19_412018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_412018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412018 prefixEnd_412018 := by exact prefixLift 412018
  have htrace : WordTrace (prefixWord ++ tailWord_412018) baseStart_412018 baseEnd_412018 := by
    simpa [prefixWord, tailWord_412018, baseEnd_412018] using wordTrace_append hprefix tailTrace_412018
  have hstable : (prefixWord ++ tailWord_412018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412018).length < 2 ^ (prefixWord ++ tailWord_412018).sum := by decide
  have hdescent : baseEnd_412018 < baseStart_412018 := by decide
  rcases family_descends (prefixWord ++ tailWord_412018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412056 : List Nat := [2, 1, 2, 5, 1, 8]
def baseStart_412056 : Nat := 118140960795 + 412056 * 2 ^ 59
def prefixEnd_412056 : Nat := 4983230072969 + 3 ^ 40 * 412056 * 2
def baseEnd_412056 : Nat := 13931376761754407420905

theorem tailTrace_412056 : CollatzResearch.WordTrace tailWord_412056 prefixEnd_412056 13931376761754407420905 := by
  unfold tailWord_412056
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514458497599480203592011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10019277996799306938122681 7514458497599480203592011)
  ·
    refine ⟨11271687746399220305388017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7514458497599480203592011 11271687746399220305388017)
    ·
      refine ⟨8453765809799415229041013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11271687746399220305388017 8453765809799415229041013)
      ·
        refine ⟨792540544668695177722595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8453765809799415229041013 792540544668695177722595)
        ·
          refine ⟨1188810817003042766583893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792540544668695177722595 1188810817003042766583893)
          ·
            refine ⟨13931376761754407420905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1188810817003042766583893 13931376761754407420905)
            ·
              rfl

theorem cell19_412056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_412056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412056 prefixEnd_412056 := by exact prefixLift 412056
  have htrace : WordTrace (prefixWord ++ tailWord_412056) baseStart_412056 baseEnd_412056 := by
    simpa [prefixWord, tailWord_412056, baseEnd_412056] using wordTrace_append hprefix tailTrace_412056
  have hstable : (prefixWord ++ tailWord_412056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412056).length < 2 ^ (prefixWord ++ tailWord_412056).sum := by decide
  have hdescent : baseEnd_412056 < baseStart_412056 := by decide
  rcases family_descends (prefixWord ++ tailWord_412056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412094 : List Nat := [4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_412094 : Nat := 118140960795 + 412094 * 2 ^ 59
def prefixEnd_412094 : Nat := 4983230072969 + 3 ^ 40 * 412094 * 2
def baseEnd_412094 : Nat := 125393953679416837943597

theorem tailTrace_412094 : CollatzResearch.WordTrace tailWord_412094 prefixEnd_412094 125393953679416837943597 := by
  unfold tailWord_412094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878787871132661612133417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10020201979374195264711557 1878787871132661612133417)
  ·
    refine ⟨1409090903349496209100063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1878787871132661612133417 1409090903349496209100063)
    ·
      refine ⟨2113636355024244313650095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409090903349496209100063 2113636355024244313650095)
      ·
        refine ⟨3170454532536366470475143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113636355024244313650095 3170454532536366470475143)
        ·
          refine ⟨4755681798804549705712715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170454532536366470475143 4755681798804549705712715)
          ·
            refine ⟨7133522698206824558569073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755681798804549705712715 7133522698206824558569073)
            ·
              refine ⟨5350142023655118418926805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7133522698206824558569073 5350142023655118418926805)
              ·
                refine ⟨125393953679416837943597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5350142023655118418926805 125393953679416837943597)
                ·
                  rfl

theorem cell19_412094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_412094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412094 prefixEnd_412094 := by exact prefixLift 412094
  have htrace : WordTrace (prefixWord ++ tailWord_412094) baseStart_412094 baseEnd_412094 := by
    simpa [prefixWord, tailWord_412094, baseEnd_412094] using wordTrace_append hprefix tailTrace_412094
  have hstable : (prefixWord ++ tailWord_412094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412094).length < 2 ^ (prefixWord ++ tailWord_412094).sum := by decide
  have hdescent : baseEnd_412094 < baseStart_412094 := by decide
  rcases family_descends (prefixWord ++ tailWord_412094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412189 : List Nat := [1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_412189 : Nat := 118140960795 + 412189 * 2 ^ 59
def prefixEnd_412189 : Nat := 4983230072969 + 3 ^ 40 * 412189 * 2
def baseEnd_412189 : Nat := 125422860738484765832227

theorem tailTrace_412189 : CollatzResearch.WordTrace tailWord_412189 prefixEnd_412189 125422860738484765832227 := by
  unfold tailWord_412189
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033767903717124121775621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10022511935811416081183747 15033767903717124121775621)
  ·
    refine ⟨2818831481946960772832929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15033767903717124121775621 2818831481946960772832929)
    ·
      refine ⟨2114123611460220579624697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818831481946960772832929 2114123611460220579624697)
      ·
        refine ⟨1585592708595165434718523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2114123611460220579624697 1585592708595165434718523)
        ·
          refine ⟨2378389062892748152077785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585592708595165434718523 2378389062892748152077785)
          ·
            refine ⟨1783791797169561114058339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2378389062892748152077785 1783791797169561114058339)
            ·
              refine ⟨2675687695754341671087509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783791797169561114058339 2675687695754341671087509)
              ·
                refine ⟨125422860738484765832227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2675687695754341671087509 125422860738484765832227)
                ·
                  rfl

theorem cell19_412189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_412189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412189 prefixEnd_412189 := by exact prefixLift 412189
  have htrace : WordTrace (prefixWord ++ tailWord_412189) baseStart_412189 baseEnd_412189 := by
    simpa [prefixWord, tailWord_412189, baseEnd_412189] using wordTrace_append hprefix tailTrace_412189
  have hstable : (prefixWord ++ tailWord_412189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412189).length < 2 ^ (prefixWord ++ tailWord_412189).sum := by decide
  have hdescent : baseEnd_412189 < baseStart_412189 := by decide
  rcases family_descends (prefixWord ++ tailWord_412189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412229 : List Nat := [1, 3, 1, 1, 1, 12]
def baseStart_412229 : Nat := 118140960795 + 412229 * 2 ^ 59
def prefixEnd_412229 : Nat := 4983230072969 + 3 ^ 40 * 412229 * 2
def baseEnd_412229 : Nat := 13937225792419613882581

theorem tailTrace_412229 : CollatzResearch.WordTrace tailWord_412229 prefixEnd_412229 13937225792419613882581 := by
  unfold tailWord_412229
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035226823572210953231741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10023484549048140635487827 15035226823572210953231741)
  ·
    refine ⟨5638210058839579107461903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15035226823572210953231741 5638210058839579107461903)
    ·
      refine ⟨8457315088259368661192855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638210058839579107461903 8457315088259368661192855)
      ·
        refine ⟨12685972632389052991789283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457315088259368661192855 12685972632389052991789283)
        ·
          refine ⟨19028958948583579487683925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685972632389052991789283 19028958948583579487683925)
          ·
            refine ⟨13937225792419613882581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19028958948583579487683925 13937225792419613882581)
            ·
              rfl

theorem cell19_412229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_412229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412229 prefixEnd_412229 := by exact prefixLift 412229
  have htrace : WordTrace (prefixWord ++ tailWord_412229) baseStart_412229 baseEnd_412229 := by
    simpa [prefixWord, tailWord_412229, baseEnd_412229] using wordTrace_append hprefix tailTrace_412229
  have hstable : (prefixWord ++ tailWord_412229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412229).length < 2 ^ (prefixWord ++ tailWord_412229).sum := by decide
  have hdescent : baseEnd_412229 < baseStart_412229 := by decide
  rcases family_descends (prefixWord ++ tailWord_412229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412244 : List Nat := [2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_412244 : Nat := 118140960795 + 412244 * 2 ^ 59
def prefixEnd_412244 : Nat := 4983230072969 + 3 ^ 40 * 412244 * 2
def baseEnd_412244 : Nat := 125439596404260934609855

theorem tailTrace_412244 : CollatzResearch.WordTrace tailWord_412244 prefixEnd_412244 125439596404260934609855 := by
  unfold tailWord_412244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517886959258934257513893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10023849279011912343351857 7517886959258934257513893)
  ·
    refine ⟨1409603804861050173283855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7517886959258934257513893 1409603804861050173283855)
    ·
      refine ⟨2114405707291575259925783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409603804861050173283855 2114405707291575259925783)
      ·
        refine ⟨3171608560937362889888675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114405707291575259925783 3171608560937362889888675)
        ·
          refine ⟨4757412841406044334833013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171608560937362889888675 4757412841406044334833013)
          ·
            refine ⟨446007453881816656390595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4757412841406044334833013 446007453881816656390595)
            ·
              refine ⟨669011180822724984585893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446007453881816656390595 669011180822724984585893)
              ·
                refine ⟨125439596404260934609855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669011180822724984585893 125439596404260934609855)
                ·
                  rfl

theorem cell19_412244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_412244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412244 prefixEnd_412244 := by exact prefixLift 412244
  have htrace : WordTrace (prefixWord ++ tailWord_412244) baseStart_412244 baseEnd_412244 := by
    simpa [prefixWord, tailWord_412244, baseEnd_412244] using wordTrace_append hprefix tailTrace_412244
  have hstable : (prefixWord ++ tailWord_412244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412244).length < 2 ^ (prefixWord ++ tailWord_412244).sum := by decide
  have hdescent : baseEnd_412244 < baseStart_412244 := by decide
  rcases family_descends (prefixWord ++ tailWord_412244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412337 : List Nat := [1, 2, 2, 6, 2, 1, 5]
def baseStart_412337 : Nat := 118140960795 + 412337 * 2 ^ 59
def prefixEnd_412337 : Nat := 4983230072969 + 3 ^ 40 * 412337 * 2
def baseEnd_412337 : Nat := 41822631631221424847645

theorem tailTrace_412337 : CollatzResearch.WordTrace tailWord_412337 prefixEnd_412337 41822631631221424847645 := by
  unfold tailWord_412337
  simp only [CollatzResearch.WordTrace]
  refine ⟨15039165907180945398163265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10026110604787296932108843 15039165907180945398163265)
  ·
    refine ⟨11279374430385709048622449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15039165907180945398163265 11279374430385709048622449)
    ·
      refine ⟨8459530822789281786466837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11279374430385709048622449 8459530822789281786466837)
      ·
        refine ⟨396540507318247583740633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8459530822789281786466837 396540507318247583740633)
        ·
          refine ⟨297405380488685687805475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396540507318247583740633 297405380488685687805475)
          ·
            refine ⟨446108070733028531708213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297405380488685687805475 446108070733028531708213)
            ·
              refine ⟨41822631631221424847645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446108070733028531708213 41822631631221424847645)
              ·
                rfl

theorem cell19_412337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_412337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412337 prefixEnd_412337 := by exact prefixLift 412337
  have htrace : WordTrace (prefixWord ++ tailWord_412337) baseStart_412337 baseEnd_412337 := by
    simpa [prefixWord, tailWord_412337, baseEnd_412337] using wordTrace_append hprefix tailTrace_412337
  have hstable : (prefixWord ++ tailWord_412337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412337).length < 2 ^ (prefixWord ++ tailWord_412337).sum := by decide
  have hdescent : baseEnd_412337 < baseStart_412337 := by decide
  rcases family_descends (prefixWord ++ tailWord_412337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412341 : List Nat := [1, 3, 3, 3, 1, 1, 7]
def baseStart_412341 : Nat := 118140960795 + 412341 * 2 ^ 59
def prefixEnd_412341 : Nat := 4983230072969 + 3 ^ 40 * 412341 * 2
def baseEnd_412341 : Nat := 41823037344331150151345

theorem tailTrace_412341 : CollatzResearch.WordTrace tailWord_412341 prefixEnd_412341 41823037344331150151345 := by
  unfold tailWord_412341
  simp only [CollatzResearch.WordTrace]
  refine ⟨15039311799166454081308877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10026207866110969387539251 15039311799166454081308877)
  ·
    refine ⟨5639741924687420280490829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15039311799166454081308877 5639741924687420280490829)
    ·
      refine ⟨2114903221757782605184061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5639741924687420280490829 2114903221757782605184061)
      ·
        refine ⟨793088708159168476944023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2114903221757782605184061 793088708159168476944023)
        ·
          refine ⟨1189633062238752715416035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793088708159168476944023 1189633062238752715416035)
          ·
            refine ⟨1784449593358129073124053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189633062238752715416035 1784449593358129073124053)
            ·
              refine ⟨41823037344331150151345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1784449593358129073124053 41823037344331150151345)
              ·
                rfl

theorem cell19_412341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_412341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412341 prefixEnd_412341 := by exact prefixLift 412341
  have htrace : WordTrace (prefixWord ++ tailWord_412341) baseStart_412341 baseEnd_412341 := by
    simpa [prefixWord, tailWord_412341, baseEnd_412341] using wordTrace_append hprefix tailTrace_412341
  have hstable : (prefixWord ++ tailWord_412341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412341).length < 2 ^ (prefixWord ++ tailWord_412341).sum := by decide
  have hdescent : baseEnd_412341 < baseStart_412341 := by decide
  rcases family_descends (prefixWord ++ tailWord_412341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412360 : List Nat := [2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_412360 : Nat := 118140960795 + 412360 * 2 ^ 59
def prefixEnd_412360 : Nat := 4983230072969 + 3 ^ 40 * 412360 * 2
def baseEnd_412360 : Nat := 125474893444807036031761

theorem tailTrace_412360 : CollatzResearch.WordTrace tailWord_412360 prefixEnd_412360 125474893444807036031761 := by
  unfold tailWord_412360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520002393048810163125267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10026669857398413550833689 7520002393048810163125267)
  ·
    refine ⟨11280003589573215244687901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7520002393048810163125267 11280003589573215244687901)
    ·
      refine ⟨4230001346089955716757963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11280003589573215244687901 4230001346089955716757963)
      ·
        refine ⟨6345002019134933575136945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230001346089955716757963 6345002019134933575136945)
        ·
          refine ⟨4758751514351200181352709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345002019134933575136945 4758751514351200181352709)
          ·
            refine ⟨892265908940850034003633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4758751514351200181352709 892265908940850034003633)
            ·
              refine ⟨669199431705637525502725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892265908940850034003633 669199431705637525502725)
              ·
                refine ⟨125474893444807036031761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669199431705637525502725 125474893444807036031761)
                ·
                  rfl

theorem cell19_412360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_412360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412360 prefixEnd_412360 := by exact prefixLift 412360
  have htrace : WordTrace (prefixWord ++ tailWord_412360) baseStart_412360 baseEnd_412360 := by
    simpa [prefixWord, tailWord_412360, baseEnd_412360] using wordTrace_append hprefix tailTrace_412360
  have hstable : (prefixWord ++ tailWord_412360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412360).length < 2 ^ (prefixWord ++ tailWord_412360).sum := by decide
  have hdescent : baseEnd_412360 < baseStart_412360 := by decide
  rcases family_descends (prefixWord ++ tailWord_412360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412476 : List Nat := [2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_412476 : Nat := 118140960795 + 412476 * 2 ^ 59
def prefixEnd_412476 : Nat := 4983230072969 + 3 ^ 40 * 412476 * 2
def baseEnd_412476 : Nat := 125510190485353137453667

theorem tailTrace_412476 : CollatzResearch.WordTrace tailWord_412476 prefixEnd_412476 125510190485353137453667 := by
  unfold tailWord_412476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522117826838686068736641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10029490435784914758315521 7522117826838686068736641)
  ·
    refine ⟨5641588370129014551552481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7522117826838686068736641 5641588370129014551552481)
    ·
      refine ⟨4231191277596760913664361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5641588370129014551552481 4231191277596760913664361)
      ·
        refine ⟨3173393458197570685248271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4231191277596760913664361 3173393458197570685248271)
        ·
          refine ⟨4760090187296356027872407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173393458197570685248271 4760090187296356027872407)
          ·
            refine ⟨7140135280944534041808611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760090187296356027872407 7140135280944534041808611)
            ·
              refine ⟨10710202921416801062712917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140135280944534041808611 10710202921416801062712917)
              ·
                refine ⟨125510190485353137453667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10710202921416801062712917 125510190485353137453667)
                ·
                  rfl

theorem cell19_412476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_412476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412476 prefixEnd_412476 := by exact prefixLift 412476
  have htrace : WordTrace (prefixWord ++ tailWord_412476) baseStart_412476 baseEnd_412476 := by
    simpa [prefixWord, tailWord_412476, baseEnd_412476] using wordTrace_append hprefix tailTrace_412476
  have hstable : (prefixWord ++ tailWord_412476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412476).length < 2 ^ (prefixWord ++ tailWord_412476).sum := by decide
  have hdescent : baseEnd_412476 < baseStart_412476 := by decide
  rcases family_descends (prefixWord ++ tailWord_412476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412605 : List Nat := [1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_412605 : Nat := 118140960795 + 412605 * 2 ^ 59
def prefixEnd_412605 : Nat := 4983230072969 + 3 ^ 40 * 412605 * 2
def baseEnd_412605 : Nat := 125549443228719060586649

theorem tailTrace_412605 : CollatzResearch.WordTrace tailWord_412605 prefixEnd_412605 125549443228719060586649 := by
  unfold tailWord_412605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15048940670210027168919269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10032627113473351445946179 15048940670210027168919269)
  ·
    refine ⟨2821676375664380094172363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15048940670210027168919269 2821676375664380094172363)
    ·
      refine ⟨4232514563496570141258545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821676375664380094172363 4232514563496570141258545)
      ·
        refine ⟨3174385922622427605943909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232514563496570141258545 3174385922622427605943909)
        ·
          refine ⟨595197360491705176114483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3174385922622427605943909 595197360491705176114483)
          ·
            refine ⟨892796040737557764171725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595197360491705176114483 892796040737557764171725)
            ·
              refine ⟨334798515276584161564397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 892796040737557764171725 334798515276584161564397)
              ·
                refine ⟨125549443228719060586649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334798515276584161564397 125549443228719060586649)
                ·
                  rfl

theorem cell19_412605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_412605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412605 prefixEnd_412605 := by exact prefixLift 412605
  have htrace : WordTrace (prefixWord ++ tailWord_412605) baseStart_412605 baseEnd_412605 := by
    simpa [prefixWord, tailWord_412605, baseEnd_412605] using wordTrace_append hprefix tailTrace_412605
  have hstable : (prefixWord ++ tailWord_412605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412605).length < 2 ^ (prefixWord ++ tailWord_412605).sum := by decide
  have hdescent : baseEnd_412605 < baseStart_412605 := by decide
  rcases family_descends (prefixWord ++ tailWord_412605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412626 : List Nat := [3, 2, 2, 3, 1, 2, 6]
def baseStart_412626 : Nat := 118140960795 + 412626 * 2 ^ 59
def prefixEnd_412626 : Nat := 4983230072969 + 3 ^ 40 * 412626 * 2
def baseEnd_412626 : Nat := 41851944403399078039975

theorem tailTrace_412626 : CollatzResearch.WordTrace tailWord_412626 prefixEnd_412626 41851944403399078039975 := by
  unfold tailWord_412626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762426650783486938858433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10033137735422631836955821 3762426650783486938858433)
  ·
    refine ⟨2821819988087615204143825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3762426650783486938858433 2821819988087615204143825)
    ·
      refine ⟨2116364991065711403107869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2821819988087615204143825 2116364991065711403107869)
      ·
        refine ⟨793636871649641776165451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2116364991065711403107869 793636871649641776165451)
        ·
          refine ⟨1190455307474462664248177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793636871649641776165451 1190455307474462664248177)
          ·
            refine ⟨892841480605846998186133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190455307474462664248177 892841480605846998186133)
            ·
              refine ⟨41851944403399078039975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 892841480605846998186133 41851944403399078039975)
              ·
                rfl

theorem cell19_412626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_412626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412626 prefixEnd_412626 := by exact prefixLift 412626
  have htrace : WordTrace (prefixWord ++ tailWord_412626) baseStart_412626 baseEnd_412626 := by
    simpa [prefixWord, tailWord_412626, baseEnd_412626] using wordTrace_append hprefix tailTrace_412626
  have hstable : (prefixWord ++ tailWord_412626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412626).length < 2 ^ (prefixWord ++ tailWord_412626).sum := by decide
  have hdescent : baseEnd_412626 < baseStart_412626 := by decide
  rcases family_descends (prefixWord ++ tailWord_412626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412658 : List Nat := [3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_412658 : Nat := 118140960795 + 412658 * 2 ^ 59
def prefixEnd_412658 : Nat := 4983230072969 + 3 ^ 40 * 412658 * 2
def baseEnd_412658 : Nat := 125565570324830641408727

theorem tailTrace_412658 : CollatzResearch.WordTrace tailWord_412658 prefixEnd_412658 125565570324830641408727 := by
  unfold tailWord_412658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762718434754504305149657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10033915826012011480399085 3762718434754504305149657)
  ·
    refine ⟨2822038826065878228862243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3762718434754504305149657 2822038826065878228862243)
    ·
      refine ⟨4233058239098817343293365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822038826065878228862243 4233058239098817343293365)
      ·
        refine ⟨396849209915514125933753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4233058239098817343293365 396849209915514125933753)
        ·
          refine ⟨297636907436635594450315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396849209915514125933753 297636907436635594450315)
          ·
            refine ⟨446455361154953391675473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297636907436635594450315 446455361154953391675473)
            ·
              refine ⟨334841520866215043756605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446455361154953391675473 334841520866215043756605)
              ·
                refine ⟨125565570324830641408727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334841520866215043756605 125565570324830641408727)
                ·
                  rfl

theorem cell19_412658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_412658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412658 prefixEnd_412658 := by exact prefixLift 412658
  have htrace : WordTrace (prefixWord ++ tailWord_412658) baseStart_412658 baseEnd_412658 := by
    simpa [prefixWord, tailWord_412658, baseEnd_412658] using wordTrace_append hprefix tailTrace_412658
  have hstable : (prefixWord ++ tailWord_412658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412658).length < 2 ^ (prefixWord ++ tailWord_412658).sum := by decide
  have hdescent : baseEnd_412658 < baseStart_412658 := by decide
  rcases family_descends (prefixWord ++ tailWord_412658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412662 : List Nat := [5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_412662 : Nat := 118140960795 + 412662 * 2 ^ 59
def prefixEnd_412662 : Nat := 4983230072969 + 3 ^ 40 * 412662 * 2
def baseEnd_412662 : Nat := 125566787464159817319827

theorem tailTrace_412662 : CollatzResearch.WordTrace tailWord_412662 prefixEnd_412662 125566787464159817319827 := by
  unfold tailWord_412662
  simp only [CollatzResearch.WordTrace]
  refine ⟨940688726937720368984015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10034013087335683935829493 940688726937720368984015)
  ·
    refine ⟨1411033090406580553476023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940688726937720368984015 1411033090406580553476023)
    ·
      refine ⟨2116549635609870830214035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411033090406580553476023 2116549635609870830214035)
      ·
        refine ⟨3174824453414806245321053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116549635609870830214035 3174824453414806245321053)
        ·
          refine ⟨1190559170030552341995395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3174824453414806245321053 1190559170030552341995395)
          ·
            refine ⟨1785838755045828512993093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190559170030552341995395 1785838755045828512993093)
            ·
              refine ⟨334844766571092846186205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1785838755045828512993093 334844766571092846186205)
              ·
                refine ⟨125566787464159817319827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334844766571092846186205 125566787464159817319827)
                ·
                  rfl

theorem cell19_412662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_412662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412662 prefixEnd_412662 := by exact prefixLift 412662
  have htrace : WordTrace (prefixWord ++ tailWord_412662) baseStart_412662 baseEnd_412662 := by
    simpa [prefixWord, tailWord_412662, baseEnd_412662] using wordTrace_append hprefix tailTrace_412662
  have hstable : (prefixWord ++ tailWord_412662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412662).length < 2 ^ (prefixWord ++ tailWord_412662).sum := by decide
  have hdescent : baseEnd_412662 < baseStart_412662 := by decide
  rcases family_descends (prefixWord ++ tailWord_412662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412831 : List Nat := [1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_412831 : Nat := 118140960795 + 412831 * 2 ^ 59
def prefixEnd_412831 : Nat := 4983230072969 + 3 ^ 40 * 412831 * 2
def baseEnd_412831 : Nat := 125618211600817499563811

theorem tailTrace_412831 : CollatzResearch.WordTrace tailWord_412831 prefixEnd_412831 125618211600817499563811 := by
  unfold tailWord_412831
  simp only [CollatzResearch.WordTrace]
  refine ⟨15057183567391267766646347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10038122378260845177764231 15057183567391267766646347)
  ·
    refine ⟨22585775351086901649969521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15057183567391267766646347 22585775351086901649969521)
    ·
      refine ⟨16939331513315176237477141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22585775351086901649969521 16939331513315176237477141)
      ·
        refine ⟨794031164686648886131741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16939331513315176237477141 794031164686648886131741)
        ·
          refine ⟨297761686757493332299403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794031164686648886131741 297761686757493332299403)
          ·
            refine ⟨446642530136239998449105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297761686757493332299403 446642530136239998449105)
            ·
              refine ⟨334981897602179998836829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446642530136239998449105 334981897602179998836829)
              ·
                refine ⟨125618211600817499563811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334981897602179998836829 125618211600817499563811)
                ·
                  rfl

theorem cell19_412831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_412831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412831 prefixEnd_412831 := by exact prefixLift 412831
  have htrace : WordTrace (prefixWord ++ tailWord_412831) baseStart_412831 baseEnd_412831 := by
    simpa [prefixWord, tailWord_412831, baseEnd_412831] using wordTrace_append hprefix tailTrace_412831
  have hstable : (prefixWord ++ tailWord_412831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412831).length < 2 ^ (prefixWord ++ tailWord_412831).sum := by decide
  have hdescent : baseEnd_412831 < baseStart_412831 := by decide
  rcases family_descends (prefixWord ++ tailWord_412831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412837 : List Nat := [1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_412837 : Nat := 118140960795 + 412837 * 2 ^ 59
def prefixEnd_412837 : Nat := 4983230072969 + 3 ^ 40 * 412837 * 2
def baseEnd_412837 : Nat := 125620037309811263430461

theorem tailTrace_412837 : CollatzResearch.WordTrace tailWord_412837 prefixEnd_412837 125620037309811263430461 := by
  unfold tailWord_412837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15057402405369530791364765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10038268270246353860909843 15057402405369530791364765)
  ·
    refine ⟨5646525902013574046761787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15057402405369530791364765 5646525902013574046761787)
    ·
      refine ⟨8469788853020361070142681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646525902013574046761787 8469788853020361070142681)
      ·
        refine ⟨6352341639765270802607011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8469788853020361070142681 6352341639765270802607011)
        ·
          refine ⟨9528512459647906203910517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352341639765270802607011 9528512459647906203910517)
          ·
            refine ⟨893298043091991206616611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9528512459647906203910517 893298043091991206616611)
            ·
              refine ⟨1339947064637986809924917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893298043091991206616611 1339947064637986809924917)
              ·
                refine ⟨125620037309811263430461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1339947064637986809924917 125620037309811263430461)
                ·
                  rfl

theorem cell19_412837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_412837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412837 prefixEnd_412837 := by exact prefixLift 412837
  have htrace : WordTrace (prefixWord ++ tailWord_412837) baseStart_412837 baseEnd_412837 := by
    simpa [prefixWord, tailWord_412837, baseEnd_412837] using wordTrace_append hprefix tailTrace_412837
  have hstable : (prefixWord ++ tailWord_412837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412837).length < 2 ^ (prefixWord ++ tailWord_412837).sum := by decide
  have hdescent : baseEnd_412837 < baseStart_412837 := by decide
  rcases family_descends (prefixWord ++ tailWord_412837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412915 : List Nat := [1, 1, 1, 2, 2, 12]
def baseStart_412915 : Nat := 118140960795 + 412915 * 2 ^ 59
def prefixEnd_412915 : Nat := 4983230072969 + 3 ^ 40 * 412915 * 2
def baseEnd_412915 : Nat := 13960419058525577077435

theorem tailTrace_412915 : CollatzResearch.WordTrace tailWord_412915 prefixEnd_412915 13960419058525577077435 := by
  unfold tailWord_412915
  simp only [CollatzResearch.WordTrace]
  refine ⟨15060247299086950112704199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10040164866057966741802799 15060247299086950112704199)
  ·
    refine ⟨22590370948630425169056299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15060247299086950112704199 22590370948630425169056299)
    ·
      refine ⟨33885556422945637753584449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22590370948630425169056299 33885556422945637753584449)
      ·
        refine ⟨25414167317209228315188337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33885556422945637753584449 25414167317209228315188337)
        ·
          refine ⟨19060625487906921236391253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25414167317209228315188337 19060625487906921236391253)
          ·
            refine ⟨13960419058525577077435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19060625487906921236391253 13960419058525577077435)
            ·
              rfl

theorem cell19_412915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_412915 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412915 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412915 prefixEnd_412915 := by exact prefixLift 412915
  have htrace : WordTrace (prefixWord ++ tailWord_412915) baseStart_412915 baseEnd_412915 := by
    simpa [prefixWord, tailWord_412915, baseEnd_412915] using wordTrace_append hprefix tailTrace_412915
  have hstable : (prefixWord ++ tailWord_412915).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412915).length < 2 ^ (prefixWord ++ tailWord_412915).sum := by decide
  have hdescent : baseEnd_412915 < baseStart_412915 := by decide
  rcases family_descends (prefixWord ++ tailWord_412915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412998 : List Nat := [6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_412998 : Nat := 118140960795 + 412998 * 2 ^ 59
def prefixEnd_412998 : Nat := 4983230072969 + 3 ^ 40 * 412998 * 2
def baseEnd_412998 : Nat := 125669027167810593852245

theorem tailTrace_412998 : CollatzResearch.WordTrace tailWord_412998 prefixEnd_412998 125669027167810593852245 := by
  unfold tailWord_412998
  simp only [CollatzResearch.WordTrace]
  refine ⟨470727329930820477749239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10042183038524170191983765 470727329930820477749239)
  ·
    refine ⟨706090994896230716623859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470727329930820477749239 706090994896230716623859)
    ·
      refine ⟨1059136492344346074935789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706090994896230716623859 1059136492344346074935789)
      ·
        refine ⟨397176184629129778100921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1059136492344346074935789 397176184629129778100921)
        ·
          refine ⟨297882138471847333575691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397176184629129778100921 297882138471847333575691)
          ·
            refine ⟨446823207707771000363537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297882138471847333575691 446823207707771000363537)
            ·
              refine ⟨335117405780828250272653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446823207707771000363537 335117405780828250272653)
              ·
                refine ⟨125669027167810593852245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335117405780828250272653 125669027167810593852245)
                ·
                  rfl

theorem cell19_412998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_412998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_412998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_412998 prefixEnd_412998 := by exact prefixLift 412998
  have htrace : WordTrace (prefixWord ++ tailWord_412998) baseStart_412998 baseEnd_412998 := by
    simpa [prefixWord, tailWord_412998, baseEnd_412998] using wordTrace_append hprefix tailTrace_412998
  have hstable : (prefixWord ++ tailWord_412998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412998).length < 2 ^ (prefixWord ++ tailWord_412998).sum := by decide
  have hdescent : baseEnd_412998 < baseStart_412998 := by decide
  rcases family_descends (prefixWord ++ tailWord_412998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413021 : List Nat := [1, 4, 5, 1, 1, 2, 5]
def baseStart_413021 : Nat := 118140960795 + 413021 * 2 ^ 59
def prefixEnd_413021 : Nat := 4983230072969 + 3 ^ 40 * 413021 * 2
def baseEnd_413021 : Nat := 41892008572984451780357

theorem tailTrace_413021 : CollatzResearch.WordTrace tailWord_413021 prefixEnd_413021 41892008572984451780357 := by
  unfold tailWord_413021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15064113436702930216062917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10042742291135286810708611 15064113436702930216062917)
  ·
    refine ⟨2824521269381799415511797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15064113436702930216062917 2824521269381799415511797)
    ·
      refine ⟨264798869004543695204231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2824521269381799415511797 264798869004543695204231)
      ·
        refine ⟨397198303506815542806347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264798869004543695204231 397198303506815542806347)
        ·
          refine ⟨595797455260223314209521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397198303506815542806347 595797455260223314209521)
          ·
            refine ⟨446848091445167485657141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595797455260223314209521 446848091445167485657141)
            ·
              refine ⟨41892008572984451780357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446848091445167485657141 41892008572984451780357)
              ·
                rfl

theorem cell19_413021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_413021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413021 prefixEnd_413021 := by exact prefixLift 413021
  have htrace : WordTrace (prefixWord ++ tailWord_413021) baseStart_413021 baseEnd_413021 := by
    simpa [prefixWord, tailWord_413021, baseEnd_413021] using wordTrace_append hprefix tailTrace_413021
  have hstable : (prefixWord ++ tailWord_413021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413021).length < 2 ^ (prefixWord ++ tailWord_413021).sum := by decide
  have hdescent : baseEnd_413021 < baseStart_413021 := by decide
  rcases family_descends (prefixWord ++ tailWord_413021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413027 : List Nat := [1, 1, 1, 5, 2, 4, 5]
def baseStart_413027 : Nat := 118140960795 + 413027 * 2 ^ 59
def prefixEnd_413027 : Nat := 4983230072969 + 3 ^ 40 * 413027 * 2
def baseEnd_413027 : Nat := 41892617142649039735907

theorem tailTrace_413027 : CollatzResearch.WordTrace tailWord_413027 prefixEnd_413027 41892617142649039735907 := by
  unfold tailWord_413027
  simp only [CollatzResearch.WordTrace]
  refine ⟨15064332274681193240781335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10042888183120795493854223 15064332274681193240781335)
  ·
    refine ⟨22596498412021789861172003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15064332274681193240781335 22596498412021789861172003)
    ·
      refine ⟨33894747618032684791758005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22596498412021789861172003 33894747618032684791758005)
      ·
        refine ⟨3177632589190564199227313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33894747618032684791758005 3177632589190564199227313)
        ·
          refine ⟨2383224441892923149420485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3177632589190564199227313 2383224441892923149420485)
          ·
            refine ⟨446854582854923090516341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2383224441892923149420485 446854582854923090516341)
            ·
              refine ⟨41892617142649039735907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446854582854923090516341 41892617142649039735907)
              ·
                rfl

theorem cell19_413027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_413027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413027 prefixEnd_413027 := by exact prefixLift 413027
  have htrace : WordTrace (prefixWord ++ tailWord_413027) baseStart_413027 baseEnd_413027 := by
    simpa [prefixWord, tailWord_413027, baseEnd_413027] using wordTrace_append hprefix tailTrace_413027
  have hstable : (prefixWord ++ tailWord_413027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413027).length < 2 ^ (prefixWord ++ tailWord_413027).sum := by decide
  have hdescent : baseEnd_413027 < baseStart_413027 := by decide
  rcases family_descends (prefixWord ++ tailWord_413027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413067 : List Nat := [1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_413067 : Nat := 118140960795 + 413067 * 2 ^ 59
def prefixEnd_413067 : Nat := 4983230072969 + 3 ^ 40 * 413067 * 2
def baseEnd_413067 : Nat := 125690022821238878318723

theorem tailTrace_413067 : CollatzResearch.WordTrace tailWord_413067 prefixEnd_413067 125690022821238878318723 := by
  unfold tailWord_413067
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065791194536280072237455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10043860796357520048158303 15065791194536280072237455)
  ·
    refine ⟨22598686791804420108356183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15065791194536280072237455 22598686791804420108356183)
    ·
      refine ⟨33898030187706630162534275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22598686791804420108356183 33898030187706630162534275)
      ·
        refine ⟨50847045281559945243801413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33898030187706630162534275 50847045281559945243801413)
        ·
          refine ⟨9533820990292489733212765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50847045281559945243801413 9533820990292489733212765)
          ·
            refine ⟨3575182871359683649954787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9533820990292489733212765 3575182871359683649954787)
            ·
              refine ⟨5362774307039525474932181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575182871359683649954787 5362774307039525474932181)
              ·
                refine ⟨125690022821238878318723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5362774307039525474932181 125690022821238878318723)
                ·
                  rfl

theorem cell19_413067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_413067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413067 prefixEnd_413067 := by exact prefixLift 413067
  have htrace : WordTrace (prefixWord ++ tailWord_413067) baseStart_413067 baseEnd_413067 := by
    simpa [prefixWord, tailWord_413067, baseEnd_413067] using wordTrace_append hprefix tailTrace_413067
  have hstable : (prefixWord ++ tailWord_413067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413067).length < 2 ^ (prefixWord ++ tailWord_413067).sum := by decide
  have hdescent : baseEnd_413067 < baseStart_413067 := by decide
  rcases family_descends (prefixWord ++ tailWord_413067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413084 : List Nat := [2, 2, 3, 4, 8]
def baseStart_413084 : Nat := 118140960795 + 413084 * 2 ^ 59
def prefixEnd_413084 : Nat := 4983230072969 + 3 ^ 40 * 413084 * 2
def baseEnd_413084 : Nat := 4655377617162513923737

theorem tailTrace_413084 : CollatzResearch.WordTrace tailWord_413084 prefixEnd_413084 4655377617162513923737 := by
  unfold tailWord_413084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533205617737345987803153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10044274156983127983737537 7533205617737345987803153)
  ·
    refine ⟨5649904213303009490852365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7533205617737345987803153 5649904213303009490852365)
    ·
      refine ⟨2118714079988628559069637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5649904213303009490852365 2118714079988628559069637)
      ·
        refine ⟨397258889997867854825557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2118714079988628559069637 397258889997867854825557)
        ·
          refine ⟨4655377617162513923737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 397258889997867854825557 4655377617162513923737)
          ·
            rfl

theorem cell19_413084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 8].length) (baseStart_413084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413084 prefixEnd_413084 := by exact prefixLift 413084
  have htrace : WordTrace (prefixWord ++ tailWord_413084) baseStart_413084 baseEnd_413084 := by
    simpa [prefixWord, tailWord_413084, baseEnd_413084] using wordTrace_append hprefix tailTrace_413084
  have hstable : (prefixWord ++ tailWord_413084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413084).length < 2 ^ (prefixWord ++ tailWord_413084).sum := by decide
  have hdescent : baseEnd_413084 < baseStart_413084 := by decide
  rcases family_descends (prefixWord ++ tailWord_413084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413101 : List Nat := [1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_413101 : Nat := 118140960795 + 413101 * 2 ^ 59
def prefixEnd_413101 : Nat := 4983230072969 + 3 ^ 40 * 413101 * 2
def baseEnd_413101 : Nat := 125700368505536873563075

theorem tailTrace_413101 : CollatzResearch.WordTrace tailWord_413101 prefixEnd_413101 125700368505536873563075 := by
  unfold tailWord_413101
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067031276413103878975157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10044687517608735919316771 15067031276413103878975157)
  ·
    refine ⟨1412534182163728488653921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15067031276413103878975157 1412534182163728488653921)
    ·
      refine ⟨1059400636622796366490441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412534182163728488653921 1059400636622796366490441)
      ·
        refine ⟨794550477467097274867831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059400636622796366490441 794550477467097274867831)
        ·
          refine ⟨1191825716200645912301747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794550477467097274867831 1191825716200645912301747)
          ·
            refine ⟨1787738574300968868452621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191825716200645912301747 1787738574300968868452621)
            ·
              refine ⟨670401965362863325669733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787738574300968868452621 670401965362863325669733)
              ·
                refine ⟨125700368505536873563075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 670401965362863325669733 125700368505536873563075)
                ·
                  rfl

theorem cell19_413101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_413101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413101 prefixEnd_413101 := by exact prefixLift 413101
  have htrace : WordTrace (prefixWord ++ tailWord_413101) baseStart_413101 baseEnd_413101 := by
    simpa [prefixWord, tailWord_413101, baseEnd_413101] using wordTrace_append hprefix tailTrace_413101
  have hstable : (prefixWord ++ tailWord_413101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413101).length < 2 ^ (prefixWord ++ tailWord_413101).sum := by decide
  have hdescent : baseEnd_413101 < baseStart_413101 := by decide
  rcases family_descends (prefixWord ++ tailWord_413101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413190 : List Nat := [6, 2, 1, 1, 3, 1, 5]
def baseStart_413190 : Nat := 118140960795 + 413190 * 2 ^ 59
def prefixEnd_413190 : Nat := 4983230072969 + 3 ^ 40 * 413190 * 2
def baseEnd_413190 : Nat := 41909149951870345861685

theorem tailTrace_413190 : CollatzResearch.WordTrace tailWord_413190 prefixEnd_413190 41909149951870345861685 := by
  unfold tailWord_413190
  simp only [CollatzResearch.WordTrace]
  refine ⟨470946167909083502467657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10046851582060448052643349 470946167909083502467657)
  ·
    refine ⟨353209625931812626850743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 470946167909083502467657 353209625931812626850743)
    ·
      refine ⟨529814438897718940276115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353209625931812626850743 529814438897718940276115)
      ·
        refine ⟨794721658346578410414173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529814438897718940276115 794721658346578410414173)
        ·
          refine ⟨298020621879966903905315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794721658346578410414173 298020621879966903905315)
          ·
            refine ⟨447030932819950355857973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298020621879966903905315 447030932819950355857973)
            ·
              refine ⟨41909149951870345861685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447030932819950355857973 41909149951870345861685)
              ·
                rfl

theorem cell19_413190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_413190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413190 prefixEnd_413190 := by exact prefixLift 413190
  have htrace : WordTrace (prefixWord ++ tailWord_413190) baseStart_413190 baseEnd_413190 := by
    simpa [prefixWord, tailWord_413190, baseEnd_413190] using wordTrace_append hprefix tailTrace_413190
  have hstable : (prefixWord ++ tailWord_413190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413190).length < 2 ^ (prefixWord ++ tailWord_413190).sum := by decide
  have hdescent : baseEnd_413190 < baseStart_413190 := by decide
  rcases family_descends (prefixWord ++ tailWord_413190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413196 : List Nat := [2, 2, 1, 2, 6, 1, 5]
def baseStart_413196 : Nat := 118140960795 + 413196 * 2 ^ 59
def prefixEnd_413196 : Nat := 4983230072969 + 3 ^ 40 * 413196 * 2
def baseEnd_413196 : Nat := 41909758521534933817235

theorem tailTrace_413196 : CollatzResearch.WordTrace tailWord_413196 prefixEnd_413196 41909758521534933817235 := by
  unfold tailWord_413196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535248105534467551841721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10046997474045956735788961 7535248105534467551841721)
  ·
    refine ⟨5651436079150850663881291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7535248105534467551841721 5651436079150850663881291)
    ·
      refine ⟨8477154118726275995821937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651436079150850663881291 8477154118726275995821937)
      ·
        refine ⟨6357865589044706996866453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8477154118726275995821937 6357865589044706996866453)
        ·
          refine ⟨298024949486470640478115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6357865589044706996866453 298024949486470640478115)
          ·
            refine ⟨447037424229705960717173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298024949486470640478115 447037424229705960717173)
            ·
              refine ⟨41909758521534933817235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447037424229705960717173 41909758521534933817235)
              ·
                rfl

theorem cell19_413196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_413196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413196 prefixEnd_413196 := by exact prefixLift 413196
  have htrace : WordTrace (prefixWord ++ tailWord_413196) baseStart_413196 baseEnd_413196 := by
    simpa [prefixWord, tailWord_413196, baseEnd_413196] using wordTrace_append hprefix tailTrace_413196
  have hstable : (prefixWord ++ tailWord_413196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413196).length < 2 ^ (prefixWord ++ tailWord_413196).sum := by decide
  have hdescent : baseEnd_413196 < baseStart_413196 := by decide
  rcases family_descends (prefixWord ++ tailWord_413196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413217 : List Nat := [1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_413217 : Nat := 118140960795 + 413217 * 2 ^ 59
def prefixEnd_413217 : Nat := 4983230072969 + 3 ^ 40 * 413217 * 2
def baseEnd_413217 : Nat := 125735665546082974984981

theorem tailTrace_413217 : CollatzResearch.WordTrace tailWord_413217 prefixEnd_413217 125735665546082974984981 := by
  unfold tailWord_413217
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071262143992855690197905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10047508095995237126798603 15071262143992855690197905)
  ·
    refine ⟨11303446607994641767648429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15071262143992855690197905 11303446607994641767648429)
    ·
      refine ⟨4238792477997990662868161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11303446607994641767648429 4238792477997990662868161)
      ·
        refine ⟨3179094358498492997151121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4238792477997990662868161 3179094358498492997151121)
        ·
          refine ⟨2384320768873869747863341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3179094358498492997151121 2384320768873869747863341)
          ·
            refine ⟨894120288327701155448753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2384320768873869747863341 894120288327701155448753)
            ·
              refine ⟨670590216245775866586565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894120288327701155448753 670590216245775866586565)
              ·
                refine ⟨125735665546082974984981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 670590216245775866586565 125735665546082974984981)
                ·
                  rfl

theorem cell19_413217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_413217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413217 prefixEnd_413217 := by exact prefixLift 413217
  have htrace : WordTrace (prefixWord ++ tailWord_413217) baseStart_413217 baseEnd_413217 := by
    simpa [prefixWord, tailWord_413217, baseEnd_413217] using wordTrace_append hprefix tailTrace_413217
  have hstable : (prefixWord ++ tailWord_413217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413217).length < 2 ^ (prefixWord ++ tailWord_413217).sum := by decide
  have hdescent : baseEnd_413217 < baseStart_413217 := by decide
  rcases family_descends (prefixWord ++ tailWord_413217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413255 : List Nat := [1, 1, 4, 1, 6, 6]
def baseStart_413255 : Nat := 118140960795 + 413255 * 2 ^ 59
def prefixEnd_413255 : Nat := 4983230072969 + 3 ^ 40 * 413255 * 2
def baseEnd_413255 : Nat := 13971914263301127348937

theorem tailTrace_413255 : CollatzResearch.WordTrace tailWord_413255 prefixEnd_413255 13971914263301127348937 := by
  unfold tailWord_413255
  simp only [CollatzResearch.WordTrace]
  refine ⟨15072648117855188180081219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10048432078570125453387479 15072648117855188180081219)
  ·
    refine ⟨22608972176782782270121829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15072648117855188180081219 22608972176782782270121829)
    ·
      refine ⟨4239182283146771675647843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22608972176782782270121829 4239182283146771675647843)
      ·
        refine ⟨6358773424720157513471765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239182283146771675647843 6358773424720157513471765)
        ·
          refine ⟨298067504283757383443989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6358773424720157513471765 298067504283757383443989)
          ·
            refine ⟨13971914263301127348937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 298067504283757383443989 13971914263301127348937)
            ·
              rfl

theorem cell19_413255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_413255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413255 prefixEnd_413255 := by exact prefixLift 413255
  have htrace : WordTrace (prefixWord ++ tailWord_413255) baseStart_413255 baseEnd_413255 := by
    simpa [prefixWord, tailWord_413255, baseEnd_413255] using wordTrace_append hprefix tailTrace_413255
  have hstable : (prefixWord ++ tailWord_413255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413255).length < 2 ^ (prefixWord ++ tailWord_413255).sum := by decide
  have hdescent : baseEnd_413255 < baseStart_413255 := by decide
  rcases family_descends (prefixWord ++ tailWord_413255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413348 : List Nat := [2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_413348 : Nat := 118140960795 + 413348 * 2 ^ 59
def prefixEnd_413348 : Nat := 4983230072969 + 3 ^ 40 * 413348 * 2
def baseEnd_413348 : Nat := 125775526859113486073513

theorem tailTrace_413348 : CollatzResearch.WordTrace tailWord_413348 prefixEnd_413348 125775526859113486073513 := by
  unfold tailWord_413348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538020053259132531608349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10050693404345510042144465 7538020053259132531608349)
  ·
    refine ⟨2826757519972174699353131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7538020053259132531608349 2826757519972174699353131)
    ·
      refine ⟨4240136279958262049029697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826757519972174699353131 4240136279958262049029697)
      ·
        refine ⟨3180102209968696536772273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4240136279958262049029697 3180102209968696536772273)
        ·
          refine ⟨2385076657476522402579205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180102209968696536772273 2385076657476522402579205)
          ·
            refine ⟨447201873276847950483601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2385076657476522402579205 447201873276847950483601)
            ·
              refine ⟨335401404957635962862701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447201873276847950483601 335401404957635962862701)
              ·
                refine ⟨125775526859113486073513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335401404957635962862701 125775526859113486073513)
                ·
                  rfl

theorem cell19_413348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_413348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413348 prefixEnd_413348 := by exact prefixLift 413348
  have htrace : WordTrace (prefixWord ++ tailWord_413348) baseStart_413348 baseEnd_413348 := by
    simpa [prefixWord, tailWord_413348, baseEnd_413348] using wordTrace_append hprefix tailTrace_413348
  have hstable : (prefixWord ++ tailWord_413348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413348).length < 2 ^ (prefixWord ++ tailWord_413348).sum := by decide
  have hdescent : baseEnd_413348 < baseStart_413348 := by decide
  rcases family_descends (prefixWord ++ tailWord_413348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413517 : List Nat := [1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_413517 : Nat := 118140960795 + 413517 * 2 ^ 59
def prefixEnd_413517 : Nat := 4983230072969 + 3 ^ 40 * 413517 * 2
def baseEnd_413517 : Nat := 125826950995771168317497

theorem tailTrace_413517 : CollatzResearch.WordTrace tailWord_413517 prefixEnd_413517 125826950995771168317497 := by
  unfold tailWord_413517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15082204042906006926118805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10054802695270671284079203 15082204042906006926118805)
  ·
    refine ⟨706978314511219074661819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15082204042906006926118805 706978314511219074661819)
    ·
      refine ⟨1060467471766828611992729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706978314511219074661819 1060467471766828611992729)
      ·
        refine ⟨795350603825121458994547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1060467471766828611992729 795350603825121458994547)
        ·
          refine ⟨1193025905737682188491821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795350603825121458994547 1193025905737682188491821)
          ·
            refine ⟨447384714651630820684433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1193025905737682188491821 447384714651630820684433)
            ·
              refine ⟨335538535988723115513325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447384714651630820684433 335538535988723115513325)
              ·
                refine ⟨125826950995771168317497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335538535988723115513325 125826950995771168317497)
                ·
                  rfl

theorem cell19_413517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_413517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413517 prefixEnd_413517 := by exact prefixLift 413517
  have htrace : WordTrace (prefixWord ++ tailWord_413517) baseStart_413517 baseEnd_413517 := by
    simpa [prefixWord, tailWord_413517, baseEnd_413517] using wordTrace_append hprefix tailTrace_413517
  have hstable : (prefixWord ++ tailWord_413517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413517).length < 2 ^ (prefixWord ++ tailWord_413517).sum := by decide
  have hdescent : baseEnd_413517 < baseStart_413517 := by decide
  rcases family_descends (prefixWord ++ tailWord_413517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413521 : List Nat := [1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_413521 : Nat := 118140960795 + 413521 * 2 ^ 59
def prefixEnd_413521 : Nat := 4983230072969 + 3 ^ 40 * 413521 * 2
def baseEnd_413521 : Nat := 125828168135100344228597

theorem tailTrace_413521 : CollatzResearch.WordTrace tailWord_413521 prefixEnd_413521 125828168135100344228597 := by
  unfold tailWord_413521
  simp only [CollatzResearch.WordTrace]
  refine ⟨15082349934891515609264417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10054899956594343739509611 15082349934891515609264417)
  ·
    refine ⟨11311762451168636706948313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15082349934891515609264417 11311762451168636706948313)
    ·
      refine ⟨8483821838376477530211235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11311762451168636706948313 8483821838376477530211235)
      ·
        refine ⟨12725732757564716295316853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483821838376477530211235 12725732757564716295316853)
        ·
          refine ⟨1193037446021692152685955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12725732757564716295316853 1193037446021692152685955)
          ·
            refine ⟨1789556169032538229028933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193037446021692152685955 1789556169032538229028933)
            ·
              refine ⟨335541781693600917942925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1789556169032538229028933 335541781693600917942925)
              ·
                refine ⟨125828168135100344228597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335541781693600917942925 125828168135100344228597)
                ·
                  rfl

theorem cell19_413521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_413521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413521 prefixEnd_413521 := by exact prefixLift 413521
  have htrace : WordTrace (prefixWord ++ tailWord_413521) baseStart_413521 baseEnd_413521 := by
    simpa [prefixWord, tailWord_413521, baseEnd_413521] using wordTrace_append hprefix tailTrace_413521
  have hstable : (prefixWord ++ tailWord_413521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413521).length < 2 ^ (prefixWord ++ tailWord_413521).sum := by decide
  have hdescent : baseEnd_413521 < baseStart_413521 := by decide
  rcases family_descends (prefixWord ++ tailWord_413521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413540 : List Nat := [2, 3, 1, 1, 5, 2, 5]
def baseStart_413540 : Nat := 118140960795 + 413540 * 2 ^ 59
def prefixEnd_413540 : Nat := 4983230072969 + 3 ^ 40 * 413540 * 2
def baseEnd_413540 : Nat := 41944649848971309935441

theorem tailTrace_413540 : CollatzResearch.WordTrace tailWord_413540 prefixEnd_413540 41944649848971309935441 := by
  unfold tailWord_413540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541521460911340927103037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10055361947881787902804049 7541521460911340927103037)
  ·
    refine ⟨2828070547841752847663639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7541521460911340927103037 2828070547841752847663639)
    ·
      refine ⟨4242105821762629271495459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828070547841752847663639 4242105821762629271495459)
      ·
        refine ⟨6363158732643943907243189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242105821762629271495459 6363158732643943907243189)
        ·
          refine ⟨596546131185369741304049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6363158732643943907243189 596546131185369741304049)
          ·
            refine ⟨447409598389027305978037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596546131185369741304049 447409598389027305978037)
            ·
              refine ⟨41944649848971309935441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447409598389027305978037 41944649848971309935441)
              ·
                rfl

theorem cell19_413540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_413540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413540 prefixEnd_413540 := by exact prefixLift 413540
  have htrace : WordTrace (prefixWord ++ tailWord_413540) baseStart_413540 baseEnd_413540 := by
    simpa [prefixWord, tailWord_413540, baseEnd_413540] using wordTrace_append hprefix tailTrace_413540
  have hstable : (prefixWord ++ tailWord_413540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413540).length < 2 ^ (prefixWord ++ tailWord_413540).sum := by decide
  have hdescent : baseEnd_413540 < baseStart_413540 := by decide
  rcases family_descends (prefixWord ++ tailWord_413540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413561 : List Nat := [1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_413561 : Nat := 118140960795 + 413561 * 2 ^ 59
def prefixEnd_413561 : Nat := 4983230072969 + 3 ^ 40 * 413561 * 2
def baseEnd_413561 : Nat := 125840339528392103339599

theorem tailTrace_413561 : CollatzResearch.WordTrace tailWord_413561 prefixEnd_413561 125840339528392103339599 := by
  unfold tailWord_413561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15083808854746602440720537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10055872569831068293813691 15083808854746602440720537)
  ·
    refine ⟨11312856641059951830540403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15083808854746602440720537 11312856641059951830540403)
    ·
      refine ⟨16969284961589927745810605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11312856641059951830540403 16969284961589927745810605)
      ·
        refine ⟨6363481860596222904678977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16969284961589927745810605 6363481860596222904678977)
        ·
          refine ⟨4772611395447167178509233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6363481860596222904678977 4772611395447167178509233)
          ·
            refine ⟨3579458546585375383881925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4772611395447167178509233 3579458546585375383881925)
            ·
              refine ⟨671148477484757884477861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3579458546585375383881925 671148477484757884477861)
              ·
                refine ⟨125840339528392103339599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671148477484757884477861 125840339528392103339599)
                ·
                  rfl

theorem cell19_413561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_413561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413561 prefixEnd_413561 := by exact prefixLift 413561
  have htrace : WordTrace (prefixWord ++ tailWord_413561) baseStart_413561 baseEnd_413561 := by
    simpa [prefixWord, tailWord_413561, baseEnd_413561] using wordTrace_append hprefix tailTrace_413561
  have hstable : (prefixWord ++ tailWord_413561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413561).length < 2 ^ (prefixWord ++ tailWord_413561).sum := by decide
  have hdescent : baseEnd_413561 < baseStart_413561 := by decide
  rcases family_descends (prefixWord ++ tailWord_413561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413599 : List Nat := [1, 1, 2, 5, 3, 7]
def baseStart_413599 : Nat := 118140960795 + 413599 * 2 ^ 59
def prefixEnd_413599 : Nat := 4983230072969 + 3 ^ 40 * 413599 * 2
def baseEnd_413599 : Nat := 13983544705779919388339

theorem tailTrace_413599 : CollatzResearch.WordTrace tailWord_413599 prefixEnd_413599 13983544705779919388339 := by
  unfold tailWord_413599
  simp only [CollatzResearch.WordTrace]
  refine ⟨15085194828608934930603851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10056796552405956620402567 15085194828608934930603851)
  ·
    refine ⟨22627792242913402395905777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15085194828608934930603851 22627792242913402395905777)
    ·
      refine ⟨16970844182185051796929333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22627792242913402395905777 16970844182185051796929333)
      ·
        refine ⟨1591016642079848605962125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16970844182185051796929333 1591016642079848605962125)
        ·
          refine ⟨596631240779943227235797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1591016642079848605962125 596631240779943227235797)
          ·
            refine ⟨13983544705779919388339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 596631240779943227235797 13983544705779919388339)
            ·
              rfl

theorem cell19_413599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_413599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413599 prefixEnd_413599 := by exact prefixLift 413599
  have htrace : WordTrace (prefixWord ++ tailWord_413599) baseStart_413599 baseEnd_413599 := by
    simpa [prefixWord, tailWord_413599, baseEnd_413599] using wordTrace_append hprefix tailTrace_413599
  have hstable : (prefixWord ++ tailWord_413599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413599).length < 2 ^ (prefixWord ++ tailWord_413599).sum := by decide
  have hdescent : baseEnd_413599 < baseStart_413599 := by decide
  rcases family_descends (prefixWord ++ tailWord_413599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413715 : List Nat := [1, 1, 1, 2, 1, 4, 9]
def baseStart_413715 : Nat := 118140960795 + 413715 * 2 ^ 59
def prefixEnd_413715 : Nat := 4983230072969 + 3 ^ 40 * 413715 * 2
def baseEnd_413715 : Nat := 41962399797521791972319

theorem tailTrace_413715 : CollatzResearch.WordTrace tailWord_413715 prefixEnd_413715 41962399797521791972319 := by
  unfold tailWord_413715
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089425696188686741826599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10059617130792457827884399 15089425696188686741826599)
  ·
    refine ⟨22634138544283030112739899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15089425696188686741826599 22634138544283030112739899)
    ·
      refine ⟨33951207816424545169109849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22634138544283030112739899 33951207816424545169109849)
      ·
        refine ⟨25463405862318408876832387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33951207816424545169109849 25463405862318408876832387)
        ·
          refine ⟨38195108793477613315248581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25463405862318408876832387 38195108793477613315248581)
          ·
            refine ⟨7161582898777052496609109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38195108793477613315248581 7161582898777052496609109)
            ·
              refine ⟨41962399797521791972319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7161582898777052496609109 41962399797521791972319)
              ·
                rfl

theorem cell19_413715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_413715 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413715 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413715 prefixEnd_413715 := by exact prefixLift 413715
  have htrace : WordTrace (prefixWord ++ tailWord_413715) baseStart_413715 baseEnd_413715 := by
    simpa [prefixWord, tailWord_413715, baseEnd_413715] using wordTrace_append hprefix tailTrace_413715
  have hstable : (prefixWord ++ tailWord_413715).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413715).length < 2 ^ (prefixWord ++ tailWord_413715).sum := by decide
  have hdescent : baseEnd_413715 < baseStart_413715 := by decide
  rcases family_descends (prefixWord ++ tailWord_413715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413791 : List Nat := [1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_413791 : Nat := 118140960795 + 413791 * 2 ^ 59
def prefixEnd_413791 : Nat := 4983230072969 + 3 ^ 40 * 413791 * 2
def baseEnd_413791 : Nat := 125910325039819718227861

theorem tailTrace_413791 : CollatzResearch.WordTrace tailWord_413791 prefixEnd_413791 125910325039819718227861 := by
  unfold tailWord_413791
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092197643913351721593227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10061465095942234481062151 15092197643913351721593227)
  ·
    refine ⟨22638296465870027582389841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15092197643913351721593227 22638296465870027582389841)
    ·
      refine ⟨16978722349402520686792381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22638296465870027582389841 16978722349402520686792381)
      ·
        refine ⟨6367020881025945257547143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16978722349402520686792381 6367020881025945257547143)
        ·
          refine ⟨9550531321538917886320715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367020881025945257547143 9550531321538917886320715)
          ·
            refine ⟨14325796982308376829481073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550531321538917886320715 14325796982308376829481073)
            ·
              refine ⟨10744347736731282622110805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14325796982308376829481073 10744347736731282622110805)
              ·
                refine ⟨125910325039819718227861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10744347736731282622110805 125910325039819718227861)
                ·
                  rfl

theorem cell19_413791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_413791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413791 prefixEnd_413791 := by exact prefixLift 413791
  have htrace : WordTrace (prefixWord ++ tailWord_413791) baseStart_413791 baseEnd_413791 := by
    simpa [prefixWord, tailWord_413791, baseEnd_413791] using wordTrace_append hprefix tailTrace_413791
  have hstable : (prefixWord ++ tailWord_413791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413791).length < 2 ^ (prefixWord ++ tailWord_413791).sum := by decide
  have hdescent : baseEnd_413791 < baseStart_413791 := by decide
  rcases family_descends (prefixWord ++ tailWord_413791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413806 : List Nat := [4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_413806 : Nat := 118140960795 + 413806 * 2 ^ 59
def prefixEnd_413806 : Nat := 4983230072969 + 3 ^ 40 * 413806 * 2
def baseEnd_413806 : Nat := 125914889312304127894487

theorem tailTrace_413806 : CollatzResearch.WordTrace tailWord_413806 prefixEnd_413806 125914889312304127894487 := by
  unfold tailWord_413806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886593092357376160423659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10061829825906006188926181 1886593092357376160423659)
  ·
    refine ⟨2829889638536064240635489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1886593092357376160423659 2829889638536064240635489)
    ·
      refine ⟨2122417228902048180476617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2829889638536064240635489 2122417228902048180476617)
      ·
        refine ⟨1591812921676536135357463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2122417228902048180476617 1591812921676536135357463)
        ·
          refine ⟨2387719382514804203036195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591812921676536135357463 2387719382514804203036195)
          ·
            refine ⟨3581579073772206304554293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387719382514804203036195 3581579073772206304554293)
            ·
              refine ⟨335773038166144341051965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3581579073772206304554293 335773038166144341051965)
              ·
                refine ⟨125914889312304127894487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335773038166144341051965 125914889312304127894487)
                ·
                  rfl

theorem cell19_413806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_413806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413806 prefixEnd_413806 := by exact prefixLift 413806
  have htrace : WordTrace (prefixWord ++ tailWord_413806) baseStart_413806 baseEnd_413806 := by
    simpa [prefixWord, tailWord_413806, baseEnd_413806] using wordTrace_append hprefix tailTrace_413806
  have hstable : (prefixWord ++ tailWord_413806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413806).length < 2 ^ (prefixWord ++ tailWord_413806).sum := by decide
  have hdescent : baseEnd_413806 < baseStart_413806 := by decide
  rcases family_descends (prefixWord ++ tailWord_413806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413863 : List Nat := [1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_413863 : Nat := 118140960795 + 413863 * 2 ^ 59
def prefixEnd_413863 : Nat := 4983230072969 + 3 ^ 40 * 413863 * 2
def baseEnd_413863 : Nat := 125932233547744884627665

theorem tailTrace_413863 : CollatzResearch.WordTrace tailWord_413863 prefixEnd_413863 125932233547744884627665 := by
  unfold tailWord_413863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15094823699652508018214243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10063215799768338678809495 15094823699652508018214243)
  ·
    refine ⟨22642235549478762027321365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15094823699652508018214243 22642235549478762027321365)
    ·
      refine ⟨1061354791381816970030689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22642235549478762027321365 1061354791381816970030689)
      ·
        refine ⟨796016093536362727523017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061354791381816970030689 796016093536362727523017)
        ·
          refine ⟨597012070152272045642263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796016093536362727523017 597012070152272045642263)
          ·
            refine ⟨895518105228408068463395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597012070152272045642263 895518105228408068463395)
            ·
              refine ⟨1343277157842612102695093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895518105228408068463395 1343277157842612102695093)
              ·
                refine ⟨125932233547744884627665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343277157842612102695093 125932233547744884627665)
                ·
                  rfl

theorem cell19_413863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_413863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413863 prefixEnd_413863 := by exact prefixLift 413863
  have htrace : WordTrace (prefixWord ++ tailWord_413863) baseStart_413863 baseEnd_413863 := by
    simpa [prefixWord, tailWord_413863, baseEnd_413863] using wordTrace_append hprefix tailTrace_413863
  have hstable : (prefixWord ++ tailWord_413863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413863).length < 2 ^ (prefixWord ++ tailWord_413863).sum := by decide
  have hdescent : baseEnd_413863 < baseStart_413863 := by decide
  rcases family_descends (prefixWord ++ tailWord_413863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413876 : List Nat := [2, 5, 3, 1, 2, 1, 5]
def baseStart_413876 : Nat := 118140960795 + 413876 * 2 ^ 59
def prefixEnd_413876 : Nat := 4983230072969 + 3 ^ 40 * 413876 * 2
def baseEnd_413876 : Nat := 41978729750188235446247

theorem tailTrace_413876 : CollatzResearch.WordTrace tailWord_413876 prefixEnd_413876 41978729750188235446247 := by
  unfold tailWord_413876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547648924302705619218741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10063531899070274158958321 7547648924302705619218741)
  ·
    refine ⟨707592086653378651801757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7547648924302705619218741 707592086653378651801757)
    ·
      refine ⟨265347032495016994425659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 707592086653378651801757 265347032495016994425659)
      ·
        refine ⟨398020548742525491638489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265347032495016994425659 398020548742525491638489)
        ·
          refine ⟨298515411556894118728867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398020548742525491638489 298515411556894118728867)
          ·
            refine ⟨447773117335341178093301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298515411556894118728867 447773117335341178093301)
            ·
              refine ⟨41978729750188235446247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447773117335341178093301 41978729750188235446247)
              ·
                rfl

theorem cell19_413876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_413876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413876 prefixEnd_413876 := by exact prefixLift 413876
  have htrace : WordTrace (prefixWord ++ tailWord_413876) baseStart_413876 baseEnd_413876 := by
    simpa [prefixWord, tailWord_413876, baseEnd_413876] using wordTrace_append hprefix tailTrace_413876
  have hstable : (prefixWord ++ tailWord_413876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413876).length < 2 ^ (prefixWord ++ tailWord_413876).sum := by decide
  have hdescent : baseEnd_413876 < baseStart_413876 := by decide
  rcases family_descends (prefixWord ++ tailWord_413876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413905 : List Nat := [1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_413905 : Nat := 118140960795 + 413905 * 2 ^ 59
def prefixEnd_413905 : Nat := 4983230072969 + 3 ^ 40 * 413905 * 2
def baseEnd_413905 : Nat := 125945013510701231694217

theorem tailTrace_413905 : CollatzResearch.WordTrace tailWord_413905 prefixEnd_413905 125945013510701231694217 := by
  unfold tailWord_413905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15096355565500349191243169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10064237043666899460828779 15096355565500349191243169)
  ·
    refine ⟨11322266674125261893432377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15096355565500349191243169 11322266674125261893432377)
    ·
      refine ⟨8491700005593946420074283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11322266674125261893432377 8491700005593946420074283)
      ·
        refine ⟨12737550008390919630111425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491700005593946420074283 12737550008390919630111425)
        ·
          refine ⟨9553162506293189722583569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12737550008390919630111425 9553162506293189722583569)
          ·
            refine ⟨7164871879719892291937677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9553162506293189722583569 7164871879719892291937677)
            ·
              refine ⟨2686826954894959609476629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7164871879719892291937677 2686826954894959609476629)
              ·
                refine ⟨125945013510701231694217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2686826954894959609476629 125945013510701231694217)
                ·
                  rfl

theorem cell19_413905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_413905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413905 prefixEnd_413905 := by exact prefixLift 413905
  have htrace : WordTrace (prefixWord ++ tailWord_413905) baseStart_413905 baseEnd_413905 := by
    simpa [prefixWord, tailWord_413905, baseEnd_413905] using wordTrace_append hprefix tailTrace_413905
  have hstable : (prefixWord ++ tailWord_413905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413905).length < 2 ^ (prefixWord ++ tailWord_413905).sum := by decide
  have hdescent : baseEnd_413905 < baseStart_413905 := by decide
  rcases family_descends (prefixWord ++ tailWord_413905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413956 : List Nat := [2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_413956 : Nat := 118140960795 + 413956 * 2 ^ 59
def prefixEnd_413956 : Nat := 4983230072969 + 3 ^ 40 * 413956 * 2
def baseEnd_413956 : Nat := 125960532037148224560745

theorem tailTrace_413956 : CollatzResearch.WordTrace tailWord_413956 prefixEnd_413956 125960532037148224560745 := by
  unfold tailWord_413956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549107844157792450674861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10065477125543723267566481 7549107844157792450674861)
  ·
    refine ⟨2830915441559172169003073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7549107844157792450674861 2830915441559172169003073)
    ·
      refine ⟨2123186581169379126752305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2830915441559172169003073 2123186581169379126752305)
      ·
        refine ⟨1592389935877034345064229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2123186581169379126752305 1592389935877034345064229)
        ·
          refine ⟨298573112976943939699543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1592389935877034345064229 298573112976943939699543)
          ·
            refine ⟨447859669465415909549315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298573112976943939699543 447859669465415909549315)
            ·
              refine ⟨671789504198123864323973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447859669465415909549315 671789504198123864323973)
              ·
                refine ⟨125960532037148224560745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671789504198123864323973 125960532037148224560745)
                ·
                  rfl

theorem cell19_413956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_413956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413956 prefixEnd_413956 := by exact prefixLift 413956
  have htrace : WordTrace (prefixWord ++ tailWord_413956) baseStart_413956 baseEnd_413956 := by
    simpa [prefixWord, tailWord_413956, baseEnd_413956] using wordTrace_append hprefix tailTrace_413956
  have hstable : (prefixWord ++ tailWord_413956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413956).length < 2 ^ (prefixWord ++ tailWord_413956).sum := by decide
  have hdescent : baseEnd_413956 < baseStart_413956 := by decide
  rcases family_descends (prefixWord ++ tailWord_413956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413960 : List Nat := [2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_413960 : Nat := 118140960795 + 413960 * 2 ^ 59
def prefixEnd_413960 : Nat := 4983230072969 + 3 ^ 40 * 413960 * 2
def baseEnd_413960 : Nat := 125961749176477400471845

theorem tailTrace_413960 : CollatzResearch.WordTrace tailWord_413960 prefixEnd_413960 125961749176477400471845 := by
  unfold tailWord_413960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549180790150546792247667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10065574386867395722996889 7549180790150546792247667)
  ·
    refine ⟨11323771185225820188371501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7549180790150546792247667 11323771185225820188371501)
    ·
      refine ⟨4246414194459682570639313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11323771185225820188371501 4246414194459682570639313)
      ·
        refine ⟨3184810645844761927979485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4246414194459682570639313 3184810645844761927979485)
        ·
          refine ⟨1194303992191785722992307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3184810645844761927979485 1194303992191785722992307)
          ·
            refine ⟨1791455988287678584488461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194303992191785722992307 1791455988287678584488461)
            ·
              refine ⟨671795995607879469183173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1791455988287678584488461 671795995607879469183173)
              ·
                refine ⟨125961749176477400471845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671795995607879469183173 125961749176477400471845)
                ·
                  rfl

theorem cell19_413960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_413960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_413960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_413960 prefixEnd_413960 := by exact prefixLift 413960
  have htrace : WordTrace (prefixWord ++ tailWord_413960) baseStart_413960 baseEnd_413960 := by
    simpa [prefixWord, tailWord_413960, baseEnd_413960] using wordTrace_append hprefix tailTrace_413960
  have hstable : (prefixWord ++ tailWord_413960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413960).length < 2 ^ (prefixWord ++ tailWord_413960).sum := by decide
  have hdescent : baseEnd_413960 < baseStart_413960 := by decide
  rcases family_descends (prefixWord ++ tailWord_413960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414036 : List Nat := [2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_414036 : Nat := 118140960795 + 414036 * 2 ^ 59
def prefixEnd_414036 : Nat := 4983230072969 + 3 ^ 40 * 414036 * 2
def baseEnd_414036 : Nat := 125984874823731742782749

theorem tailTrace_414036 : CollatzResearch.WordTrace tailWord_414036 prefixEnd_414036 125984874823731742782749 := by
  unfold tailWord_414036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550566764012879282130981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10067422352017172376174641 7550566764012879282130981)
  ·
    refine ⟨1415731268252414865399559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7550566764012879282130981 1415731268252414865399559)
    ·
      refine ⟨2123596902378622298099339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415731268252414865399559 2123596902378622298099339)
      ·
        refine ⟨3185395353567933447149009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123596902378622298099339 3185395353567933447149009)
        ·
          refine ⟨2389046515175950085361757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185395353567933447149009 2389046515175950085361757)
          ·
            refine ⟨895892443190981282010659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2389046515175950085361757 895892443190981282010659)
            ·
              refine ⟨1343838664786471923015989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895892443190981282010659 1343838664786471923015989)
              ·
                refine ⟨125984874823731742782749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343838664786471923015989 125984874823731742782749)
                ·
                  rfl

theorem cell19_414036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_414036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414036 prefixEnd_414036 := by exact prefixLift 414036
  have htrace : WordTrace (prefixWord ++ tailWord_414036) baseStart_414036 baseEnd_414036 := by
    simpa [prefixWord, tailWord_414036, baseEnd_414036] using wordTrace_append hprefix tailTrace_414036
  have hstable : (prefixWord ++ tailWord_414036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414036).length < 2 ^ (prefixWord ++ tailWord_414036).sum := by decide
  have hdescent : baseEnd_414036 < baseStart_414036 := by decide
  rcases family_descends (prefixWord ++ tailWord_414036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414055 : List Nat := [1, 1, 5, 1, 3, 3, 5]
def baseStart_414055 : Nat := 118140960795 + 414055 * 2 ^ 59
def prefixEnd_414055 : Nat := 4983230072969 + 3 ^ 40 * 414055 * 2
def baseEnd_414055 : Nat := 41996885411848442786825

theorem tailTrace_414055 : CollatzResearch.WordTrace tailWord_414055 prefixEnd_414055 41996885411848442786825 := by
  unfold tailWord_414055
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101826514956924809203619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10067884343304616539469079 15101826514956924809203619)
  ·
    refine ⟨22652739772435387213805429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15101826514956924809203619 22652739772435387213805429)
    ·
      refine ⟨2123694353665817551294259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22652739772435387213805429 2123694353665817551294259)
      ·
        refine ⟨3185541530498726326941389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123694353665817551294259 3185541530498726326941389)
        ·
          refine ⟨1194578073937022372603021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3185541530498726326941389 1194578073937022372603021)
          ·
            refine ⟨447966777726383389726133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1194578073937022372603021 447966777726383389726133)
            ·
              refine ⟨41996885411848442786825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447966777726383389726133 41996885411848442786825)
              ·
                rfl

theorem cell19_414055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_414055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414055 prefixEnd_414055 := by exact prefixLift 414055
  have htrace : WordTrace (prefixWord ++ tailWord_414055) baseStart_414055 baseEnd_414055 := by
    simpa [prefixWord, tailWord_414055, baseEnd_414055] using wordTrace_append hprefix tailTrace_414055
  have hstable : (prefixWord ++ tailWord_414055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414055).length < 2 ^ (prefixWord ++ tailWord_414055).sum := by decide
  have hdescent : baseEnd_414055 < baseStart_414055 := by decide
  rcases family_descends (prefixWord ++ tailWord_414055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414070 : List Nat := [5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_414070 : Nat := 118140960795 + 414070 * 2 ^ 59
def prefixEnd_414070 : Nat := 4983230072969 + 3 ^ 40 * 414070 * 2
def baseEnd_414070 : Nat := 125995220508029738027101

theorem tailTrace_414070 : CollatzResearch.WordTrace tailWord_414070 prefixEnd_414070 125995220508029738027101 := by
  unfold tailWord_414070
  simp only [CollatzResearch.WordTrace]
  refine ⟨943898350618911398187479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10068249073268388247333109 943898350618911398187479)
  ·
    refine ⟨1415847525928367097281219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943898350618911398187479 1415847525928367097281219)
    ·
      refine ⟨2123771288892550645921829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415847525928367097281219 2123771288892550645921829)
      ·
        refine ⟨398207116667353246110343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2123771288892550645921829 398207116667353246110343)
        ·
          refine ⟨597310675001029869165515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398207116667353246110343 597310675001029869165515)
          ·
            refine ⟨895966012501544803748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597310675001029869165515 895966012501544803748273)
            ·
              refine ⟨671974509376158602811205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895966012501544803748273 671974509376158602811205)
              ·
                refine ⟨125995220508029738027101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671974509376158602811205 125995220508029738027101)
                ·
                  rfl

theorem cell19_414070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_414070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414070 prefixEnd_414070 := by exact prefixLift 414070
  have htrace : WordTrace (prefixWord ++ tailWord_414070) baseStart_414070 baseEnd_414070 := by
    simpa [prefixWord, tailWord_414070, baseEnd_414070] using wordTrace_append hprefix tailTrace_414070
  have hstable : (prefixWord ++ tailWord_414070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414070).length < 2 ^ (prefixWord ++ tailWord_414070).sum := by decide
  have hdescent : baseEnd_414070 < baseStart_414070 := by decide
  rcases family_descends (prefixWord ++ tailWord_414070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414266 : List Nat := [3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_414266 : Nat := 118140960795 + 414266 * 2 ^ 59
def prefixEnd_414266 : Nat := 4983230072969 + 3 ^ 40 * 414266 * 2
def baseEnd_414266 : Nat := 126054860335159357671011

theorem tailTrace_414266 : CollatzResearch.WordTrace tailWord_414266 prefixEnd_414266 126054860335159357671011 := by
  unfold tailWord_414266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777380579298126961283663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10073014878128338563423101 3777380579298126961283663)
  ·
    refine ⟨5666070868947190441925495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777380579298126961283663 5666070868947190441925495)
    ·
      refine ⟨8499106303420785662888243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666070868947190441925495 8499106303420785662888243)
      ·
        refine ⟨12748659455131178494332365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499106303420785662888243 12748659455131178494332365)
        ·
          refine ⟨4780747295674191935374637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12748659455131178494332365 4780747295674191935374637)
          ·
            refine ⟨1792780235877821975765489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4780747295674191935374637 1792780235877821975765489)
            ·
              refine ⟨1344585176908366481824117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792780235877821975765489 1344585176908366481824117)
              ·
                refine ⟨126054860335159357671011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1344585176908366481824117 126054860335159357671011)
                ·
                  rfl

theorem cell19_414266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_414266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414266 prefixEnd_414266 := by exact prefixLift 414266
  have htrace : WordTrace (prefixWord ++ tailWord_414266) baseStart_414266 baseEnd_414266 := by
    simpa [prefixWord, tailWord_414266, baseEnd_414266] using wordTrace_append hprefix tailTrace_414266
  have hstable : (prefixWord ++ tailWord_414266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414266).length < 2 ^ (prefixWord ++ tailWord_414266).sum := by decide
  have hdescent : baseEnd_414266 < baseStart_414266 := by decide
  rcases family_descends (prefixWord ++ tailWord_414266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414300 : List Nat := [2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_414300 : Nat := 118140960795 + 414300 * 2 ^ 59
def prefixEnd_414300 : Nat := 4983230072969 + 3 ^ 40 * 414300 * 2
def baseEnd_414300 : Nat := 126065206019457352915363

theorem tailTrace_414300 : CollatzResearch.WordTrace tailWord_414300 prefixEnd_414300 126065206019457352915363 := by
  unfold tailWord_414300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555381199534665825936177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10073841599379554434581569 7555381199534665825936177)
  ·
    refine ⟨5666535899650999369452133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7555381199534665825936177 5666535899650999369452133)
    ·
      refine ⟨1062475481184562381772275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5666535899650999369452133 1062475481184562381772275)
      ·
        refine ⟨1593713221776843572658413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062475481184562381772275 1593713221776843572658413)
        ·
          refine ⟨597642458166316339746905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1593713221776843572658413 597642458166316339746905)
          ·
            refine ⟨448231843624737254810179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597642458166316339746905 448231843624737254810179)
            ·
              refine ⟨672347765437105882215269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448231843624737254810179 672347765437105882215269)
              ·
                refine ⟨126065206019457352915363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672347765437105882215269 126065206019457352915363)
                ·
                  rfl

theorem cell19_414300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_414300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414300 prefixEnd_414300 := by exact prefixLift 414300
  have htrace : WordTrace (prefixWord ++ tailWord_414300) baseStart_414300 baseEnd_414300 := by
    simpa [prefixWord, tailWord_414300, baseEnd_414300] using wordTrace_append hprefix tailTrace_414300
  have hstable : (prefixWord ++ tailWord_414300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414300).length < 2 ^ (prefixWord ++ tailWord_414300).sum := by decide
  have hdescent : baseEnd_414300 < baseStart_414300 := by decide
  rcases family_descends (prefixWord ++ tailWord_414300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414304 : List Nat := [2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_414304 : Nat := 118140960795 + 414304 * 2 ^ 59
def prefixEnd_414304 : Nat := 4983230072969 + 3 ^ 40 * 414304 * 2
def baseEnd_414304 : Nat := 126066423158786528826463

theorem tailTrace_414304 : CollatzResearch.WordTrace tailWord_414304 prefixEnd_414304 126066423158786528826463 := by
  unfold tailWord_414304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555454145527420167508983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10073938860703226890011977 7555454145527420167508983)
  ·
    refine ⟨11333181218291130251263475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7555454145527420167508983 11333181218291130251263475)
    ·
      refine ⟨16999771827436695376895213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11333181218291130251263475 16999771827436695376895213)
      ·
        refine ⟨6374914435288760766335705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16999771827436695376895213 6374914435288760766335705)
        ·
          refine ⟨4781185826466570574751779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6374914435288760766335705 4781185826466570574751779)
          ·
            refine ⟨7171778739699855862127669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781185826466570574751779 7171778739699855862127669)
            ·
              refine ⟨672354256846861487074469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7171778739699855862127669 672354256846861487074469)
              ·
                refine ⟨126066423158786528826463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672354256846861487074469 126066423158786528826463)
                ·
                  rfl

theorem cell19_414304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_414304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414304 prefixEnd_414304 := by exact prefixLift 414304
  have htrace : WordTrace (prefixWord ++ tailWord_414304) baseStart_414304 baseEnd_414304 := by
    simpa [prefixWord, tailWord_414304, baseEnd_414304] using wordTrace_append hprefix tailTrace_414304
  have hstable : (prefixWord ++ tailWord_414304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414304).length < 2 ^ (prefixWord ++ tailWord_414304).sum := by decide
  have hdescent : baseEnd_414304 < baseStart_414304 := by decide
  rcases family_descends (prefixWord ++ tailWord_414304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414399 : List Nat := [1, 1, 2, 2, 2, 6, 5]
def baseStart_414399 : Nat := 118140960795 + 414399 * 2 ^ 59
def prefixEnd_414399 : Nat := 4983230072969 + 3 ^ 40 * 414399 * 2
def baseEnd_414399 : Nat := 42031776739284818905031

theorem tailTrace_414399 : CollatzResearch.WordTrace tailWord_414399 prefixEnd_414399 42031776739284818905031 := by
  unfold tailWord_414399
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114373225710671559726251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10076248817140447706484167 15114373225710671559726251)
  ·
    refine ⟨22671559838566007339589377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15114373225710671559726251 22671559838566007339589377)
    ·
      refine ⟨17003669878924505504692033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22671559838566007339589377 17003669878924505504692033)
      ·
        refine ⟨12752752409193379128519025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003669878924505504692033 12752752409193379128519025)
        ·
          refine ⟨9564564306895034346389269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12752752409193379128519025 9564564306895034346389269)
          ·
            refine ⟨448338951885704734986997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9564564306895034346389269 448338951885704734986997)
            ·
              refine ⟨42031776739284818905031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448338951885704734986997 42031776739284818905031)
              ·
                rfl

theorem cell19_414399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_414399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414399 prefixEnd_414399 := by exact prefixLift 414399
  have htrace : WordTrace (prefixWord ++ tailWord_414399) baseStart_414399 baseEnd_414399 := by
    simpa [prefixWord, tailWord_414399, baseEnd_414399] using wordTrace_append hprefix tailTrace_414399
  have hstable : (prefixWord ++ tailWord_414399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414399).length < 2 ^ (prefixWord ++ tailWord_414399).sum := by decide
  have hdescent : baseEnd_414399 < baseStart_414399 := by decide
  rcases family_descends (prefixWord ++ tailWord_414399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414437 : List Nat := [1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_414437 : Nat := 118140960795 + 414437 * 2 ^ 59
def prefixEnd_414437 : Nat := 4983230072969 + 3 ^ 40 * 414437 * 2
def baseEnd_414437 : Nat := 126106893041481627870545

theorem tailTrace_414437 : CollatzResearch.WordTrace tailWord_414437 prefixEnd_414437 126106893041481627870545 := by
  unfold tailWord_414437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15115759199573004049609565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10077172799715336033073043 15115759199573004049609565)
  ·
    refine ⟨5668409699839876518603587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15115759199573004049609565 5668409699839876518603587)
    ·
      refine ⟨8502614549759814777905381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668409699839876518603587 8502614549759814777905381)
      ·
        refine ⟨1594240228079965270857259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8502614549759814777905381 1594240228079965270857259)
        ·
          refine ⟨2391360342119947906285889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594240228079965270857259 2391360342119947906285889)
          ·
            refine ⟨1793520256589960929714417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391360342119947906285889 1793520256589960929714417)
            ·
              refine ⟨1345140192442470697285813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793520256589960929714417 1345140192442470697285813)
              ·
                refine ⟨126106893041481627870545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1345140192442470697285813 126106893041481627870545)
                ·
                  rfl

theorem cell19_414437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_414437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414437 prefixEnd_414437 := by exact prefixLift 414437
  have htrace : WordTrace (prefixWord ++ tailWord_414437) baseStart_414437 baseEnd_414437 := by
    simpa [prefixWord, tailWord_414437, baseEnd_414437] using wordTrace_append hprefix tailTrace_414437
  have hstable : (prefixWord ++ tailWord_414437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414437).length < 2 ^ (prefixWord ++ tailWord_414437).sum := by decide
  have hdescent : baseEnd_414437 < baseStart_414437 := by decide
  rcases family_descends (prefixWord ++ tailWord_414437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414452 : List Nat := [2, 6, 1, 1, 2, 7]
def baseStart_414452 : Nat := 118140960795 + 414452 * 2 ^ 59
def prefixEnd_414452 : Nat := 4983230072969 + 3 ^ 40 * 414452 * 2
def baseEnd_414452 : Nat := 14012384145996226393019

theorem tailTrace_414452 : CollatzResearch.WordTrace tailWord_414452 prefixEnd_414452 14012384145996226393019 := by
  unfold tailWord_414452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558153147259330805702805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10077537529679107740937073 7558153147259330805702805)
  ·
    refine ⟨354288428777781131517319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7558153147259330805702805 354288428777781131517319)
    ·
      refine ⟨531432643166671697275979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354288428777781131517319 531432643166671697275979)
      ·
        refine ⟨797148964750007545913969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531432643166671697275979 797148964750007545913969)
        ·
          refine ⟨597861723562505659435477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797148964750007545913969 597861723562505659435477)
          ·
            refine ⟨14012384145996226393019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 597861723562505659435477 14012384145996226393019)
            ·
              rfl

theorem cell19_414452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_414452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414452 prefixEnd_414452 := by exact prefixLift 414452
  have htrace : WordTrace (prefixWord ++ tailWord_414452) baseStart_414452 baseEnd_414452 := by
    simpa [prefixWord, tailWord_414452, baseEnd_414452] using wordTrace_append hprefix tailTrace_414452
  have hstable : (prefixWord ++ tailWord_414452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414452).length < 2 ^ (prefixWord ++ tailWord_414452).sum := by decide
  have hdescent : baseEnd_414452 < baseStart_414452 := by decide
  rcases family_descends (prefixWord ++ tailWord_414452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414492 : List Nat := [2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_414492 : Nat := 118140960795 + 414492 * 2 ^ 59
def prefixEnd_414492 : Nat := 4983230072969 + 3 ^ 40 * 414492 * 2
def baseEnd_414492 : Nat := 126123628707257796648173

theorem tailTrace_414492 : CollatzResearch.WordTrace tailWord_414492 prefixEnd_414492 126123628707257796648173 := by
  unfold tailWord_414492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558882607186874221430865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10078510142915832295241153 7558882607186874221430865)
  ·
    refine ⟨5669161955390155666073149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7558882607186874221430865 5669161955390155666073149)
    ·
      refine ⟨2125935733271308374777431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5669161955390155666073149 2125935733271308374777431)
      ·
        refine ⟨3188903599906962562166147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125935733271308374777431 3188903599906962562166147)
        ·
          refine ⟨4783355399860443843249221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188903599906962562166147 4783355399860443843249221)
          ·
            refine ⟨896879137473833220609229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4783355399860443843249221 896879137473833220609229)
            ·
              refine ⟨336329676552687457728461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 896879137473833220609229 336329676552687457728461)
              ·
                refine ⟨126123628707257796648173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336329676552687457728461 126123628707257796648173)
                ·
                  rfl

theorem cell19_414492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_414492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414492 prefixEnd_414492 := by exact prefixLift 414492
  have htrace : WordTrace (prefixWord ++ tailWord_414492) baseStart_414492 baseEnd_414492 := by
    simpa [prefixWord, tailWord_414492, baseEnd_414492] using wordTrace_append hprefix tailTrace_414492
  have hstable : (prefixWord ++ tailWord_414492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414492).length < 2 ^ (prefixWord ++ tailWord_414492).sum := by decide
  have hdescent : baseEnd_414492 < baseStart_414492 := by decide
  rcases family_descends (prefixWord ++ tailWord_414492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414509 : List Nat := [1, 5, 3, 2, 1, 1, 6]
def baseStart_414509 : Nat := 118140960795 + 414509 * 2 ^ 59
def prefixEnd_414509 : Nat := 4983230072969 + 3 ^ 40 * 414509 * 2
def baseEnd_414509 : Nat := 42042933849802264756783

theorem tailTrace_414509 : CollatzResearch.WordTrace tailWord_414509 prefixEnd_414509 42042933849802264756783 := by
  unfold tailWord_414509
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118385255312160346230581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10078923503541440230820387 15118385255312160346230581)
  ·
    refine ⟨1417348617685515032459117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15118385255312160346230581 1417348617685515032459117)
    ·
      refine ⟨531505731632068137172169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1417348617685515032459117 531505731632068137172169)
      ·
        refine ⟨398629298724051102879127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531505731632068137172169 398629298724051102879127)
        ·
          refine ⟨597943948086076654318691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398629298724051102879127 597943948086076654318691)
          ·
            refine ⟨896915922129114981478037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597943948086076654318691 896915922129114981478037)
            ·
              refine ⟨42042933849802264756783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 896915922129114981478037 42042933849802264756783)
              ·
                rfl

theorem cell19_414509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_414509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414509 prefixEnd_414509 := by exact prefixLift 414509
  have htrace : WordTrace (prefixWord ++ tailWord_414509) baseStart_414509 baseEnd_414509 := by
    simpa [prefixWord, tailWord_414509, baseEnd_414509] using wordTrace_append hprefix tailTrace_414509
  have hstable : (prefixWord ++ tailWord_414509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414509).length < 2 ^ (prefixWord ++ tailWord_414509).sum := by decide
  have hdescent : baseEnd_414509 < baseStart_414509 := by decide
  rcases family_descends (prefixWord ++ tailWord_414509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414551 : List Nat := [1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_414551 : Nat := 118140960795 + 414551 * 2 ^ 59
def prefixEnd_414551 : Nat := 4983230072969 + 3 ^ 40 * 414551 * 2
def baseEnd_414551 : Nat := 126141581512363141336901

theorem tailTrace_414551 : CollatzResearch.WordTrace tailWord_414551 prefixEnd_414551 126141581512363141336901 := by
  unfold tailWord_414551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15119917121160001519259507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10079944747440001012839671 15119917121160001519259507)
  ·
    refine ⟨22679875681740002278889261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15119917121160001519259507 22679875681740002278889261)
    ·
      refine ⟨8504953380652500854583473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22679875681740002278889261 8504953380652500854583473)
      ·
        refine ⟨6378715035489375640937605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8504953380652500854583473 6378715035489375640937605)
        ·
          refine ⟨1196009069154257932675801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6378715035489375640937605 1196009069154257932675801)
          ·
            refine ⟨897006801865693449506851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196009069154257932675801 897006801865693449506851)
            ·
              refine ⟨1345510202798540174260277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897006801865693449506851 1345510202798540174260277)
              ·
                refine ⟨126141581512363141336901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1345510202798540174260277 126141581512363141336901)
                ·
                  rfl

theorem cell19_414551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_414551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414551 prefixEnd_414551 := by exact prefixLift 414551
  have htrace : WordTrace (prefixWord ++ tailWord_414551) baseStart_414551 baseEnd_414551 := by
    simpa [prefixWord, tailWord_414551, baseEnd_414551] using wordTrace_append hprefix tailTrace_414551
  have hstable : (prefixWord ++ tailWord_414551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414551).length < 2 ^ (prefixWord ++ tailWord_414551).sum := by decide
  have hdescent : baseEnd_414551 < baseStart_414551 := by decide
  rcases family_descends (prefixWord ++ tailWord_414551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414591 : List Nat := [1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_414591 : Nat := 118140960795 + 414591 * 2 ^ 59
def prefixEnd_414591 : Nat := 4983230072969 + 3 ^ 40 * 414591 * 2
def baseEnd_414591 : Nat := 126153752905654900447903

theorem tailTrace_414591 : CollatzResearch.WordTrace tailWord_414591 prefixEnd_414591 126153752905654900447903 := by
  unfold tailWord_414591
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121376041015088350715627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10080917360676725567143751 15121376041015088350715627)
  ·
    refine ⟨22682064061522632526073441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15121376041015088350715627 22682064061522632526073441)
    ·
      refine ⟨17011548046141974394555081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22682064061522632526073441 17011548046141974394555081)
      ·
        refine ⟨12758661034606480795916311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17011548046141974394555081 12758661034606480795916311)
        ·
          refine ⟨19137991551909721193874467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12758661034606480795916311 19137991551909721193874467)
          ·
            refine ⟨28706987327864581790811701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19137991551909721193874467 28706987327864581790811701)
            ·
              refine ⟨2691280061987304542888597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28706987327864581790811701 2691280061987304542888597)
              ·
                refine ⟨126153752905654900447903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2691280061987304542888597 126153752905654900447903)
                ·
                  rfl

theorem cell19_414591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_414591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414591 prefixEnd_414591 := by exact prefixLift 414591
  have htrace : WordTrace (prefixWord ++ tailWord_414591) baseStart_414591 baseEnd_414591 := by
    simpa [prefixWord, tailWord_414591, baseEnd_414591] using wordTrace_append hprefix tailTrace_414591
  have hstable : (prefixWord ++ tailWord_414591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414591).length < 2 ^ (prefixWord ++ tailWord_414591).sum := by decide
  have hdescent : baseEnd_414591 < baseStart_414591 := by decide
  rcases family_descends (prefixWord ++ tailWord_414591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414741 : List Nat := [1, 3, 2, 1, 4, 3, 5]
def baseStart_414741 : Nat := 118140960795 + 414741 * 2 ^ 59
def prefixEnd_414741 : Nat := 4983230072969 + 3 ^ 40 * 414741 * 2
def baseEnd_414741 : Nat := 42066465210166332371387

theorem tailTrace_414741 : CollatzResearch.WordTrace tailWord_414741 prefixEnd_414741 42066465210166332371387 := by
  unfold tailWord_414741
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126846990471663968676077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10084564660314442645784051 15126846990471663968676077)
  ·
    refine ⟨5672567621426873988253529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15126846990471663968676077 5672567621426873988253529)
    ·
      refine ⟨4254425716070155491190147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5672567621426873988253529 4254425716070155491190147)
      ·
        refine ⟨6381638574105233236785221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254425716070155491190147 6381638574105233236785221)
        ·
          refine ⟨1196557232644731231897229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6381638574105233236785221 1196557232644731231897229)
          ·
            refine ⟨448708962241774211961461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1196557232644731231897229 448708962241774211961461)
            ·
              refine ⟨42066465210166332371387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448708962241774211961461 42066465210166332371387)
              ·
                rfl

theorem cell19_414741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_414741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414741 prefixEnd_414741 := by exact prefixLift 414741
  have htrace : WordTrace (prefixWord ++ tailWord_414741) baseStart_414741 baseEnd_414741 := by
    simpa [prefixWord, tailWord_414741, baseEnd_414741] using wordTrace_append hprefix tailTrace_414741
  have hstable : (prefixWord ++ tailWord_414741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414741).length < 2 ^ (prefixWord ++ tailWord_414741).sum := by decide
  have hdescent : baseEnd_414741 < baseStart_414741 := by decide
  rcases family_descends (prefixWord ++ tailWord_414741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414813 : List Nat := [1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_414813 : Nat := 118140960795 + 414813 * 2 ^ 59
def prefixEnd_414813 : Nat := 4983230072969 + 3 ^ 40 * 414813 * 2
def baseEnd_414813 : Nat := 126221304138424163513965

theorem tailTrace_414813 : CollatzResearch.WordTrace tailWord_414813 prefixEnd_414813 126221304138424163513965 := by
  unfold tailWord_414813
  simp only [CollatzResearch.WordTrace]
  refine ⟨15129473046210820265297093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10086315364140546843531395 15129473046210820265297093)
  ·
    refine ⟨2836776196164528799743205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15129473046210820265297093 2836776196164528799743205)
    ·
      refine ⟨531895536780849149951851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2836776196164528799743205 531895536780849149951851)
      ·
        refine ⟨797843305171273724927777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531895536780849149951851 797843305171273724927777)
        ·
          refine ⟨598382478878455293695833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797843305171273724927777 598382478878455293695833)
          ·
            refine ⟨448786859158841470271875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598382478878455293695833 448786859158841470271875)
            ·
              refine ⟨673180288738262205407813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448786859158841470271875 673180288738262205407813)
              ·
                refine ⟨126221304138424163513965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673180288738262205407813 126221304138424163513965)
                ·
                  rfl

theorem cell19_414813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_414813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414813 prefixEnd_414813 := by exact prefixLift 414813
  have htrace : WordTrace (prefixWord ++ tailWord_414813) baseStart_414813 baseEnd_414813 := by
    simpa [prefixWord, tailWord_414813, baseEnd_414813] using wordTrace_append hprefix tailTrace_414813
  have hstable : (prefixWord ++ tailWord_414813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414813).length < 2 ^ (prefixWord ++ tailWord_414813).sum := by decide
  have hdescent : baseEnd_414813 < baseStart_414813 := by decide
  rcases family_descends (prefixWord ++ tailWord_414813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414857 : List Nat := [1, 2, 1, 1, 4, 4, 6]
def baseStart_414857 : Nat := 118140960795 + 414857 * 2 ^ 59
def prefixEnd_414857 : Nat := 4983230072969 + 3 ^ 40 * 414857 * 2
def baseEnd_414857 : Nat := 42078230890348366178689

theorem tailTrace_414857 : CollatzResearch.WordTrace tailWord_414857 prefixEnd_414857 42078230890348366178689 := by
  unfold tailWord_414857
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131077858051415779898825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10087385238700943853265883 15131077858051415779898825)
  ·
    refine ⟨11348308393538561834924119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15131077858051415779898825 11348308393538561834924119)
    ·
      refine ⟨17022462590307842752386179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348308393538561834924119 17022462590307842752386179)
      ·
        refine ⟨25533693885461764128579269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17022462590307842752386179 25533693885461764128579269)
        ·
          refine ⟨4787567603524080774108613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25533693885461764128579269 4787567603524080774108613)
          ·
            refine ⟨897668925660765145145365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4787567603524080774108613 897668925660765145145365)
            ·
              refine ⟨42078230890348366178689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 897668925660765145145365 42078230890348366178689)
              ·
                rfl

theorem cell19_414857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_414857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414857 prefixEnd_414857 := by exact prefixLift 414857
  have htrace : WordTrace (prefixWord ++ tailWord_414857) baseStart_414857 baseEnd_414857 := by
    simpa [prefixWord, tailWord_414857, baseEnd_414857] using wordTrace_append hprefix tailTrace_414857
  have hstable : (prefixWord ++ tailWord_414857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414857).length < 2 ^ (prefixWord ++ tailWord_414857).sum := by decide
  have hdescent : baseEnd_414857 < baseStart_414857 := by decide
  rcases family_descends (prefixWord ++ tailWord_414857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414912 : List Nat := [2, 1, 1, 2, 6, 2, 5]
def baseStart_414912 : Nat := 118140960795 + 414912 * 2 ^ 59
def prefixEnd_414912 : Nat := 4983230072969 + 3 ^ 40 * 414912 * 2
def baseEnd_414912 : Nat := 42083809445607089104565

theorem tailTrace_414912 : CollatzResearch.WordTrace tailWord_414912 prefixEnd_414912 42083809445607089104565 := by
  unfold tailWord_414912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566541936426080086575495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10088722581901440115433993 7566541936426080086575495)
  ·
    refine ⟨11349812904639120129863243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7566541936426080086575495 11349812904639120129863243)
    ·
      refine ⟨17024719356958680194794865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11349812904639120129863243 17024719356958680194794865)
      ·
        refine ⟨12768539517719010146096149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17024719356958680194794865 12768539517719010146096149)
        ·
          refine ⟨598525289893078600598257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12768539517719010146096149 598525289893078600598257)
          ·
            refine ⟨448893967419808950448693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598525289893078600598257 448893967419808950448693)
            ·
              refine ⟨42083809445607089104565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448893967419808950448693 42083809445607089104565)
              ·
                rfl

theorem cell19_414912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_414912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414912 prefixEnd_414912 := by exact prefixLift 414912
  have htrace : WordTrace (prefixWord ++ tailWord_414912) baseStart_414912 baseEnd_414912 := by
    simpa [prefixWord, tailWord_414912, baseEnd_414912] using wordTrace_append hprefix tailTrace_414912
  have hstable : (prefixWord ++ tailWord_414912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414912).length < 2 ^ (prefixWord ++ tailWord_414912).sum := by decide
  have hdescent : baseEnd_414912 < baseStart_414912 := by decide
  rcases family_descends (prefixWord ++ tailWord_414912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414952 : List Nat := [2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_414952 : Nat := 118140960795 + 414952 * 2 ^ 59
def prefixEnd_414952 : Nat := 4983230072969 + 3 ^ 40 * 414952 * 2
def baseEnd_414952 : Nat := 126263599730113026424697

theorem tailTrace_414952 : CollatzResearch.WordTrace tailWord_414952 prefixEnd_414952 126263599730113026424697 := by
  unfold tailWord_414952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567271396353623502303555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10089695195138164669738073 7567271396353623502303555)
  ·
    refine ⟨11350907094530435253455333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7567271396353623502303555 11350907094530435253455333)
    ·
      refine ⟨2128295080224456610022875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11350907094530435253455333 2128295080224456610022875)
      ·
        refine ⟨3192442620336684915034313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128295080224456610022875 3192442620336684915034313)
        ·
          refine ⟨2394331965252513686275735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3192442620336684915034313 2394331965252513686275735)
          ·
            refine ⟨3591497947878770529413603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394331965252513686275735 3591497947878770529413603)
            ·
              refine ⟨5387246921818155794120405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591497947878770529413603 5387246921818155794120405)
              ·
                refine ⟨126263599730113026424697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5387246921818155794120405 126263599730113026424697)
                ·
                  rfl

theorem cell19_414952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_414952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414952 prefixEnd_414952 := by exact prefixLift 414952
  have htrace : WordTrace (prefixWord ++ tailWord_414952) baseStart_414952 baseEnd_414952 := by
    simpa [prefixWord, tailWord_414952, baseEnd_414952] using wordTrace_append hprefix tailTrace_414952
  have hstable : (prefixWord ++ tailWord_414952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414952).length < 2 ^ (prefixWord ++ tailWord_414952).sum := by decide
  have hdescent : baseEnd_414952 < baseStart_414952 := by decide
  rcases family_descends (prefixWord ++ tailWord_414952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414988 : List Nat := [2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_414988 : Nat := 118140960795 + 414988 * 2 ^ 59
def prefixEnd_414988 : Nat := 4983230072969 + 3 ^ 40 * 414988 * 2
def baseEnd_414988 : Nat := 126274553984075609624599

theorem tailTrace_414988 : CollatzResearch.WordTrace tailWord_414988 prefixEnd_414988 126274553984075609624599 := by
  unfold tailWord_414988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567927910288412576458809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10090570547051216768611745 7567927910288412576458809)
  ·
    refine ⟨5675945932716309432344107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7567927910288412576458809 5675945932716309432344107)
    ·
      refine ⟨8513918899074464148516161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5675945932716309432344107 8513918899074464148516161)
      ·
        refine ⟨6385439174305848111387121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8513918899074464148516161 6385439174305848111387121)
        ·
          refine ⟨4789079380729386083540341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6385439174305848111387121 4789079380729386083540341)
          ·
            refine ⟨448976191943379945331907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4789079380729386083540341 448976191943379945331907)
            ·
              refine ⟨673464287915069917997861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448976191943379945331907 673464287915069917997861)
              ·
                refine ⟨126274553984075609624599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673464287915069917997861 126274553984075609624599)
                ·
                  rfl

theorem cell19_414988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_414988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_414988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_414988 prefixEnd_414988 := by exact prefixLift 414988
  have htrace : WordTrace (prefixWord ++ tailWord_414988) baseStart_414988 baseEnd_414988 := by
    simpa [prefixWord, tailWord_414988, baseEnd_414988] using wordTrace_append hprefix tailTrace_414988
  have hstable : (prefixWord ++ tailWord_414988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414988).length < 2 ^ (prefixWord ++ tailWord_414988).sum := by decide
  have hdescent : baseEnd_414988 < baseStart_414988 := by decide
  rcases family_descends (prefixWord ++ tailWord_414988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415005 : List Nat := [1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_415005 : Nat := 118140960795 + 415005 * 2 ^ 59
def prefixEnd_415005 : Nat := 4983230072969 + 3 ^ 40 * 415005 * 2
def baseEnd_415005 : Nat := 126279726826224607246775

theorem tailTrace_415005 : CollatzResearch.WordTrace tailWord_415005 prefixEnd_415005 126279726826224607246775 := by
  unfold tailWord_415005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136475861515237056286469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10090983907676824704190979 15136475861515237056286469)
  ·
    refine ⟨2838089224034106948053713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15136475861515237056286469 2838089224034106948053713)
    ·
      refine ⟨2128566918025580211040285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2838089224034106948053713 2128566918025580211040285)
      ·
        refine ⟨798212594259592579140107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2128566918025580211040285 798212594259592579140107)
        ·
          refine ⟨1197318891389388868710161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798212594259592579140107 1197318891389388868710161)
          ·
            refine ⟨897989168542041651532621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197318891389388868710161 897989168542041651532621)
            ·
              refine ⟨336745938203265619324733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897989168542041651532621 336745938203265619324733)
              ·
                refine ⟨126279726826224607246775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336745938203265619324733 126279726826224607246775)
                ·
                  rfl

theorem cell19_415005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_415005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415005 prefixEnd_415005 := by exact prefixLift 415005
  have htrace : WordTrace (prefixWord ++ tailWord_415005) baseStart_415005 baseEnd_415005 := by
    simpa [prefixWord, tailWord_415005, baseEnd_415005] using wordTrace_append hprefix tailTrace_415005
  have hstable : (prefixWord ++ tailWord_415005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415005).length < 2 ^ (prefixWord ++ tailWord_415005).sum := by decide
  have hdescent : baseEnd_415005 < baseStart_415005 := by decide
  rcases family_descends (prefixWord ++ tailWord_415005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415085 : List Nat := [1, 5, 1, 1, 1, 3, 7]
def baseStart_415085 : Nat := 118140960795 + 415085 * 2 ^ 59
def prefixEnd_415085 : Nat := 4983230072969 + 3 ^ 40 * 415085 * 2
def baseEnd_415085 : Nat := 42101356537602708489593

theorem tailTrace_415085 : CollatzResearch.WordTrace tailWord_415085 prefixEnd_415085 42101356537602708489593 := by
  unfold tailWord_415085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15139393701225410719198709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10092929134150273812799139 15139393701225410719198709)
  ·
    refine ⟨1419318159489882254924879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15139393701225410719198709 1419318159489882254924879)
    ·
      refine ⟨2128977239234823382387319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419318159489882254924879 2128977239234823382387319)
      ·
        refine ⟨3193465858852235073580979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128977239234823382387319 3193465858852235073580979)
        ·
          refine ⟨4790198788278352610371469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193465858852235073580979 4790198788278352610371469)
          ·
            refine ⟨1796324545604382228889301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4790198788278352610371469 1796324545604382228889301)
            ·
              refine ⟨42101356537602708489593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1796324545604382228889301 42101356537602708489593)
              ·
                rfl

theorem cell19_415085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_415085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415085 prefixEnd_415085 := by exact prefixLift 415085
  have htrace : WordTrace (prefixWord ++ tailWord_415085) baseStart_415085 baseEnd_415085 := by
    simpa [prefixWord, tailWord_415085, baseEnd_415085] using wordTrace_append hprefix tailTrace_415085
  have hstable : (prefixWord ++ tailWord_415085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415085).length < 2 ^ (prefixWord ++ tailWord_415085).sum := by decide
  have hdescent : baseEnd_415085 < baseStart_415085 := by decide
  rcases family_descends (prefixWord ++ tailWord_415085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415170 : List Nat := [3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_415170 : Nat := 118140960795 + 415170 * 2 ^ 59
def prefixEnd_415170 : Nat := 4983230072969 + 3 ^ 40 * 415170 * 2
def baseEnd_415170 : Nat := 126329933823553113579659

theorem tailTrace_415170 : CollatzResearch.WordTrace tailWord_415170 prefixEnd_415170 126329933823553113579659 := by
  unfold tailWord_415170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785623476479367559010741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10094995937278313490695309 3785623476479367559010741)
  ·
    refine ⟨354902200919940708657257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3785623476479367559010741 354902200919940708657257)
    ·
      refine ⟨266176650689955531492943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354902200919940708657257 266176650689955531492943)
      ·
        refine ⟨399264976034933297239415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266176650689955531492943 399264976034933297239415)
        ·
          refine ⟨598897464052399945859123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399264976034933297239415 598897464052399945859123)
          ·
            refine ⟨898346196078599918788685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598897464052399945859123 898346196078599918788685)
            ·
              refine ⟨336879823529474969545757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898346196078599918788685 336879823529474969545757)
              ·
                refine ⟨126329933823553113579659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336879823529474969545757 126329933823553113579659)
                ·
                  rfl

theorem cell19_415170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_415170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415170 prefixEnd_415170 := by exact prefixLift 415170
  have htrace : WordTrace (prefixWord ++ tailWord_415170) baseStart_415170 baseEnd_415170 := by
    simpa [prefixWord, tailWord_415170, baseEnd_415170] using wordTrace_append hprefix tailTrace_415170
  have hstable : (prefixWord ++ tailWord_415170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415170).length < 2 ^ (prefixWord ++ tailWord_415170).sum := by decide
  have hdescent : baseEnd_415170 < baseStart_415170 := by decide
  rcases family_descends (prefixWord ++ tailWord_415170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415178 : List Nat := [3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_415178 : Nat := 118140960795 + 415178 * 2 ^ 59
def prefixEnd_415178 : Nat := 4983230072969 + 3 ^ 40 * 415178 * 2
def baseEnd_415178 : Nat := 126332368102211465401859

theorem tailTrace_415178 : CollatzResearch.WordTrace tailWord_415178 prefixEnd_415178 126332368102211465401859 := by
  unfold tailWord_415178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785696422472121900583547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10095190459925658401556125 3785696422472121900583547)
  ·
    refine ⟨5678544633708182850875321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3785696422472121900583547 5678544633708182850875321)
    ·
      refine ⟨4258908475281137138156491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5678544633708182850875321 4258908475281137138156491)
      ·
        refine ⟨6388362712921705707234737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258908475281137138156491 6388362712921705707234737)
        ·
          refine ⟨4791272034691279280426053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6388362712921705707234737 4791272034691279280426053)
          ·
            refine ⟨898363506504614865079885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4791272034691279280426053 898363506504614865079885)
            ·
              refine ⟨336886314939230574404957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898363506504614865079885 336886314939230574404957)
              ·
                refine ⟨126332368102211465401859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336886314939230574404957 126332368102211465401859)
                ·
                  rfl

theorem cell19_415178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_415178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415178 prefixEnd_415178 := by exact prefixLift 415178
  have htrace : WordTrace (prefixWord ++ tailWord_415178) baseStart_415178 baseEnd_415178 := by
    simpa [prefixWord, tailWord_415178, baseEnd_415178] using wordTrace_append hprefix tailTrace_415178
  have hstable : (prefixWord ++ tailWord_415178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415178).length < 2 ^ (prefixWord ++ tailWord_415178).sum := by decide
  have hdescent : baseEnd_415178 < baseStart_415178 := by decide
  rcases family_descends (prefixWord ++ tailWord_415178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415233 : List Nat := [1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_415233 : Nat := 118140960795 + 415233 * 2 ^ 59
def prefixEnd_415233 : Nat := 4983230072969 + 3 ^ 40 * 415233 * 2
def baseEnd_415233 : Nat := 126349103767987634179487

theorem tailTrace_415233 : CollatzResearch.WordTrace tailWord_415233 prefixEnd_415233 126349103767987634179487 := by
  unfold tailWord_415233
  simp only [CollatzResearch.WordTrace]
  refine ⟨15144791704689231995586353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10096527803126154663724235 15144791704689231995586353)
  ·
    refine ⟨11358593778516923996689765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15144791704689231995586353 11358593778516923996689765)
    ·
      refine ⟨2129736333471923249379331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11358593778516923996689765 2129736333471923249379331)
      ·
        refine ⟨3194604500207884874068997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129736333471923249379331 3194604500207884874068997)
        ·
          refine ⟨598988343788978413887937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3194604500207884874068997 598988343788978413887937)
          ·
            refine ⟨449241257841733810415953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598988343788978413887937 449241257841733810415953)
            ·
              refine ⟨336930943381300357811965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449241257841733810415953 336930943381300357811965)
              ·
                refine ⟨126349103767987634179487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336930943381300357811965 126349103767987634179487)
                ·
                  rfl

theorem cell19_415233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_415233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415233 prefixEnd_415233 := by exact prefixLift 415233
  have htrace : WordTrace (prefixWord ++ tailWord_415233) baseStart_415233 baseEnd_415233 := by
    simpa [prefixWord, tailWord_415233, baseEnd_415233] using wordTrace_append hprefix tailTrace_415233
  have hstable : (prefixWord ++ tailWord_415233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415233).length < 2 ^ (prefixWord ++ tailWord_415233).sum := by decide
  have hdescent : baseEnd_415233 < baseStart_415233 := by decide
  rcases family_descends (prefixWord ++ tailWord_415233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415252 : List Nat := [2, 4, 3, 1, 2, 2, 5]
def baseStart_415252 : Nat := 118140960795 + 415252 * 2 ^ 59
def prefixEnd_415252 : Nat := 4983230072969 + 3 ^ 40 * 415252 * 2
def baseEnd_415252 : Nat := 42118295059933739919071

theorem tailTrace_415252 : CollatzResearch.WordTrace tailWord_415252 prefixEnd_415252 42118295059933739919071 := by
  unfold tailWord_415252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7572742345810199120264005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10096989794413598827018673 7572742345810199120264005)
  ·
    refine ⟨1419889189839412335049501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7572742345810199120264005 1419889189839412335049501)
    ·
      refine ⟨532458446189779625643563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1419889189839412335049501 532458446189779625643563)
      ·
        refine ⟨798687669284669438465345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532458446189779625643563 798687669284669438465345)
        ·
          refine ⟨599015751963502078849009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798687669284669438465345 599015751963502078849009)
          ·
            refine ⟨449261813972626559136757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599015751963502078849009 449261813972626559136757)
            ·
              refine ⟨42118295059933739919071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449261813972626559136757 42118295059933739919071)
              ·
                rfl

theorem cell19_415252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_415252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415252 prefixEnd_415252 := by exact prefixLift 415252
  have htrace : WordTrace (prefixWord ++ tailWord_415252) baseStart_415252 baseEnd_415252 := by
    simpa [prefixWord, tailWord_415252, baseEnd_415252] using wordTrace_append hprefix tailTrace_415252
  have hstable : (prefixWord ++ tailWord_415252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415252).length < 2 ^ (prefixWord ++ tailWord_415252).sum := by decide
  have hdescent : baseEnd_415252 < baseStart_415252 := by decide
  rcases family_descends (prefixWord ++ tailWord_415252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415332 : List Nat := [2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_415332 : Nat := 118140960795 + 415332 * 2 ^ 59
def prefixEnd_415332 : Nat := 4983230072969 + 3 ^ 40 * 415332 * 2
def baseEnd_415332 : Nat := 126379227966384737979217

theorem tailTrace_415332 : CollatzResearch.WordTrace tailWord_415332 prefixEnd_415332 126379227966384737979217 := by
  unfold tailWord_415332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574201265665285951720125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10098935020887047935626833 7574201265665285951720125)
  ·
    refine ⟨2840325474624482231895047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7574201265665285951720125 2840325474624482231895047)
    ·
      refine ⟨4260488211936723347842571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840325474624482231895047 4260488211936723347842571)
      ·
        refine ⟨6390732317905085021763857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260488211936723347842571 6390732317905085021763857)
        ·
          refine ⟨4793049238428813766322893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390732317905085021763857 4793049238428813766322893)
          ·
            refine ⟨1797393464410805162371085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4793049238428813766322893 1797393464410805162371085)
            ·
              refine ⟨674022549154051935889157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797393464410805162371085 674022549154051935889157)
              ·
                refine ⟨126379227966384737979217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674022549154051935889157 126379227966384737979217)
                ·
                  rfl

theorem cell19_415332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_415332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415332 prefixEnd_415332 := by exact prefixLift 415332
  have htrace : WordTrace (prefixWord ++ tailWord_415332) baseStart_415332 baseEnd_415332 := by
    simpa [prefixWord, tailWord_415332, baseEnd_415332] using wordTrace_append hprefix tailTrace_415332
  have hstable : (prefixWord ++ tailWord_415332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415332).length < 2 ^ (prefixWord ++ tailWord_415332).sum := by decide
  have hdescent : baseEnd_415332 < baseStart_415332 := by decide
  rcases family_descends (prefixWord ++ tailWord_415332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415368 : List Nat := [2, 1, 3, 5, 1, 1, 6]
def baseStart_415368 : Nat := 118140960795 + 415368 * 2 ^ 59
def prefixEnd_415368 : Nat := 4983230072969 + 3 ^ 40 * 415368 * 2
def baseEnd_415368 : Nat := 42130060740115773726373

theorem tailTrace_415368 : CollatzResearch.WordTrace tailWord_415368 prefixEnd_415368 42130060740115773726373 := by
  unfold tailWord_415368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574857779600075025875379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10099810372800100034500505 7574857779600075025875379)
  ·
    refine ⟨11362286669400112538813069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574857779600075025875379 11362286669400112538813069)
    ·
      refine ⟨4260857501025042202054901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11362286669400112538813069 4260857501025042202054901)
      ·
        refine ⟨399455390721097706442647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4260857501025042202054901 399455390721097706442647)
        ·
          refine ⟨599183086081646559663971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399455390721097706442647 599183086081646559663971)
          ·
            refine ⟨898774629122469839495957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599183086081646559663971 898774629122469839495957)
            ·
              refine ⟨42130060740115773726373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 898774629122469839495957 42130060740115773726373)
              ·
                rfl

theorem cell19_415368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_415368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415368 prefixEnd_415368 := by exact prefixLift 415368
  have htrace : WordTrace (prefixWord ++ tailWord_415368) baseStart_415368 baseEnd_415368 := by
    simpa [prefixWord, tailWord_415368, baseEnd_415368] using wordTrace_append hprefix tailTrace_415368
  have hstable : (prefixWord ++ tailWord_415368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415368).length < 2 ^ (prefixWord ++ tailWord_415368).sum := by decide
  have hdescent : baseEnd_415368 < baseStart_415368 := by decide
  rcases family_descends (prefixWord ++ tailWord_415368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415370 : List Nat := [3, 1, 2, 3, 2, 2, 6]
def baseStart_415370 : Nat := 118140960795 + 415370 * 2 ^ 59
def prefixEnd_415370 : Nat := 4983230072969 + 3 ^ 40 * 415370 * 2
def baseEnd_415370 : Nat := 42130263596670636378223

theorem tailTrace_415370 : CollatzResearch.WordTrace tailWord_415370 prefixEnd_415370 42130263596670636378223 := by
  unfold tailWord_415370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787447126298226098330891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10099859003461936262215709 3787447126298226098330891)
  ·
    refine ⟨5681170689447339147496337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787447126298226098330891 5681170689447339147496337)
    ·
      refine ⟨4260878017085504360622253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5681170689447339147496337 4260878017085504360622253)
      ·
        refine ⟨1597829256407064135233345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4260878017085504360622253 1597829256407064135233345)
        ·
          refine ⟨1198371942305298101425009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597829256407064135233345 1198371942305298101425009)
          ·
            refine ⟨898778956728973576068757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198371942305298101425009 898778956728973576068757)
            ·
              refine ⟨42130263596670636378223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 898778956728973576068757 42130263596670636378223)
              ·
                rfl

theorem cell19_415370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_415370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415370 prefixEnd_415370 := by exact prefixLift 415370
  have htrace : WordTrace (prefixWord ++ tailWord_415370) baseStart_415370 baseEnd_415370 := by
    simpa [prefixWord, tailWord_415370, baseEnd_415370] using wordTrace_append hprefix tailTrace_415370
  have hstable : (prefixWord ++ tailWord_415370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415370).length < 2 ^ (prefixWord ++ tailWord_415370).sum := by decide
  have hdescent : baseEnd_415370 < baseStart_415370 := by decide
  rcases family_descends (prefixWord ++ tailWord_415370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415372 : List Nat := [2, 2, 1, 2, 1, 1, 10]
def baseStart_415372 : Nat := 118140960795 + 415372 * 2 ^ 59
def prefixEnd_415372 : Nat := 4983230072969 + 3 ^ 40 * 415372 * 2
def baseEnd_415372 : Nat := 42130466453225499030073

theorem tailTrace_415372 : CollatzResearch.WordTrace tailWord_415372 prefixEnd_415372 42130466453225499030073 := by
  unfold tailWord_415372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574930725592829367448185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10099907634123772489930913 7574930725592829367448185)
  ·
    refine ⟨5681198044194622025586139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7574930725592829367448185 5681198044194622025586139)
    ·
      refine ⟨8521797066291933038379209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681198044194622025586139 8521797066291933038379209)
      ·
        refine ⟨6391347799718949778784407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8521797066291933038379209 6391347799718949778784407)
        ·
          refine ⟨9587021699578424668176611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391347799718949778784407 9587021699578424668176611)
          ·
            refine ⟨14380532549367637002264917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587021699578424668176611 14380532549367637002264917)
            ·
              refine ⟨42130466453225499030073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14380532549367637002264917 42130466453225499030073)
              ·
                rfl

theorem cell19_415372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_415372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415372 prefixEnd_415372 := by exact prefixLift 415372
  have htrace : WordTrace (prefixWord ++ tailWord_415372) baseStart_415372 baseEnd_415372 := by
    simpa [prefixWord, tailWord_415372, baseEnd_415372] using wordTrace_append hprefix tailTrace_415372
  have hstable : (prefixWord ++ tailWord_415372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415372).length < 2 ^ (prefixWord ++ tailWord_415372).sum := by decide
  have hdescent : baseEnd_415372 < baseStart_415372 := by decide
  rcases family_descends (prefixWord ++ tailWord_415372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415400 : List Nat := [2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_415400 : Nat := 118140960795 + 415400 * 2 ^ 59
def prefixEnd_415400 : Nat := 4983230072969 + 3 ^ 40 * 415400 * 2
def baseEnd_415400 : Nat := 126399919334980728467921

theorem tailTrace_415400 : CollatzResearch.WordTrace tailWord_415400 prefixEnd_415400 126399919334980728467921 := by
  unfold tailWord_415400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575441347542109758457827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10100588463389479677943769 7575441347542109758457827)
  ·
    refine ⟨11363162021313164637686741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7575441347542109758457827 11363162021313164637686741)
    ·
      refine ⟨266324109874527296195783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11363162021313164637686741 266324109874527296195783)
      ·
        refine ⟨399486164811790944293675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266324109874527296195783 399486164811790944293675)
        ·
          refine ⟨599229247217686416440513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399486164811790944293675 599229247217686416440513)
          ·
            refine ⟨449421935413264812330385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599229247217686416440513 449421935413264812330385)
            ·
              refine ⟨337066451559948609247789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449421935413264812330385 337066451559948609247789)
              ·
                refine ⟨126399919334980728467921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337066451559948609247789 126399919334980728467921)
                ·
                  rfl

theorem cell19_415400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_415400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415400 prefixEnd_415400 := by exact prefixLift 415400
  have htrace : WordTrace (prefixWord ++ tailWord_415400) baseStart_415400 baseEnd_415400 := by
    simpa [prefixWord, tailWord_415400, baseEnd_415400] using wordTrace_append hprefix tailTrace_415400
  have hstable : (prefixWord ++ tailWord_415400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415400).length < 2 ^ (prefixWord ++ tailWord_415400).sum := by decide
  have hdescent : baseEnd_415400 < baseStart_415400 := by decide
  rcases family_descends (prefixWord ++ tailWord_415400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415408 : List Nat := [2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_415408 : Nat := 118140960795 + 415408 * 2 ^ 59
def prefixEnd_415408 : Nat := 4983230072969 + 3 ^ 40 * 415408 * 2
def baseEnd_415408 : Nat := 126402353613639080290121

theorem tailTrace_415408 : CollatzResearch.WordTrace tailWord_415408 prefixEnd_415408 126402353613639080290121 := by
  unfold tailWord_415408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575587239527618441603439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10100782986036824588804585 7575587239527618441603439)
  ·
    refine ⟨11363380859291427662405159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7575587239527618441603439 11363380859291427662405159)
    ·
      refine ⟨17045071288937141493607739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11363380859291427662405159 17045071288937141493607739)
      ·
        refine ⟨25567606933405712240411609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17045071288937141493607739 25567606933405712240411609)
        ·
          refine ⟨19175705200054284180308707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25567606933405712240411609 19175705200054284180308707)
          ·
            refine ⟨28763557800081426270463061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19175705200054284180308707 28763557800081426270463061)
            ·
              refine ⟨337072942969704214106989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 28763557800081426270463061 337072942969704214106989)
              ·
                refine ⟨126402353613639080290121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337072942969704214106989 126402353613639080290121)
                ·
                  rfl

theorem cell19_415408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_415408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415408 prefixEnd_415408 := by exact prefixLift 415408
  have htrace : WordTrace (prefixWord ++ tailWord_415408) baseStart_415408 baseEnd_415408 := by
    simpa [prefixWord, tailWord_415408, baseEnd_415408] using wordTrace_append hprefix tailTrace_415408
  have hstable : (prefixWord ++ tailWord_415408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415408).length < 2 ^ (prefixWord ++ tailWord_415408).sum := by decide
  have hdescent : baseEnd_415408 < baseStart_415408 := by decide
  rcases family_descends (prefixWord ++ tailWord_415408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415444 : List Nat := [2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_415444 : Nat := 118140960795 + 415444 * 2 ^ 59
def prefixEnd_415444 : Nat := 4983230072969 + 3 ^ 40 * 415444 * 2
def baseEnd_415444 : Nat := 126413307867601663490023

theorem tailTrace_415444 : CollatzResearch.WordTrace tailWord_415444 prefixEnd_415444 126413307867601663490023 := by
  unfold tailWord_415444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576243753462407515758693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10101658337949876687678257 7576243753462407515758693)
  ·
    refine ⟨1420545703774201409204755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7576243753462407515758693 1420545703774201409204755)
    ·
      refine ⟨2130818555661302113807133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1420545703774201409204755 2130818555661302113807133)
      ·
        refine ⟨799056958372988292677675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2130818555661302113807133 799056958372988292677675)
        ·
          refine ⟨1198585437559482439016513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799056958372988292677675 1198585437559482439016513)
          ·
            refine ⟨898939078169611829262385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198585437559482439016513 898939078169611829262385)
            ·
              refine ⟨674204308627208871946789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898939078169611829262385 674204308627208871946789)
              ·
                refine ⟨126413307867601663490023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674204308627208871946789 126413307867601663490023)
                ·
                  rfl

theorem cell19_415444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_415444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415444 prefixEnd_415444 := by exact prefixLift 415444
  have htrace : WordTrace (prefixWord ++ tailWord_415444) baseStart_415444 baseEnd_415444 := by
    simpa [prefixWord, tailWord_415444, baseEnd_415444] using wordTrace_append hprefix tailTrace_415444
  have hstable : (prefixWord ++ tailWord_415444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415444).length < 2 ^ (prefixWord ++ tailWord_415444).sum := by decide
  have hdescent : baseEnd_415444 < baseStart_415444 := by decide
  rcases family_descends (prefixWord ++ tailWord_415444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415467 : List Nat := [1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_415467 : Nat := 118140960795 + 415467 * 2 ^ 59
def prefixEnd_415467 : Nat := 4983230072969 + 3 ^ 40 * 415467 * 2
def baseEnd_415467 : Nat := 126420306418744424978849

theorem tailTrace_415467 : CollatzResearch.WordTrace tailWord_415467 prefixEnd_415467 126420306418744424978849 := by
  unfold tailWord_415467
  simp only [CollatzResearch.WordTrace]
  refine ⟨15153326385841489959604655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10102217590560993306403103 15153326385841489959604655)
  ·
    refine ⟨22729989578762234939406983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15153326385841489959604655 22729989578762234939406983)
    ·
      refine ⟨34094984368143352409110475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729989578762234939406983 34094984368143352409110475)
      ·
        refine ⟨51142476552215028613665713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34094984368143352409110475 51142476552215028613665713)
        ·
          refine ⟨38356857414161271460249285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51142476552215028613665713 38356857414161271460249285)
          ·
            refine ⟨7191910765155238398796741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38356857414161271460249285 7191910765155238398796741)
            ·
              refine ⟨1348483268466607199774389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7191910765155238398796741 1348483268466607199774389)
              ·
                refine ⟨126420306418744424978849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1348483268466607199774389 126420306418744424978849)
                ·
                  rfl

theorem cell19_415467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_415467 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415467 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415467 prefixEnd_415467 := by exact prefixLift 415467
  have htrace : WordTrace (prefixWord ++ tailWord_415467) baseStart_415467 baseEnd_415467 := by
    simpa [prefixWord, tailWord_415467, baseEnd_415467] using wordTrace_append hprefix tailTrace_415467
  have hstable : (prefixWord ++ tailWord_415467).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415467).length < 2 ^ (prefixWord ++ tailWord_415467).sum := by decide
  have hdescent : baseEnd_415467 < baseStart_415467 := by decide
  rcases family_descends (prefixWord ++ tailWord_415467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415541 : List Nat := [1, 3, 3, 1, 4, 1, 6]
def baseStart_415541 : Nat := 118140960795 + 415541 * 2 ^ 59
def prefixEnd_415541 : Nat := 4983230072969 + 3 ^ 40 * 415541 * 2
def baseEnd_415541 : Nat := 42147607832111393111401

theorem tailTrace_415541 : CollatzResearch.WordTrace tailWord_415541 prefixEnd_415541 42147607832111393111401 := by
  unfold tailWord_415541
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156025387573400597798477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10104016925048933731865651 15156025387573400597798477)
  ·
    refine ⟨5683509520340025224174429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15156025387573400597798477 5683509520340025224174429)
    ·
      refine ⟨2131316070127509459065411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5683509520340025224174429 2131316070127509459065411)
      ·
        refine ⟨3196974105191264188598117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131316070127509459065411 3196974105191264188598117)
        ·
          refine ⟨599432644723362035362147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3196974105191264188598117 599432644723362035362147)
          ·
            refine ⟨899148967085043053043221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599432644723362035362147 899148967085043053043221)
            ·
              refine ⟨42147607832111393111401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 899148967085043053043221 42147607832111393111401)
              ·
                rfl

theorem cell19_415541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_415541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415541 prefixEnd_415541 := by exact prefixLift 415541
  have htrace : WordTrace (prefixWord ++ tailWord_415541) baseStart_415541 baseEnd_415541 := by
    simpa [prefixWord, tailWord_415541, baseEnd_415541] using wordTrace_append hprefix tailTrace_415541
  have hstable : (prefixWord ++ tailWord_415541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415541).length < 2 ^ (prefixWord ++ tailWord_415541).sum := by decide
  have hdescent : baseEnd_415541 < baseStart_415541 := by decide
  rcases family_descends (prefixWord ++ tailWord_415541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415562 : List Nat := [3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_415562 : Nat := 118140960795 + 415562 * 2 ^ 59
def prefixEnd_415562 : Nat := 4983230072969 + 3 ^ 40 * 415562 * 2
def baseEnd_415562 : Nat := 126449213477812352867479

theorem tailTrace_415562 : CollatzResearch.WordTrace tailWord_415562 prefixEnd_415562 126449213477812352867479 := by
  unfold tailWord_415562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789197830124330296078235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10104527546998214122875293 3789197830124330296078235)
  ·
    refine ⟨5683796745186495444117353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789197830124330296078235 5683796745186495444117353)
    ·
      refine ⟨4262847558889871583088015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5683796745186495444117353 4262847558889871583088015)
      ·
        refine ⟨6394271338334807374632023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4262847558889871583088015 6394271338334807374632023)
        ·
          refine ⟨9591407007502211061948035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6394271338334807374632023 9591407007502211061948035)
          ·
            refine ⟨14387110511253316592922053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591407007502211061948035 14387110511253316592922053)
            ·
              refine ⟨2697583220859996861172885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14387110511253316592922053 2697583220859996861172885)
              ·
                refine ⟨126449213477812352867479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2697583220859996861172885 126449213477812352867479)
                ·
                  rfl

theorem cell19_415562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_415562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415562 prefixEnd_415562 := by exact prefixLift 415562
  have htrace : WordTrace (prefixWord ++ tailWord_415562) baseStart_415562 baseEnd_415562 := by
    simpa [prefixWord, tailWord_415562, baseEnd_415562] using wordTrace_append hprefix tailTrace_415562
  have hstable : (prefixWord ++ tailWord_415562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415562).length < 2 ^ (prefixWord ++ tailWord_415562).sum := by decide
  have hdescent : baseEnd_415562 < baseStart_415562 := by decide
  rcases family_descends (prefixWord ++ tailWord_415562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415575 : List Nat := [1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_415575 : Nat := 118140960795 + 415575 * 2 ^ 59
def prefixEnd_415575 : Nat := 4983230072969 + 3 ^ 40 * 415575 * 2
def baseEnd_415575 : Nat := 126453169180632174578555

theorem tailTrace_415575 : CollatzResearch.WordTrace tailWord_415575 prefixEnd_415575 126453169180632174578555 := by
  unfold tailWord_415575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15157265469450224404536179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10104843646300149603024119 15157265469450224404536179)
  ·
    refine ⟨22735898204175336606804269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15157265469450224404536179 22735898204175336606804269)
    ·
      refine ⟨8525961826565751227551601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22735898204175336606804269 8525961826565751227551601)
      ·
        refine ⟨6394471369924313420663701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8525961826565751227551601 6394471369924313420663701)
        ·
          refine ⟨299740845465202191593611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6394471369924313420663701 299740845465202191593611)
          ·
            refine ⟨449611268197803287390417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299740845465202191593611 449611268197803287390417)
            ·
              refine ⟨337208451148352465542813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449611268197803287390417 337208451148352465542813)
              ·
                refine ⟨126453169180632174578555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337208451148352465542813 126453169180632174578555)
                ·
                  rfl

theorem cell19_415575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_415575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415575 prefixEnd_415575 := by exact prefixLift 415575
  have htrace : WordTrace (prefixWord ++ tailWord_415575) baseStart_415575 baseEnd_415575 := by
    simpa [prefixWord, tailWord_415575, baseEnd_415575] using wordTrace_append hprefix tailTrace_415575
  have hstable : (prefixWord ++ tailWord_415575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415575).length < 2 ^ (prefixWord ++ tailWord_415575).sum := by decide
  have hdescent : baseEnd_415575 < baseStart_415575 := by decide
  rcases family_descends (prefixWord ++ tailWord_415575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415594 : List Nat := [3, 1, 3, 4, 2, 1, 5]
def baseStart_415594 : Nat := 118140960795 + 415594 * 2 ^ 59
def prefixEnd_415594 : Nat := 4983230072969 + 3 ^ 40 * 415594 * 2
def baseEnd_415594 : Nat := 42152983530815253385427

theorem tailTrace_415594 : CollatzResearch.WordTrace tailWord_415594 prefixEnd_415594 42152983530815253385427 := by
  unfold tailWord_415594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789489614095347662369459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10105305637587593766318557 3789489614095347662369459)
  ·
    refine ⟨5684234421143021493554189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789489614095347662369459 5684234421143021493554189)
    ·
      refine ⟨2131587907928633060082821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5684234421143021493554189 2131587907928633060082821)
      ·
        refine ⟨399672732736618698765529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2131587907928633060082821 399672732736618698765529)
        ·
          refine ⟨299754549552464024074147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399672732736618698765529 299754549552464024074147)
          ·
            refine ⟨449631824328696036111221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299754549552464024074147 449631824328696036111221)
            ·
              refine ⟨42152983530815253385427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449631824328696036111221 42152983530815253385427)
              ·
                rfl

theorem cell19_415594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_415594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415594 prefixEnd_415594 := by exact prefixLift 415594
  have htrace : WordTrace (prefixWord ++ tailWord_415594) baseStart_415594 baseEnd_415594 := by
    simpa [prefixWord, tailWord_415594, baseEnd_415594] using wordTrace_append hprefix tailTrace_415594
  have hstable : (prefixWord ++ tailWord_415594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415594).length < 2 ^ (prefixWord ++ tailWord_415594).sum := by decide
  have hdescent : baseEnd_415594 < baseStart_415594 := by decide
  rcases family_descends (prefixWord ++ tailWord_415594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415598 : List Nat := [4, 1, 2, 3, 1, 1, 7]
def baseStart_415598 : Nat := 118140960795 + 415598 * 2 ^ 59
def prefixEnd_415598 : Nat := 4983230072969 + 3 ^ 40 * 415598 * 2
def baseEnd_415598 : Nat := 42153389243924978689127

theorem tailTrace_415598 : CollatzResearch.WordTrace tailWord_415598 prefixEnd_415598 42153389243924978689127 := by
  unfold tailWord_415598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894763043545862416577931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10105402898911266221748965 1894763043545862416577931)
  ·
    refine ⟨2842144565318793624866897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1894763043545862416577931 2842144565318793624866897)
    ·
      refine ⟨2131608423989095218650173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2842144565318793624866897 2131608423989095218650173)
      ·
        refine ⟨799353158995910706993815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2131608423989095218650173 799353158995910706993815)
        ·
          refine ⟨1199029738493866060490723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799353158995910706993815 1199029738493866060490723)
          ·
            refine ⟨1798544607740799090736085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199029738493866060490723 1798544607740799090736085)
            ·
              refine ⟨42153389243924978689127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1798544607740799090736085 42153389243924978689127)
              ·
                rfl

theorem cell19_415598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_415598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415598 prefixEnd_415598 := by exact prefixLift 415598
  have htrace : WordTrace (prefixWord ++ tailWord_415598) baseStart_415598 baseEnd_415598 := by
    simpa [prefixWord, tailWord_415598, baseEnd_415598] using wordTrace_append hprefix tailTrace_415598
  have hstable : (prefixWord ++ tailWord_415598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415598).length < 2 ^ (prefixWord ++ tailWord_415598).sum := by decide
  have hdescent : baseEnd_415598 < baseStart_415598 := by decide
  rcases family_descends (prefixWord ++ tailWord_415598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415619 : List Nat := [1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_415619 : Nat := 118140960795 + 415619 * 2 ^ 59
def prefixEnd_415619 : Nat := 4983230072969 + 3 ^ 40 * 415619 * 2
def baseEnd_415619 : Nat := 126466557713253109600657

theorem tailTrace_415619 : CollatzResearch.WordTrace tailWord_415619 prefixEnd_415619 126466557713253109600657 := by
  unfold tailWord_415619
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158870281290819919137911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10105913520860546612758607 15158870281290819919137911)
  ·
    refine ⟨22738305421936229878706867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158870281290819919137911 22738305421936229878706867)
    ·
      refine ⟨34107458132904344818060301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22738305421936229878706867 34107458132904344818060301)
      ·
        refine ⟨12790296799839129306772613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34107458132904344818060301 12790296799839129306772613)
        ·
          refine ⟨2398180649969836745019865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12790296799839129306772613 2398180649969836745019865)
          ·
            refine ⟨1798635487477377558764899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398180649969836745019865 1798635487477377558764899)
            ·
              refine ⟨2697953231216066338147349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798635487477377558764899 2697953231216066338147349)
              ·
                refine ⟨126466557713253109600657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2697953231216066338147349 126466557713253109600657)
                ·
                  rfl

theorem cell19_415619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_415619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415619 prefixEnd_415619 := by exact prefixLift 415619
  have htrace : WordTrace (prefixWord ++ tailWord_415619) baseStart_415619 baseEnd_415619 := by
    simpa [prefixWord, tailWord_415619, baseEnd_415619] using wordTrace_append hprefix tailTrace_415619
  have hstable : (prefixWord ++ tailWord_415619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415619).length < 2 ^ (prefixWord ++ tailWord_415619).sum := by decide
  have hdescent : baseEnd_415619 < baseStart_415619 := by decide
  rcases family_descends (prefixWord ++ tailWord_415619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415636 : List Nat := [2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_415636 : Nat := 118140960795 + 415636 * 2 ^ 59
def prefixEnd_415636 : Nat := 4983230072969 + 3 ^ 40 * 415636 * 2
def baseEnd_415636 : Nat := 126471730555402107222833

theorem tailTrace_415636 : CollatzResearch.WordTrace tailWord_415636 prefixEnd_415636 126471730555402107222833 := by
  unfold tailWord_415636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579745161114615911253381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10106326881486154548337841 7579745161114615911253381)
  ·
    refine ⟨1421202217708990483360009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7579745161114615911253381 1421202217708990483360009)
    ·
      refine ⟨1065901663281742862520007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1421202217708990483360009 1065901663281742862520007)
      ·
        refine ⟨1598852494922614293780011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065901663281742862520007 1598852494922614293780011)
        ·
          refine ⟨2398278742383921440670017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598852494922614293780011 2398278742383921440670017)
          ·
            refine ⟨1798709056787941080502513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398278742383921440670017 1798709056787941080502513)
            ·
              refine ⟨1349031792590955810376885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798709056787941080502513 1349031792590955810376885)
              ·
                refine ⟨126471730555402107222833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349031792590955810376885 126471730555402107222833)
                ·
                  rfl

theorem cell19_415636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_415636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415636 prefixEnd_415636 := by exact prefixLift 415636
  have htrace : WordTrace (prefixWord ++ tailWord_415636) baseStart_415636 baseEnd_415636 := by
    simpa [prefixWord, tailWord_415636, baseEnd_415636] using wordTrace_append hprefix tailTrace_415636
  have hstable : (prefixWord ++ tailWord_415636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415636).length < 2 ^ (prefixWord ++ tailWord_415636).sum := by decide
  have hdescent : baseEnd_415636 < baseStart_415636 := by decide
  rcases family_descends (prefixWord ++ tailWord_415636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415668 : List Nat := [2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_415668 : Nat := 118140960795 + 415668 * 2 ^ 59
def prefixEnd_415668 : Nat := 4983230072969 + 3 ^ 40 * 415668 * 2
def baseEnd_415668 : Nat := 126481467670035514511635

theorem tailTrace_415668 : CollatzResearch.WordTrace tailWord_415668 prefixEnd_415668 126481467670035514511635 := by
  unfold tailWord_415668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580328729056650643835829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10107104972075534191781105 7580328729056650643835829)
  ·
    refine ⟨710655818349060997859609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7580328729056650643835829 710655818349060997859609)
    ·
      refine ⟨532991863761795748394707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710655818349060997859609 532991863761795748394707)
      ·
        refine ⟨799487795642693622592061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532991863761795748394707 799487795642693622592061)
        ·
          refine ⟨299807923366010108472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 799487795642693622592061 299807923366010108472023)
          ·
            refine ⟨449711885049015162708035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299807923366010108472023 449711885049015162708035)
            ·
              refine ⟨674567827573522744062053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449711885049015162708035 674567827573522744062053)
              ·
                refine ⟨126481467670035514511635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674567827573522744062053 126481467670035514511635)
                ·
                  rfl

theorem cell19_415668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_415668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415668 prefixEnd_415668 := by exact prefixLift 415668
  have htrace : WordTrace (prefixWord ++ tailWord_415668) baseStart_415668 baseEnd_415668 := by
    simpa [prefixWord, tailWord_415668, baseEnd_415668] using wordTrace_append hprefix tailTrace_415668
  have hstable : (prefixWord ++ tailWord_415668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415668).length < 2 ^ (prefixWord ++ tailWord_415668).sum := by decide
  have hdescent : baseEnd_415668 < baseStart_415668 := by decide
  rcases family_descends (prefixWord ++ tailWord_415668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415708 : List Nat := [2, 2, 6, 1, 1, 1, 6]
def baseStart_415708 : Nat := 118140960795 + 415708 * 2 ^ 59
def prefixEnd_415708 : Nat := 4983230072969 + 3 ^ 40 * 415708 * 2
def baseEnd_415708 : Nat := 42164546354442424540879

theorem tailTrace_415708 : CollatzResearch.WordTrace tailWord_415708 prefixEnd_415708 42164546354442424540879 := by
  unfold tailWord_415708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581058188984194059563889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10108077585312258746085185 7581058188984194059563889)
  ·
    refine ⟨5685793641738145544672917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7581058188984194059563889 5685793641738145544672917)
    ·
      refine ⟨266521576956475572406543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5685793641738145544672917 266521576956475572406543)
      ·
        refine ⟨399782365434713358609815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266521576956475572406543 399782365434713358609815)
        ·
          refine ⟨599673548152070037914723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399782365434713358609815 599673548152070037914723)
          ·
            refine ⟨899510322228105056872085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599673548152070037914723 899510322228105056872085)
            ·
              refine ⟨42164546354442424540879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 899510322228105056872085 42164546354442424540879)
              ·
                rfl

theorem cell19_415708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_415708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415708 prefixEnd_415708 := by exact prefixLift 415708
  have htrace : WordTrace (prefixWord ++ tailWord_415708) baseStart_415708 baseEnd_415708 := by
    simpa [prefixWord, tailWord_415708, baseEnd_415708] using wordTrace_append hprefix tailTrace_415708
  have hstable : (prefixWord ++ tailWord_415708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415708).length < 2 ^ (prefixWord ++ tailWord_415708).sum := by decide
  have hdescent : baseEnd_415708 < baseStart_415708 := by decide
  rcases family_descends (prefixWord ++ tailWord_415708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415748 : List Nat := [2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_415748 : Nat := 118140960795 + 415748 * 2 ^ 59
def prefixEnd_415748 : Nat := 4983230072969 + 3 ^ 40 * 415748 * 2
def baseEnd_415748 : Nat := 126505810456619032733639

theorem tailTrace_415748 : CollatzResearch.WordTrace tailWord_415748 prefixEnd_415748 126505810456619032733639 := by
  unfold tailWord_415748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581787648911737475291949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10109050198548983300389265 7581787648911737475291949)
  ·
    refine ⟨2843170368341901553234481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7581787648911737475291949 2843170368341901553234481)
    ·
      refine ⟨2132377776256426164925861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843170368341901553234481 2132377776256426164925861)
      ·
        refine ⟨399820833048079905923599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2132377776256426164925861 399820833048079905923599)
        ·
          refine ⟨599731249572119858885399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399820833048079905923599 599731249572119858885399)
          ·
            refine ⟨899596874358179788328099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599731249572119858885399 899596874358179788328099)
            ·
              refine ⟨1349395311537269682492149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899596874358179788328099 1349395311537269682492149)
              ·
                refine ⟨126505810456619032733639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349395311537269682492149 126505810456619032733639)
                ·
                  rfl

theorem cell19_415748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_415748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415748 prefixEnd_415748 := by exact prefixLift 415748
  have htrace : WordTrace (prefixWord ++ tailWord_415748) baseStart_415748 baseEnd_415748 := by
    simpa [prefixWord, tailWord_415748, baseEnd_415748] using wordTrace_append hprefix tailTrace_415748
  have hstable : (prefixWord ++ tailWord_415748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415748).length < 2 ^ (prefixWord ++ tailWord_415748).sum := by decide
  have hdescent : baseEnd_415748 < baseStart_415748 := by decide
  rcases family_descends (prefixWord ++ tailWord_415748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415752 : List Nat := [2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_415752 : Nat := 118140960795 + 415752 * 2 ^ 59
def prefixEnd_415752 : Nat := 4983230072969 + 3 ^ 40 * 415752 * 2
def baseEnd_415752 : Nat := 126507027595948208644739

theorem tailTrace_415752 : CollatzResearch.WordTrace tailWord_415752 prefixEnd_415752 126507027595948208644739 := by
  unfold tailWord_415752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581860594904491816864755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10109147459872655755819673 7581860594904491816864755)
  ·
    refine ⟨11372790892356737725297133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7581860594904491816864755 11372790892356737725297133)
    ·
      refine ⟨4264796584633776646986425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11372790892356737725297133 4264796584633776646986425)
      ·
        refine ⟨3198597438475332485239819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4264796584633776646986425 3198597438475332485239819)
        ·
          refine ⟨4797896157712998727859729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198597438475332485239819 4797896157712998727859729)
          ·
            refine ⟨3598422118284749045894797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4797896157712998727859729 3598422118284749045894797)
            ·
              refine ⟨1349408294356780892210549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3598422118284749045894797 1349408294356780892210549)
              ·
                refine ⟨126507027595948208644739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349408294356780892210549 126507027595948208644739)
                ·
                  rfl

theorem cell19_415752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_415752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415752 prefixEnd_415752 := by exact prefixLift 415752
  have htrace : WordTrace (prefixWord ++ tailWord_415752) baseStart_415752 baseEnd_415752 := by
    simpa [prefixWord, tailWord_415752, baseEnd_415752] using wordTrace_append hprefix tailTrace_415752
  have hstable : (prefixWord ++ tailWord_415752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415752).length < 2 ^ (prefixWord ++ tailWord_415752).sum := by decide
  have hdescent : baseEnd_415752 < baseStart_415752 := by decide
  rcases family_descends (prefixWord ++ tailWord_415752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415767 : List Nat := [1, 1, 3, 5, 3, 1, 5]
def baseStart_415767 : Nat := 118140960795 + 415767 * 2 ^ 59
def prefixEnd_415767 : Nat := 4983230072969 + 3 ^ 40 * 415767 * 2
def baseEnd_415767 : Nat := 42170530622810872770455

theorem tailTrace_415767 : CollatzResearch.WordTrace tailWord_415767 prefixEnd_415767 42170530622810872770455 := by
  unfold tailWord_415767
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164268284754641195525555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10109512189836427463683703 15164268284754641195525555)
  ·
    refine ⟨22746402427131961793288333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15164268284754641195525555 22746402427131961793288333)
    ·
      refine ⟨8529900910174485672483125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22746402427131961793288333 8529900910174485672483125)
      ·
        refine ⟨799678210328858031795293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8529900910174485672483125 799678210328858031795293)
        ·
          refine ⟨299879328873321761923235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 799678210328858031795293 299879328873321761923235)
          ·
            refine ⟨449818993309982642884853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299879328873321761923235 449818993309982642884853)
            ·
              refine ⟨42170530622810872770455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449818993309982642884853 42170530622810872770455)
              ·
                rfl

theorem cell19_415767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_415767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415767 prefixEnd_415767 := by exact prefixLift 415767
  have htrace : WordTrace (prefixWord ++ tailWord_415767) baseStart_415767 baseEnd_415767 := by
    simpa [prefixWord, tailWord_415767, baseEnd_415767] using wordTrace_append hprefix tailTrace_415767
  have hstable : (prefixWord ++ tailWord_415767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415767).length < 2 ^ (prefixWord ++ tailWord_415767).sum := by decide
  have hdescent : baseEnd_415767 < baseStart_415767 := by decide
  rcases family_descends (prefixWord ++ tailWord_415767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415826 : List Nat := [3, 2, 2, 1, 5, 6]
def baseStart_415826 : Nat := 118140960795 + 415826 * 2 ^ 59
def prefixEnd_415826 : Nat := 4983230072969 + 3 ^ 40 * 415826 * 2
def baseEnd_415826 : Nat := 14058838297059773666677

theorem tailTrace_415826 : CollatzResearch.WordTrace tailWord_415826 prefixEnd_415826 14058838297059773666677 := by
  unfold tailWord_415826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791605047885223567980833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10110946794360596181282221 3791605047885223567980833)
  ·
    refine ⟨2843703785913917675985625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3791605047885223567980833 2843703785913917675985625)
    ·
      refine ⟨2132777839435438256989219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843703785913917675985625 2132777839435438256989219)
      ·
        refine ⟨3199166759153157385483829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132777839435438256989219 3199166759153157385483829)
        ·
          refine ⟨299921883670608504889109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3199166759153157385483829 299921883670608504889109)
          ·
            refine ⟨14058838297059773666677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 299921883670608504889109 14058838297059773666677)
            ·
              rfl

theorem cell19_415826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_415826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415826 prefixEnd_415826 := by exact prefixLift 415826
  have htrace : WordTrace (prefixWord ++ tailWord_415826) baseStart_415826 baseEnd_415826 := by
    simpa [prefixWord, tailWord_415826, baseEnd_415826] using wordTrace_append hprefix tailTrace_415826
  have hstable : (prefixWord ++ tailWord_415826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415826).length < 2 ^ (prefixWord ++ tailWord_415826).sum := by decide
  have hdescent : baseEnd_415826 < baseStart_415826 := by decide
  rcases family_descends (prefixWord ++ tailWord_415826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415845 : List Nat := [1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_415845 : Nat := 118140960795 + 415845 * 2 ^ 59
def prefixEnd_415845 : Nat := 4983230072969 + 3 ^ 40 * 415845 * 2
def baseEnd_415845 : Nat := 126535326085351548577819

theorem tailTrace_415845 : CollatzResearch.WordTrace tailWord_415845 prefixEnd_415845 126535326085351548577819 := by
  unfold tailWord_415845
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167113178472060516864989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10111408785648040344576659 15167113178472060516864989)
  ·
    refine ⟨5687667441927022693824371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15167113178472060516864989 5687667441927022693824371)
    ·
      refine ⟨8531501162890534040736557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687667441927022693824371 8531501162890534040736557)
      ·
        refine ⟨3199312936083950265276209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8531501162890534040736557 3199312936083950265276209)
        ·
          refine ⟨2399484702062962698957157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199312936083950265276209 2399484702062962698957157)
          ·
            refine ⟨449903381636805506054467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2399484702062962698957157 449903381636805506054467)
            ·
              refine ⟨674855072455208259081701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449903381636805506054467 674855072455208259081701)
              ·
                refine ⟨126535326085351548577819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674855072455208259081701 126535326085351548577819)
                ·
                  rfl

theorem cell19_415845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_415845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415845 prefixEnd_415845 := by exact prefixLift 415845
  have htrace : WordTrace (prefixWord ++ tailWord_415845) baseStart_415845 baseEnd_415845 := by
    simpa [prefixWord, tailWord_415845, baseEnd_415845] using wordTrace_append hprefix tailTrace_415845
  have hstable : (prefixWord ++ tailWord_415845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415845).length < 2 ^ (prefixWord ++ tailWord_415845).sum := by decide
  have hdescent : baseEnd_415845 < baseStart_415845 := by decide
  rcases family_descends (prefixWord ++ tailWord_415845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415862 : List Nat := [5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_415862 : Nat := 118140960795 + 415862 * 2 ^ 59
def prefixEnd_415862 : Nat := 4983230072969 + 3 ^ 40 * 415862 * 2
def baseEnd_415862 : Nat := 126540498927500546199995

theorem tailTrace_415862 : CollatzResearch.WordTrace tailWord_415862 prefixEnd_415862 126540498927500546199995 := by
  unfold tailWord_415862
  simp only [CollatzResearch.WordTrace]
  refine ⟨947983326213154526264615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10111822146273648280155893 947983326213154526264615)
  ·
    refine ⟨1421974989319731789396923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947983326213154526264615 1421974989319731789396923)
    ·
      refine ⟨2132962483979597684095385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421974989319731789396923 2132962483979597684095385)
      ·
        refine ⟨1599721862984698263071539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132962483979597684095385 1599721862984698263071539)
        ·
          refine ⟨2399582794477047394607309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599721862984698263071539 2399582794477047394607309)
          ·
            refine ⟨899843547928892772977741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2399582794477047394607309 899843547928892772977741)
            ·
              refine ⟨337441330473334789866653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899843547928892772977741 337441330473334789866653)
              ·
                refine ⟨126540498927500546199995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337441330473334789866653 126540498927500546199995)
                ·
                  rfl

theorem cell19_415862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_415862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415862 prefixEnd_415862 := by exact prefixLift 415862
  have htrace : WordTrace (prefixWord ++ tailWord_415862) baseStart_415862 baseEnd_415862 := by
    simpa [prefixWord, tailWord_415862, baseEnd_415862] using wordTrace_append hprefix tailTrace_415862
  have hstable : (prefixWord ++ tailWord_415862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415862).length < 2 ^ (prefixWord ++ tailWord_415862).sum := by decide
  have hdescent : baseEnd_415862 < baseStart_415862 := by decide
  rcases family_descends (prefixWord ++ tailWord_415862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415921 : List Nat := [1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_415921 : Nat := 118140960795 + 415921 * 2 ^ 59
def prefixEnd_415921 : Nat := 4983230072969 + 3 ^ 40 * 415921 * 2
def baseEnd_415921 : Nat := 126558451732605890888723

theorem tailTrace_415921 : CollatzResearch.WordTrace tailWord_415921 prefixEnd_415921 126558451732605890888723 := by
  unfold tailWord_415921
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169885126196725496631617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10113256750797816997754411 15169885126196725496631617)
  ·
    refine ⟨11377413844647544122473713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15169885126196725496631617 11377413844647544122473713)
    ·
      refine ⟨8533060383485658091855285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11377413844647544122473713 8533060383485658091855285)
      ·
        refine ⟨799974410951780446111433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8533060383485658091855285 799974410951780446111433)
        ·
          refine ⟨599980808213835334583575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799974410951780446111433 599980808213835334583575)
          ·
            refine ⟨899971212320753001875363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599980808213835334583575 899971212320753001875363)
            ·
              refine ⟨1349956818481129502813045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899971212320753001875363 1349956818481129502813045)
              ·
                refine ⟨126558451732605890888723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349956818481129502813045 126558451732605890888723)
                ·
                  rfl

theorem cell19_415921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_415921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415921 prefixEnd_415921 := by exact prefixLift 415921
  have htrace : WordTrace (prefixWord ++ tailWord_415921) baseStart_415921 baseEnd_415921 := by
    simpa [prefixWord, tailWord_415921, baseEnd_415921] using wordTrace_append hprefix tailTrace_415921
  have hstable : (prefixWord ++ tailWord_415921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415921).length < 2 ^ (prefixWord ++ tailWord_415921).sum := by decide
  have hdescent : baseEnd_415921 < baseStart_415921 := by decide
  rcases family_descends (prefixWord ++ tailWord_415921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415938 : List Nat := [3, 5, 1, 1, 1, 1, 7]
def baseStart_415938 : Nat := 118140960795 + 415938 * 2 ^ 59
def prefixEnd_415938 : Nat := 4983230072969 + 3 ^ 40 * 415938 * 2
def baseEnd_415938 : Nat := 42187874858251629503633

theorem tailTrace_415938 : CollatzResearch.WordTrace tailWord_415938 prefixEnd_415938 42187874858251629503633 := by
  unfold tailWord_415938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792626291783784350000117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10113670111423424933333645 3792626291783784350000117)
  ·
    refine ⟨355558714854729782812511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3792626291783784350000117 355558714854729782812511)
    ·
      refine ⟨533338072282094674218767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355558714854729782812511 533338072282094674218767)
      ·
        refine ⟨800007108423142011328151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533338072282094674218767 800007108423142011328151)
        ·
          refine ⟨1200010662634713016992227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800007108423142011328151 1200010662634713016992227)
          ·
            refine ⟨1800015993952069525488341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200010662634713016992227 1800015993952069525488341)
            ·
              refine ⟨42187874858251629503633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1800015993952069525488341 42187874858251629503633)
              ·
                rfl

theorem cell19_415938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_415938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415938 prefixEnd_415938 := by exact prefixLift 415938
  have htrace : WordTrace (prefixWord ++ tailWord_415938) baseStart_415938 baseEnd_415938 := by
    simpa [prefixWord, tailWord_415938, baseEnd_415938] using wordTrace_append hprefix tailTrace_415938
  have hstable : (prefixWord ++ tailWord_415938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415938).length < 2 ^ (prefixWord ++ tailWord_415938).sum := by decide
  have hdescent : baseEnd_415938 < baseStart_415938 := by decide
  rcases family_descends (prefixWord ++ tailWord_415938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415940 : List Nat := [2, 3, 3, 1, 2, 3, 5]
def baseStart_415940 : Nat := 118140960795 + 415940 * 2 ^ 59
def prefixEnd_415940 : Nat := 4983230072969 + 3 ^ 40 * 415940 * 2
def baseEnd_415940 : Nat := 42188077714806492155483

theorem tailTrace_415940 : CollatzResearch.WordTrace tailWord_415940 prefixEnd_415940 42188077714806492155483 := by
  unfold tailWord_415940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585289056563945870786637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10113718742085261161048849 7585289056563945870786637)
  ·
    refine ⟨2844483396211479701544989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7585289056563945870786637 2844483396211479701544989)
    ·
      refine ⟨1066681273579304888079371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2844483396211479701544989 1066681273579304888079371)
      ·
        refine ⟨1600021910368957332119057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066681273579304888079371 1600021910368957332119057)
        ·
          refine ⟨1200016432776717999089293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1600021910368957332119057 1200016432776717999089293)
          ·
            refine ⟨450006162291269249658485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1200016432776717999089293 450006162291269249658485)
            ·
              refine ⟨42188077714806492155483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 450006162291269249658485 42188077714806492155483)
              ·
                rfl

theorem cell19_415940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_415940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415940 prefixEnd_415940 := by exact prefixLift 415940
  have htrace : WordTrace (prefixWord ++ tailWord_415940) baseStart_415940 baseEnd_415940 := by
    simpa [prefixWord, tailWord_415940, baseEnd_415940] using wordTrace_append hprefix tailTrace_415940
  have hstable : (prefixWord ++ tailWord_415940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415940).length < 2 ^ (prefixWord ++ tailWord_415940).sum := by decide
  have hdescent : baseEnd_415940 < baseStart_415940 := by decide
  rcases family_descends (prefixWord ++ tailWord_415940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415963 : List Nat := [1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_415963 : Nat := 118140960795 + 415963 * 2 ^ 59
def prefixEnd_415963 : Nat := 4983230072969 + 3 ^ 40 * 415963 * 2
def baseEnd_415963 : Nat := 126571231695562237955275

theorem tailTrace_415963 : CollatzResearch.WordTrace tailWord_415963 prefixEnd_415963 126571231695562237955275 := by
  unfold tailWord_415963
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171416992044566669660543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10114277994696377779773695 15171416992044566669660543)
  ·
    refine ⟨22757125488066850004490815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15171416992044566669660543 22757125488066850004490815)
    ·
      refine ⟨34135688232100275006736223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22757125488066850004490815 34135688232100275006736223)
      ·
        refine ⟨51203532348150412510104335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34135688232100275006736223 51203532348150412510104335)
        ·
          refine ⟨76805298522225618765156503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51203532348150412510104335 76805298522225618765156503)
          ·
            refine ⟨115207947783338428147734755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76805298522225618765156503 115207947783338428147734755)
            ·
              refine ⟨172811921675007642221602133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115207947783338428147734755 172811921675007642221602133)
              ·
                refine ⟨126571231695562237955275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 172811921675007642221602133 126571231695562237955275)
                ·
                  rfl

theorem cell19_415963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_415963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_415963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_415963 prefixEnd_415963 := by exact prefixLift 415963
  have htrace : WordTrace (prefixWord ++ tailWord_415963) baseStart_415963 baseEnd_415963 := by
    simpa [prefixWord, tailWord_415963, baseEnd_415963] using wordTrace_append hprefix tailTrace_415963
  have hstable : (prefixWord ++ tailWord_415963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415963).length < 2 ^ (prefixWord ++ tailWord_415963).sum := by decide
  have hdescent : baseEnd_415963 < baseStart_415963 := by decide
  rcases family_descends (prefixWord ++ tailWord_415963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416132 : List Nat := [2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_416132 : Nat := 118140960795 + 416132 * 2 ^ 59
def prefixEnd_416132 : Nat := 4983230072969 + 3 ^ 40 * 416132 * 2
def baseEnd_416132 : Nat := 126622655832219920199259

theorem tailTrace_416132 : CollatzResearch.WordTrace tailWord_416132 prefixEnd_416132 126622655832219920199259 := by
  unfold tailWord_416132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588790464216154266281325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10118387285621539021708433 7588790464216154266281325)
  ·
    refine ⟨2845796424081057849855497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7588790464216154266281325 2845796424081057849855497)
    ·
      refine ⟨2134347318060793387391623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2845796424081057849855497 2134347318060793387391623)
      ·
        refine ⟨3201520977091190081087435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134347318060793387391623 3201520977091190081087435)
        ·
          refine ⟨4802281465636785121631153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201520977091190081087435 4802281465636785121631153)
          ·
            refine ⟨3601711099227588841223365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4802281465636785121631153 3601711099227588841223365)
            ·
              refine ⟨675320831105172907729381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3601711099227588841223365 675320831105172907729381)
              ·
                refine ⟨126622655832219920199259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675320831105172907729381 126622655832219920199259)
                ·
                  rfl

theorem cell19_416132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_416132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416132 prefixEnd_416132 := by exact prefixLift 416132
  have htrace : WordTrace (prefixWord ++ tailWord_416132) baseStart_416132 baseEnd_416132 := by
    simpa [prefixWord, tailWord_416132, baseEnd_416132] using wordTrace_append hprefix tailTrace_416132
  have hstable : (prefixWord ++ tailWord_416132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416132).length < 2 ^ (prefixWord ++ tailWord_416132).sum := by decide
  have hdescent : baseEnd_416132 < baseStart_416132 := by decide
  rcases family_descends (prefixWord ++ tailWord_416132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416153 : List Nat := [1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_416153 : Nat := 118140960795 + 416153 * 2 ^ 59
def prefixEnd_416153 : Nat := 4983230072969 + 3 ^ 40 * 416153 * 2
def baseEnd_416153 : Nat := 126629045813698093732535

theorem tailTrace_416153 : CollatzResearch.WordTrace tailWord_416153 prefixEnd_416153 126629045813698093732535 := by
  unfold tailWord_416153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15178346861356229119077113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10118897907570819412718075 15178346861356229119077113)
  ·
    refine ⟨11383760146017171839307835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15178346861356229119077113 11383760146017171839307835)
    ·
      refine ⟨17075640219025757758961753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11383760146017171839307835 17075640219025757758961753)
      ·
        refine ⟨12806730164269318319221315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17075640219025757758961753 12806730164269318319221315)
        ·
          refine ⟨19210095246403977478831973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12806730164269318319221315 19210095246403977478831973)
          ·
            refine ⟨3601892858700745777280995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19210095246403977478831973 3601892858700745777280995)
            ·
              refine ⟨5402839288051118665921493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601892858700745777280995 5402839288051118665921493)
              ·
                refine ⟨126629045813698093732535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5402839288051118665921493 126629045813698093732535)
                ·
                  rfl

theorem cell19_416153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_416153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416153 prefixEnd_416153 := by exact prefixLift 416153
  have htrace : WordTrace (prefixWord ++ tailWord_416153) baseStart_416153 baseEnd_416153 := by
    simpa [prefixWord, tailWord_416153, baseEnd_416153] using wordTrace_append hprefix tailTrace_416153
  have hstable : (prefixWord ++ tailWord_416153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416153).length < 2 ^ (prefixWord ++ tailWord_416153).sum := by decide
  have hdescent : baseEnd_416153 < baseStart_416153 := by decide
  rcases family_descends (prefixWord ++ tailWord_416153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416189 : List Nat := [1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_416189 : Nat := 118140960795 + 416189 * 2 ^ 59
def prefixEnd_416189 : Nat := 4983230072969 + 3 ^ 40 * 416189 * 2
def baseEnd_416189 : Nat := 126640000067660676932437

theorem tailTrace_416189 : CollatzResearch.WordTrace tailWord_416189 prefixEnd_416189 126640000067660676932437 := by
  unfold tailWord_416189
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179659889225807267387621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10119773259483871511591747 15179659889225807267387621)
  ·
    refine ⟨2846186229229838862635179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15179659889225807267387621 2846186229229838862635179)
    ·
      refine ⟨4269279343844758293952769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846186229229838862635179 4269279343844758293952769)
      ·
        refine ⟨3201959507883568720464577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4269279343844758293952769 3201959507883568720464577)
        ·
          refine ⟨2401469630912676540348433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201959507883568720464577 2401469630912676540348433)
          ·
            refine ⟨1801102223184507405261325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401469630912676540348433 1801102223184507405261325)
            ·
              refine ⟨675413333694190276972997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1801102223184507405261325 675413333694190276972997)
              ·
                refine ⟨126640000067660676932437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675413333694190276972997 126640000067660676932437)
                ·
                  rfl

theorem cell19_416189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_416189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416189 prefixEnd_416189 := by exact prefixLift 416189
  have htrace : WordTrace (prefixWord ++ tailWord_416189) baseStart_416189 baseEnd_416189 := by
    simpa [prefixWord, tailWord_416189, baseEnd_416189] using wordTrace_append hprefix tailTrace_416189
  have hstable : (prefixWord ++ tailWord_416189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416189).length < 2 ^ (prefixWord ++ tailWord_416189).sum := by decide
  have hdescent : baseEnd_416189 < baseStart_416189 := by decide
  rcases family_descends (prefixWord ++ tailWord_416189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416227 : List Nat := [1, 1, 1, 6, 3, 1, 6]
def baseStart_416227 : Nat := 118140960795 + 416227 * 2 ^ 59
def prefixEnd_416227 : Nat := 4983230072969 + 3 ^ 40 * 416227 * 2
def baseEnd_416227 : Nat := 42217187630429282695963

theorem tailTrace_416227 : CollatzResearch.WordTrace tailWord_416227 prefixEnd_416227 42217187630429282695963 := by
  unfold tailWord_416227
  simp only [CollatzResearch.WordTrace]
  refine ⟨15181045863088139757270935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10120697242058759838180623 15181045863088139757270935)
  ·
    refine ⟨22771568794632209635906403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15181045863088139757270935 22771568794632209635906403)
    ·
      refine ⟨34157353191948314453859605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22771568794632209635906403 34157353191948314453859605)
      ·
        refine ⟨1601125930872577240024669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34157353191948314453859605 1601125930872577240024669)
        ·
          refine ⟨600422224077216465009251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1601125930872577240024669 600422224077216465009251)
          ·
            refine ⟨900633336115824697513877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600422224077216465009251 900633336115824697513877)
            ·
              refine ⟨42217187630429282695963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 900633336115824697513877 42217187630429282695963)
              ·
                rfl

theorem cell19_416227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_416227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416227 prefixEnd_416227 := by exact prefixLift 416227
  have htrace : WordTrace (prefixWord ++ tailWord_416227) baseStart_416227 baseEnd_416227 := by
    simpa [prefixWord, tailWord_416227, baseEnd_416227] using wordTrace_append hprefix tailTrace_416227
  have hstable : (prefixWord ++ tailWord_416227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416227).length < 2 ^ (prefixWord ++ tailWord_416227).sum := by decide
  have hdescent : baseEnd_416227 < baseStart_416227 := by decide
  rcases family_descends (prefixWord ++ tailWord_416227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416246 : List Nat := [5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_416246 : Nat := 118140960795 + 416246 * 2 ^ 59
def prefixEnd_416246 : Nat := 4983230072969 + 3 ^ 40 * 416246 * 2
def baseEnd_416246 : Nat := 126657344303101433665615

theorem tailTrace_416246 : CollatzResearch.WordTrace tailWord_416246 prefixEnd_416246 126657344303101433665615 := by
  unfold tailWord_416246
  simp only [CollatzResearch.WordTrace]
  refine ⟨948858678126206625138287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10121159233346204001475061 948858678126206625138287)
  ·
    refine ⟨1423288017189309937707431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948858678126206625138287 1423288017189309937707431)
    ·
      refine ⟨2134932025783964906561147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423288017189309937707431 2134932025783964906561147)
      ·
        refine ⟨3202398038675947359841721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134932025783964906561147 3202398038675947359841721)
        ·
          refine ⟨2401798529006960519881291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202398038675947359841721 2401798529006960519881291)
          ·
            refine ⟨3602697793510440779821937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401798529006960519881291 3602697793510440779821937)
            ·
              refine ⟨2702023345132830584866453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3602697793510440779821937 2702023345132830584866453)
              ·
                refine ⟨126657344303101433665615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2702023345132830584866453 126657344303101433665615)
                ·
                  rfl

theorem cell19_416246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_416246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416246 prefixEnd_416246 := by exact prefixLift 416246
  have htrace : WordTrace (prefixWord ++ tailWord_416246) baseStart_416246 baseEnd_416246 := by
    simpa [prefixWord, tailWord_416246, baseEnd_416246] using wordTrace_append hprefix tailTrace_416246
  have hstable : (prefixWord ++ tailWord_416246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416246).length < 2 ^ (prefixWord ++ tailWord_416246).sum := by decide
  have hdescent : baseEnd_416246 < baseStart_416246 := by decide
  rcases family_descends (prefixWord ++ tailWord_416246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416248 : List Nat := [2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_416248 : Nat := 118140960795 + 416248 * 2 ^ 59
def prefixEnd_416248 : Nat := 4983230072969 + 3 ^ 40 * 416248 * 2
def baseEnd_416248 : Nat := 126657952872766021621165

theorem tailTrace_416248 : CollatzResearch.WordTrace tailWord_416248 prefixEnd_416248 126657952872766021621165 := by
  unfold tailWord_416248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7590905898006030171892699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10121207864008040229190265 7590905898006030171892699)
  ·
    refine ⟨11386358847009045257839049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7590905898006030171892699 11386358847009045257839049)
    ·
      refine ⟨8539769135256783943379287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11386358847009045257839049 8539769135256783943379287)
      ·
        refine ⟨12809653702885175915068931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539769135256783943379287 12809653702885175915068931)
        ·
          refine ⟨19214480554327763872603397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809653702885175915068931 19214480554327763872603397)
          ·
            refine ⟨3602715103936455726113137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19214480554327763872603397 3602715103936455726113137)
            ·
              refine ⟨2702036327952341794584853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3602715103936455726113137 2702036327952341794584853)
              ·
                refine ⟨126657952872766021621165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2702036327952341794584853 126657952872766021621165)
                ·
                  rfl

theorem cell19_416248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_416248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416248 prefixEnd_416248 := by exact prefixLift 416248
  have htrace : WordTrace (prefixWord ++ tailWord_416248) baseStart_416248 baseEnd_416248 := by
    simpa [prefixWord, tailWord_416248, baseEnd_416248] using wordTrace_append hprefix tailTrace_416248
  have hstable : (prefixWord ++ tailWord_416248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416248).length < 2 ^ (prefixWord ++ tailWord_416248).sum := by decide
  have hdescent : baseEnd_416248 < baseStart_416248 := by decide
  rcases family_descends (prefixWord ++ tailWord_416248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416284 : List Nat := [2, 2, 3, 1, 2, 4, 5]
def baseStart_416284 : Nat := 118140960795 + 416284 * 2 ^ 59
def prefixEnd_416284 : Nat := 4983230072969 + 3 ^ 40 * 416284 * 2
def baseEnd_416284 : Nat := 42222969042242868273689

theorem tailTrace_416284 : CollatzResearch.WordTrace tailWord_416284 prefixEnd_416284 42222969042242868273689 := by
  unfold tailWord_416284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7591562411940819246047953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10122083215921092328063937 7591562411940819246047953)
  ·
    refine ⟨5693671808955614434535965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7591562411940819246047953 5693671808955614434535965)
    ·
      refine ⟨2135126928358355412950987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5693671808955614434535965 2135126928358355412950987)
      ·
        refine ⟨3202690392537533119426481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135126928358355412950987 3202690392537533119426481)
        ·
          refine ⟨2402017794403149839569861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202690392537533119426481 2402017794403149839569861)
          ·
            refine ⟨450378336450590594919349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2402017794403149839569861 450378336450590594919349)
            ·
              refine ⟨42222969042242868273689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 450378336450590594919349 42222969042242868273689)
              ·
                rfl

theorem cell19_416284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_416284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416284 prefixEnd_416284 := by exact prefixLift 416284
  have htrace : WordTrace (prefixWord ++ tailWord_416284) baseStart_416284 baseEnd_416284 := by
    simpa [prefixWord, tailWord_416284, baseEnd_416284] using wordTrace_append hprefix tailTrace_416284
  have hstable : (prefixWord ++ tailWord_416284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416284).length < 2 ^ (prefixWord ++ tailWord_416284).sum := by decide
  have hdescent : baseEnd_416284 < baseStart_416284 := by decide
  rcases family_descends (prefixWord ++ tailWord_416284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416305 : List Nat := [1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_416305 : Nat := 118140960795 + 416305 * 2 ^ 59
def prefixEnd_416305 : Nat := 4983230072969 + 3 ^ 40 * 416305 * 2
def baseEnd_416305 : Nat := 126675297108206778354343

theorem tailTrace_416305 : CollatzResearch.WordTrace tailWord_416305 prefixEnd_416305 126675297108206778354343 := by
  unfold tailWord_416305
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183890756805559078610369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10122593837870372719073579 15183890756805559078610369)
  ·
    refine ⟨11387918067604169308957777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15183890756805559078610369 11387918067604169308957777)
    ·
      refine ⟨8540938550703126981718333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11387918067604169308957777 8540938550703126981718333)
      ·
        refine ⟨3202851956513672618144375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8540938550703126981718333 3202851956513672618144375)
        ·
          refine ⟨4804277934770508927216563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202851956513672618144375 4804277934770508927216563)
          ·
            refine ⟨7206416902155763390824845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804277934770508927216563 7206416902155763390824845)
            ·
              refine ⟨2702406338308411271559317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7206416902155763390824845 2702406338308411271559317)
              ·
                refine ⟨126675297108206778354343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2702406338308411271559317 126675297108206778354343)
                ·
                  rfl

theorem cell19_416305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_416305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416305 prefixEnd_416305 := by exact prefixLift 416305
  have htrace : WordTrace (prefixWord ++ tailWord_416305) baseStart_416305 baseEnd_416305 := by
    simpa [prefixWord, tailWord_416305, baseEnd_416305] using wordTrace_append hprefix tailTrace_416305
  have hstable : (prefixWord ++ tailWord_416305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416305).length < 2 ^ (prefixWord ++ tailWord_416305).sum := by decide
  have hdescent : baseEnd_416305 < baseStart_416305 := by decide
  rcases family_descends (prefixWord ++ tailWord_416305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416354 : List Nat := [3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_416354 : Nat := 118140960795 + 416354 * 2 ^ 59
def prefixEnd_416354 : Nat := 4983230072969 + 3 ^ 40 * 416354 * 2
def baseEnd_416354 : Nat := 126690207064989183265321

theorem tailTrace_416354 : CollatzResearch.WordTrace tailWord_416354 prefixEnd_416354 126690207064989183265321 := by
  unfold tailWord_416354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796419483407010111786029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10123785289085360298096077 3796419483407010111786029)
  ·
    refine ⟨1423657306277628791919761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3796419483407010111786029 1423657306277628791919761)
    ·
      refine ⟨1067742979708221593939821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423657306277628791919761 1067742979708221593939821)
      ·
        refine ⟨400403617390583097727433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1067742979708221593939821 400403617390583097727433)
        ·
          refine ⟨300302713042937323295575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400403617390583097727433 300302713042937323295575)
          ·
            refine ⟨450454069564405984943363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300302713042937323295575 450454069564405984943363)
            ·
              refine ⟨675681104346608977415045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450454069564405984943363 675681104346608977415045)
              ·
                refine ⟨126690207064989183265321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675681104346608977415045 126690207064989183265321)
                ·
                  rfl

theorem cell19_416354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_416354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416354 prefixEnd_416354 := by exact prefixLift 416354
  have htrace : WordTrace (prefixWord ++ tailWord_416354) baseStart_416354 baseEnd_416354 := by
    simpa [prefixWord, tailWord_416354, baseEnd_416354] using wordTrace_append hprefix tailTrace_416354
  have hstable : (prefixWord ++ tailWord_416354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416354).length < 2 ^ (prefixWord ++ tailWord_416354).sum := by decide
  have hdescent : baseEnd_416354 < baseStart_416354 := by decide
  rcases family_descends (prefixWord ++ tailWord_416354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416495 : List Nat := [1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_416495 : Nat := 118140960795 + 416495 * 2 ^ 59
def prefixEnd_416495 : Nat := 4983230072969 + 3 ^ 40 * 416495 * 2
def baseEnd_416495 : Nat := 126733111226342634131603

theorem tailTrace_416495 : CollatzResearch.WordTrace tailWord_416495 prefixEnd_416495 126733111226342634131603 := by
  unfold tailWord_416495
  simp only [CollatzResearch.WordTrace]
  refine ⟨15190820626117221528026939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10127213750744814352017959 15190820626117221528026939)
  ·
    refine ⟨22786230939175832292040409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15190820626117221528026939 22786230939175832292040409)
    ·
      refine ⟨17089673204381874219030307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22786230939175832292040409 17089673204381874219030307)
      ·
        refine ⟨25634509806572811328545461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17089673204381874219030307 25634509806572811328545461)
        ·
          refine ⟨2403235294366201062051137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25634509806572811328545461 2403235294366201062051137)
          ·
            refine ⟨1802426470774650796538353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403235294366201062051137 1802426470774650796538353)
            ·
              refine ⟨1351819853080988097403765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802426470774650796538353 1351819853080988097403765)
              ·
                refine ⟨126733111226342634131603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351819853080988097403765 126733111226342634131603)
                ·
                  rfl

theorem cell19_416495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_416495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416495 prefixEnd_416495 := by exact prefixLift 416495
  have htrace : WordTrace (prefixWord ++ tailWord_416495) baseStart_416495 baseEnd_416495 := by
    simpa [prefixWord, tailWord_416495, baseEnd_416495] using wordTrace_append hprefix tailTrace_416495
  have hstable : (prefixWord ++ tailWord_416495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416495).length < 2 ^ (prefixWord ++ tailWord_416495).sum := by decide
  have hdescent : baseEnd_416495 < baseStart_416495 := by decide
  rcases family_descends (prefixWord ++ tailWord_416495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416548 : List Nat := [2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_416548 : Nat := 118140960795 + 416548 * 2 ^ 59
def prefixEnd_416548 : Nat := 4983230072969 + 3 ^ 40 * 416548 * 2
def baseEnd_416548 : Nat := 126749238322454214953681

theorem tailTrace_416548 : CollatzResearch.WordTrace tailWord_416548 prefixEnd_416548 126749238322454214953681 := by
  unfold tailWord_416548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596376847462605789853149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10128502463283474386470865 7596376847462605789853149)
  ·
    refine ⟨2848641317798477171194931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7596376847462605789853149 2848641317798477171194931)
    ·
      refine ⟨4272961976697715756792397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848641317798477171194931 4272961976697715756792397)
      ·
        refine ⟨1602360741261643408797149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4272961976697715756792397 1602360741261643408797149)
        ·
          refine ⟨600885277973116278298931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1602360741261643408797149 600885277973116278298931)
          ·
            refine ⟨901327916959674417448397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600885277973116278298931 901327916959674417448397)
            ·
              refine ⟨337997968859877906543149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 901327916959674417448397 337997968859877906543149)
              ·
                refine ⟨126749238322454214953681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337997968859877906543149 126749238322454214953681)
                ·
                  rfl

theorem cell19_416548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_416548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416548 prefixEnd_416548 := by exact prefixLift 416548
  have htrace : WordTrace (prefixWord ++ tailWord_416548) baseStart_416548 baseEnd_416548 := by
    simpa [prefixWord, tailWord_416548, baseEnd_416548] using wordTrace_append hprefix tailTrace_416548
  have hstable : (prefixWord ++ tailWord_416548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416548).length < 2 ^ (prefixWord ++ tailWord_416548).sum := by decide
  have hdescent : baseEnd_416548 < baseStart_416548 := by decide
  rcases family_descends (prefixWord ++ tailWord_416548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416647 : List Nat := [1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_416647 : Nat := 118140960795 + 416647 * 2 ^ 59
def prefixEnd_416647 : Nat := 4983230072969 + 3 ^ 40 * 416647 * 2
def baseEnd_416647 : Nat := 126779362520851318753411

theorem tailTrace_416647 : CollatzResearch.WordTrace tailWord_416647 prefixEnd_416647 126779362520851318753411 := by
  unfold tailWord_416647
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196364521566551487560195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10130909681044367658373463 15196364521566551487560195)
  ·
    refine ⟨22794546782349827231340293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15196364521566551487560195 22794546782349827231340293)
    ·
      refine ⟨4273977521690592605876305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22794546782349827231340293 4273977521690592605876305)
      ·
        refine ⟨3205483141267944454407229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273977521690592605876305 3205483141267944454407229)
        ·
          refine ⟨1202056177975479170402711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3205483141267944454407229 1202056177975479170402711)
          ·
            refine ⟨1803084266963218755604067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202056177975479170402711 1803084266963218755604067)
            ·
              refine ⟨2704626400444828133406101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803084266963218755604067 2704626400444828133406101)
              ·
                refine ⟨126779362520851318753411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2704626400444828133406101 126779362520851318753411)
                ·
                  rfl

theorem cell19_416647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_416647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416647 prefixEnd_416647 := by exact prefixLift 416647
  have htrace : WordTrace (prefixWord ++ tailWord_416647) baseStart_416647 baseEnd_416647 := by
    simpa [prefixWord, tailWord_416647, baseEnd_416647] using wordTrace_append hprefix tailTrace_416647
  have hstable : (prefixWord ++ tailWord_416647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416647).length < 2 ^ (prefixWord ++ tailWord_416647).sum := by decide
  have hdescent : baseEnd_416647 < baseStart_416647 := by decide
  rcases family_descends (prefixWord ++ tailWord_416647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416694 : List Nat := [5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_416694 : Nat := 118140960795 + 416694 * 2 ^ 59
def prefixEnd_416694 : Nat := 4983230072969 + 3 ^ 40 * 416694 * 2
def baseEnd_416694 : Nat := 126793663907969135708839

theorem tailTrace_416694 : CollatzResearch.WordTrace tailWord_416694 prefixEnd_416694 126793663907969135708839 := by
  unfold tailWord_416694
  simp only [CollatzResearch.WordTrace]
  refine ⟨949879922024767407157571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10132052501597519009680757 949879922024767407157571)
  ·
    refine ⟨1424819883037151110736357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949879922024767407157571 1424819883037151110736357)
    ·
      refine ⟨267153728069465833263067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1424819883037151110736357 267153728069465833263067)
      ·
        refine ⟨400730592104198749894601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267153728069465833263067 400730592104198749894601)
        ·
          refine ⟨300547944078149062420951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400730592104198749894601 300547944078149062420951)
          ·
            refine ⟨450821916117223593631427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300547944078149062420951 450821916117223593631427)
            ·
              refine ⟨676232874175835390447141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450821916117223593631427 676232874175835390447141)
              ·
                refine ⟨126793663907969135708839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676232874175835390447141 126793663907969135708839)
                ·
                  rfl

theorem cell19_416694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_416694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416694 prefixEnd_416694 := by exact prefixLift 416694
  have htrace : WordTrace (prefixWord ++ tailWord_416694) baseStart_416694 baseEnd_416694 := by
    simpa [prefixWord, tailWord_416694, baseEnd_416694] using wordTrace_append hprefix tailTrace_416694
  have hstable : (prefixWord ++ tailWord_416694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416694).length < 2 ^ (prefixWord ++ tailWord_416694).sum := by decide
  have hdescent : baseEnd_416694 < baseStart_416694 := by decide
  rcases family_descends (prefixWord ++ tailWord_416694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416704 : List Nat := [2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_416704 : Nat := 118140960795 + 416704 * 2 ^ 59
def prefixEnd_416704 : Nat := 4983230072969 + 3 ^ 40 * 416704 * 2
def baseEnd_416704 : Nat := 126796706756292075486589

theorem tailTrace_416704 : CollatzResearch.WordTrace tailWord_416704 prefixEnd_416704 126796706756292075486589 := by
  unfold tailWord_416704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599221741180025111192583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10132295654906700148256777 7599221741180025111192583)
  ·
    refine ⟨11398832611770037666788875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599221741180025111192583 11398832611770037666788875)
    ·
      refine ⟨17098248917655056500183313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398832611770037666788875 17098248917655056500183313)
      ·
        refine ⟨12823686688241292375137485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17098248917655056500183313 12823686688241292375137485)
        ·
          refine ⟨4808882508090484640676557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12823686688241292375137485 4808882508090484640676557)
          ·
            refine ⟨1803330940533931740253709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4808882508090484640676557 1803330940533931740253709)
            ·
              refine ⟨676249102700224402595141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1803330940533931740253709 676249102700224402595141)
              ·
                refine ⟨126796706756292075486589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676249102700224402595141 126796706756292075486589)
                ·
                  rfl

theorem cell19_416704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_416704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416704 prefixEnd_416704 := by exact prefixLift 416704
  have htrace : WordTrace (prefixWord ++ tailWord_416704) baseStart_416704 baseEnd_416704 := by
    simpa [prefixWord, tailWord_416704, baseEnd_416704] using wordTrace_append hprefix tailTrace_416704
  have hstable : (prefixWord ++ tailWord_416704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416704).length < 2 ^ (prefixWord ++ tailWord_416704).sum := by decide
  have hdescent : baseEnd_416704 < baseStart_416704 := by decide
  rcases family_descends (prefixWord ++ tailWord_416704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416763 : List Nat := [1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_416763 : Nat := 118140960795 + 416763 * 2 ^ 59
def prefixEnd_416763 : Nat := 4983230072969 + 3 ^ 40 * 416763 * 2
def baseEnd_416763 : Nat := 126814659561397420175317

theorem tailTrace_416763 : CollatzResearch.WordTrace tailWord_416763 prefixEnd_416763 126814659561397420175317 := by
  unfold tailWord_416763
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200595389146303298782943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10133730259430868865855295 15200595389146303298782943)
  ·
    refine ⟨22800893083719454948174415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15200595389146303298782943 22800893083719454948174415)
    ·
      refine ⟨34201339625579182422261623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22800893083719454948174415 34201339625579182422261623)
      ·
        refine ⟨51302009438368773633392435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34201339625579182422261623 51302009438368773633392435)
        ·
          refine ⟨76953014157553160450088653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51302009438368773633392435 76953014157553160450088653)
          ·
            refine ⟨28857380309082435168783245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76953014157553160450088653 28857380309082435168783245)
            ·
              refine ⟨10821517615905913188293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28857380309082435168783245 10821517615905913188293717)
              ·
                refine ⟨126814659561397420175317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10821517615905913188293717 126814659561397420175317)
                ·
                  rfl

theorem cell19_416763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_416763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416763 prefixEnd_416763 := by exact prefixLift 416763
  have htrace : WordTrace (prefixWord ++ tailWord_416763) baseStart_416763 baseEnd_416763 := by
    simpa [prefixWord, tailWord_416763, baseEnd_416763] using wordTrace_append hprefix tailTrace_416763
  have hstable : (prefixWord ++ tailWord_416763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416763).length < 2 ^ (prefixWord ++ tailWord_416763).sum := by decide
  have hdescent : baseEnd_416763 < baseStart_416763 := by decide
  rcases family_descends (prefixWord ++ tailWord_416763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416778 : List Nat := [3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_416778 : Nat := 118140960795 + 416778 * 2 ^ 59
def prefixEnd_416778 : Nat := 4983230072969 + 3 ^ 40 * 416778 * 2
def baseEnd_416778 : Nat := 126819223833881829841943

theorem tailTrace_416778 : CollatzResearch.WordTrace tailWord_416778 prefixEnd_416778 126819223833881829841943 := by
  unfold tailWord_416778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800285621022990215144747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10134094989394640573719325 3800285621022990215144747)
  ·
    refine ⟨5700428431534485322717121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3800285621022990215144747 5700428431534485322717121)
    ·
      refine ⟨4275321323650863992037841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700428431534485322717121 4275321323650863992037841)
      ·
        refine ⟨3206490992738147994028381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4275321323650863992037841 3206490992738147994028381)
        ·
          refine ⟨1202434122276805497760643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3206490992738147994028381 1202434122276805497760643)
          ·
            refine ⟨1803651183415208246640965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202434122276805497760643 1803651183415208246640965)
            ·
              refine ⟨338184596890351546245181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1803651183415208246640965 338184596890351546245181)
              ·
                refine ⟨126819223833881829841943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338184596890351546245181 126819223833881829841943)
                ·
                  rfl

theorem cell19_416778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_416778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416778 prefixEnd_416778 := by exact prefixLift 416778
  have htrace : WordTrace (prefixWord ++ tailWord_416778) baseStart_416778 baseEnd_416778 := by
    simpa [prefixWord, tailWord_416778, baseEnd_416778] using wordTrace_append hprefix tailTrace_416778
  have hstable : (prefixWord ++ tailWord_416778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416778).length < 2 ^ (prefixWord ++ tailWord_416778).sum := by decide
  have hdescent : baseEnd_416778 < baseStart_416778 := by decide
  rcases family_descends (prefixWord ++ tailWord_416778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416780 : List Nat := [2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_416780 : Nat := 118140960795 + 416780 * 2 ^ 59
def prefixEnd_416780 : Nat := 4983230072969 + 3 ^ 40 * 416780 * 2
def baseEnd_416780 : Nat := 126819832403546417797493

theorem tailTrace_416780 : CollatzResearch.WordTrace tailWord_416780 prefixEnd_416780 126819832403546417797493 := by
  unfold tailWord_416780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600607715042357601075897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10134143620056476801434529 7600607715042357601075897)
  ·
    refine ⟨5700455786281768200806923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7600607715042357601075897 5700455786281768200806923)
    ·
      refine ⟨8550683679422652301210385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700455786281768200806923 8550683679422652301210385)
      ·
        refine ⟨6413012759566989225907789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8550683679422652301210385 6413012759566989225907789)
        ·
          refine ⟨2404879784837620959715421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6413012759566989225907789 2404879784837620959715421)
          ·
            refine ⟨901829919314107859893283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2404879784837620959715421 901829919314107859893283)
            ·
              refine ⟨1352744878971161789839925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901829919314107859893283 1352744878971161789839925)
              ·
                refine ⟨126819832403546417797493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1352744878971161789839925 126819832403546417797493)
                ·
                  rfl

theorem cell19_416780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_416780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416780 prefixEnd_416780 := by exact prefixLift 416780
  have htrace : WordTrace (prefixWord ++ tailWord_416780) baseStart_416780 baseEnd_416780 := by
    simpa [prefixWord, tailWord_416780, baseEnd_416780] using wordTrace_append hprefix tailTrace_416780
  have hstable : (prefixWord ++ tailWord_416780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416780).length < 2 ^ (prefixWord ++ tailWord_416780).sum := by decide
  have hdescent : baseEnd_416780 < baseStart_416780 := by decide
  rcases family_descends (prefixWord ++ tailWord_416780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416797 : List Nat := [1, 4, 2, 2, 3, 2, 5]
def baseStart_416797 : Nat := 118140960795 + 416797 * 2 ^ 59
def prefixEnd_416797 : Nat := 4983230072969 + 3 ^ 40 * 416797 * 2
def baseEnd_416797 : Nat := 42275001748565138473223

theorem tailTrace_416797 : CollatzResearch.WordTrace tailWord_416797 prefixEnd_416797 42275001748565138473223 := by
  unfold tailWord_416797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201835471023127105520645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10134556980682084737013763 15201835471023127105520645)
  ·
    refine ⟨2850344150816836332285121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15201835471023127105520645 2850344150816836332285121)
    ·
      refine ⟨2137758113112627249213841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2850344150816836332285121 2137758113112627249213841)
      ·
        refine ⟨1603318584834470436910381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2137758113112627249213841 1603318584834470436910381)
        ·
          refine ⟨601244469312926413841393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1603318584834470436910381 601244469312926413841393)
          ·
            refine ⟨450933351984694810381045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601244469312926413841393 450933351984694810381045)
            ·
              refine ⟨42275001748565138473223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 450933351984694810381045 42275001748565138473223)
              ·
                rfl

theorem cell19_416797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_416797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416797 prefixEnd_416797 := by exact prefixLift 416797
  have htrace : WordTrace (prefixWord ++ tailWord_416797) baseStart_416797 baseEnd_416797 := by
    simpa [prefixWord, tailWord_416797, baseEnd_416797] using wordTrace_append hprefix tailTrace_416797
  have hstable : (prefixWord ++ tailWord_416797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416797).length < 2 ^ (prefixWord ++ tailWord_416797).sum := by decide
  have hdescent : baseEnd_416797 < baseStart_416797 := by decide
  rcases family_descends (prefixWord ++ tailWord_416797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416799 : List Nat := [1, 1, 2, 4, 1, 5, 5]
def baseStart_416799 : Nat := 118140960795 + 416799 * 2 ^ 59
def prefixEnd_416799 : Nat := 4983230072969 + 3 ^ 40 * 416799 * 2
def baseEnd_416799 : Nat := 42275204605120001125073

theorem tailTrace_416799 : CollatzResearch.WordTrace tailWord_416799 prefixEnd_416799 42275204605120001125073 := by
  unfold tailWord_416799
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201908417015881447093451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10134605611343920964728967 15201908417015881447093451)
  ·
    refine ⟨22802862625523822170640177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15201908417015881447093451 22802862625523822170640177)
    ·
      refine ⟨17102146969142866627980133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22802862625523822170640177 17102146969142866627980133)
      ·
        refine ⟨3206652556714287492746275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17102146969142866627980133 3206652556714287492746275)
        ·
          refine ⟨4809978835071431239119413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206652556714287492746275 4809978835071431239119413)
          ·
            refine ⟨450935515787946678667445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4809978835071431239119413 450935515787946678667445)
            ·
              refine ⟨42275204605120001125073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 450935515787946678667445 42275204605120001125073)
              ·
                rfl

theorem cell19_416799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_416799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416799 prefixEnd_416799 := by exact prefixLift 416799
  have htrace : WordTrace (prefixWord ++ tailWord_416799) baseStart_416799 baseEnd_416799 := by
    simpa [prefixWord, tailWord_416799, baseEnd_416799] using wordTrace_append hprefix tailTrace_416799
  have hstable : (prefixWord ++ tailWord_416799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416799).length < 2 ^ (prefixWord ++ tailWord_416799).sum := by decide
  have hdescent : baseEnd_416799 < baseStart_416799 := by decide
  rcases family_descends (prefixWord ++ tailWord_416799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416818 : List Nat := [3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_416818 : Nat := 118140960795 + 416818 * 2 ^ 59
def prefixEnd_416818 : Nat := 4983230072969 + 3 ^ 40 * 416818 * 2
def baseEnd_416818 : Nat := 126831395227173588952945

theorem tailTrace_416818 : CollatzResearch.WordTrace tailWord_416818 prefixEnd_416818 126831395227173588952945 := by
  unfold tailWord_416818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800650350986761923008777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10135067602631365128023405 3800650350986761923008777)
  ·
    refine ⟨2850487763240071442256583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3800650350986761923008777 2850487763240071442256583)
    ·
      refine ⟨4275731644860107163384875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850487763240071442256583 4275731644860107163384875)
      ·
        refine ⟨6413597467290160745077313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275731644860107163384875 6413597467290160745077313)
        ·
          refine ⟨4810198100467620558807985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413597467290160745077313 4810198100467620558807985)
          ·
            refine ⟨3607648575350715419105989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4810198100467620558807985 3607648575350715419105989)
            ·
              refine ⟨676434107878259141082373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3607648575350715419105989 676434107878259141082373)
              ·
                refine ⟨126831395227173588952945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676434107878259141082373 126831395227173588952945)
                ·
                  rfl

theorem cell19_416818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_416818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416818 prefixEnd_416818 := by exact prefixLift 416818
  have htrace : WordTrace (prefixWord ++ tailWord_416818) baseStart_416818 baseEnd_416818 := by
    simpa [prefixWord, tailWord_416818, baseEnd_416818] using wordTrace_append hprefix tailTrace_416818
  have hstable : (prefixWord ++ tailWord_416818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416818).length < 2 ^ (prefixWord ++ tailWord_416818).sum := by decide
  have hdescent : baseEnd_416818 < baseStart_416818 := by decide
  rcases family_descends (prefixWord ++ tailWord_416818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416854 : List Nat := [5, 2, 2, 1, 9]
def baseStart_416854 : Nat := 118140960795 + 416854 * 2 ^ 59
def prefixEnd_416854 : Nat := 4983230072969 + 3 ^ 40 * 416854 * 2
def baseEnd_416854 : Nat := 4697864795597636005661

theorem tailTrace_416854 : CollatzResearch.WordTrace tailWord_416854 prefixEnd_416854 4697864795597636005661 := by
  unfold tailWord_416854
  simp only [CollatzResearch.WordTrace]
  refine ⟨950244651988539115021601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10135942954544417226897077 950244651988539115021601)
  ·
    refine ⟨712683488991404336266201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 950244651988539115021601 712683488991404336266201)
    ·
      refine ⟨534512616743553252199651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712683488991404336266201 534512616743553252199651)
      ·
        refine ⟨801768925115329878299477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534512616743553252199651 801768925115329878299477)
        ·
          refine ⟨4697864795597636005661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 801768925115329878299477 4697864795597636005661)
          ·
            rfl

theorem cell19_416854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 9].length) (baseStart_416854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416854 prefixEnd_416854 := by exact prefixLift 416854
  have htrace : WordTrace (prefixWord ++ tailWord_416854) baseStart_416854 baseEnd_416854 := by
    simpa [prefixWord, tailWord_416854, baseEnd_416854] using wordTrace_append hprefix tailTrace_416854
  have hstable : (prefixWord ++ tailWord_416854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416854).length < 2 ^ (prefixWord ++ tailWord_416854).sum := by decide
  have hdescent : baseEnd_416854 < baseStart_416854 := by decide
  rcases family_descends (prefixWord ++ tailWord_416854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416896 : List Nat := [2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_416896 : Nat := 118140960795 + 416896 * 2 ^ 59
def prefixEnd_416896 : Nat := 4983230072969 + 3 ^ 40 * 416896 * 2
def baseEnd_416896 : Nat := 126855129444092519219399

theorem tailTrace_416896 : CollatzResearch.WordTrace tailWord_416896 prefixEnd_416896 126855129444092519219399 := by
  unfold tailWord_416896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602723148832233506687271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10136964198442978008916361 7602723148832233506687271)
  ·
    refine ⟨11404084723248350260030907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7602723148832233506687271 11404084723248350260030907)
    ·
      refine ⟨17106127084872525390046361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11404084723248350260030907 17106127084872525390046361)
      ·
        refine ⟨12829595313654394042534771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17106127084872525390046361 12829595313654394042534771)
        ·
          refine ⟨19244392970481591063802157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12829595313654394042534771 19244392970481591063802157)
          ·
            refine ⟨7216647363930596648925809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19244392970481591063802157 7216647363930596648925809)
            ·
              refine ⟨5412485522947947486694357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216647363930596648925809 5412485522947947486694357)
              ·
                refine ⟨126855129444092519219399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5412485522947947486694357 126855129444092519219399)
                ·
                  rfl

theorem cell19_416896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_416896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416896 prefixEnd_416896 := by exact prefixLift 416896
  have htrace : WordTrace (prefixWord ++ tailWord_416896) baseStart_416896 baseEnd_416896 := by
    simpa [prefixWord, tailWord_416896, baseEnd_416896] using wordTrace_append hprefix tailTrace_416896
  have hstable : (prefixWord ++ tailWord_416896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416896).length < 2 ^ (prefixWord ++ tailWord_416896).sum := by decide
  have hdescent : baseEnd_416896 < baseStart_416896 := by decide
  rcases family_descends (prefixWord ++ tailWord_416896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416970 : List Nat := [3, 1, 2, 1, 3, 4, 5]
def baseStart_416970 : Nat := 118140960795 + 416970 * 2 ^ 59
def prefixEnd_416970 : Nat := 4983230072969 + 3 ^ 40 * 416970 * 2
def baseEnd_416970 : Nat := 42292548840560757858251

theorem tailTrace_416970 : CollatzResearch.WordTrace tailWord_416970 prefixEnd_416970 42292548840560757858251 := by
  unfold tailWord_416970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802036324849094412892091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10138763532930918434378909 3802036324849094412892091)
  ·
    refine ⟨5703054487273641619338137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802036324849094412892091 5703054487273641619338137)
    ·
      refine ⟨4277290865455231214503603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5703054487273641619338137 4277290865455231214503603)
      ·
        refine ⟨6415936298182846821755405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277290865455231214503603 6415936298182846821755405)
        ·
          refine ⟨2405976111818567558158277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6415936298182846821755405 2405976111818567558158277)
          ·
            refine ⟨451120520965981417154677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2405976111818567558158277 451120520965981417154677)
            ·
              refine ⟨42292548840560757858251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451120520965981417154677 42292548840560757858251)
              ·
                rfl

theorem cell19_416970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_416970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416970 prefixEnd_416970 := by exact prefixLift 416970
  have htrace : WordTrace (prefixWord ++ tailWord_416970) baseStart_416970 baseEnd_416970 := by
    simpa [prefixWord, tailWord_416970, baseEnd_416970] using wordTrace_append hprefix tailTrace_416970
  have hstable : (prefixWord ++ tailWord_416970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416970).length < 2 ^ (prefixWord ++ tailWord_416970).sum := by decide
  have hdescent : baseEnd_416970 < baseStart_416970 := by decide
  rcases family_descends (prefixWord ++ tailWord_416970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416991 : List Nat := [1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_416991 : Nat := 118140960795 + 416991 * 2 ^ 59
def prefixEnd_416991 : Nat := 4983230072969 + 3 ^ 40 * 416991 * 2
def baseEnd_416991 : Nat := 126884036503160447108029

theorem tailTrace_416991 : CollatzResearch.WordTrace tailWord_416991 prefixEnd_416991 126884036503160447108029 := by
  unfold tailWord_416991
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208911232320298238082827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139274154880198825388551 15208911232320298238082827)
  ·
    refine ⟨22813366848480447357124241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15208911232320298238082827 22813366848480447357124241)
    ·
      refine ⟨17110025136360335517843181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22813366848480447357124241 17110025136360335517843181)
      ·
        refine ⟨6416259426135125819191193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17110025136360335517843181 6416259426135125819191193)
        ·
          refine ⟨4812194569601344364393395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6416259426135125819191193 4812194569601344364393395)
          ·
            refine ⟨7218291854402016546590093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812194569601344364393395 7218291854402016546590093)
            ·
              refine ⟨2706859445400756204971285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7218291854402016546590093 2706859445400756204971285)
              ·
                refine ⟨126884036503160447108029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2706859445400756204971285 126884036503160447108029)
                ·
                  rfl

theorem cell19_416991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_416991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_416991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_416991 prefixEnd_416991 := by exact prefixLift 416991
  have htrace : WordTrace (prefixWord ++ tailWord_416991) baseStart_416991 baseEnd_416991 := by
    simpa [prefixWord, tailWord_416991, baseEnd_416991] using wordTrace_append hprefix tailTrace_416991
  have hstable : (prefixWord ++ tailWord_416991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416991).length < 2 ^ (prefixWord ++ tailWord_416991).sum := by decide
  have hdescent : baseEnd_416991 < baseStart_416991 := by decide
  rcases family_descends (prefixWord ++ tailWord_416991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417105 : List Nat := [1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_417105 : Nat := 118140960795 + 417105 * 2 ^ 59
def prefixEnd_417105 : Nat := 4983230072969 + 3 ^ 40 * 417105 * 2
def baseEnd_417105 : Nat := 126918724974041960574385

theorem tailTrace_417105 : CollatzResearch.WordTrace tailWord_417105 prefixEnd_417105 126918724974041960574385 := by
  unfold tailWord_417105
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213069153907295707732769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10142046102604863805155179 15213069153907295707732769)
  ·
    refine ⟨11409801865430471780799577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15213069153907295707732769 11409801865430471780799577)
    ·
      refine ⟨8557351399072853835599683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11409801865430471780799577 8557351399072853835599683)
      ·
        refine ⟨12836027098609280753399525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557351399072853835599683 12836027098609280753399525)
        ·
          refine ⟨2406755080989240141262411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12836027098609280753399525 2406755080989240141262411)
          ·
            refine ⟨3610132621483860211893617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406755080989240141262411 3610132621483860211893617)
            ·
              refine ⟨2707599466112895158920213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610132621483860211893617 2707599466112895158920213)
              ·
                refine ⟨126918724974041960574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2707599466112895158920213 126918724974041960574385)
                ·
                  rfl

theorem cell19_417105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_417105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417105 prefixEnd_417105 := by exact prefixLift 417105
  have htrace : WordTrace (prefixWord ++ tailWord_417105) baseStart_417105 baseEnd_417105 := by
    simpa [prefixWord, tailWord_417105, baseEnd_417105] using wordTrace_append hprefix tailTrace_417105
  have hstable : (prefixWord ++ tailWord_417105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417105).length < 2 ^ (prefixWord ++ tailWord_417105).sum := by decide
  have hdescent : baseEnd_417105 < baseStart_417105 := by decide
  rcases family_descends (prefixWord ++ tailWord_417105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417120 : List Nat := [2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_417120 : Nat := 118140960795 + 417120 * 2 ^ 59
def prefixEnd_417120 : Nat := 4983230072969 + 3 ^ 40 * 417120 * 2
def baseEnd_417120 : Nat := 126923289246526370241011

theorem tailTrace_417120 : CollatzResearch.WordTrace tailWord_417120 prefixEnd_417120 126923289246526370241011 := by
  unfold tailWord_417120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7606808124426476634764407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10142410832568635513019209 7606808124426476634764407)
  ·
    refine ⟨11410212186639714952146611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7606808124426476634764407 11410212186639714952146611)
    ·
      refine ⟨17115318279959572428219917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11410212186639714952146611 17115318279959572428219917)
      ·
        refine ⟨6418244354984839660582469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17115318279959572428219917 6418244354984839660582469)
        ·
          refine ⟨1203420816559657436359213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6418244354984839660582469 1203420816559657436359213)
          ·
            refine ⟨451282806209871538634705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1203420816559657436359213 451282806209871538634705)
            ·
              refine ⟨338462104657403653976029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451282806209871538634705 338462104657403653976029)
              ·
                refine ⟨126923289246526370241011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338462104657403653976029 126923289246526370241011)
                ·
                  rfl

theorem cell19_417120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_417120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417120 prefixEnd_417120 := by exact prefixLift 417120
  have htrace : WordTrace (prefixWord ++ tailWord_417120) baseStart_417120 baseEnd_417120 := by
    simpa [prefixWord, tailWord_417120, baseEnd_417120] using wordTrace_append hprefix tailTrace_417120
  have hstable : (prefixWord ++ tailWord_417120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417120).length < 2 ^ (prefixWord ++ tailWord_417120).sum := by decide
  have hdescent : baseEnd_417120 < baseStart_417120 := by decide
  rcases family_descends (prefixWord ++ tailWord_417120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417122 : List Nat := [3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_417122 : Nat := 118140960795 + 417122 * 2 ^ 59
def prefixEnd_417122 : Nat := 4983230072969 + 3 ^ 40 * 417122 * 2
def baseEnd_417122 : Nat := 126923897816190958196561

theorem tailTrace_417122 : CollatzResearch.WordTrace tailWord_417122 prefixEnd_417122 126923897816190958196561 := by
  unfold tailWord_417122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803422298711426902775405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10142459463230471740734413 3803422298711426902775405)
  ·
    refine ⟨1426283362016785088540777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3803422298711426902775405 1426283362016785088540777)
    ·
      refine ⟨1069712521512588816405583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1426283362016785088540777 1069712521512588816405583)
      ·
        refine ⟨1604568782268883224608375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069712521512588816405583 1604568782268883224608375)
        ·
          refine ⟨2406853173403324836912563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604568782268883224608375 2406853173403324836912563)
          ·
            refine ⟨3610279760104987255368845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406853173403324836912563 3610279760104987255368845)
            ·
              refine ⟨1353854910039370220763317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610279760104987255368845 1353854910039370220763317)
              ·
                refine ⟨126923897816190958196561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1353854910039370220763317 126923897816190958196561)
                ·
                  rfl

theorem cell19_417122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_417122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417122 prefixEnd_417122 := by exact prefixLift 417122
  have htrace : WordTrace (prefixWord ++ tailWord_417122) baseStart_417122 baseEnd_417122 := by
    simpa [prefixWord, tailWord_417122, baseEnd_417122] using wordTrace_append hprefix tailTrace_417122
  have hstable : (prefixWord ++ tailWord_417122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417122).length < 2 ^ (prefixWord ++ tailWord_417122).sum := by decide
  have hdescent : baseEnd_417122 < baseStart_417122 := by decide
  rcases family_descends (prefixWord ++ tailWord_417122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417160 : List Nat := [2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_417160 : Nat := 118140960795 + 417160 * 2 ^ 59
def prefixEnd_417160 : Nat := 4983230072969 + 3 ^ 40 * 417160 * 2
def baseEnd_417160 : Nat := 126935460639818129352013

theorem tailTrace_417160 : CollatzResearch.WordTrace tailWord_417160 prefixEnd_417160 126935460639818129352013 := by
  unfold tailWord_417160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607537584354020050492467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10143383445805360067323289 7607537584354020050492467)
  ·
    refine ⟨11411306376531030075738701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7607537584354020050492467 11411306376531030075738701)
    ·
      refine ⟨4279239891199136278402013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11411306376531030075738701 4279239891199136278402013)
      ·
        refine ⟨1604714959199676104400755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4279239891199136278402013 1604714959199676104400755)
        ·
          refine ⟨2407072438799514156601133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604714959199676104400755 2407072438799514156601133)
          ·
            refine ⟨902652164549817808725425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407072438799514156601133 902652164549817808725425)
            ·
              refine ⟨676989123412363356544069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902652164549817808725425 676989123412363356544069)
              ·
                refine ⟨126935460639818129352013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676989123412363356544069 126935460639818129352013)
                ·
                  rfl

theorem cell19_417160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_417160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417160 prefixEnd_417160 := by exact prefixLift 417160
  have htrace : WordTrace (prefixWord ++ tailWord_417160) baseStart_417160 baseEnd_417160 := by
    simpa [prefixWord, tailWord_417160, baseEnd_417160] using wordTrace_append hprefix tailTrace_417160
  have hstable : (prefixWord ++ tailWord_417160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417160).length < 2 ^ (prefixWord ++ tailWord_417160).sum := by decide
  have hdescent : baseEnd_417160 < baseStart_417160 := by decide
  rcases family_descends (prefixWord ++ tailWord_417160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417219 : List Nat := [1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_417219 : Nat := 118140960795 + 417219 * 2 ^ 59
def prefixEnd_417219 : Nat := 4983230072969 + 3 ^ 40 * 417219 * 2
def baseEnd_417219 : Nat := 126953413444923474040741

theorem tailTrace_417219 : CollatzResearch.WordTrace tailWord_417219 prefixEnd_417219 126953413444923474040741 := by
  unfold tailWord_417219
  simp only [CollatzResearch.WordTrace]
  refine ⟨15217227075494293177382711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10144818050329528784921807 15217227075494293177382711)
  ·
    refine ⟨22825840613241439766074067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15217227075494293177382711 22825840613241439766074067)
    ·
      refine ⟨34238760919862159649111101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22825840613241439766074067 34238760919862159649111101)
      ·
        refine ⟨12839535344948309868416663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34238760919862159649111101 12839535344948309868416663)
        ·
          refine ⟨19259303017422464802624995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839535344948309868416663 19259303017422464802624995)
          ·
            refine ⟨28888954526133697203937493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19259303017422464802624995 28888954526133697203937493)
            ·
              refine ⟨677084871706258528217285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28888954526133697203937493 677084871706258528217285)
              ·
                refine ⟨126953413444923474040741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677084871706258528217285 126953413444923474040741)
                ·
                  rfl

theorem cell19_417219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_417219 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417219 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417219 prefixEnd_417219 := by exact prefixLift 417219
  have htrace : WordTrace (prefixWord ++ tailWord_417219) baseStart_417219 baseEnd_417219 := by
    simpa [prefixWord, tailWord_417219, baseEnd_417219] using wordTrace_append hprefix tailTrace_417219
  have hstable : (prefixWord ++ tailWord_417219).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417219).length < 2 ^ (prefixWord ++ tailWord_417219).sum := by decide
  have hdescent : baseEnd_417219 < baseStart_417219 := by decide
  rcases family_descends (prefixWord ++ tailWord_417219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417291 : List Nat := [1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_417291 : Nat := 118140960795 + 417291 * 2 ^ 59
def prefixEnd_417291 : Nat := 4983230072969 + 3 ^ 40 * 417291 * 2
def baseEnd_417291 : Nat := 126975321952848640440545

theorem tailTrace_417291 : CollatzResearch.WordTrace tailWord_417291 prefixEnd_417291 126975321952848640440545 := by
  unfold tailWord_417291
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219853131233449474003727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10146568754155632982669151 15219853131233449474003727)
  ·
    refine ⟨22829779696850174211005591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15219853131233449474003727 22829779696850174211005591)
    ·
      refine ⟨34244669545275261316508387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829779696850174211005591 34244669545275261316508387)
      ·
        refine ⟨51367004317912891974762581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34244669545275261316508387 51367004317912891974762581)
        ·
          refine ⟨601957081850541702829249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 51367004317912891974762581 601957081850541702829249)
          ·
            refine ⟨451467811387906277121937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601957081850541702829249 451467811387906277121937)
            ·
              refine ⟨338600858540929707841453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451467811387906277121937 338600858540929707841453)
              ·
                refine ⟨126975321952848640440545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338600858540929707841453 126975321952848640440545)
                ·
                  rfl

theorem cell19_417291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_417291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417291 prefixEnd_417291 := by exact prefixLift 417291
  have htrace : WordTrace (prefixWord ++ tailWord_417291) baseStart_417291 baseEnd_417291 := by
    simpa [prefixWord, tailWord_417291, baseEnd_417291] using wordTrace_append hprefix tailTrace_417291
  have hstable : (prefixWord ++ tailWord_417291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417291).length < 2 ^ (prefixWord ++ tailWord_417291).sum := by decide
  have hdescent : baseEnd_417291 < baseStart_417291 := by decide
  rcases family_descends (prefixWord ++ tailWord_417291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417312 : List Nat := [2, 1, 1, 6, 1, 3, 5]
def baseStart_417312 : Nat := 118140960795 + 417312 * 2 ^ 59
def prefixEnd_417312 : Nat := 4983230072969 + 3 ^ 40 * 417312 * 2
def baseEnd_417312 : Nat := 42327237311442271324607

theorem tailTrace_417312 : CollatzResearch.WordTrace tailWord_417312 prefixEnd_417312 42327237311442271324607 := by
  unfold tailWord_417312
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610309532078685030259095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10147079376104913373678793 7610309532078685030259095)
  ·
    refine ⟨11415464298118027545388643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7610309532078685030259095 11415464298118027545388643)
    ·
      refine ⟨17123196447177041318082965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11415464298118027545388643 17123196447177041318082965)
      ·
        refine ⟨802649833461423811785139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17123196447177041318082965 802649833461423811785139)
        ·
          refine ⟨1203974750192135717677709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802649833461423811785139 1203974750192135717677709)
          ·
            refine ⟨451490531322050894129141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1203974750192135717677709 451490531322050894129141)
            ·
              refine ⟨42327237311442271324607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451490531322050894129141 42327237311442271324607)
              ·
                rfl

theorem cell19_417312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_417312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417312 prefixEnd_417312 := by exact prefixLift 417312
  have htrace : WordTrace (prefixWord ++ tailWord_417312) baseStart_417312 baseEnd_417312 := by
    simpa [prefixWord, tailWord_417312, baseEnd_417312] using wordTrace_append hprefix tailTrace_417312
  have hstable : (prefixWord ++ tailWord_417312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417312).length < 2 ^ (prefixWord ++ tailWord_417312).sum := by decide
  have hdescent : baseEnd_417312 < baseStart_417312 := by decide
  rcases family_descends (prefixWord ++ tailWord_417312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417314 : List Nat := [3, 3, 1, 1, 1, 1, 9]
def baseStart_417314 : Nat := 118140960795 + 417314 * 2 ^ 59
def prefixEnd_417314 : Nat := 4983230072969 + 3 ^ 40 * 417314 * 2
def baseEnd_417314 : Nat := 42327440167997133976457

theorem tailTrace_417314 : CollatzResearch.WordTrace tailWord_417314 prefixEnd_417314 42327440167997133976457 := by
  unfold tailWord_417314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805173002537531100522749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10147128006766749601393997 3805173002537531100522749)
  ·
    refine ⟨1426939875951574162696031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3805173002537531100522749 1426939875951574162696031)
    ·
      refine ⟨2140409813927361244044047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426939875951574162696031 2140409813927361244044047)
      ·
        refine ⟨3210614720891041866066071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140409813927361244044047 3210614720891041866066071)
        ·
          refine ⟨4815922081336562799099107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210614720891041866066071 4815922081336562799099107)
          ·
            refine ⟨7223883122004844198648661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815922081336562799099107 7223883122004844198648661)
            ·
              refine ⟨42327440167997133976457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7223883122004844198648661 42327440167997133976457)
              ·
                rfl

theorem cell19_417314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_417314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417314 prefixEnd_417314 := by exact prefixLift 417314
  have htrace : WordTrace (prefixWord ++ tailWord_417314) baseStart_417314 baseEnd_417314 := by
    simpa [prefixWord, tailWord_417314, baseEnd_417314] using wordTrace_append hprefix tailTrace_417314
  have hstable : (prefixWord ++ tailWord_417314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417314).length < 2 ^ (prefixWord ++ tailWord_417314).sum := by decide
  have hdescent : baseEnd_417314 < baseStart_417314 := by decide
  rcases family_descends (prefixWord ++ tailWord_417314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417333 : List Nat := [1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_417333 : Nat := 118140960795 + 417333 * 2 ^ 59
def prefixEnd_417333 : Nat := 4983230072969 + 3 ^ 40 * 417333 * 2
def baseEnd_417333 : Nat := 126988101915804987507097

theorem tailTrace_417333 : CollatzResearch.WordTrace tailWord_417333 prefixEnd_417333 126988101915804987507097 := by
  unfold tailWord_417333
  simp only [CollatzResearch.WordTrace]
  refine ⟨15221384997081290647032653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10147589998054193764688435 15221384997081290647032653)
  ·
    refine ⟨5708019373905483992637245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15221384997081290647032653 5708019373905483992637245)
    ·
      refine ⟨2140507265214556497238967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5708019373905483992637245 2140507265214556497238967)
      ·
        refine ⟨3210760897821834745858451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140507265214556497238967 3210760897821834745858451)
        ·
          refine ⟨4816141346732752118787677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210760897821834745858451 4816141346732752118787677)
          ·
            refine ⟨1806053005024782044545379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4816141346732752118787677 1806053005024782044545379)
            ·
              refine ⟨2709079507537173066818069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806053005024782044545379 2709079507537173066818069)
              ·
                refine ⟨126988101915804987507097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2709079507537173066818069 126988101915804987507097)
                ·
                  rfl

theorem cell19_417333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_417333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417333 prefixEnd_417333 := by exact prefixLift 417333
  have htrace : WordTrace (prefixWord ++ tailWord_417333) baseStart_417333 baseEnd_417333 := by
    simpa [prefixWord, tailWord_417333, baseEnd_417333] using wordTrace_append hprefix tailTrace_417333
  have hstable : (prefixWord ++ tailWord_417333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417333).length < 2 ^ (prefixWord ++ tailWord_417333).sum := by decide
  have hdescent : baseEnd_417333 < baseStart_417333 := by decide
  rcases family_descends (prefixWord ++ tailWord_417333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417426 : List Nat := [3, 2, 3, 1, 3, 1, 6]
def baseStart_417426 : Nat := 118140960795 + 417426 * 2 ^ 59
def prefixEnd_417426 : Nat := 4983230072969 + 3 ^ 40 * 417426 * 2
def baseEnd_417426 : Nat := 42338800135069442480059

theorem tailTrace_417426 : CollatzResearch.WordTrace tailWord_417426 prefixEnd_417426 42338800135069442480059 := by
  unfold tailWord_417426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806194246436091882542033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10149851323829578353445421 3806194246436091882542033)
  ·
    refine ⟨2854645684827068911906525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3806194246436091882542033 2854645684827068911906525)
    ·
      refine ⟨1070492131810150841964947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2854645684827068911906525 1070492131810150841964947)
      ·
        refine ⟨1605738197715226262947421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070492131810150841964947 1605738197715226262947421)
        ·
          refine ⟨602151824143209848605283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1605738197715226262947421 602151824143209848605283)
          ·
            refine ⟨903227736214814772907925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602151824143209848605283 903227736214814772907925)
            ·
              refine ⟨42338800135069442480059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 903227736214814772907925 42338800135069442480059)
              ·
                rfl

theorem cell19_417426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_417426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417426 prefixEnd_417426 := by exact prefixLift 417426
  have htrace : WordTrace (prefixWord ++ tailWord_417426) baseStart_417426 baseEnd_417426 := by
    simpa [prefixWord, tailWord_417426, baseEnd_417426] using wordTrace_append hprefix tailTrace_417426
  have hstable : (prefixWord ++ tailWord_417426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417426).length < 2 ^ (prefixWord ++ tailWord_417426).sum := by decide
  have hdescent : baseEnd_417426 < baseStart_417426 := by decide
  rcases family_descends (prefixWord ++ tailWord_417426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417462 : List Nat := [5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_417462 : Nat := 118140960795 + 417462 * 2 ^ 59
def prefixEnd_417462 : Nat := 4983230072969 + 3 ^ 40 * 417462 * 2
def baseEnd_417462 : Nat := 127027354659170910640079

theorem tailTrace_417462 : CollatzResearch.WordTrace tailWord_417462 prefixEnd_417462 127027354659170910640079 := by
  unfold tailWord_417462
  simp only [CollatzResearch.WordTrace]
  refine ⟨951630625850871604904915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10150726675742630452319093 951630625850871604904915)
  ·
    refine ⟨1427445938776307407357373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951630625850871604904915 1427445938776307407357373)
    ·
      refine ⟨535292227041115277759015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1427445938776307407357373 535292227041115277759015)
      ·
        refine ⟨802938340561672916638523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535292227041115277759015 802938340561672916638523)
        ·
          refine ⟨1204407510842509374957785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802938340561672916638523 1204407510842509374957785)
          ·
            refine ⟨903305633131882031218339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204407510842509374957785 903305633131882031218339)
            ·
              refine ⟨1354958449697823046827509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903305633131882031218339 1354958449697823046827509)
              ·
                refine ⟨127027354659170910640079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1354958449697823046827509 127027354659170910640079)
                ·
                  rfl

theorem cell19_417462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_417462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417462 prefixEnd_417462 := by exact prefixLift 417462
  have htrace : WordTrace (prefixWord ++ tailWord_417462) baseStart_417462 baseEnd_417462 := by
    simpa [prefixWord, tailWord_417462, baseEnd_417462] using wordTrace_append hprefix tailTrace_417462
  have hstable : (prefixWord ++ tailWord_417462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417462).length < 2 ^ (prefixWord ++ tailWord_417462).sum := by decide
  have hdescent : baseEnd_417462 < baseStart_417462 := by decide
  rcases family_descends (prefixWord ++ tailWord_417462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417466 : List Nat := [3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_417466 : Nat := 118140960795 + 417466 * 2 ^ 59
def prefixEnd_417466 : Nat := 4983230072969 + 3 ^ 40 * 417466 * 2
def baseEnd_417466 : Nat := 127028571798500086551179

theorem tailTrace_417466 : CollatzResearch.WordTrace tailWord_417466 prefixEnd_417466 127028571798500086551179 := by
  unfold tailWord_417466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806558976399863590406063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10150823937066302907749501 3806558976399863590406063)
  ·
    refine ⟨5709838464599795385609095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3806558976399863590406063 5709838464599795385609095)
    ·
      refine ⟨8564757696899693078413643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709838464599795385609095 8564757696899693078413643)
      ·
        refine ⟨12847136545349539617620465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564757696899693078413643 12847136545349539617620465)
        ·
          refine ⟨9635352409012154713215349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12847136545349539617620465 9635352409012154713215349)
          ·
            refine ⟨903314288344889504363939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9635352409012154713215349 903314288344889504363939)
            ·
              refine ⟨1354971432517334256545909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903314288344889504363939 1354971432517334256545909)
              ·
                refine ⟨127028571798500086551179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1354971432517334256545909 127028571798500086551179)
                ·
                  rfl

theorem cell19_417466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_417466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417466 prefixEnd_417466 := by exact prefixLift 417466
  have htrace : WordTrace (prefixWord ++ tailWord_417466) baseStart_417466 baseEnd_417466 := by
    simpa [prefixWord, tailWord_417466, baseEnd_417466] using wordTrace_append hprefix tailTrace_417466
  have hstable : (prefixWord ++ tailWord_417466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417466).length < 2 ^ (prefixWord ++ tailWord_417466).sum := by decide
  have hdescent : baseEnd_417466 < baseStart_417466 := by decide
  rcases family_descends (prefixWord ++ tailWord_417466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417500 : List Nat := [2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_417500 : Nat := 118140960795 + 417500 * 2 ^ 59
def prefixEnd_417500 : Nat := 4983230072969 + 3 ^ 40 * 417500 * 2
def baseEnd_417500 : Nat := 127038917482798081795531

theorem tailTrace_417500 : CollatzResearch.WordTrace tailWord_417500 prefixEnd_417500 127038917482798081795531 := by
  unfold tailWord_417500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7613737993738139084180977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10151650658317518778907969 7613737993738139084180977)
  ·
    refine ⟨5710303495303604313135733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7613737993738139084180977 5710303495303604313135733)
    ·
      refine ⟨535340952684712904356475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5710303495303604313135733 535340952684712904356475)
      ·
        refine ⟨803011429027069356534713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535340952684712904356475 803011429027069356534713)
        ·
          refine ⟨602258571770302017401035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803011429027069356534713 602258571770302017401035)
          ·
            refine ⟨903387857655453026101553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602258571770302017401035 903387857655453026101553)
            ·
              refine ⟨677540893241589769576165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903387857655453026101553 677540893241589769576165)
              ·
                refine ⟨127038917482798081795531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677540893241589769576165 127038917482798081795531)
                ·
                  rfl

theorem cell19_417500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_417500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417500 prefixEnd_417500 := by exact prefixLift 417500
  have htrace : WordTrace (prefixWord ++ tailWord_417500) baseStart_417500 baseEnd_417500 := by
    simpa [prefixWord, tailWord_417500, baseEnd_417500] using wordTrace_append hprefix tailTrace_417500
  have hstable : (prefixWord ++ tailWord_417500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417500).length < 2 ^ (prefixWord ++ tailWord_417500).sum := by decide
  have hdescent : baseEnd_417500 < baseStart_417500 := by decide
  rcases family_descends (prefixWord ++ tailWord_417500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417559 : List Nat := [1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_417559 : Nat := 118140960795 + 417559 * 2 ^ 59
def prefixEnd_417559 : Nat := 4983230072969 + 3 ^ 40 * 417559 * 2
def baseEnd_417559 : Nat := 127056870287903426484259

theorem tailTrace_417559 : CollatzResearch.WordTrace tailWord_417559 prefixEnd_417559 127056870287903426484259 := by
  unfold tailWord_417559
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229627894262531244759731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10153085262841687496506487 15229627894262531244759731)
  ·
    refine ⟨22844441841393796867139597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15229627894262531244759731 22844441841393796867139597)
    ·
      refine ⟨8566665690522673825177349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22844441841393796867139597 8566665690522673825177349)
      ·
        refine ⟨1606249816973001342220753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8566665690522673825177349 1606249816973001342220753)
        ·
          refine ⟨1204687362729751006665565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606249816973001342220753 1204687362729751006665565)
          ·
            refine ⟨451757761023656627499587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1204687362729751006665565 451757761023656627499587)
            ·
              refine ⟨677636641535484941249381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451757761023656627499587 677636641535484941249381)
              ·
                refine ⟨127056870287903426484259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677636641535484941249381 127056870287903426484259)
                ·
                  rfl

theorem cell19_417559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_417559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417559 prefixEnd_417559 := by exact prefixLift 417559
  have htrace : WordTrace (prefixWord ++ tailWord_417559) baseStart_417559 baseEnd_417559 := by
    simpa [prefixWord, tailWord_417559, baseEnd_417559] using wordTrace_append hprefix tailTrace_417559
  have hstable : (prefixWord ++ tailWord_417559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417559).length < 2 ^ (prefixWord ++ tailWord_417559).sum := by decide
  have hdescent : baseEnd_417559 < baseStart_417559 := by decide
  rcases family_descends (prefixWord ++ tailWord_417559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417599 : List Nat := [1, 1, 2, 2, 6, 1, 6]
def baseStart_417599 : Nat := 118140960795 + 417599 * 2 ^ 59
def prefixEnd_417599 : Nat := 4983230072969 + 3 ^ 40 * 417599 * 2
def baseEnd_417599 : Nat := 42356347227065061865087

theorem tailTrace_417599 : CollatzResearch.WordTrace tailWord_417599 prefixEnd_417599 42356347227065061865087 := by
  unfold tailWord_417599
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231086814117618076215851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10154057876078412050810567 15231086814117618076215851)
  ·
    refine ⟨22846630221176427114323777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15231086814117618076215851 22846630221176427114323777)
    ·
      refine ⟨17134972665882320335742833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22846630221176427114323777 17134972665882320335742833)
      ·
        refine ⟨12851229499411740251807125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17134972665882320335742833 12851229499411740251807125)
        ·
          refine ⟨602401382784925324303459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12851229499411740251807125 602401382784925324303459)
          ·
            refine ⟨903602074177387986455189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602401382784925324303459 903602074177387986455189)
            ·
              refine ⟨42356347227065061865087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 903602074177387986455189 42356347227065061865087)
              ·
                rfl

theorem cell19_417599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_417599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417599 prefixEnd_417599 := by exact prefixLift 417599
  have htrace : WordTrace (prefixWord ++ tailWord_417599) baseStart_417599 baseEnd_417599 := by
    simpa [prefixWord, tailWord_417599, baseEnd_417599] using wordTrace_append hprefix tailTrace_417599
  have hstable : (prefixWord ++ tailWord_417599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417599).length < 2 ^ (prefixWord ++ tailWord_417599).sum := by decide
  have hdescent : baseEnd_417599 < baseStart_417599 := by decide
  rcases family_descends (prefixWord ++ tailWord_417599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417658 : List Nat := [3, 1, 1, 1, 1, 1, 11]
def baseStart_417658 : Nat := 118140960795 + 417658 * 2 ^ 59
def prefixEnd_417658 : Nat := 4983230072969 + 3 ^ 40 * 417658 * 2
def baseEnd_417658 : Nat := 42362331495433510094663

theorem tailTrace_417658 : CollatzResearch.WordTrace tailWord_417658 prefixEnd_417658 42362331495433510094663 := by
  unfold tailWord_417658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808309680225967788153407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10155492480602580768409085 3808309680225967788153407)
  ·
    refine ⟨5712464520338951682230111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808309680225967788153407 5712464520338951682230111)
    ·
      refine ⟨8568696780508427523345167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5712464520338951682230111 8568696780508427523345167)
      ·
        refine ⟨12853045170762641285017751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568696780508427523345167 12853045170762641285017751)
        ·
          refine ⟨19279567756143961927526627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853045170762641285017751 19279567756143961927526627)
          ·
            refine ⟨28919351634215942891289941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19279567756143961927526627 28919351634215942891289941)
            ·
              refine ⟨42362331495433510094663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28919351634215942891289941 42362331495433510094663)
              ·
                rfl

theorem cell19_417658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_417658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417658 prefixEnd_417658 := by exact prefixLift 417658
  have htrace : WordTrace (prefixWord ++ tailWord_417658) baseStart_417658 baseEnd_417658 := by
    simpa [prefixWord, tailWord_417658, baseEnd_417658] using wordTrace_append hprefix tailTrace_417658
  have hstable : (prefixWord ++ tailWord_417658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417658).length < 2 ^ (prefixWord ++ tailWord_417658).sum := by decide
  have hdescent : baseEnd_417658 < baseStart_417658 := by decide
  rcases family_descends (prefixWord ++ tailWord_417658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417749 : List Nat := [1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_417749 : Nat := 118140960795 + 417749 * 2 ^ 59
def prefixEnd_417749 : Nat := 4983230072969 + 3 ^ 40 * 417749 * 2
def baseEnd_417749 : Nat := 127114684406039282261519

theorem tailTrace_417749 : CollatzResearch.WordTrace tailWord_417749 prefixEnd_417749 127114684406039282261519 := by
  unfold tailWord_417749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236557763574193694176301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10157705175716129129450867 15236557763574193694176301)
  ·
    refine ⟨5713709161340322635316113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15236557763574193694176301 5713709161340322635316113)
    ·
      refine ⟨4285281871005241976487085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5713709161340322635316113 4285281871005241976487085)
      ·
        refine ⟨1606980701626965741182657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4285281871005241976487085 1606980701626965741182657)
        ·
          refine ⟨1205235526220224305886993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606980701626965741182657 1205235526220224305886993)
          ·
            refine ⟨903926644665168229415245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1205235526220224305886993 903926644665168229415245)
            ·
              refine ⟨338972491749438086030717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 903926644665168229415245 338972491749438086030717)
              ·
                refine ⟨127114684406039282261519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338972491749438086030717 127114684406039282261519)
                ·
                  rfl

theorem cell19_417749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_417749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417749 prefixEnd_417749 := by exact prefixLift 417749
  have htrace : WordTrace (prefixWord ++ tailWord_417749) baseStart_417749 baseEnd_417749 := by
    simpa [prefixWord, tailWord_417749, baseEnd_417749] using wordTrace_append hprefix tailTrace_417749
  have hstable : (prefixWord ++ tailWord_417749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417749).length < 2 ^ (prefixWord ++ tailWord_417749).sum := by decide
  have hdescent : baseEnd_417749 < baseStart_417749 := by decide
  rcases family_descends (prefixWord ++ tailWord_417749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417751 : List Nat := [1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_417751 : Nat := 118140960795 + 417751 * 2 ^ 59
def prefixEnd_417751 : Nat := 4983230072969 + 3 ^ 40 * 417751 * 2
def baseEnd_417751 : Nat := 127115292975703870217069

theorem tailTrace_417751 : CollatzResearch.WordTrace tailWord_417751 prefixEnd_417751 127115292975703870217069 := by
  unfold tailWord_417751
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236630709566948035749107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10157753806377965357166071 15236630709566948035749107)
  ·
    refine ⟨22854946064350422053623661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15236630709566948035749107 22854946064350422053623661)
    ·
      refine ⟨8570604774131408270108873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22854946064350422053623661 8570604774131408270108873)
      ·
        refine ⟨6427953580598556202581655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8570604774131408270108873 6427953580598556202581655)
        ·
          refine ⟨9641930370897834303872483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427953580598556202581655 9641930370897834303872483)
          ·
            refine ⟨14462895556346751455808725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641930370897834303872483 14462895556346751455808725)
            ·
              refine ⟨338974114601876987245517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14462895556346751455808725 338974114601876987245517)
              ·
                refine ⟨127115292975703870217069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338974114601876987245517 127115292975703870217069)
                ·
                  rfl

theorem cell19_417751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_417751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417751 prefixEnd_417751 := by exact prefixLift 417751
  have htrace : WordTrace (prefixWord ++ tailWord_417751) baseStart_417751 baseEnd_417751 := by
    simpa [prefixWord, tailWord_417751, baseEnd_417751] using wordTrace_append hprefix tailTrace_417751
  have hstable : (prefixWord ++ tailWord_417751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417751).length < 2 ^ (prefixWord ++ tailWord_417751).sum := by decide
  have hdescent : baseEnd_417751 < baseStart_417751 := by decide
  rcases family_descends (prefixWord ++ tailWord_417751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417798 : List Nat := [6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_417798 : Nat := 118140960795 + 417798 * 2 ^ 59
def prefixEnd_417798 : Nat := 4983230072969 + 3 ^ 40 * 417798 * 2
def baseEnd_417798 : Nat := 127129594362821687172497

theorem tailTrace_417798 : CollatzResearch.WordTrace tailWord_417798 prefixEnd_417798 127129594362821687172497 := by
  unfold tailWord_417798
  simp only [CollatzResearch.WordTrace]
  refine ⟨476198279387396095709689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10158896626931116708473365 476198279387396095709689)
  ·
    refine ⟨357148709540547071782267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 476198279387396095709689 357148709540547071782267)
    ·
      refine ⟨535723064310820607673401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357148709540547071782267 535723064310820607673401)
      ·
        refine ⟨401792298233115455755051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535723064310820607673401 401792298233115455755051)
        ·
          refine ⟨602688447349673183632577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401792298233115455755051 602688447349673183632577)
          ·
            refine ⟨452016335512254887724433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602688447349673183632577 452016335512254887724433)
            ·
              refine ⟨339012251634191165793325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452016335512254887724433 339012251634191165793325)
              ·
                refine ⟨127129594362821687172497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339012251634191165793325 127129594362821687172497)
                ·
                  rfl

theorem cell19_417798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_417798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417798 prefixEnd_417798 := by exact prefixLift 417798
  have htrace : WordTrace (prefixWord ++ tailWord_417798) baseStart_417798 baseEnd_417798 := by
    simpa [prefixWord, tailWord_417798, baseEnd_417798] using wordTrace_append hprefix tailTrace_417798
  have hstable : (prefixWord ++ tailWord_417798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417798).length < 2 ^ (prefixWord ++ tailWord_417798).sum := by decide
  have hdescent : baseEnd_417798 < baseStart_417798 := by decide
  rcases family_descends (prefixWord ++ tailWord_417798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417825 : List Nat := [1, 2, 3, 2, 5, 1, 5]
def baseStart_417825 : Nat := 118140960795 + 417825 * 2 ^ 59
def prefixEnd_417825 : Nat := 4983230072969 + 3 ^ 40 * 417825 * 2
def baseEnd_417825 : Nat := 42379270017764541524141

theorem tailTrace_417825 : CollatzResearch.WordTrace tailWord_417825 prefixEnd_417825 42379270017764541524141 := by
  unfold tailWord_417825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15239329711298858673942929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10159553140865905782628619 15239329711298858673942929)
  ·
    refine ⟨11429497283474144005457197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15239329711298858673942929 11429497283474144005457197)
    ·
      refine ⟨4286061481302804002046449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11429497283474144005457197 4286061481302804002046449)
      ·
        refine ⟨3214546110977103001534837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4286061481302804002046449 3214546110977103001534837)
        ·
          refine ⟨301363697904103406393891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3214546110977103001534837 301363697904103406393891)
          ·
            refine ⟨452045546856155109590837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301363697904103406393891 452045546856155109590837)
            ·
              refine ⟨42379270017764541524141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452045546856155109590837 42379270017764541524141)
              ·
                rfl

theorem cell19_417825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_417825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417825 prefixEnd_417825 := by exact prefixLift 417825
  have htrace : WordTrace (prefixWord ++ tailWord_417825) baseStart_417825 baseEnd_417825 := by
    simpa [prefixWord, tailWord_417825, baseEnd_417825] using wordTrace_append hprefix tailTrace_417825
  have hstable : (prefixWord ++ tailWord_417825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417825).length < 2 ^ (prefixWord ++ tailWord_417825).sum := by decide
  have hdescent : baseEnd_417825 < baseStart_417825 := by decide
  rcases family_descends (prefixWord ++ tailWord_417825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417829 : List Nat := [1, 3, 1, 2, 2, 3, 7]
def baseStart_417829 : Nat := 118140960795 + 417829 * 2 ^ 59
def prefixEnd_417829 : Nat := 4983230072969 + 3 ^ 40 * 417829 * 2
def baseEnd_417829 : Nat := 42379675730874266827841

theorem tailTrace_417829 : CollatzResearch.WordTrace tailWord_417829 prefixEnd_417829 42379675730874266827841 := by
  unfold tailWord_417829
  simp only [CollatzResearch.WordTrace]
  refine ⟨15239475603284367357088541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10159650402189578238059027 15239475603284367357088541)
  ·
    refine ⟨5714803351231637758908203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15239475603284367357088541 5714803351231637758908203)
    ·
      refine ⟨8572205026847456638362305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5714803351231637758908203 8572205026847456638362305)
      ·
        refine ⟨6429153770135592478771729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8572205026847456638362305 6429153770135592478771729)
        ·
          refine ⟨4821865327601694359078797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429153770135592478771729 4821865327601694359078797)
          ·
            refine ⟨1808199497850635384654549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4821865327601694359078797 1808199497850635384654549)
            ·
              refine ⟨42379675730874266827841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1808199497850635384654549 42379675730874266827841)
              ·
                rfl

theorem cell19_417829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_417829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417829 prefixEnd_417829 := by exact prefixLift 417829
  have htrace : WordTrace (prefixWord ++ tailWord_417829) baseStart_417829 baseEnd_417829 := by
    simpa [prefixWord, tailWord_417829, baseEnd_417829] using wordTrace_append hprefix tailTrace_417829
  have hstable : (prefixWord ++ tailWord_417829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417829).length < 2 ^ (prefixWord ++ tailWord_417829).sum := by decide
  have hdescent : baseEnd_417829 < baseStart_417829 := by decide
  rcases family_descends (prefixWord ++ tailWord_417829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417903 : List Nat := [1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_417903 : Nat := 118140960795 + 417903 * 2 ^ 59
def prefixEnd_417903 : Nat := 4983230072969 + 3 ^ 40 * 417903 * 2
def baseEnd_417903 : Nat := 127161544270212554838877

theorem tailTrace_417903 : CollatzResearch.WordTrace tailWord_417903 prefixEnd_417903 127161544270212554838877 := by
  unfold tailWord_417903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15242174605016277995282363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10161449736677518663521575 15242174605016277995282363)
  ·
    refine ⟨22863261907524416992923545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15242174605016277995282363 22863261907524416992923545)
    ·
      refine ⟨17147446430643312744692659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22863261907524416992923545 17147446430643312744692659)
      ·
        refine ⟨25721169645964969117038989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17147446430643312744692659 25721169645964969117038989)
        ·
          refine ⟨9645438617236863418889621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25721169645964969117038989 9645438617236863418889621)
          ·
            refine ⟨452129935182977972760451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9645438617236863418889621 452129935182977972760451)
            ·
              refine ⟨678194902774466959140677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452129935182977972760451 678194902774466959140677)
              ·
                refine ⟨127161544270212554838877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678194902774466959140677 127161544270212554838877)
                ·
                  rfl

theorem cell19_417903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_417903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417903 prefixEnd_417903 := by exact prefixLift 417903
  have htrace : WordTrace (prefixWord ++ tailWord_417903) baseStart_417903 baseEnd_417903 := by
    simpa [prefixWord, tailWord_417903, baseEnd_417903] using wordTrace_append hprefix tailTrace_417903
  have hstable : (prefixWord ++ tailWord_417903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417903).length < 2 ^ (prefixWord ++ tailWord_417903).sum := by decide
  have hdescent : baseEnd_417903 < baseStart_417903 := by decide
  rcases family_descends (prefixWord ++ tailWord_417903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417973 : List Nat := [1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_417973 : Nat := 118140960795 + 417973 * 2 ^ 59
def prefixEnd_417973 : Nat := 4983230072969 + 3 ^ 40 * 417973 * 2
def baseEnd_417973 : Nat := 127182844208473133283131

theorem tailTrace_417973 : CollatzResearch.WordTrace tailWord_417973 prefixEnd_417973 127182844208473133283131 := by
  unfold tailWord_417973
  simp only [CollatzResearch.WordTrace]
  refine ⟨15244727714762679950330573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10163151809841786633553715 15244727714762679950330573)
  ·
    refine ⟨5716772893036004981373965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15244727714762679950330573 5716772893036004981373965)
    ·
      refine ⟨2143789834888501868015237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5716772893036004981373965 2143789834888501868015237)
      ·
        refine ⟨401960594041594100252857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2143789834888501868015237 401960594041594100252857)
        ·
          refine ⟨301470445531195575189643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401960594041594100252857 301470445531195575189643)
          ·
            refine ⟨452205668296793362784465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301470445531195575189643 452205668296793362784465)
            ·
              refine ⟨339154251222595022088349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452205668296793362784465 339154251222595022088349)
              ·
                refine ⟨127182844208473133283131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339154251222595022088349 127182844208473133283131)
                ·
                  rfl

theorem cell19_417973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_417973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417973 prefixEnd_417973 := by exact prefixLift 417973
  have htrace : WordTrace (prefixWord ++ tailWord_417973) baseStart_417973 baseEnd_417973 := by
    simpa [prefixWord, tailWord_417973, baseEnd_417973] using wordTrace_append hprefix tailTrace_417973
  have hstable : (prefixWord ++ tailWord_417973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417973).length < 2 ^ (prefixWord ++ tailWord_417973).sum := by decide
  have hdescent : baseEnd_417973 < baseStart_417973 := by decide
  rcases family_descends (prefixWord ++ tailWord_417973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417996 : List Nat := [2, 2, 1, 6, 1, 2, 5]
def baseStart_417996 : Nat := 118140960795 + 417996 * 2 ^ 59
def prefixEnd_417996 : Nat := 4983230072969 + 3 ^ 40 * 417996 * 2
def baseEnd_417996 : Nat := 42396614253205298257319

theorem tailTrace_417996 : CollatzResearch.WordTrace tailWord_417996 prefixEnd_417996 42396614253205298257319 := by
  unfold tailWord_417996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622783296839677439208921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10163711062452903252278561 7622783296839677439208921)
  ·
    refine ⟨5717087472629758079406691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7622783296839677439208921 5717087472629758079406691)
    ·
      refine ⟨8575631208944637119110037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5717087472629758079406691 8575631208944637119110037)
      ·
        refine ⟨401982712919279864958283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8575631208944637119110037 401982712919279864958283)
        ·
          refine ⟨602974069378919797437425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401982712919279864958283 602974069378919797437425)
          ·
            refine ⟨452230552034189848078069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602974069378919797437425 452230552034189848078069)
            ·
              refine ⟨42396614253205298257319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452230552034189848078069 42396614253205298257319)
              ·
                rfl

theorem cell19_417996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_417996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417996 prefixEnd_417996 := by exact prefixLift 417996
  have htrace : WordTrace (prefixWord ++ tailWord_417996) baseStart_417996 baseEnd_417996 := by
    simpa [prefixWord, tailWord_417996, baseEnd_417996] using wordTrace_append hprefix tailTrace_417996
  have hstable : (prefixWord ++ tailWord_417996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417996).length < 2 ^ (prefixWord ++ tailWord_417996).sum := by decide
  have hdescent : baseEnd_417996 < baseStart_417996 := by decide
  rcases family_descends (prefixWord ++ tailWord_417996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417998 : List Nat := [4, 1, 1, 1, 4, 3, 5]
def baseStart_417998 : Nat := 118140960795 + 417998 * 2 ^ 59
def prefixEnd_417998 : Nat := 4983230072969 + 3 ^ 40 * 417998 * 2
def baseEnd_417998 : Nat := 42396817109760160909169

theorem tailTrace_417998 : CollatzResearch.WordTrace tailWord_417998 prefixEnd_417998 42396817109760160909169 := by
  unfold tailWord_417998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905704942459013652498831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10163759693114739479993765 1905704942459013652498831)
  ·
    refine ⟨2858557413688520478748247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905704942459013652498831 2858557413688520478748247)
    ·
      refine ⟨4287836120532780718122371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858557413688520478748247 4287836120532780718122371)
      ·
        refine ⟨6431754180799171077183557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287836120532780718122371 6431754180799171077183557)
        ·
          refine ⟨1205953908899844576971917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6431754180799171077183557 1205953908899844576971917)
          ·
            refine ⟨452232715837441716364469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1205953908899844576971917 452232715837441716364469)
            ·
              refine ⟨42396817109760160909169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452232715837441716364469 42396817109760160909169)
              ·
                rfl

theorem cell19_417998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_417998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_417998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_417998 prefixEnd_417998 := by exact prefixLift 417998
  have htrace : WordTrace (prefixWord ++ tailWord_417998) baseStart_417998 baseEnd_417998 := by
    simpa [prefixWord, tailWord_417998, baseEnd_417998] using wordTrace_append hprefix tailTrace_417998
  have hstable : (prefixWord ++ tailWord_417998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417998).length < 2 ^ (prefixWord ++ tailWord_417998).sum := by decide
  have hdescent : baseEnd_417998 < baseStart_417998 := by decide
  rcases family_descends (prefixWord ++ tailWord_417998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418055 : List Nat := [1, 1, 4, 5, 1, 7]
def baseStart_418055 : Nat := 118140960795 + 418055 * 2 ^ 59
def prefixEnd_418055 : Nat := 4983230072969 + 3 ^ 40 * 418055 * 2
def baseEnd_418055 : Nat := 14134199507191248828965

theorem tailTrace_418055 : CollatzResearch.WordTrace tailWord_418055 prefixEnd_418055 14134199507191248828965 := by
  unfold tailWord_418055
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247718500465607954815619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10165145666977071969877079 15247718500465607954815619)
  ·
    refine ⟨22871577750698411932223429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15247718500465607954815619 22871577750698411932223429)
    ·
      refine ⟨4288420828255952237291893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22871577750698411932223429 4288420828255952237291893)
      ·
        refine ⟨402039452648995522246115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4288420828255952237291893 402039452648995522246115)
        ·
          refine ⟨603059178973493283369173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402039452648995522246115 603059178973493283369173)
          ·
            refine ⟨14134199507191248828965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 603059178973493283369173 14134199507191248828965)
            ·
              rfl

theorem cell19_418055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_418055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418055 prefixEnd_418055 := by exact prefixLift 418055
  have htrace : WordTrace (prefixWord ++ tailWord_418055) baseStart_418055 baseEnd_418055 := by
    simpa [prefixWord, tailWord_418055, baseEnd_418055] using wordTrace_append hprefix tailTrace_418055
  have hstable : (prefixWord ++ tailWord_418055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418055).length < 2 ^ (prefixWord ++ tailWord_418055).sum := by decide
  have hdescent : baseEnd_418055 < baseStart_418055 := by decide
  rcases family_descends (prefixWord ++ tailWord_418055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418087 : List Nat := [1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_418087 : Nat := 118140960795 + 418087 * 2 ^ 59
def prefixEnd_418087 : Nat := 4983230072969 + 3 ^ 40 * 418087 * 2
def baseEnd_418087 : Nat := 127217532679354646749487

theorem tailTrace_418087 : CollatzResearch.WordTrace tailWord_418087 prefixEnd_418087 127217532679354646749487 := by
  unfold tailWord_418087
  simp only [CollatzResearch.WordTrace]
  refine ⟨15248885636349677419980515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10165923757566451613320343 15248885636349677419980515)
  ·
    refine ⟨22873328454524516129970773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15248885636349677419980515 22873328454524516129970773)
    ·
      refine ⟨268046817826459173398095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 22873328454524516129970773 268046817826459173398095)
      ·
        refine ⟨402070226739688760097143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268046817826459173398095 402070226739688760097143)
        ·
          refine ⟨603105340109533140145715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402070226739688760097143 603105340109533140145715)
          ·
            refine ⟨904658010164299710218573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603105340109533140145715 904658010164299710218573)
            ·
              refine ⟨339246753811612391331965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904658010164299710218573 339246753811612391331965)
              ·
                refine ⟨127217532679354646749487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339246753811612391331965 127217532679354646749487)
                ·
                  rfl

theorem cell19_418087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_418087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418087 prefixEnd_418087 := by exact prefixLift 418087
  have htrace : WordTrace (prefixWord ++ tailWord_418087) baseStart_418087 baseEnd_418087 := by
    simpa [prefixWord, tailWord_418087, baseEnd_418087] using wordTrace_append hprefix tailTrace_418087
  have hstable : (prefixWord ++ tailWord_418087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418087).length < 2 ^ (prefixWord ++ tailWord_418087).sum := by decide
  have hdescent : baseEnd_418087 < baseStart_418087 := by decide
  rcases family_descends (prefixWord ++ tailWord_418087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418171 : List Nat := [1, 1, 1, 1, 1, 9, 5]
def baseStart_418171 : Nat := 118140960795 + 418171 * 2 ^ 59
def prefixEnd_418171 : Nat := 4983230072969 + 3 ^ 40 * 418171 * 2
def baseEnd_418171 : Nat := 42414364201755780294197

theorem tailTrace_418171 : CollatzResearch.WordTrace tailWord_418171 prefixEnd_418171 42414364201755780294197 := by
  unfold tailWord_418171
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251949368045359766038367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10167966245363573177358911 15251949368045359766038367)
  ·
    refine ⟨22877924052068039649057551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15251949368045359766038367 22877924052068039649057551)
    ·
      refine ⟨34316886078102059473586327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22877924052068039649057551 34316886078102059473586327)
      ·
        refine ⟨51475329117153089210379491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34316886078102059473586327 51475329117153089210379491)
        ·
          refine ⟨77212993675729633815569237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51475329117153089210379491 77212993675729633815569237)
          ·
            refine ⟨452419884818728323138101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 77212993675729633815569237 452419884818728323138101)
            ·
              refine ⟨42414364201755780294197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452419884818728323138101 42414364201755780294197)
              ·
                rfl

theorem cell19_418171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_418171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418171 prefixEnd_418171 := by exact prefixLift 418171
  have htrace : WordTrace (prefixWord ++ tailWord_418171) baseStart_418171 baseEnd_418171 := by
    simpa [prefixWord, tailWord_418171, baseEnd_418171] using wordTrace_append hprefix tailTrace_418171
  have hstable : (prefixWord ++ tailWord_418171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418171).length < 2 ^ (prefixWord ++ tailWord_418171).sum := by decide
  have hdescent : baseEnd_418171 < baseStart_418171 := by decide
  rcases family_descends (prefixWord ++ tailWord_418171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418186 : List Nat := [3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_418186 : Nat := 118140960795 + 418186 * 2 ^ 59
def prefixEnd_418186 : Nat := 4983230072969 + 3 ^ 40 * 418186 * 2
def baseEnd_418186 : Nat := 127247656877751750549217

theorem tailTrace_418186 : CollatzResearch.WordTrace tailWord_418186 prefixEnd_418186 127247656877751750549217 := by
  unfold tailWord_418186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813124115747754331958603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10168330975327344885222941 3813124115747754331958603)
  ·
    refine ⟨5719686173621631497937905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813124115747754331958603 5719686173621631497937905)
    ·
      refine ⟨4289764630216223623453429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5719686173621631497937905 4289764630216223623453429)
      ·
        refine ⟨402165434082770964698759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4289764630216223623453429 402165434082770964698759)
        ·
          refine ⟨603248151124156447048139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402165434082770964698759 603248151124156447048139)
          ·
            refine ⟨904872226686234670572209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603248151124156447048139 904872226686234670572209)
            ·
              refine ⟨678654170014676002929157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904872226686234670572209 678654170014676002929157)
              ·
                refine ⟨127247656877751750549217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678654170014676002929157 127247656877751750549217)
                ·
                  rfl

theorem cell19_418186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_418186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418186 prefixEnd_418186 := by exact prefixLift 418186
  have htrace : WordTrace (prefixWord ++ tailWord_418186) baseStart_418186 baseEnd_418186 := by
    simpa [prefixWord, tailWord_418186, baseEnd_418186] using wordTrace_append hprefix tailTrace_418186
  have hstable : (prefixWord ++ tailWord_418186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418186).length < 2 ^ (prefixWord ++ tailWord_418186).sum := by decide
  have hdescent : baseEnd_418186 < baseStart_418186 := by decide
  rcases family_descends (prefixWord ++ tailWord_418186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418247 : List Nat := [1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_418247 : Nat := 118140960795 + 418247 * 2 ^ 59
def prefixEnd_418247 : Nat := 4983230072969 + 3 ^ 40 * 418247 * 2
def baseEnd_418247 : Nat := 127266218252521683193495

theorem tailTrace_418247 : CollatzResearch.WordTrace tailWord_418247 prefixEnd_418247 127266218252521683193495 := by
  unfold tailWord_418247
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254721315770024745804995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10169814210513349830536663 15254721315770024745804995)
  ·
    refine ⟨22882081973655037118707493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15254721315770024745804995 22882081973655037118707493)
    ·
      refine ⟨4290390370060319459757655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22882081973655037118707493 4290390370060319459757655)
      ·
        refine ⟨6435585555090479189636483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290390370060319459757655 6435585555090479189636483)
        ·
          refine ⟨9653378332635718784454725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435585555090479189636483 9653378332635718784454725)
          ·
            refine ⟨1810008437369197272085261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9653378332635718784454725 1810008437369197272085261)
            ·
              refine ⟨678753164013448977031973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1810008437369197272085261 678753164013448977031973)
              ·
                refine ⟨127266218252521683193495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678753164013448977031973 127266218252521683193495)
                ·
                  rfl

theorem cell19_418247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_418247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418247 prefixEnd_418247 := by exact prefixLift 418247
  have htrace : WordTrace (prefixWord ++ tailWord_418247) baseStart_418247 baseEnd_418247 := by
    simpa [prefixWord, tailWord_418247, baseEnd_418247] using wordTrace_append hprefix tailTrace_418247
  have hstable : (prefixWord ++ tailWord_418247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418247).length < 2 ^ (prefixWord ++ tailWord_418247).sum := by decide
  have hdescent : baseEnd_418247 < baseStart_418247 := by decide
  rcases family_descends (prefixWord ++ tailWord_418247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418262 : List Nat := [5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_418262 : Nat := 118140960795 + 418262 * 2 ^ 59
def prefixEnd_418262 : Nat := 4983230072969 + 3 ^ 40 * 418262 * 2
def baseEnd_418262 : Nat := 127270782525006092860121

theorem tailTrace_418262 : CollatzResearch.WordTrace tailWord_418262 prefixEnd_418262 127270782525006092860121 := by
  unfold tailWord_418262
  simp only [CollatzResearch.WordTrace]
  refine ⟨953454275669730144225065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10170178940477121538400693 953454275669730144225065)
  ·
    refine ⟨715090706752297608168799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 953454275669730144225065 715090706752297608168799)
    ·
      refine ⟨1072636060128446412253199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715090706752297608168799 1072636060128446412253199)
      ·
        refine ⟨1608954090192669618379799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072636060128446412253199 1608954090192669618379799)
        ·
          refine ⟨2413431135289004427569699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608954090192669618379799 2413431135289004427569699)
          ·
            refine ⟨3620146702933506641354549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413431135289004427569699 3620146702933506641354549)
            ·
              refine ⟨339388753400016247626989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3620146702933506641354549 339388753400016247626989)
              ·
                refine ⟨127270782525006092860121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339388753400016247626989 127270782525006092860121)
                ·
                  rfl

theorem cell19_418262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_418262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418262 prefixEnd_418262 := by exact prefixLift 418262
  have htrace : WordTrace (prefixWord ++ tailWord_418262) baseStart_418262 baseEnd_418262 := by
    simpa [prefixWord, tailWord_418262, baseEnd_418262] using wordTrace_append hprefix tailTrace_418262
  have hstable : (prefixWord ++ tailWord_418262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418262).length < 2 ^ (prefixWord ++ tailWord_418262).sum := by decide
  have hdescent : baseEnd_418262 < baseStart_418262 := by decide
  rcases family_descends (prefixWord ++ tailWord_418262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418317 : List Nat := [1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_418317 : Nat := 118140960795 + 418317 * 2 ^ 59
def prefixEnd_418317 : Nat := 4983230072969 + 3 ^ 40 * 418317 * 2
def baseEnd_418317 : Nat := 127287518190782261637749

theorem tailTrace_418317 : CollatzResearch.WordTrace tailWord_418317 prefixEnd_418317 127287518190782261637749 := by
  unfold tailWord_418317
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257274425516426700853205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10171516283677617800568803 15257274425516426700853205)
  ·
    refine ⟨357592369348041250801247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15257274425516426700853205 357592369348041250801247)
    ·
      refine ⟨536388554022061876201871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357592369348041250801247 536388554022061876201871)
      ·
        refine ⟨804582831033092814302807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536388554022061876201871 804582831033092814302807)
        ·
          refine ⟨1206874246549639221454211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804582831033092814302807 1206874246549639221454211)
          ·
            refine ⟨1810311369824458832181317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206874246549639221454211 1810311369824458832181317)
            ·
              refine ⟨339433381842086031033997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1810311369824458832181317 339433381842086031033997)
              ·
                refine ⟨127287518190782261637749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339433381842086031033997 127287518190782261637749)
                ·
                  rfl

theorem cell19_418317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_418317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418317 prefixEnd_418317 := by exact prefixLift 418317
  have htrace : WordTrace (prefixWord ++ tailWord_418317) baseStart_418317 baseEnd_418317 := by
    simpa [prefixWord, tailWord_418317, baseEnd_418317] using wordTrace_append hprefix tailTrace_418317
  have hstable : (prefixWord ++ tailWord_418317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418317).length < 2 ^ (prefixWord ++ tailWord_418317).sum := by decide
  have hdescent : baseEnd_418317 < baseStart_418317 := by decide
  rcases family_descends (prefixWord ++ tailWord_418317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418361 : List Nat := [1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_418361 : Nat := 118140960795 + 418361 * 2 ^ 59
def prefixEnd_418361 : Nat := 4983230072969 + 3 ^ 40 * 418361 * 2
def baseEnd_418361 : Nat := 127300906723403196659851

theorem tailTrace_418361 : CollatzResearch.WordTrace tailWord_418361 prefixEnd_418361 127300906723403196659851 := by
  unfold tailWord_418361
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258879237357022215454937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10172586158238014810303291 15258879237357022215454937)
  ·
    refine ⟨11444159428017766661591203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15258879237357022215454937 11444159428017766661591203)
    ·
      refine ⟨17166239142026649992386805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444159428017766661591203 17166239142026649992386805)
      ·
        refine ⟨1609334919564998436786263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17166239142026649992386805 1609334919564998436786263)
        ·
          refine ⟨2414002379347497655179395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609334919564998436786263 2414002379347497655179395)
          ·
            refine ⟨3621003569021246482769093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414002379347497655179395 3621003569021246482769093)
            ·
              refine ⟨678938169191483715519205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3621003569021246482769093 678938169191483715519205)
              ·
                refine ⟨127300906723403196659851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678938169191483715519205 127300906723403196659851)
                ·
                  rfl

theorem cell19_418361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_418361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418361 prefixEnd_418361 := by exact prefixLift 418361
  have htrace : WordTrace (prefixWord ++ tailWord_418361) baseStart_418361 baseEnd_418361 := by
    simpa [prefixWord, tailWord_418361, baseEnd_418361] using wordTrace_append hprefix tailTrace_418361
  have hstable : (prefixWord ++ tailWord_418361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418361).length < 2 ^ (prefixWord ++ tailWord_418361).sum := by decide
  have hdescent : baseEnd_418361 < baseStart_418361 := by decide
  rcases family_descends (prefixWord ++ tailWord_418361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418401 : List Nat := [1, 2, 3, 1, 1, 11]
def baseStart_418401 : Nat := 118140960795 + 418401 * 2 ^ 59
def prefixEnd_418401 : Nat := 4983230072969 + 3 ^ 40 * 418401 * 2
def baseEnd_418401 : Nat := 14145897568521661752317

theorem tailTrace_418401 : CollatzResearch.WordTrace tailWord_418401 prefixEnd_418401 14145897568521661752317 := by
  unfold tailWord_418401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15260338157212109046911057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10173558771474739364607371 15260338157212109046911057)
  ·
    refine ⟨11445253617909081785183293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15260338157212109046911057 11445253617909081785183293)
    ·
      refine ⟨4291970106715905669443735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11445253617909081785183293 4291970106715905669443735)
      ·
        refine ⟨6437955160073858504165603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291970106715905669443735 6437955160073858504165603)
        ·
          refine ⟨9656932740110787756248405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6437955160073858504165603 9656932740110787756248405)
          ·
            refine ⟨14145897568521661752317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9656932740110787756248405 14145897568521661752317)
            ·
              rfl

theorem cell19_418401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_418401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418401 prefixEnd_418401 := by exact prefixLift 418401
  have htrace : WordTrace (prefixWord ++ tailWord_418401) baseStart_418401 baseEnd_418401 := by
    simpa [prefixWord, tailWord_418401, baseEnd_418401] using wordTrace_append hprefix tailTrace_418401
  have hstable : (prefixWord ++ tailWord_418401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418401).length < 2 ^ (prefixWord ++ tailWord_418401).sum := by decide
  have hdescent : baseEnd_418401 < baseStart_418401 := by decide
  rcases family_descends (prefixWord ++ tailWord_418401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418416 : List Nat := [2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_418416 : Nat := 118140960795 + 418416 * 2 ^ 59
def prefixEnd_418416 : Nat := 4983230072969 + 3 ^ 40 * 418416 * 2
def baseEnd_418416 : Nat := 127317642389179365437479

theorem tailTrace_418416 : CollatzResearch.WordTrace tailWord_418416 prefixEnd_418416 127317642389179365437479 := by
  unfold tailWord_418416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7630442626078883304353551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10173923501438511072471401 7630442626078883304353551)
  ·
    refine ⟨11445663939118324956530327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7630442626078883304353551 11445663939118324956530327)
    ·
      refine ⟨17168495908677487434795491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11445663939118324956530327 17168495908677487434795491)
      ·
        refine ⟨25752743863016231152193237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17168495908677487434795491 25752743863016231152193237)
        ·
          refine ⟨603579934289442917629529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25752743863016231152193237 603579934289442917629529)
          ·
            refine ⟨452684950717082188222147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603579934289442917629529 452684950717082188222147)
            ·
              refine ⟨679027426075623282333221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452684950717082188222147 679027426075623282333221)
              ·
                refine ⟨127317642389179365437479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679027426075623282333221 127317642389179365437479)
                ·
                  rfl

theorem cell19_418416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_418416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418416 prefixEnd_418416 := by exact prefixLift 418416
  have htrace : WordTrace (prefixWord ++ tailWord_418416) baseStart_418416 baseEnd_418416 := by
    simpa [prefixWord, tailWord_418416, baseEnd_418416] using wordTrace_append hprefix tailTrace_418416
  have hstable : (prefixWord ++ tailWord_418416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418416).length < 2 ^ (prefixWord ++ tailWord_418416).sum := by decide
  have hdescent : baseEnd_418416 < baseStart_418416 := by decide
  rcases family_descends (prefixWord ++ tailWord_418416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418486 : List Nat := [5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_418486 : Nat := 118140960795 + 418486 * 2 ^ 59
def prefixEnd_418486 : Nat := 4983230072969 + 3 ^ 40 * 418486 * 2
def baseEnd_418486 : Nat := 127338942327439943881733

theorem tailTrace_418486 : CollatzResearch.WordTrace tailWord_418486 prefixEnd_418486 127338942327439943881733 := by
  unfold tailWord_418486
  simp only [CollatzResearch.WordTrace]
  refine ⟨953964897619010535234707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10175625574602779042503541 953964897619010535234707)
  ·
    refine ⟨1430947346428515802852061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 953964897619010535234707 1430947346428515802852061)
    ·
      refine ⟨536605254910693426069523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1430947346428515802852061 536605254910693426069523)
      ·
        refine ⟨804907882366040139104285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536605254910693426069523 804907882366040139104285)
        ·
          refine ⟨301840455887265052164107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 804907882366040139104285 301840455887265052164107)
          ·
            refine ⟨452760683830897578246161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301840455887265052164107 452760683830897578246161)
            ·
              refine ⟨339570512873173183684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452760683830897578246161 339570512873173183684621)
              ·
                refine ⟨127338942327439943881733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339570512873173183684621 127338942327439943881733)
                ·
                  rfl

theorem cell19_418486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_418486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418486 prefixEnd_418486 := by exact prefixLift 418486
  have htrace : WordTrace (prefixWord ++ tailWord_418486) baseStart_418486 baseEnd_418486 := by
    simpa [prefixWord, tailWord_418486, baseEnd_418486] using wordTrace_append hprefix tailTrace_418486
  have hstable : (prefixWord ++ tailWord_418486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418486).length < 2 ^ (prefixWord ++ tailWord_418486).sum := by decide
  have hdescent : baseEnd_418486 < baseStart_418486 := by decide
  rcases family_descends (prefixWord ++ tailWord_418486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418494 : List Nat := [4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_418494 : Nat := 118140960795 + 418494 * 2 ^ 59
def prefixEnd_418494 : Nat := 4983230072969 + 3 ^ 40 * 418494 * 2
def baseEnd_418494 : Nat := 127341376606098295703933

theorem tailTrace_418494 : CollatzResearch.WordTrace tailWord_418494 prefixEnd_418494 127341376606098295703933 := by
  unfold tailWord_418494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907966268234398241255817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10175820097250123953364357 1907966268234398241255817)
  ·
    refine ⟨1430974701175798680941863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1907966268234398241255817 1430974701175798680941863)
    ·
      refine ⟨2146462051763698021412795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430974701175798680941863 2146462051763698021412795)
      ·
        refine ⟨3219693077645547032119193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146462051763698021412795 3219693077645547032119193)
        ·
          refine ⟨2414769808234160274089395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3219693077645547032119193 2414769808234160274089395)
          ·
            refine ⟨3622154712351240411134093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414769808234160274089395 3622154712351240411134093)
            ·
              refine ⟨1358308017131715154175285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622154712351240411134093 1358308017131715154175285)
              ·
                refine ⟨127341376606098295703933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1358308017131715154175285 127341376606098295703933)
                ·
                  rfl

theorem cell19_418494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_418494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418494 prefixEnd_418494 := by exact prefixLift 418494
  have htrace : WordTrace (prefixWord ++ tailWord_418494) baseStart_418494 baseEnd_418494 := by
    simpa [prefixWord, tailWord_418494, baseEnd_418494] using wordTrace_append hprefix tailTrace_418494
  have hstable : (prefixWord ++ tailWord_418494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418494).length < 2 ^ (prefixWord ++ tailWord_418494).sum := by decide
  have hdescent : baseEnd_418494 < baseStart_418494 := by decide
  rcases family_descends (prefixWord ++ tailWord_418494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418509 : List Nat := [1, 6, 2, 1, 2, 2, 5]
def baseStart_418509 : Nat := 118140960795 + 418509 * 2 ^ 59
def prefixEnd_418509 : Nat := 4983230072969 + 3 ^ 40 * 418509 * 2
def baseEnd_418509 : Nat := 42448646959527568456853

theorem tailTrace_418509 : CollatzResearch.WordTrace tailWord_418509 prefixEnd_418509 42448646959527568456853 := by
  unfold tailWord_418509
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264277240820843491842581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10176184827213895661228387 15264277240820843491842581)
  ·
    refine ⟨715512995663477038680121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15264277240820843491842581 715512995663477038680121)
    ·
      refine ⟨536634746747607779010091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 715512995663477038680121 536634746747607779010091)
      ·
        refine ⟨804952120121411668515137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536634746747607779010091 804952120121411668515137)
        ·
          refine ⟨603714090091058751386353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804952120121411668515137 603714090091058751386353)
          ·
            refine ⟨452785567568294063539765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603714090091058751386353 452785567568294063539765)
            ·
              refine ⟨42448646959527568456853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452785567568294063539765 42448646959527568456853)
              ·
                rfl

theorem cell19_418509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_418509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418509 prefixEnd_418509 := by exact prefixLift 418509
  have htrace : WordTrace (prefixWord ++ tailWord_418509) baseStart_418509 baseEnd_418509 := by
    simpa [prefixWord, tailWord_418509, baseEnd_418509] using wordTrace_append hprefix tailTrace_418509
  have hstable : (prefixWord ++ tailWord_418509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418509).length < 2 ^ (prefixWord ++ tailWord_418509).sum := by decide
  have hdescent : baseEnd_418509 < baseStart_418509 := by decide
  rcases family_descends (prefixWord ++ tailWord_418509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418532 : List Nat := [2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_418532 : Nat := 118140960795 + 418532 * 2 ^ 59
def prefixEnd_418532 : Nat := 4983230072969 + 3 ^ 40 * 418532 * 2
def baseEnd_418532 : Nat := 127352939429725466859385

theorem tailTrace_418532 : CollatzResearch.WordTrace tailWord_418532 prefixEnd_418532 127352939429725466859385 := by
  unfold tailWord_418532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7632558059868759209964925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10176744079825012279953233 7632558059868759209964925)
  ·
    refine ⟨2862209272450784703736847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7632558059868759209964925 2862209272450784703736847)
    ·
      refine ⟨4293313908676177055605271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862209272450784703736847 4293313908676177055605271)
      ·
        refine ⟨6439970863014265583407907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293313908676177055605271 6439970863014265583407907)
        ·
          refine ⟨9659956294521398375111861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439970863014265583407907 9659956294521398375111861)
          ·
            refine ⟨905620902611381097666737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9659956294521398375111861 905620902611381097666737)
            ·
              refine ⟨679215676958535823250053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905620902611381097666737 679215676958535823250053)
              ·
                refine ⟨127352939429725466859385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679215676958535823250053 127352939429725466859385)
                ·
                  rfl

theorem cell19_418532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_418532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418532 prefixEnd_418532 := by exact prefixLift 418532
  have htrace : WordTrace (prefixWord ++ tailWord_418532) baseStart_418532 baseEnd_418532 := by
    simpa [prefixWord, tailWord_418532, baseEnd_418532] using wordTrace_append hprefix tailTrace_418532
  have hstable : (prefixWord ++ tailWord_418532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418532).length < 2 ^ (prefixWord ++ tailWord_418532).sum := by decide
  have hdescent : baseEnd_418532 < baseStart_418532 := by decide
  rcases family_descends (prefixWord ++ tailWord_418532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418566 : List Nat := [6, 2, 2, 9]
def baseStart_418566 : Nat := 118140960795 + 418566 * 2 ^ 59
def prefixEnd_418566 : Nat := 4983230072969 + 3 ^ 40 * 418566 * 2
def baseEnd_418566 : Nat := 1572386235975598297577

theorem tailTrace_418566 : CollatzResearch.WordTrace tailWord_418566 prefixEnd_418566 1572386235975598297577 := by
  unfold tailWord_418566
  simp only [CollatzResearch.WordTrace]
  refine ⟨477073631300448194583361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10177570801076228151111701 477073631300448194583361)
  ·
    refine ⟨357805223475336145937521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 477073631300448194583361 357805223475336145937521)
    ·
      refine ⟨268353917606502109453141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357805223475336145937521 268353917606502109453141)
      ·
        refine ⟨1572386235975598297577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 268353917606502109453141 1572386235975598297577)
        ·
          rfl

theorem cell19_418566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 9].length) (baseStart_418566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418566 prefixEnd_418566 := by exact prefixLift 418566
  have htrace : WordTrace (prefixWord ++ tailWord_418566) baseStart_418566 baseEnd_418566 := by
    simpa [prefixWord, tailWord_418566, baseEnd_418566] using wordTrace_append hprefix tailTrace_418566
  have hstable : (prefixWord ++ tailWord_418566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418566).length < 2 ^ (prefixWord ++ tailWord_418566).sum := by decide
  have hdescent : baseEnd_418566 < baseStart_418566 := by decide
  rcases family_descends (prefixWord ++ tailWord_418566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418625 : List Nat := [1, 2, 5, 3, 1, 1, 6]
def baseStart_418625 : Nat := 118140960795 + 418625 * 2 ^ 59
def prefixEnd_418625 : Nat := 4983230072969 + 3 ^ 40 * 418625 * 2
def baseEnd_418625 : Nat := 42460412639709602264155

theorem tailTrace_418625 : CollatzResearch.WordTrace tailWord_418625 prefixEnd_418625 42460412639709602264155 := by
  unfold tailWord_418625
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268508108400595303065329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10179005405600396868710219 15268508108400595303065329)
  ·
    refine ⟨11451381081300446477298997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15268508108400595303065329 11451381081300446477298997)
    ·
      refine ⟨1073566976371916857246781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11451381081300446477298997 1073566976371916857246781)
      ·
        refine ⟨402587616139468821467543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1073566976371916857246781 402587616139468821467543)
        ·
          refine ⟨603881424209203232201315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402587616139468821467543 603881424209203232201315)
          ·
            refine ⟨905822136313804848301973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603881424209203232201315 905822136313804848301973)
            ·
              refine ⟨42460412639709602264155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 905822136313804848301973 42460412639709602264155)
              ·
                rfl

theorem cell19_418625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_418625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418625 prefixEnd_418625 := by exact prefixLift 418625
  have htrace : WordTrace (prefixWord ++ tailWord_418625) baseStart_418625 baseEnd_418625 := by
    simpa [prefixWord, tailWord_418625, baseEnd_418625] using wordTrace_append hprefix tailTrace_418625
  have hstable : (prefixWord ++ tailWord_418625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418625).length < 2 ^ (prefixWord ++ tailWord_418625).sum := by decide
  have hdescent : baseEnd_418625 < baseStart_418625 := by decide
  rcases family_descends (prefixWord ++ tailWord_418625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418663 : List Nat := [1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_418663 : Nat := 118140960795 + 418663 * 2 ^ 59
def prefixEnd_418663 : Nat := 4983230072969 + 3 ^ 40 * 418663 * 2
def baseEnd_418663 : Nat := 127392800742755977947917

theorem tailTrace_418663 : CollatzResearch.WordTrace tailWord_418663 prefixEnd_418663 127392800742755977947917 := by
  unfold tailWord_418663
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269894082262927792948643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10179929388175285195299095 15269894082262927792948643)
  ·
    refine ⟨22904841123394391689422965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15269894082262927792948643 22904841123394391689422965)
    ·
      refine ⟨2147328855318224220883403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22904841123394391689422965 2147328855318224220883403)
      ·
        refine ⟨3220993282977336331325105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147328855318224220883403 3220993282977336331325105)
        ·
          refine ⟨2415744962233002248493829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220993282977336331325105 2415744962233002248493829)
          ·
            refine ⟨452952180418687921592593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2415744962233002248493829 452952180418687921592593)
            ·
              refine ⟨339714135314015941194445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452952180418687921592593 339714135314015941194445)
              ·
                refine ⟨127392800742755977947917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339714135314015941194445 127392800742755977947917)
                ·
                  rfl

theorem cell19_418663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_418663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418663 prefixEnd_418663 := by exact prefixLift 418663
  have htrace : WordTrace (prefixWord ++ tailWord_418663) baseStart_418663 baseEnd_418663 := by
    simpa [prefixWord, tailWord_418663, baseEnd_418663] using wordTrace_append hprefix tailTrace_418663
  have hstable : (prefixWord ++ tailWord_418663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418663).length < 2 ^ (prefixWord ++ tailWord_418663).sum := by decide
  have hdescent : baseEnd_418663 < baseStart_418663 := by decide
  rcases family_descends (prefixWord ++ tailWord_418663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418722 : List Nat := [3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_418722 : Nat := 118140960795 + 418722 * 2 ^ 59
def prefixEnd_418722 : Nat := 4983230072969 + 3 ^ 40 * 418722 * 2
def baseEnd_418722 : Nat := 127410753547861322636645

theorem tailTrace_418722 : CollatzResearch.WordTrace tailWord_418722 prefixEnd_418722 127410753547861322636645 := by
  unfold tailWord_418722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818011497262295217336605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10181363992699453912897613 3818011497262295217336605)
  ·
    refine ⟨1431754311473360706501227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3818011497262295217336605 1431754311473360706501227)
    ·
      refine ⟨2147631467210041059751841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431754311473360706501227 2147631467210041059751841)
      ·
        refine ⟨1610723600407530794813881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147631467210041059751841 1610723600407530794813881)
        ·
          refine ⟨1208042700305648096110411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610723600407530794813881 1208042700305648096110411)
          ·
            refine ⟨1812064050458472144165617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208042700305648096110411 1812064050458472144165617)
            ·
              refine ⟨1359048037843854108124213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812064050458472144165617 1359048037843854108124213)
              ·
                refine ⟨127410753547861322636645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1359048037843854108124213 127410753547861322636645)
                ·
                  rfl

theorem cell19_418722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_418722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418722 prefixEnd_418722 := by exact prefixLift 418722
  have htrace : WordTrace (prefixWord ++ tailWord_418722) baseStart_418722 baseEnd_418722 := by
    simpa [prefixWord, tailWord_418722, baseEnd_418722] using wordTrace_append hprefix tailTrace_418722
  have hstable : (prefixWord ++ tailWord_418722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418722).length < 2 ^ (prefixWord ++ tailWord_418722).sum := by decide
  have hdescent : baseEnd_418722 < baseStart_418722 := by decide
  rcases family_descends (prefixWord ++ tailWord_418722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418724 : List Nat := [2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_418724 : Nat := 118140960795 + 418724 * 2 ^ 59
def prefixEnd_418724 : Nat := 4983230072969 + 3 ^ 40 * 418724 * 2
def baseEnd_418724 : Nat := 127411362117525910592195

theorem tailTrace_418724 : CollatzResearch.WordTrace tailWord_418724 prefixEnd_418724 127411362117525910592195 := by
  unfold tailWord_418724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636059467520967605459613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10181412623361290140612817 7636059467520967605459613)
  ·
    refine ⟨2863522300320362852047355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7636059467520967605459613 2863522300320362852047355)
    ·
      refine ⟨4295283450480544278071033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863522300320362852047355 4295283450480544278071033)
      ·
        refine ⟨3221462587860408208553275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4295283450480544278071033 3221462587860408208553275)
        ·
          refine ⟨4832193881790612312829913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221462587860408208553275 4832193881790612312829913)
          ·
            refine ⟨3624145411342959234622435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4832193881790612312829913 3624145411342959234622435)
            ·
              refine ⟨5436218117014438851933653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624145411342959234622435 5436218117014438851933653)
              ·
                refine ⟨127411362117525910592195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5436218117014438851933653 127411362117525910592195)
                ·
                  rfl

theorem cell19_418724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_418724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418724 prefixEnd_418724 := by exact prefixLift 418724
  have htrace : WordTrace (prefixWord ++ tailWord_418724) baseStart_418724 baseEnd_418724 := by
    simpa [prefixWord, tailWord_418724, baseEnd_418724] using wordTrace_append hprefix tailTrace_418724
  have hstable : (prefixWord ++ tailWord_418724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418724).length < 2 ^ (prefixWord ++ tailWord_418724).sum := by decide
  have hdescent : baseEnd_418724 < baseStart_418724 := by decide
  rcases family_descends (prefixWord ++ tailWord_418724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418756 : List Nat := [2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_418756 : Nat := 118140960795 + 418756 * 2 ^ 59
def prefixEnd_418756 : Nat := 4983230072969 + 3 ^ 40 * 418756 * 2
def baseEnd_418756 : Nat := 127421099232159317880997

theorem tailTrace_418756 : CollatzResearch.WordTrace tailWord_418756 prefixEnd_418756 127421099232159317880997 := by
  unfold tailWord_418756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636643035463002338042061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10182190713950669784056081 7636643035463002338042061)
  ·
    refine ⟨2863741138298625876765773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7636643035463002338042061 2863741138298625876765773)
    ·
      refine ⟨1073902926861984703787165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2863741138298625876765773 1073902926861984703787165)
      ·
        refine ⟨402713597573244263920187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1073902926861984703787165 402713597573244263920187)
        ·
          refine ⟨604070396359866395880281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402713597573244263920187 604070396359866395880281)
          ·
            refine ⟨453052797269899796910211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604070396359866395880281 453052797269899796910211)
            ·
              refine ⟨679579195904849695365317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453052797269899796910211 679579195904849695365317)
              ·
                refine ⟨127421099232159317880997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679579195904849695365317 127421099232159317880997)
                ·
                  rfl

theorem cell19_418756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_418756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418756 prefixEnd_418756 := by exact prefixLift 418756
  have htrace : WordTrace (prefixWord ++ tailWord_418756) baseStart_418756 baseEnd_418756 := by
    simpa [prefixWord, tailWord_418756, baseEnd_418756] using wordTrace_append hprefix tailTrace_418756
  have hstable : (prefixWord ++ tailWord_418756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418756).length < 2 ^ (prefixWord ++ tailWord_418756).sum := by decide
  have hdescent : baseEnd_418756 < baseStart_418756 := by decide
  rcases family_descends (prefixWord ++ tailWord_418756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418798 : List Nat := [4, 1, 2, 1, 4, 1, 6]
def baseStart_418798 : Nat := 118140960795 + 418798 * 2 ^ 59
def prefixEnd_418798 : Nat := 4983230072969 + 3 ^ 40 * 418798 * 2
def baseEnd_418798 : Nat := 42477959731705221649183

theorem tailTrace_418798 : CollatzResearch.WordTrace tailWord_418798 prefixEnd_418798 42477959731705221649183 := by
  unfold tailWord_418798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909352242096730731139131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10183211957849230566075365 1909352242096730731139131)
  ·
    refine ⟨2864028363145096096708697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909352242096730731139131 2864028363145096096708697)
    ·
      refine ⟨2148021272358822072531523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2864028363145096096708697 2148021272358822072531523)
      ·
        refine ⟨3222031908538233108797285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148021272358822072531523 3222031908538233108797285)
        ·
          refine ⟨604130982850918707899491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3222031908538233108797285 604130982850918707899491)
          ·
            refine ⟨906196474276378061849237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604130982850918707899491 906196474276378061849237)
            ·
              refine ⟨42477959731705221649183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906196474276378061849237 42477959731705221649183)
              ·
                rfl

theorem cell19_418798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_418798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418798 prefixEnd_418798 := by exact prefixLift 418798
  have htrace : WordTrace (prefixWord ++ tailWord_418798) baseStart_418798 baseEnd_418798 := by
    simpa [prefixWord, tailWord_418798, baseEnd_418798] using wordTrace_append hprefix tailTrace_418798
  have hstable : (prefixWord ++ tailWord_418798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418798).length < 2 ^ (prefixWord ++ tailWord_418798).sum := by decide
  have hdescent : baseEnd_418798 < baseStart_418798 := by decide
  rcases family_descends (prefixWord ++ tailWord_418798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418855 : List Nat := [1, 1, 7, 1, 1, 1, 7]
def baseStart_418855 : Nat := 118140960795 + 418855 * 2 ^ 59
def prefixEnd_418855 : Nat := 4983230072969 + 3 ^ 40 * 418855 * 2
def baseEnd_418855 : Nat := 42483741143518807226909

theorem tailTrace_418855 : CollatzResearch.WordTrace tailWord_418855 prefixEnd_418855 42483741143518807226909 := by
  unfold tailWord_418855
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276896897567344583938019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10184597931711563055958679 15276896897567344583938019)
  ·
    refine ⟨22915345346351016875907029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15276896897567344583938019 22915345346351016875907029)
    ·
      refine ⟨537078406555101958029071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22915345346351016875907029 537078406555101958029071)
      ·
        refine ⟨805617609832652937043607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537078406555101958029071 805617609832652937043607)
        ·
          refine ⟨1208426414748979405565411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805617609832652937043607 1208426414748979405565411)
          ·
            refine ⟨1812639622123469108348117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208426414748979405565411 1812639622123469108348117)
            ·
              refine ⟨42483741143518807226909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1812639622123469108348117 42483741143518807226909)
              ·
                rfl

theorem cell19_418855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_418855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418855 prefixEnd_418855 := by exact prefixLift 418855
  have htrace : WordTrace (prefixWord ++ tailWord_418855) baseStart_418855 baseEnd_418855 := by
    simpa [prefixWord, tailWord_418855, baseEnd_418855] using wordTrace_append hprefix tailTrace_418855
  have hstable : (prefixWord ++ tailWord_418855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418855).length < 2 ^ (prefixWord ++ tailWord_418855).sum := by decide
  have hdescent : baseEnd_418855 < baseStart_418855 := by decide
  rcases family_descends (prefixWord ++ tailWord_418855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418876 : List Nat := [2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_418876 : Nat := 118140960795 + 418876 * 2 ^ 59
def prefixEnd_418876 : Nat := 4983230072969 + 3 ^ 40 * 418876 * 2
def baseEnd_418876 : Nat := 127457613412034595214003

theorem tailTrace_418876 : CollatzResearch.WordTrace tailWord_418876 prefixEnd_418876 127457613412034595214003 := by
  unfold tailWord_418876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638831415245632585226241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10185108553660843446968321 7638831415245632585226241)
  ·
    refine ⟨5729123561434224438919681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638831415245632585226241 5729123561434224438919681)
    ·
      refine ⟨4296842671075668329189761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5729123561434224438919681 4296842671075668329189761)
      ·
        refine ⟨3222632003306751246892321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4296842671075668329189761 3222632003306751246892321)
        ·
          refine ⟨2416974002480063435169241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222632003306751246892321 2416974002480063435169241)
          ·
            refine ⟨1812730501860047576376931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416974002480063435169241 1812730501860047576376931)
            ·
              refine ⟨2719095752790071364565397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812730501860047576376931 2719095752790071364565397)
              ·
                refine ⟨127457613412034595214003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2719095752790071364565397 127457613412034595214003)
                ·
                  rfl

theorem cell19_418876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_418876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418876 prefixEnd_418876 := by exact prefixLift 418876
  have htrace : WordTrace (prefixWord ++ tailWord_418876) baseStart_418876 baseEnd_418876 := by
    simpa [prefixWord, tailWord_418876, baseEnd_418876] using wordTrace_append hprefix tailTrace_418876
  have hstable : (prefixWord ++ tailWord_418876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418876).length < 2 ^ (prefixWord ++ tailWord_418876).sum := by decide
  have hdescent : baseEnd_418876 < baseStart_418876 := by decide
  rcases family_descends (prefixWord ++ tailWord_418876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418893 : List Nat := [1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_418893 : Nat := 118140960795 + 418893 * 2 ^ 59
def prefixEnd_418893 : Nat := 4983230072969 + 3 ^ 40 * 418893 * 2
def baseEnd_418893 : Nat := 127462786254183592836179

theorem tailTrace_418893 : CollatzResearch.WordTrace tailWord_418893 prefixEnd_418893 127462786254183592836179 := by
  unfold tailWord_418893
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278282871429677073821333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10185521914286451382547555 15278282871429677073821333)
  ·
    refine ⟨716169509598266112835375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15278282871429677073821333 716169509598266112835375)
    ·
      refine ⟨1074254264397399169253063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716169509598266112835375 1074254264397399169253063)
      ·
        refine ⟨1611381396596098753879595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074254264397399169253063 1611381396596098753879595)
        ·
          refine ⟨2417072094894148130819393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611381396596098753879595 2417072094894148130819393)
          ·
            refine ⟨1812804071170611098114545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417072094894148130819393 1812804071170611098114545)
            ·
              refine ⟨1359603053377958323585909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812804071170611098114545 1359603053377958323585909)
              ·
                refine ⟨127462786254183592836179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1359603053377958323585909 127462786254183592836179)
                ·
                  rfl

theorem cell19_418893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_418893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418893 prefixEnd_418893 := by exact prefixLift 418893
  have htrace : WordTrace (prefixWord ++ tailWord_418893) baseStart_418893 baseEnd_418893 := by
    simpa [prefixWord, tailWord_418893, baseEnd_418893] using wordTrace_append hprefix tailTrace_418893
  have hstable : (prefixWord ++ tailWord_418893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418893).length < 2 ^ (prefixWord ++ tailWord_418893).sum := by decide
  have hdescent : baseEnd_418893 < baseStart_418893 := by decide
  rcases family_descends (prefixWord ++ tailWord_418893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418910 : List Nat := [4, 4, 1, 1, 1, 8]
def baseStart_418910 : Nat := 118140960795 + 418910 * 2 ^ 59
def prefixEnd_418910 : Nat := 4983230072969 + 3 ^ 40 * 418910 * 2
def baseEnd_418910 : Nat := 14163106566259176717595

theorem tailTrace_418910 : CollatzResearch.WordTrace tailWord_418910 prefixEnd_418910 14163106566259176717595 := by
  unfold tailWord_418910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909862864046011122148773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10185935274912059318126789 1909862864046011122148773)
  ·
    refine ⟨358099287008627085402895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1909862864046011122148773 358099287008627085402895)
    ·
      refine ⟨537148930512940628104343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358099287008627085402895 537148930512940628104343)
      ·
        refine ⟨805723395769410942156515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537148930512940628104343 805723395769410942156515)
        ·
          refine ⟨1208585093654116413234773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805723395769410942156515 1208585093654116413234773)
          ·
            refine ⟨14163106566259176717595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1208585093654116413234773 14163106566259176717595)
            ·
              rfl

theorem cell19_418910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_418910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_418910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_418910 prefixEnd_418910 := by exact prefixLift 418910
  have htrace : WordTrace (prefixWord ++ tailWord_418910) baseStart_418910 baseEnd_418910 := by
    simpa [prefixWord, tailWord_418910, baseEnd_418910] using wordTrace_append hprefix tailTrace_418910
  have hstable : (prefixWord ++ tailWord_418910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418910).length < 2 ^ (prefixWord ++ tailWord_418910).sum := by decide
  have hdescent : baseEnd_418910 < baseStart_418910 := by decide
  rcases family_descends (prefixWord ++ tailWord_418910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419045 : List Nat := [1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_419045 : Nat := 118140960795 + 419045 * 2 ^ 59
def prefixEnd_419045 : Nat := 4983230072969 + 3 ^ 40 * 419045 * 2
def baseEnd_419045 : Nat := 127509037548692277457987

theorem tailTrace_419045 : CollatzResearch.WordTrace tailWord_419045 prefixEnd_419045 127509037548692277457987 := by
  unfold tailWord_419045
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283826766879007033354589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10189217844586004688903059 15283826766879007033354589)
  ·
    refine ⟨5731435037579627637507971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15283826766879007033354589 5731435037579627637507971)
    ·
      refine ⟨8597152556369441456261957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731435037579627637507971 8597152556369441456261957)
      ·
        refine ⟨1611966104319270273049117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8597152556369441456261957 1611966104319270273049117)
        ·
          refine ⟨604487289119726352393419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1611966104319270273049117 604487289119726352393419)
          ·
            refine ⟨906730933679589528590129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604487289119726352393419 906730933679589528590129)
            ·
              refine ⟨680048200259692146442597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906730933679589528590129 680048200259692146442597)
              ·
                refine ⟨127509037548692277457987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680048200259692146442597 127509037548692277457987)
                ·
                  rfl

theorem cell19_419045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_419045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419045 prefixEnd_419045 := by exact prefixLift 419045
  have htrace : WordTrace (prefixWord ++ tailWord_419045) baseStart_419045 baseEnd_419045 := by
    simpa [prefixWord, tailWord_419045, baseEnd_419045] using wordTrace_append hprefix tailTrace_419045
  have hstable : (prefixWord ++ tailWord_419045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419045).length < 2 ^ (prefixWord ++ tailWord_419045).sum := by decide
  have hdescent : baseEnd_419045 < baseStart_419045 := by decide
  rcases family_descends (prefixWord ++ tailWord_419045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419085 : List Nat := [1, 7, 11]
def baseStart_419085 : Nat := 118140960795 + 419085 * 2 ^ 59
def prefixEnd_419085 : Nat := 4983230072969 + 3 ^ 40 * 419085 * 2
def baseEnd_419085 : Nat := 524778637621333483823

theorem tailTrace_419085 : CollatzResearch.WordTrace tailWord_419085 prefixEnd_419085 524778637621333483823 := by
  unfold tailWord_419085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285285686734093864810709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10190190457822729243207139 15285285686734093864810709)
  ·
    refine ⟨358248883282830324956501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15285285686734093864810709 358248883282830324956501)
    ·
      refine ⟨524778637621333483823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 358248883282830324956501 524778637621333483823)
      ·
        rfl

theorem cell19_419085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 11].length) (baseStart_419085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419085 prefixEnd_419085 := by exact prefixLift 419085
  have htrace : WordTrace (prefixWord ++ tailWord_419085) baseStart_419085 baseEnd_419085 := by
    simpa [prefixWord, tailWord_419085, baseEnd_419085] using wordTrace_append hprefix tailTrace_419085
  have hstable : (prefixWord ++ tailWord_419085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419085).length < 2 ^ (prefixWord ++ tailWord_419085).sum := by decide
  have hdescent : baseEnd_419085 < baseStart_419085 := by decide
  rcases family_descends (prefixWord ++ tailWord_419085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419121 : List Nat := [1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_419121 : Nat := 118140960795 + 419121 * 2 ^ 59
def prefixEnd_419121 : Nat := 4983230072969 + 3 ^ 40 * 419121 * 2
def baseEnd_419121 : Nat := 127532163195946619768891

theorem tailTrace_419121 : CollatzResearch.WordTrace tailWord_419121 prefixEnd_419121 127532163195946619768891 := by
  unfold tailWord_419121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286598714603672013121217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10191065809735781342080811 15286598714603672013121217)
  ·
    refine ⟨11464949035952754009840913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15286598714603672013121217 11464949035952754009840913)
    ·
      refine ⟨8598711776964565507380685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11464949035952754009840913 8598711776964565507380685)
      ·
        refine ⟨3224516916361712065267757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8598711776964565507380685 3224516916361712065267757)
        ·
          refine ⟨1209193843635642024475409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3224516916361712065267757 1209193843635642024475409)
          ·
            refine ⟨906895382726731518356557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209193843635642024475409 906895382726731518356557)
            ·
              refine ⟨340085768522524319383709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 906895382726731518356557 340085768522524319383709)
              ·
                refine ⟨127532163195946619768891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340085768522524319383709 127532163195946619768891)
                ·
                  rfl

theorem cell19_419121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_419121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419121 prefixEnd_419121 := by exact prefixLift 419121
  have htrace : WordTrace (prefixWord ++ tailWord_419121) baseStart_419121 baseEnd_419121 := by
    simpa [prefixWord, tailWord_419121, baseEnd_419121] using wordTrace_append hprefix tailTrace_419121
  have hstable : (prefixWord ++ tailWord_419121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419121).length < 2 ^ (prefixWord ++ tailWord_419121).sum := by decide
  have hdescent : baseEnd_419121 < baseStart_419121 := by decide
  rcases family_descends (prefixWord ++ tailWord_419121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419140 : List Nat := [2, 3, 4, 1, 1, 2, 6]
def baseStart_419140 : Nat := 118140960795 + 419140 * 2 ^ 59
def prefixEnd_419140 : Nat := 4983230072969 + 3 ^ 40 * 419140 * 2
def baseEnd_419140 : Nat := 42512648202586735115539

theorem tailTrace_419140 : CollatzResearch.WordTrace tailWord_419140 prefixEnd_419140 42512648202586735115539 := by
  unfold tailWord_419140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643645850767419129031437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10191527801023225505375249 7643645850767419129031437)
  ·
    refine ⟨2866367194037782173386789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7643645850767419129031437 2866367194037782173386789)
    ·
      refine ⟨537443848882084157510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2866367194037782173386789 537443848882084157510023)
      ·
        refine ⟨806165773323126236265035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537443848882084157510023 806165773323126236265035)
        ·
          refine ⟨1209248659984689354397553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806165773323126236265035 1209248659984689354397553)
          ·
            refine ⟨906936494988517015798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209248659984689354397553 906936494988517015798165)
            ·
              refine ⟨42512648202586735115539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906936494988517015798165 42512648202586735115539)
              ·
                rfl

theorem cell19_419140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_419140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419140 prefixEnd_419140 := by exact prefixLift 419140
  have htrace : WordTrace (prefixWord ++ tailWord_419140) baseStart_419140 baseEnd_419140 := by
    simpa [prefixWord, tailWord_419140, baseEnd_419140] using wordTrace_append hprefix tailTrace_419140
  have hstable : (prefixWord ++ tailWord_419140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419140).length < 2 ^ (prefixWord ++ tailWord_419140).sum := by decide
  have hdescent : baseEnd_419140 < baseStart_419140 := by decide
  rcases family_descends (prefixWord ++ tailWord_419140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419176 : List Nat := [2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_419176 : Nat := 118140960795 + 419176 * 2 ^ 59
def prefixEnd_419176 : Nat := 4983230072969 + 3 ^ 40 * 419176 * 2
def baseEnd_419176 : Nat := 127548898861722788546519

theorem tailTrace_419176 : CollatzResearch.WordTrace tailWord_419176 prefixEnd_419176 127548898861722788546519 := by
  unfold tailWord_419176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644302364702208203186691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10192403152936277604248921 7644302364702208203186691)
  ·
    refine ⟨11466453547053312304780037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7644302364702208203186691 11466453547053312304780037)
    ·
      refine ⟨2149960040072496057146257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11466453547053312304780037 2149960040072496057146257)
      ·
        refine ⟨1612470030054372042859693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2149960040072496057146257 1612470030054372042859693)
        ·
          refine ⟨604676261270389516072385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1612470030054372042859693 604676261270389516072385)
          ·
            refine ⟨453507195952792137054289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604676261270389516072385 453507195952792137054289)
            ·
              refine ⟨340130396964594102790717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453507195952792137054289 340130396964594102790717)
              ·
                refine ⟨127548898861722788546519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340130396964594102790717 127548898861722788546519)
                ·
                  rfl

theorem cell19_419176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_419176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419176 prefixEnd_419176 := by exact prefixLift 419176
  have htrace : WordTrace (prefixWord ++ tailWord_419176) baseStart_419176 baseEnd_419176 := by
    simpa [prefixWord, tailWord_419176, baseEnd_419176] using wordTrace_append hprefix tailTrace_419176
  have hstable : (prefixWord ++ tailWord_419176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419176).length < 2 ^ (prefixWord ++ tailWord_419176).sum := by decide
  have hdescent : baseEnd_419176 < baseStart_419176 := by decide
  rcases family_descends (prefixWord ++ tailWord_419176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419178 : List Nat := [3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_419178 : Nat := 118140960795 + 419178 * 2 ^ 59
def prefixEnd_419178 : Nat := 4983230072969 + 3 ^ 40 * 419178 * 2
def baseEnd_419178 : Nat := 127549507431387376502069

theorem tailTrace_419178 : CollatzResearch.WordTrace tailWord_419178 prefixEnd_419178 127549507431387376502069 := by
  unfold tailWord_419178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822169418849292686986547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10192451783598113831964125 3822169418849292686986547)
  ·
    refine ⟨5733254128273939030479821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3822169418849292686986547 5733254128273939030479821)
    ·
      refine ⟨2149970298102727136429933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5733254128273939030479821 2149970298102727136429933)
      ·
        refine ⟨806238861788522676161225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2149970298102727136429933 806238861788522676161225)
        ·
          refine ⟨604679146341392007120919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806238861788522676161225 604679146341392007120919)
          ·
            refine ⟨907018719512088010681379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604679146341392007120919 907018719512088010681379)
            ·
              refine ⟨1360528079268132016022069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907018719512088010681379 1360528079268132016022069)
              ·
                refine ⟨127549507431387376502069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360528079268132016022069 127549507431387376502069)
                ·
                  rfl

theorem cell19_419178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_419178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419178 prefixEnd_419178 := by exact prefixLift 419178
  have htrace : WordTrace (prefixWord ++ tailWord_419178) baseStart_419178 baseEnd_419178 := by
    simpa [prefixWord, tailWord_419178, baseEnd_419178] using wordTrace_append hprefix tailTrace_419178
  have hstable : (prefixWord ++ tailWord_419178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419178).length < 2 ^ (prefixWord ++ tailWord_419178).sum := by decide
  have hdescent : baseEnd_419178 < baseStart_419178 := by decide
  rcases family_descends (prefixWord ++ tailWord_419178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419180 : List Nat := [2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_419180 : Nat := 118140960795 + 419180 * 2 ^ 59
def prefixEnd_419180 : Nat := 4983230072969 + 3 ^ 40 * 419180 * 2
def baseEnd_419180 : Nat := 127550116001051964457619

theorem tailTrace_419180 : CollatzResearch.WordTrace tailWord_419180 prefixEnd_419180 127550116001051964457619 := by
  unfold tailWord_419180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644375310694962544759497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10192500414259950059679329 7644375310694962544759497)
  ·
    refine ⟨5733281483021221908569623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7644375310694962544759497 5733281483021221908569623)
    ·
      refine ⟨8599922224531832862854435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733281483021221908569623 8599922224531832862854435)
      ·
        refine ⟨12899883336797749294281653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8599922224531832862854435 12899883336797749294281653)
        ·
          refine ⟨1209364062824788996338905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12899883336797749294281653 1209364062824788996338905)
          ·
            refine ⟨907023047118591747254179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209364062824788996338905 907023047118591747254179)
            ·
              refine ⟨1360534570677887620881269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907023047118591747254179 1360534570677887620881269)
              ·
                refine ⟨127550116001051964457619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360534570677887620881269 127550116001051964457619)
                ·
                  rfl

theorem cell19_419180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_419180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419180 prefixEnd_419180 := by exact prefixLift 419180
  have htrace : WordTrace (prefixWord ++ tailWord_419180) baseStart_419180 baseEnd_419180 := by
    simpa [prefixWord, tailWord_419180, baseEnd_419180] using wordTrace_append hprefix tailTrace_419180
  have hstable : (prefixWord ++ tailWord_419180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419180).length < 2 ^ (prefixWord ++ tailWord_419180).sum := by decide
  have hdescent : baseEnd_419180 < baseStart_419180 := by decide
  rcases family_descends (prefixWord ++ tailWord_419180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419349 : List Nat := [1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_419349 : Nat := 118140960795 + 419349 * 2 ^ 59
def prefixEnd_419349 : Nat := 4983230072969 + 3 ^ 40 * 419349 * 2
def baseEnd_419349 : Nat := 127601540137709646701603

theorem tailTrace_419349 : CollatzResearch.WordTrace tailWord_419349 prefixEnd_419349 127601540137709646701603 := by
  unfold tailWord_419349
  simp only [CollatzResearch.WordTrace]
  refine ⟨15294914557777666952421101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10196609705185111301614067 15294914557777666952421101)
  ·
    refine ⟨5735592959166625107157913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15294914557777666952421101 5735592959166625107157913)
    ·
      refine ⟨4301694719374968830368435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5735592959166625107157913 4301694719374968830368435)
      ·
        refine ⟨6452542079062453245552653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301694719374968830368435 6452542079062453245552653)
        ·
          refine ⟨2419703279648419967082245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6452542079062453245552653 2419703279648419967082245)
          ·
            refine ⟨453694364934078743827921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2419703279648419967082245 453694364934078743827921)
            ·
              refine ⟨340270773700559057870941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453694364934078743827921 340270773700559057870941)
              ·
                refine ⟨127601540137709646701603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340270773700559057870941 127601540137709646701603)
                ·
                  rfl

theorem cell19_419349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_419349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419349 prefixEnd_419349 := by exact prefixLift 419349
  have htrace : WordTrace (prefixWord ++ tailWord_419349) baseStart_419349 baseEnd_419349 := by
    simpa [prefixWord, tailWord_419349, baseEnd_419349] using wordTrace_append hprefix tailTrace_419349
  have hstable : (prefixWord ++ tailWord_419349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419349).length < 2 ^ (prefixWord ++ tailWord_419349).sum := by decide
  have hdescent : baseEnd_419349 < baseStart_419349 := by decide
  rcases family_descends (prefixWord ++ tailWord_419349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419368 : List Nat := [2, 1, 5, 2, 2, 2, 5]
def baseStart_419368 : Nat := 118140960795 + 419368 * 2 ^ 59
def prefixEnd_419368 : Nat := 4983230072969 + 3 ^ 40 * 419368 * 2
def baseEnd_419368 : Nat := 42535773849841077426443

theorem tailTrace_419368 : CollatzResearch.WordTrace tailWord_419368 prefixEnd_419368 42535773849841077426443 := by
  unfold tailWord_419368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647803772354416598681379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10197071696472555464908505 7647803772354416598681379)
  ·
    refine ⟨11471705658531624898022069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7647803772354416598681379 11471705658531624898022069)
    ·
      refine ⟨1075472405487339834189569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11471705658531624898022069 1075472405487339834189569)
      ·
        refine ⟨806604304115504875642177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1075472405487339834189569 806604304115504875642177)
        ·
          refine ⟨604953228086628656731633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806604304115504875642177 604953228086628656731633)
          ·
            refine ⟨453714921064971492548725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604953228086628656731633 453714921064971492548725)
            ·
              refine ⟨42535773849841077426443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 453714921064971492548725 42535773849841077426443)
              ·
                rfl

theorem cell19_419368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_419368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419368 prefixEnd_419368 := by exact prefixLift 419368
  have htrace : WordTrace (prefixWord ++ tailWord_419368) baseStart_419368 baseEnd_419368 := by
    simpa [prefixWord, tailWord_419368, baseEnd_419368] using wordTrace_append hprefix tailTrace_419368
  have hstable : (prefixWord ++ tailWord_419368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419368).length < 2 ^ (prefixWord ++ tailWord_419368).sum := by decide
  have hdescent : baseEnd_419368 < baseStart_419368 := by decide
  rcases family_descends (prefixWord ++ tailWord_419368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419391 : List Nat := [1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_419391 : Nat := 118140960795 + 419391 * 2 ^ 59
def prefixEnd_419391 : Nat := 4983230072969 + 3 ^ 40 * 419391 * 2
def baseEnd_419391 : Nat := 127614320100665993768155

theorem tailTrace_419391 : CollatzResearch.WordTrace tailWord_419391 prefixEnd_419391 127614320100665993768155 := by
  unfold tailWord_419391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296446423625508125450027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10197630949083672083633351 15296446423625508125450027)
  ·
    refine ⟨22944669635438262188175041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15296446423625508125450027 22944669635438262188175041)
    ·
      refine ⟨17208502226578696641131281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22944669635438262188175041 17208502226578696641131281)
      ·
        refine ⟨12906376669934022480848461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17208502226578696641131281 12906376669934022480848461)
        ·
          refine ⟨4839891251225258430318173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12906376669934022480848461 4839891251225258430318173)
          ·
            refine ⟨1814959219209471911369315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4839891251225258430318173 1814959219209471911369315)
            ·
              refine ⟨2722438828814207867053973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814959219209471911369315 2722438828814207867053973)
              ·
                refine ⟨127614320100665993768155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2722438828814207867053973 127614320100665993768155)
                ·
                  rfl

theorem cell19_419391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_419391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419391 prefixEnd_419391 := by exact prefixLift 419391
  have htrace : WordTrace (prefixWord ++ tailWord_419391) baseStart_419391 baseEnd_419391 := by
    simpa [prefixWord, tailWord_419391, baseEnd_419391] using wordTrace_append hprefix tailTrace_419391
  have hstable : (prefixWord ++ tailWord_419391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419391).length < 2 ^ (prefixWord ++ tailWord_419391).sum := by decide
  have hdescent : baseEnd_419391 < baseStart_419391 := by decide
  rcases family_descends (prefixWord ++ tailWord_419391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419429 : List Nat := [1, 3, 1, 3, 3, 8]
def baseStart_419429 : Nat := 118140960795 + 419429 * 2 ^ 59
def prefixEnd_419429 : Nat := 4983230072969 + 3 ^ 40 * 419429 * 2
def baseEnd_419429 : Nat := 14180653658254796102623

theorem tailTrace_419429 : CollatzResearch.WordTrace tailWord_419429 prefixEnd_419429 14180653658254796102623 := by
  unfold tailWord_419429
  simp only [CollatzResearch.WordTrace]
  refine ⟨15297832397487840615333341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10198554931658560410222227 15297832397487840615333341)
  ·
    refine ⟨5736687149057940230750003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15297832397487840615333341 5736687149057940230750003)
    ·
      refine ⟨8605030723586910346125005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736687149057940230750003 8605030723586910346125005)
      ·
        refine ⟨3226886521345091379796877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8605030723586910346125005 3226886521345091379796877)
        ·
          refine ⟨1210082445504409267423829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3226886521345091379796877 1210082445504409267423829)
          ·
            refine ⟨14180653658254796102623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1210082445504409267423829 14180653658254796102623)
            ·
              rfl

theorem cell19_419429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_419429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419429 prefixEnd_419429 := by exact prefixLift 419429
  have htrace : WordTrace (prefixWord ++ tailWord_419429) baseStart_419429 baseEnd_419429 := by
    simpa [prefixWord, tailWord_419429, baseEnd_419429] using wordTrace_append hprefix tailTrace_419429
  have hstable : (prefixWord ++ tailWord_419429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419429).length < 2 ^ (prefixWord ++ tailWord_419429).sum := by decide
  have hdescent : baseEnd_419429 < baseStart_419429 := by decide
  rcases family_descends (prefixWord ++ tailWord_419429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419484 : List Nat := [2, 2, 3, 2, 3, 1, 6]
def baseStart_419484 : Nat := 118140960795 + 419484 * 2 ^ 59
def prefixEnd_419484 : Nat := 4983230072969 + 3 ^ 40 * 419484 * 2
def baseEnd_419484 : Nat := 42547539530023111233745

theorem tailTrace_419484 : CollatzResearch.WordTrace tailWord_419484 prefixEnd_419484 42547539530023111233745 := by
  unfold tailWord_419484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7649919206144292504292753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10199892274859056672390337 7649919206144292504292753)
  ·
    refine ⟨5737439404608219378219565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7649919206144292504292753 5737439404608219378219565)
    ·
      refine ⟨2151539776728082266832337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5737439404608219378219565 2151539776728082266832337)
      ·
        refine ⟨1613654832546061700124253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151539776728082266832337 1613654832546061700124253)
        ·
          refine ⟨605120562204773137546595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1613654832546061700124253 605120562204773137546595)
          ·
            refine ⟨907680843307159706319893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605120562204773137546595 907680843307159706319893)
            ·
              refine ⟨42547539530023111233745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 907680843307159706319893 42547539530023111233745)
              ·
                rfl

theorem cell19_419484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_419484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419484 prefixEnd_419484 := by exact prefixLift 419484
  have htrace : WordTrace (prefixWord ++ tailWord_419484) baseStart_419484 baseEnd_419484 := by
    simpa [prefixWord, tailWord_419484, baseEnd_419484] using wordTrace_append hprefix tailTrace_419484
  have hstable : (prefixWord ++ tailWord_419484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419484).length < 2 ^ (prefixWord ++ tailWord_419484).sum := by decide
  have hdescent : baseEnd_419484 < baseStart_419484 := by decide
  rcases family_descends (prefixWord ++ tailWord_419484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419560 : List Nat := [2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_419560 : Nat := 118140960795 + 419560 * 2 ^ 59
def prefixEnd_419560 : Nat := 4983230072969 + 3 ^ 40 * 419560 * 2
def baseEnd_419560 : Nat := 127665744237323676012139

theorem tailTrace_419560 : CollatzResearch.WordTrace tailWord_419560 prefixEnd_419560 127665744237323676012139 := by
  unfold tailWord_419560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651305180006624994176067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10201740240008833325568089 7651305180006624994176067)
  ·
    refine ⟨11476957770009937491264101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7651305180006624994176067 11476957770009937491264101)
    ·
      refine ⟨2151929581876863279612019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11476957770009937491264101 2151929581876863279612019)
      ·
        refine ⟨3227894372815294919418029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151929581876863279612019 3227894372815294919418029)
        ·
          refine ⟨1210460389805735594781761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3227894372815294919418029 1210460389805735594781761)
          ·
            refine ⟨907845292354301696086321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210460389805735594781761 907845292354301696086321)
            ·
              refine ⟨680883969265726272064741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907845292354301696086321 680883969265726272064741)
              ·
                refine ⟨127665744237323676012139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680883969265726272064741 127665744237323676012139)
                ·
                  rfl

theorem cell19_419560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_419560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419560 prefixEnd_419560 := by exact prefixLift 419560
  have htrace : WordTrace (prefixWord ++ tailWord_419560) baseStart_419560 baseEnd_419560 := by
    simpa [prefixWord, tailWord_419560, baseEnd_419560] using wordTrace_append hprefix tailTrace_419560
  have hstable : (prefixWord ++ tailWord_419560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419560).length < 2 ^ (prefixWord ++ tailWord_419560).sum := by decide
  have hdescent : baseEnd_419560 < baseStart_419560 := by decide
  rcases family_descends (prefixWord ++ tailWord_419560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419562 : List Nat := [3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_419562 : Nat := 118140960795 + 419562 * 2 ^ 59
def prefixEnd_419562 : Nat := 4983230072969 + 3 ^ 40 * 419562 * 2
def baseEnd_419562 : Nat := 127666352806988263967689

theorem tailTrace_419562 : CollatzResearch.WordTrace tailWord_419562 prefixEnd_419562 127666352806988263967689 := by
  unfold tailWord_419562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825670826501501082481235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10201788870670669553283293 3825670826501501082481235)
  ·
    refine ⟨5738506239752251623721853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3825670826501501082481235 5738506239752251623721853)
    ·
      refine ⟨2151939839907094358895695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5738506239752251623721853 2151939839907094358895695)
      ·
        refine ⟨3227909759860641538343543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151939839907094358895695 3227909759860641538343543)
        ·
          refine ⟨4841864639790962307515315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227909759860641538343543 4841864639790962307515315)
          ·
            refine ⟨7262796959686443461272973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841864639790962307515315 7262796959686443461272973)
            ·
              refine ⟨2723548859882416297977365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7262796959686443461272973 2723548859882416297977365)
              ·
                refine ⟨127666352806988263967689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2723548859882416297977365 127666352806988263967689)
                ·
                  rfl

theorem cell19_419562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_419562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419562 prefixEnd_419562 := by exact prefixLift 419562
  have htrace : WordTrace (prefixWord ++ tailWord_419562) baseStart_419562 baseEnd_419562 := by
    simpa [prefixWord, tailWord_419562, baseEnd_419562] using wordTrace_append hprefix tailTrace_419562
  have hstable : (prefixWord ++ tailWord_419562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419562).length < 2 ^ (prefixWord ++ tailWord_419562).sum := by decide
  have hdescent : baseEnd_419562 < baseStart_419562 := by decide
  rcases family_descends (prefixWord ++ tailWord_419562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419590 : List Nat := [6, 2, 2, 1, 2, 6]
def baseStart_419590 : Nat := 118140960795 + 419590 * 2 ^ 59
def prefixEnd_419590 : Nat := 4983230072969 + 3 ^ 40 * 419590 * 2
def baseEnd_419590 : Nat := 14186096975810277260599

theorem tailTrace_419590 : CollatzResearch.WordTrace tailWord_419590 prefixEnd_419590 14186096975810277260599 := by
  unfold tailWord_419590
  simp only [CollatzResearch.WordTrace]
  refine ⟨478240767184517659748257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10202469699936376741296149 478240767184517659748257)
  ·
    refine ⟨358680575388388244811193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478240767184517659748257 358680575388388244811193)
    ·
      refine ⟨269010431541291183608395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358680575388388244811193 269010431541291183608395)
      ·
        refine ⟨403515647311936775412593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269010431541291183608395 403515647311936775412593)
        ·
          refine ⟨302636735483952581559445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403515647311936775412593 302636735483952581559445)
          ·
            refine ⟨14186096975810277260599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 302636735483952581559445 14186096975810277260599)
            ·
              rfl

theorem cell19_419590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_419590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419590 prefixEnd_419590 := by exact prefixLift 419590
  have htrace : WordTrace (prefixWord ++ tailWord_419590) baseStart_419590 baseEnd_419590 := by
    simpa [prefixWord, tailWord_419590, baseEnd_419590] using wordTrace_append hprefix tailTrace_419590
  have hstable : (prefixWord ++ tailWord_419590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419590).length < 2 ^ (prefixWord ++ tailWord_419590).sum := by decide
  have hdescent : baseEnd_419590 < baseStart_419590 := by decide
  rcases family_descends (prefixWord ++ tailWord_419590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419617 : List Nat := [1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_419617 : Nat := 118140960795 + 419617 * 2 ^ 59
def prefixEnd_419617 : Nat := 4983230072969 + 3 ^ 40 * 419617 * 2
def baseEnd_419617 : Nat := 127683088472764432745317

theorem tailTrace_419617 : CollatzResearch.WordTrace tailWord_419617 prefixEnd_419617 127683088472764432745317 := by
  unfold tailWord_419617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15304689320806748723177105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10203126213871165815451403 15304689320806748723177105)
  ·
    refine ⟨11478516990605061542382829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15304689320806748723177105 11478516990605061542382829)
    ·
      refine ⟨4304443871476898078393561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11478516990605061542382829 4304443871476898078393561)
      ·
        refine ⟨3228332903607673558795171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4304443871476898078393561 3228332903607673558795171)
        ·
          refine ⟨4842499355411510338192757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228332903607673558795171 4842499355411510338192757)
          ·
            refine ⟨453984314569829094205571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4842499355411510338192757 453984314569829094205571)
            ·
              refine ⟨680976471854743641308357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453984314569829094205571 680976471854743641308357)
              ·
                refine ⟨127683088472764432745317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680976471854743641308357 127683088472764432745317)
                ·
                  rfl

theorem cell19_419617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_419617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419617 prefixEnd_419617 := by exact prefixLift 419617
  have htrace : WordTrace (prefixWord ++ tailWord_419617) baseStart_419617 baseEnd_419617 := by
    simpa [prefixWord, tailWord_419617, baseEnd_419617] using wordTrace_append hprefix tailTrace_419617
  have hstable : (prefixWord ++ tailWord_419617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419617).length < 2 ^ (prefixWord ++ tailWord_419617).sum := by decide
  have hdescent : baseEnd_419617 < baseStart_419617 := by decide
  rcases family_descends (prefixWord ++ tailWord_419617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419619 : List Nat := [1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_419619 : Nat := 118140960795 + 419619 * 2 ^ 59
def prefixEnd_419619 : Nat := 4983230072969 + 3 ^ 40 * 419619 * 2
def baseEnd_419619 : Nat := 127683697042429020700867

theorem tailTrace_419619 : CollatzResearch.WordTrace tailWord_419619 prefixEnd_419619 127683697042429020700867 := by
  unfold tailWord_419619
  simp only [CollatzResearch.WordTrace]
  refine ⟨15304762266799503064749911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10203174844533002043166607 15304762266799503064749911)
  ·
    refine ⟨22957143400199254597124867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15304762266799503064749911 22957143400199254597124867)
    ·
      refine ⟨34435715100298881895687301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22957143400199254597124867 34435715100298881895687301)
      ·
        refine ⟨6456696581306040355441369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34435715100298881895687301 6456696581306040355441369)
        ·
          refine ⟨4842522435979530266581027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456696581306040355441369 4842522435979530266581027)
          ·
            refine ⟨7263783653969295399871541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842522435979530266581027 7263783653969295399871541)
            ·
              refine ⟨680979717559621443737957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7263783653969295399871541 680979717559621443737957)
              ·
                refine ⟨127683697042429020700867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680979717559621443737957 127683697042429020700867)
                ·
                  rfl

theorem cell19_419619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_419619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419619 prefixEnd_419619 := by exact prefixLift 419619
  have htrace : WordTrace (prefixWord ++ tailWord_419619) baseStart_419619 baseEnd_419619 := by
    simpa [prefixWord, tailWord_419619, baseEnd_419619] using wordTrace_append hprefix tailTrace_419619
  have hstable : (prefixWord ++ tailWord_419619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419619).length < 2 ^ (prefixWord ++ tailWord_419619).sum := by decide
  have hdescent : baseEnd_419619 < baseStart_419619 := by decide
  rcases family_descends (prefixWord ++ tailWord_419619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419693 : List Nat := [1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_419693 : Nat := 118140960795 + 419693 * 2 ^ 59
def prefixEnd_419693 : Nat := 4983230072969 + 3 ^ 40 * 419693 * 2
def baseEnd_419693 : Nat := 127706214120018775056221

theorem tailTrace_419693 : CollatzResearch.WordTrace tailWord_419693 prefixEnd_419693 127706214120018775056221 := by
  unfold tailWord_419693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307461268531413702943733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10204974179020942468629155 15307461268531413702943733)
  ·
    refine ⟨1435074493924820034650975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15307461268531413702943733 1435074493924820034650975)
    ·
      refine ⟨2152611740887230051976463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435074493924820034650975 2152611740887230051976463)
      ·
        refine ⟨3228917611330845077964695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152611740887230051976463 3228917611330845077964695)
        ·
          refine ⟨4843376416996267616947043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228917611330845077964695 4843376416996267616947043)
          ·
            refine ⟨7265064625494401425420565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843376416996267616947043 7265064625494401425420565)
            ·
              refine ⟨340549904320050066816589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7265064625494401425420565 340549904320050066816589)
              ·
                refine ⟨127706214120018775056221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340549904320050066816589 127706214120018775056221)
                ·
                  rfl

theorem cell19_419693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_419693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419693 prefixEnd_419693 := by exact prefixLift 419693
  have htrace : WordTrace (prefixWord ++ tailWord_419693) baseStart_419693 baseEnd_419693 := by
    simpa [prefixWord, tailWord_419693, baseEnd_419693] using wordTrace_append hprefix tailTrace_419693
  have hstable : (prefixWord ++ tailWord_419693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419693).length < 2 ^ (prefixWord ++ tailWord_419693).sum := by decide
  have hdescent : baseEnd_419693 < baseStart_419693 := by decide
  rcases family_descends (prefixWord ++ tailWord_419693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419710 : List Nat := [4, 2, 3, 1, 1, 3, 5]
def baseStart_419710 : Nat := 118140960795 + 419710 * 2 ^ 59
def prefixEnd_419710 : Nat := 4983230072969 + 3 ^ 40 * 419710 * 2
def baseEnd_419710 : Nat := 42570462320722590892799

theorem tailTrace_419710 : CollatzResearch.WordTrace tailWord_419710 prefixEnd_419710 42570462320722590892799 := by
  unfold tailWord_419710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913510163683728200789073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10205387539646550404208389 1913510163683728200789073)
  ·
    refine ⟨1435132622762796150591805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1913510163683728200789073 1435132622762796150591805)
    ·
      refine ⟨538174733536048556471927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1435132622762796150591805 538174733536048556471927)
      ·
        refine ⟨807262100304072834707891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538174733536048556471927 807262100304072834707891)
        ·
          refine ⟨1210893150456109252061837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807262100304072834707891 1210893150456109252061837)
          ·
            refine ⟨454084931421040969523189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210893150456109252061837 454084931421040969523189)
            ·
              refine ⟨42570462320722590892799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 454084931421040969523189 42570462320722590892799)
              ·
                rfl

theorem cell19_419710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_419710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419710 prefixEnd_419710 := by exact prefixLift 419710
  have htrace : WordTrace (prefixWord ++ tailWord_419710) baseStart_419710 baseEnd_419710 := by
    simpa [prefixWord, tailWord_419710, baseEnd_419710] using wordTrace_append hprefix tailTrace_419710
  have hstable : (prefixWord ++ tailWord_419710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419710).length < 2 ^ (prefixWord ++ tailWord_419710).sum := by decide
  have hdescent : baseEnd_419710 < baseStart_419710 := by decide
  rcases family_descends (prefixWord ++ tailWord_419710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419733 : List Nat := [1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_419733 : Nat := 118140960795 + 419733 * 2 ^ 59
def prefixEnd_419733 : Nat := 4983230072969 + 3 ^ 40 * 419733 * 2
def baseEnd_419733 : Nat := 127718385513310534167223

theorem tailTrace_419733 : CollatzResearch.WordTrace tailWord_419733 prefixEnd_419733 127718385513310534167223 := by
  unfold tailWord_419733
  simp only [CollatzResearch.WordTrace]
  refine ⟨15308920188386500534399853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10205946792257667022933235 15308920188386500534399853)
  ·
    refine ⟨5740845070644937700399945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15308920188386500534399853 5740845070644937700399945)
    ·
      refine ⟨4305633802983703275299959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5740845070644937700399945 4305633802983703275299959)
      ·
        refine ⟨6458450704475554912949939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305633802983703275299959 6458450704475554912949939)
        ·
          refine ⟨9687676056713332369424909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458450704475554912949939 9687676056713332369424909)
          ·
            refine ⟨3632878521267499638534341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9687676056713332369424909 3632878521267499638534341)
            ·
              refine ⟨681164722737656182225189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3632878521267499638534341 681164722737656182225189)
              ·
                refine ⟨127718385513310534167223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681164722737656182225189 127718385513310534167223)
                ·
                  rfl

theorem cell19_419733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_419733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419733 prefixEnd_419733 := by exact prefixLift 419733
  have htrace : WordTrace (prefixWord ++ tailWord_419733) baseStart_419733 baseEnd_419733 := by
    simpa [prefixWord, tailWord_419733, baseEnd_419733] using wordTrace_append hprefix tailTrace_419733
  have hstable : (prefixWord ++ tailWord_419733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419733).length < 2 ^ (prefixWord ++ tailWord_419733).sum := by decide
  have hdescent : baseEnd_419733 < baseStart_419733 := by decide
  rcases family_descends (prefixWord ++ tailWord_419733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419788 : List Nat := [2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_419788 : Nat := 118140960795 + 419788 * 2 ^ 59
def prefixEnd_419788 : Nat := 4983230072969 + 3 ^ 40 * 419788 * 2
def baseEnd_419788 : Nat := 127735121179086702944851

theorem tailTrace_419788 : CollatzResearch.WordTrace tailWord_419788 prefixEnd_419788 127735121179086702944851 := by
  unfold tailWord_419788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655463101593622463826009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10207284135458163285101345 7655463101593622463826009)
  ·
    refine ⟨5741597326195216847869507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7655463101593622463826009 5741597326195216847869507)
    ·
      refine ⟨8612395989292825271804261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741597326195216847869507 8612395989292825271804261)
      ·
        refine ⟨1614824247992404738463299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8612395989292825271804261 1614824247992404738463299)
        ·
          refine ⟨2422236371988607107694949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614824247992404738463299 2422236371988607107694949)
          ·
            refine ⟨454169319747863832692803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2422236371988607107694949 454169319747863832692803)
            ·
              refine ⟨681253979621795749039205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454169319747863832692803 681253979621795749039205)
              ·
                refine ⟨127735121179086702944851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681253979621795749039205 127735121179086702944851)
                ·
                  rfl

theorem cell19_419788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_419788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419788 prefixEnd_419788 := by exact prefixLift 419788
  have htrace : WordTrace (prefixWord ++ tailWord_419788) baseStart_419788 baseEnd_419788 := by
    simpa [prefixWord, tailWord_419788, baseEnd_419788] using wordTrace_append hprefix tailTrace_419788
  have hstable : (prefixWord ++ tailWord_419788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419788).length < 2 ^ (prefixWord ++ tailWord_419788).sum := by decide
  have hdescent : baseEnd_419788 < baseStart_419788 := by decide
  rcases family_descends (prefixWord ++ tailWord_419788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419805 : List Nat := [1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_419805 : Nat := 118140960795 + 419805 * 2 ^ 59
def prefixEnd_419805 : Nat := 4983230072969 + 3 ^ 40 * 419805 * 2
def baseEnd_419805 : Nat := 127740294021235700567027

theorem tailTrace_419805 : CollatzResearch.WordTrace tailWord_419805 prefixEnd_419805 127740294021235700567027 := by
  unfold tailWord_419805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311546244125656831020869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10207697496083771220680579 15311546244125656831020869)
  ·
    refine ⟨2870914920773560655816413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15311546244125656831020869 2870914920773560655816413)
    ·
      refine ⟨1076593095290085245931155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2870914920773560655816413 1076593095290085245931155)
      ·
        refine ⟨1614889642935127868896733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076593095290085245931155 1614889642935127868896733)
        ·
          refine ⟨605583616100672950836275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1614889642935127868896733 605583616100672950836275)
          ·
            refine ⟨908375424151009426254413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605583616100672950836275 908375424151009426254413)
            ·
              refine ⟨340640784056628534845405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908375424151009426254413 340640784056628534845405)
              ·
                refine ⟨127740294021235700567027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340640784056628534845405 127740294021235700567027)
                ·
                  rfl

theorem cell19_419805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_419805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419805 prefixEnd_419805 := by exact prefixLift 419805
  have htrace : WordTrace (prefixWord ++ tailWord_419805) baseStart_419805 baseEnd_419805 := by
    simpa [prefixWord, tailWord_419805, baseEnd_419805] using wordTrace_append hprefix tailTrace_419805
  have hstable : (prefixWord ++ tailWord_419805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419805).length < 2 ^ (prefixWord ++ tailWord_419805).sum := by decide
  have hdescent : baseEnd_419805 < baseStart_419805 := by decide
  rcases family_descends (prefixWord ++ tailWord_419805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419807 : List Nat := [1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_419807 : Nat := 118140960795 + 419807 * 2 ^ 59
def prefixEnd_419807 : Nat := 4983230072969 + 3 ^ 40 * 419807 * 2
def baseEnd_419807 : Nat := 127740902590900288522577

theorem tailTrace_419807 : CollatzResearch.WordTrace tailWord_419807 prefixEnd_419807 127740902590900288522577 := by
  unfold tailWord_419807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311619190118411172593675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10207746126745607448395783 15311619190118411172593675)
  ·
    refine ⟨22967428785177616758890513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15311619190118411172593675 22967428785177616758890513)
    ·
      refine ⟨17225571588883212569167885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22967428785177616758890513 17225571588883212569167885)
      ·
        refine ⟨6459589345831204713437957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17225571588883212569167885 6459589345831204713437957)
        ·
          refine ⟨1211173002343350883769617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6459589345831204713437957 1211173002343350883769617)
          ·
            refine ⟨908379751757513162827213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211173002343350883769617 908379751757513162827213)
            ·
              refine ⟨340642406909067436060205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908379751757513162827213 340642406909067436060205)
              ·
                refine ⟨127740902590900288522577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340642406909067436060205 127740902590900288522577)
                ·
                  rfl

theorem cell19_419807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_419807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419807 prefixEnd_419807 := by exact prefixLift 419807
  have htrace : WordTrace (prefixWord ++ tailWord_419807) baseStart_419807 baseEnd_419807 := by
    simpa [prefixWord, tailWord_419807, baseEnd_419807] using wordTrace_append hprefix tailTrace_419807
  have hstable : (prefixWord ++ tailWord_419807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419807).length < 2 ^ (prefixWord ++ tailWord_419807).sum := by decide
  have hdescent : baseEnd_419807 < baseStart_419807 := by decide
  rcases family_descends (prefixWord ++ tailWord_419807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419866 : List Nat := [3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_419866 : Nat := 118140960795 + 419866 * 2 ^ 59
def prefixEnd_419866 : Nat := 4983230072969 + 3 ^ 40 * 419866 * 2
def baseEnd_419866 : Nat := 127758855396005633211305

theorem tailTrace_419866 : CollatzResearch.WordTrace tailWord_419866 prefixEnd_419866 127758855396005633211305 := by
  unfold tailWord_419866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828442774226166062247863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10209180731269776165994301 3828442774226166062247863)
  ·
    refine ⟨5742664161339249093371795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3828442774226166062247863 5742664161339249093371795)
    ·
      refine ⟨8613996242008873640057693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5742664161339249093371795 8613996242008873640057693)
      ·
        refine ⟨3230248590753327615021635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8613996242008873640057693 3230248590753327615021635)
        ·
          refine ⟨4845372886129991422532453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230248590753327615021635 4845372886129991422532453)
          ·
            refine ⟨908507416149373391724835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4845372886129991422532453 908507416149373391724835)
            ·
              refine ⟨1362761124224060087587253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908507416149373391724835 1362761124224060087587253)
              ·
                refine ⟨127758855396005633211305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1362761124224060087587253 127758855396005633211305)
                ·
                  rfl

theorem cell19_419866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_419866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419866 prefixEnd_419866 := by exact prefixLift 419866
  have htrace : WordTrace (prefixWord ++ tailWord_419866) baseStart_419866 baseEnd_419866 := by
    simpa [prefixWord, tailWord_419866, baseEnd_419866] using wordTrace_append hprefix tailTrace_419866
  have hstable : (prefixWord ++ tailWord_419866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419866).length < 2 ^ (prefixWord ++ tailWord_419866).sum := by decide
  have hdescent : baseEnd_419866 < baseStart_419866 := by decide
  rcases family_descends (prefixWord ++ tailWord_419866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419904 : List Nat := [2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_419904 : Nat := 118140960795 + 419904 * 2 ^ 59
def prefixEnd_419904 : Nat := 4983230072969 + 3 ^ 40 * 419904 * 2
def baseEnd_419904 : Nat := 127770418219632804366757

theorem tailTrace_419904 : CollatzResearch.WordTrace tailWord_419904 prefixEnd_419904 127770418219632804366757 := by
  unfold tailWord_419904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657578535383498369437383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10210104713844664492583177 7657578535383498369437383)
  ·
    refine ⟨11486367803075247554156075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7657578535383498369437383 11486367803075247554156075)
    ·
      refine ⟨17229551704612871331234113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486367803075247554156075 17229551704612871331234113)
      ·
        refine ⟨12922163778459653498425585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17229551704612871331234113 12922163778459653498425585)
        ·
          refine ⟨9691622833844740123819189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12922163778459653498425585 9691622833844740123819189)
          ·
            refine ⟨908589640672944386608049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9691622833844740123819189 908589640672944386608049)
            ·
              refine ⟨681442230504708289956037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908589640672944386608049 681442230504708289956037)
              ·
                refine ⟨127770418219632804366757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681442230504708289956037 127770418219632804366757)
                ·
                  rfl

theorem cell19_419904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_419904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419904 prefixEnd_419904 := by exact prefixLift 419904
  have htrace : WordTrace (prefixWord ++ tailWord_419904) baseStart_419904 baseEnd_419904 := by
    simpa [prefixWord, tailWord_419904, baseEnd_419904] using wordTrace_append hprefix tailTrace_419904
  have hstable : (prefixWord ++ tailWord_419904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419904).length < 2 ^ (prefixWord ++ tailWord_419904).sum := by decide
  have hdescent : baseEnd_419904 < baseStart_419904 := by decide
  rcases family_descends (prefixWord ++ tailWord_419904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419944 : List Nat := [2, 1, 4, 12]
def baseStart_419944 : Nat := 118140960795 + 419944 * 2 ^ 59
def prefixEnd_419944 : Nat := 4983230072969 + 3 ^ 40 * 419944 * 2
def baseEnd_419944 : Nat := 1577562834727463746639

theorem tailTrace_419944 : CollatzResearch.WordTrace tailWord_419944 prefixEnd_419944 1577562834727463746639 := by
  unfold tailWord_419944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658307995311041785165443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10211077327081389046887257 7658307995311041785165443)
  ·
    refine ⟨11487461992966562677748165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658307995311041785165443 11487461992966562677748165)
    ·
      refine ⟨2153899123681230502077781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11487461992966562677748165 2153899123681230502077781)
      ·
        refine ⟨1577562834727463746639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2153899123681230502077781 1577562834727463746639)
        ·
          rfl

theorem cell19_419944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 12].length) (baseStart_419944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419944 prefixEnd_419944 := by exact prefixLift 419944
  have htrace : WordTrace (prefixWord ++ tailWord_419944) baseStart_419944 baseEnd_419944 := by
    simpa [prefixWord, tailWord_419944, baseEnd_419944] using wordTrace_append hprefix tailTrace_419944
  have hstable : (prefixWord ++ tailWord_419944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419944).length < 2 ^ (prefixWord ++ tailWord_419944).sum := by decide
  have hdescent : baseEnd_419944 < baseStart_419944 := by decide
  rcases family_descends (prefixWord ++ tailWord_419944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419961 : List Nat := [1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_419961 : Nat := 118140960795 + 419961 * 2 ^ 59
def prefixEnd_419961 : Nat := 4983230072969 + 3 ^ 40 * 419961 * 2
def baseEnd_419961 : Nat := 127787762455073561099935

theorem tailTrace_419961 : CollatzResearch.WordTrace tailWord_419961 prefixEnd_419961 127787762455073561099935 := by
  unfold tailWord_419961
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317236031560495473699737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10211490687706996982466491 15317236031560495473699737)
  ·
    refine ⟨11487927023670371605274803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15317236031560495473699737 11487927023670371605274803)
    ·
      refine ⟨17231890535505557407912205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11487927023670371605274803 17231890535505557407912205)
      ·
        refine ⟨6461958950814584027967077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17231890535505557407912205 6461958950814584027967077)
        ·
          refine ⟨1211617303277734505243827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6461958950814584027967077 1211617303277734505243827)
          ·
            refine ⟨1817425954916601757865741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211617303277734505243827 1817425954916601757865741)
            ·
              refine ⟨681534733093725659199653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1817425954916601757865741 681534733093725659199653)
              ·
                refine ⟨127787762455073561099935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681534733093725659199653 127787762455073561099935)
                ·
                  rfl

theorem cell19_419961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_419961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419961 prefixEnd_419961 := by exact prefixLift 419961
  have htrace : WordTrace (prefixWord ++ tailWord_419961) baseStart_419961 baseEnd_419961 := by
    simpa [prefixWord, tailWord_419961, baseEnd_419961] using wordTrace_append hprefix tailTrace_419961
  have hstable : (prefixWord ++ tailWord_419961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419961).length < 2 ^ (prefixWord ++ tailWord_419961).sum := by decide
  have hdescent : baseEnd_419961 < baseStart_419961 := by decide
  rcases family_descends (prefixWord ++ tailWord_419961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419978 : List Nat := [3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_419978 : Nat := 118140960795 + 419978 * 2 ^ 59
def prefixEnd_419978 : Nat := 4983230072969 + 3 ^ 40 * 419978 * 2
def baseEnd_419978 : Nat := 127792935297222558722111

theorem tailTrace_419978 : CollatzResearch.WordTrace tailWord_419978 prefixEnd_419978 127792935297222558722111 := by
  unfold tailWord_419978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829464018124726844267147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10211904048332604918045725 3829464018124726844267147)
  ·
    refine ⟨5744196027187090266400721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3829464018124726844267147 5744196027187090266400721)
    ·
      refine ⟨4308147020390317699800541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5744196027187090266400721 4308147020390317699800541)
      ·
        refine ⟨1615555132646369137425203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4308147020390317699800541 1615555132646369137425203)
        ·
          refine ⟨2423332698969553706137805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615555132646369137425203 2423332698969553706137805)
          ·
            refine ⟨908749762113582639801677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2423332698969553706137805 908749762113582639801677)
            ·
              refine ⟨340781160792593489925629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908749762113582639801677 340781160792593489925629)
              ·
                refine ⟨127792935297222558722111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340781160792593489925629 127792935297222558722111)
                ·
                  rfl

theorem cell19_419978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_419978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419978 prefixEnd_419978 := by exact prefixLift 419978
  have htrace : WordTrace (prefixWord ++ tailWord_419978) baseStart_419978 baseEnd_419978 := by
    simpa [prefixWord, tailWord_419978, baseEnd_419978] using wordTrace_append hprefix tailTrace_419978
  have hstable : (prefixWord ++ tailWord_419978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419978).length < 2 ^ (prefixWord ++ tailWord_419978).sum := by decide
  have hdescent : baseEnd_419978 < baseStart_419978 := by decide
  rcases family_descends (prefixWord ++ tailWord_419978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419999 : List Nat := [1, 1, 2, 6, 1, 2, 6]
def baseStart_419999 : Nat := 118140960795 + 419999 * 2 ^ 59
def prefixEnd_419999 : Nat := 4983230072969 + 3 ^ 40 * 419999 * 2
def baseEnd_419999 : Nat := 42599775092900244085129

theorem tailTrace_419999 : CollatzResearch.WordTrace tailWord_419999 prefixEnd_419999 42599775092900244085129 := by
  unfold tailWord_419999
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318622005422827963583051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10212414670281885309055367 15318622005422827963583051)
  ·
    refine ⟨22977933008134241945374577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318622005422827963583051 22977933008134241945374577)
    ·
      refine ⟨17233449756100681459030933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22977933008134241945374577 17233449756100681459030933)
      ·
        refine ⟨807817957317219443392075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17233449756100681459030933 807817957317219443392075)
        ·
          refine ⟨1211726935975829165088113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807817957317219443392075 1211726935975829165088113)
          ·
            refine ⟨908795201981871873816085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211726935975829165088113 908795201981871873816085)
            ·
              refine ⟨42599775092900244085129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 908795201981871873816085 42599775092900244085129)
              ·
                rfl

theorem cell19_419999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_419999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_419999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_419999 prefixEnd_419999 := by exact prefixLift 419999
  have htrace : WordTrace (prefixWord ++ tailWord_419999) baseStart_419999 baseEnd_419999 := by
    simpa [prefixWord, tailWord_419999, baseEnd_419999] using wordTrace_append hprefix tailTrace_419999
  have hstable : (prefixWord ++ tailWord_419999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419999).length < 2 ^ (prefixWord ++ tailWord_419999).sum := by decide
  have hdescent : baseEnd_419999 < baseStart_419999 := by decide
  rcases family_descends (prefixWord ++ tailWord_419999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420037 : List Nat := [1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_420037 : Nat := 118140960795 + 420037 * 2 ^ 59
def prefixEnd_420037 : Nat := 4983230072969 + 3 ^ 40 * 420037 * 2
def baseEnd_420037 : Nat := 127810888102327903410839

theorem tailTrace_420037 : CollatzResearch.WordTrace tailWord_420037 prefixEnd_420037 127810888102327903410839 := by
  unfold tailWord_420037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320007979285160453466365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10213338652856773635644243 15320007979285160453466365)
  ·
    refine ⟨5745002992231935170049887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15320007979285160453466365 5745002992231935170049887)
    ·
      refine ⟨8617504488347902755074831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745002992231935170049887 8617504488347902755074831)
      ·
        refine ⟨12926256732521854132612247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8617504488347902755074831 12926256732521854132612247)
        ·
          refine ⟨19389385098782781198918371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12926256732521854132612247 19389385098782781198918371)
          ·
            refine ⟨29084077648174171798377557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19389385098782781198918371 29084077648174171798377557)
            ·
              refine ⟨340829034939541075762237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 29084077648174171798377557 340829034939541075762237)
              ·
                refine ⟨127810888102327903410839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340829034939541075762237 127810888102327903410839)
                ·
                  rfl

theorem cell19_420037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_420037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420037 prefixEnd_420037 := by exact prefixLift 420037
  have htrace : WordTrace (prefixWord ++ tailWord_420037) baseStart_420037 baseEnd_420037 := by
    simpa [prefixWord, tailWord_420037, baseEnd_420037] using wordTrace_append hprefix tailTrace_420037
  have hstable : (prefixWord ++ tailWord_420037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420037).length < 2 ^ (prefixWord ++ tailWord_420037).sum := by decide
  have hdescent : baseEnd_420037 < baseStart_420037 := by decide
  rcases family_descends (prefixWord ++ tailWord_420037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420054 : List Nat := [5, 2, 1, 2, 1, 1, 7]
def baseStart_420054 : Nat := 118140960795 + 420054 * 2 ^ 59
def prefixEnd_420054 : Nat := 4983230072969 + 3 ^ 40 * 420054 * 2
def baseEnd_420054 : Nat := 42605353648158967011005

theorem tailTrace_420054 : CollatzResearch.WordTrace tailWord_420054 prefixEnd_420054 42605353648158967011005 := by
  unfold tailWord_420054
  simp only [CollatzResearch.WordTrace]
  refine ⟨957539251263973272302201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10213752013482381571223477 957539251263973272302201)
  ·
    refine ⟨718154438447979954226651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 957539251263973272302201 718154438447979954226651)
    ·
      refine ⟨1077231657671969931339977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718154438447979954226651 1077231657671969931339977)
      ·
        refine ⟨807923743253977448504983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077231657671969931339977 807923743253977448504983)
        ·
          refine ⟨1211885614880966172757475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807923743253977448504983 1211885614880966172757475)
          ·
            refine ⟨1817828422321449259136213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211885614880966172757475 1817828422321449259136213)
            ·
              refine ⟨42605353648158967011005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1817828422321449259136213 42605353648158967011005)
              ·
                rfl

theorem cell19_420054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_420054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420054 prefixEnd_420054 := by exact prefixLift 420054
  have htrace : WordTrace (prefixWord ++ tailWord_420054) baseStart_420054 baseEnd_420054 := by
    simpa [prefixWord, tailWord_420054, baseEnd_420054] using wordTrace_append hprefix tailTrace_420054
  have hstable : (prefixWord ++ tailWord_420054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420054).length < 2 ^ (prefixWord ++ tailWord_420054).sum := by decide
  have hdescent : baseEnd_420054 < baseStart_420054 := by decide
  rcases family_descends (prefixWord ++ tailWord_420054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420056 : List Nat := [2, 1, 2, 2, 4, 3, 5]
def baseStart_420056 : Nat := 118140960795 + 420056 * 2 ^ 59
def prefixEnd_420056 : Nat := 4983230072969 + 3 ^ 40 * 420056 * 2
def baseEnd_420056 : Nat := 42605556504713829662855

theorem tailTrace_420056 : CollatzResearch.WordTrace tailWord_420056 prefixEnd_420056 42605556504713829662855 := by
  unfold tailWord_420056
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660350483108163349204011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10213800644144217798938681 7660350483108163349204011)
  ·
    refine ⟨11490525724662245023806017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7660350483108163349204011 11490525724662245023806017)
    ·
      refine ⟨8617894293496683767854513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11490525724662245023806017 8617894293496683767854513)
      ·
        refine ⟨6463420720122512825890885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8617894293496683767854513 6463420720122512825890885)
        ·
          refine ⟨1211891385022971154854541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6463420720122512825890885 1211891385022971154854541)
          ·
            refine ⟨454459269383614183070453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1211891385022971154854541 454459269383614183070453)
            ·
              refine ⟨42605556504713829662855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 454459269383614183070453 42605556504713829662855)
              ·
                rfl

theorem cell19_420056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_420056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420056 prefixEnd_420056 := by exact prefixLift 420056
  have htrace : WordTrace (prefixWord ++ tailWord_420056) baseStart_420056 baseEnd_420056 := by
    simpa [prefixWord, tailWord_420056, baseEnd_420056] using wordTrace_append hprefix tailTrace_420056
  have hstable : (prefixWord ++ tailWord_420056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420056).length < 2 ^ (prefixWord ++ tailWord_420056).sum := by decide
  have hdescent : baseEnd_420056 < baseStart_420056 := by decide
  rcases family_descends (prefixWord ++ tailWord_420056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420058 : List Nat := [3, 1, 1, 2, 2, 1, 9]
def baseStart_420058 : Nat := 118140960795 + 420058 * 2 ^ 59
def prefixEnd_420058 : Nat := 4983230072969 + 3 ^ 40 * 420058 * 2
def baseEnd_420058 : Nat := 42605759361268692314705

theorem tailTrace_420058 : CollatzResearch.WordTrace tailWord_420058 prefixEnd_420058 42605759361268692314705 := by
  unfold tailWord_420058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830193478052270259995207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10213849274806054026653885 3830193478052270259995207)
  ·
    refine ⟨5745290217078405389992811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830193478052270259995207 5745290217078405389992811)
    ·
      refine ⟨8617935325617608084989217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745290217078405389992811 8617935325617608084989217)
      ·
        refine ⟨6463451494213206063741913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8617935325617608084989217 6463451494213206063741913)
        ·
          refine ⟨4847588620659904547806435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6463451494213206063741913 4847588620659904547806435)
          ·
            refine ⟨7271382930989856821709653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847588620659904547806435 7271382930989856821709653)
            ·
              refine ⟨42605759361268692314705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7271382930989856821709653 42605759361268692314705)
              ·
                rfl

theorem cell19_420058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_420058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420058 prefixEnd_420058 := by exact prefixLift 420058
  have htrace : WordTrace (prefixWord ++ tailWord_420058) baseStart_420058 baseEnd_420058 := by
    simpa [prefixWord, tailWord_420058, baseEnd_420058] using wordTrace_append hprefix tailTrace_420058
  have hstable : (prefixWord ++ tailWord_420058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420058).length < 2 ^ (prefixWord ++ tailWord_420058).sum := by decide
  have hdescent : baseEnd_420058 < baseStart_420058 := by decide
  rcases family_descends (prefixWord ++ tailWord_420058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420094 : List Nat := [4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_420094 : Nat := 118140960795 + 420094 * 2 ^ 59
def prefixEnd_420094 : Nat := 4983230072969 + 3 ^ 40 * 420094 * 2
def baseEnd_420094 : Nat := 127828232337768660144017

theorem tailTrace_420094 : CollatzResearch.WordTrace tailWord_420094 prefixEnd_420094 127828232337768660144017 := by
  unfold tailWord_420094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915260867509832398536417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10214724626719106125527557 1915260867509832398536417)
  ·
    refine ⟨1436445650632374298902313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1915260867509832398536417 1436445650632374298902313)
    ·
      refine ⟨1077334237974280724176735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1436445650632374298902313 1077334237974280724176735)
      ·
        refine ⟨1616001356961421086265103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077334237974280724176735 1616001356961421086265103)
        ·
          refine ⟨2424002035442131629397655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616001356961421086265103 2424002035442131629397655)
          ·
            refine ⟨3636003053163197444096483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424002035442131629397655 3636003053163197444096483)
            ·
              refine ⟨5454004579744796166144725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636003053163197444096483 5454004579744796166144725)
              ·
                refine ⟨127828232337768660144017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5454004579744796166144725 127828232337768660144017)
                ·
                  rfl

theorem cell19_420094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_420094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420094 prefixEnd_420094 := by exact prefixLift 420094
  have htrace : WordTrace (prefixWord ++ tailWord_420094) baseStart_420094 baseEnd_420094 := by
    simpa [prefixWord, tailWord_420094, baseEnd_420094] using wordTrace_append hprefix tailTrace_420094
  have hstable : (prefixWord ++ tailWord_420094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420094).length < 2 ^ (prefixWord ++ tailWord_420094).sum := by decide
  have hdescent : baseEnd_420094 < baseStart_420094 := by decide
  rcases family_descends (prefixWord ++ tailWord_420094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420096 : List Nat := [2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_420096 : Nat := 118140960795 + 420096 * 2 ^ 59
def prefixEnd_420096 : Nat := 4983230072969 + 3 ^ 40 * 420096 * 2
def baseEnd_420096 : Nat := 127828840907433248099567

theorem tailTrace_420096 : CollatzResearch.WordTrace tailWord_420096 prefixEnd_420096 127828840907433248099567 := by
  unfold tailWord_420096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661079943035706764932071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10214773257380942353242761 7661079943035706764932071)
  ·
    refine ⟨11491619914553560147398107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7661079943035706764932071 11491619914553560147398107)
    ·
      refine ⟨17237429871830340221097161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11491619914553560147398107 17237429871830340221097161)
      ·
        refine ⟨12928072403872755165822871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17237429871830340221097161 12928072403872755165822871)
        ·
          refine ⟨19392108605809132748734307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12928072403872755165822871 19392108605809132748734307)
          ·
            refine ⟨29088162908713699123101461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19392108605809132748734307 29088162908713699123101461)
            ·
              refine ⟨1363507636345954646395381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29088162908713699123101461 1363507636345954646395381)
              ·
                refine ⟨127828840907433248099567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1363507636345954646395381 127828840907433248099567)
                ·
                  rfl

theorem cell19_420096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_420096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420096 prefixEnd_420096 := by exact prefixLift 420096
  have htrace : WordTrace (prefixWord ++ tailWord_420096) baseStart_420096 baseEnd_420096 := by
    simpa [prefixWord, tailWord_420096, baseEnd_420096] using wordTrace_append hprefix tailTrace_420096
  have hstable : (prefixWord ++ tailWord_420096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420096).length < 2 ^ (prefixWord ++ tailWord_420096).sum := by decide
  have hdescent : baseEnd_420096 < baseStart_420096 := by decide
  rcases family_descends (prefixWord ++ tailWord_420096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420130 : List Nat := [3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_420130 : Nat := 118140960795 + 420130 * 2 ^ 59
def prefixEnd_420130 : Nat := 4983230072969 + 3 ^ 40 * 420130 * 2
def baseEnd_420130 : Nat := 127839186591731243343919

theorem tailTrace_420130 : CollatzResearch.WordTrace tailWord_420130 prefixEnd_420130 127839186591731243343919 := by
  unfold tailWord_420130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830849991987059334150461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10215599978632158224401229 3830849991987059334150461)
  ·
    refine ⟨1436568746995147250306423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3830849991987059334150461 1436568746995147250306423)
    ·
      refine ⟨2154853120492720875459635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436568746995147250306423 2154853120492720875459635)
      ·
        refine ⟨3232279680739081313189453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154853120492720875459635 3232279680739081313189453)
        ·
          refine ⟨1212104880277155492446045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3232279680739081313189453 1212104880277155492446045)
          ·
            refine ⟨454539330103933309667267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1212104880277155492446045 454539330103933309667267)
            ·
              refine ⟨681808995155899964500901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454539330103933309667267 681808995155899964500901)
              ·
                refine ⟨127839186591731243343919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681808995155899964500901 127839186591731243343919)
                ·
                  rfl

theorem cell19_420130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_420130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420130 prefixEnd_420130 := by exact prefixLift 420130
  have htrace : WordTrace (prefixWord ++ tailWord_420130) baseStart_420130 baseEnd_420130 := by
    simpa [prefixWord, tailWord_420130, baseEnd_420130] using wordTrace_append hprefix tailTrace_420130
  have hstable : (prefixWord ++ tailWord_420130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420130).length < 2 ^ (prefixWord ++ tailWord_420130).sum := by decide
  have hdescent : baseEnd_420130 < baseStart_420130 := by decide
  rcases family_descends (prefixWord ++ tailWord_420130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420132 : List Nat := [2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_420132 : Nat := 118140960795 + 420132 * 2 ^ 59
def prefixEnd_420132 : Nat := 4983230072969 + 3 ^ 40 * 420132 * 2
def baseEnd_420132 : Nat := 127839795161395831299469

theorem tailTrace_420132 : CollatzResearch.WordTrace tailWord_420132 prefixEnd_420132 127839795161395831299469 := by
  unfold tailWord_420132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661736456970495839087325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10215648609293994452116433 7661736456970495839087325)
  ·
    refine ⟨2873151171363935939657747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7661736456970495839087325 2873151171363935939657747)
    ·
      refine ⟨4309726757045903909486621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873151171363935939657747 4309726757045903909486621)
      ·
        refine ⟨1616147533892213966057483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4309726757045903909486621 1616147533892213966057483)
        ·
          refine ⟨2424221300838320949086225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616147533892213966057483 2424221300838320949086225)
          ·
            refine ⟨1818165975628740711814669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424221300838320949086225 1818165975628740711814669)
            ·
              refine ⟨681812240860777766930501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818165975628740711814669 681812240860777766930501)
              ·
                refine ⟨127839795161395831299469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681812240860777766930501 127839795161395831299469)
                ·
                  rfl

theorem cell19_420132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_420132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420132 prefixEnd_420132 := by exact prefixLift 420132
  have htrace : WordTrace (prefixWord ++ tailWord_420132) baseStart_420132 baseEnd_420132 := by
    simpa [prefixWord, tailWord_420132, baseEnd_420132] using wordTrace_append hprefix tailTrace_420132
  have hstable : (prefixWord ++ tailWord_420132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420132).length < 2 ^ (prefixWord ++ tailWord_420132).sum := by decide
  have hdescent : baseEnd_420132 < baseStart_420132 := by decide
  rcases family_descends (prefixWord ++ tailWord_420132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420172 : List Nat := [2, 2, 1, 3, 2, 1, 8]
def baseStart_420172 : Nat := 118140960795 + 420172 * 2 ^ 59
def prefixEnd_420172 : Nat := 4983230072969 + 3 ^ 40 * 420172 * 2
def baseEnd_420172 : Nat := 42617322184895863470157

theorem tailTrace_420172 : CollatzResearch.WordTrace tailWord_420172 prefixEnd_420172 42617322184895863470157 := by
  unfold tailWord_420172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662465916898039254815385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10216621222530719006420513 7662465916898039254815385)
  ·
    refine ⟨5746849437673529441111539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7662465916898039254815385 5746849437673529441111539)
    ·
      refine ⟨8620274156510294161667309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746849437673529441111539 8620274156510294161667309)
      ·
        refine ⟨3232602808691360310625241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8620274156510294161667309 3232602808691360310625241)
        ·
          refine ⟨2424452106518520232968931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3232602808691360310625241 2424452106518520232968931)
          ·
            refine ⟨3636678159777780349453397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424452106518520232968931 3636678159777780349453397)
            ·
              refine ⟨42617322184895863470157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3636678159777780349453397 42617322184895863470157)
              ·
                rfl

theorem cell19_420172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_420172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420172 prefixEnd_420172 := by exact prefixLift 420172
  have htrace : WordTrace (prefixWord ++ tailWord_420172) baseStart_420172 baseEnd_420172 := by
    simpa [prefixWord, tailWord_420172, baseEnd_420172] using wordTrace_append hprefix tailTrace_420172
  have hstable : (prefixWord ++ tailWord_420172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420172).length < 2 ^ (prefixWord ++ tailWord_420172).sum := by decide
  have hdescent : baseEnd_420172 < baseStart_420172 := by decide
  rcases family_descends (prefixWord ++ tailWord_420172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420204 : List Nat := [2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_420204 : Nat := 118140960795 + 420204 * 2 ^ 59
def prefixEnd_420204 : Nat := 4983230072969 + 3 ^ 40 * 420204 * 2
def baseEnd_420204 : Nat := 127861703669320997699273

theorem tailTrace_420204 : CollatzResearch.WordTrace tailWord_420204 prefixEnd_420204 127861703669320997699273 := by
  unfold tailWord_420204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663049484840073987397833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10217399313120098649863777 7663049484840073987397833)
  ·
    refine ⟨5747287113630055490548375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7663049484840073987397833 5747287113630055490548375)
    ·
      refine ⟨8620930670445083235822563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5747287113630055490548375 8620930670445083235822563)
      ·
        refine ⟨12931396005667624853733845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8620930670445083235822563 12931396005667624853733845)
        ·
          refine ⟨303079593882834957509387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12931396005667624853733845 303079593882834957509387)
          ·
            refine ⟨454619390824252436264081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303079593882834957509387 454619390824252436264081)
            ·
              refine ⟨340964543118189327198061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454619390824252436264081 340964543118189327198061)
              ·
                refine ⟨127861703669320997699273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340964543118189327198061 127861703669320997699273)
                ·
                  rfl

theorem cell19_420204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_420204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420204 prefixEnd_420204 := by exact prefixLift 420204
  have htrace : WordTrace (prefixWord ++ tailWord_420204) baseStart_420204 baseEnd_420204 := by
    simpa [prefixWord, tailWord_420204, baseEnd_420204] using wordTrace_append hprefix tailTrace_420204
  have hstable : (prefixWord ++ tailWord_420204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420204).length < 2 ^ (prefixWord ++ tailWord_420204).sum := by decide
  have hdescent : baseEnd_420204 < baseStart_420204 := by decide
  rcases family_descends (prefixWord ++ tailWord_420204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420208 : List Nat := [2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_420208 : Nat := 118140960795 + 420208 * 2 ^ 59
def prefixEnd_420208 : Nat := 4983230072969 + 3 ^ 40 * 420208 * 2
def baseEnd_420208 : Nat := 127862920808650173610373

theorem tailTrace_420208 : CollatzResearch.WordTrace tailWord_420208 prefixEnd_420208 127862920808650173610373 := by
  unfold tailWord_420208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663122430832828328970639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10217496574443771105294185 7663122430832828328970639)
  ·
    refine ⟨11494683646249242493455959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7663122430832828328970639 11494683646249242493455959)
    ·
      refine ⟨17242025469373863740183939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11494683646249242493455959 17242025469373863740183939)
      ·
        refine ⟨25863038204060795610275909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17242025469373863740183939 25863038204060795610275909)
        ·
          refine ⟨4849319663261399176926733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25863038204060795610275909 4849319663261399176926733)
          ·
            refine ⟨1818494873723024691347525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4849319663261399176926733 1818494873723024691347525)
            ·
              refine ⟨340967788823067129627661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1818494873723024691347525 340967788823067129627661)
              ·
                refine ⟨127862920808650173610373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340967788823067129627661 127862920808650173610373)
                ·
                  rfl

theorem cell19_420208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_420208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420208 prefixEnd_420208 := by exact prefixLift 420208
  have htrace : WordTrace (prefixWord ++ tailWord_420208) baseStart_420208 baseEnd_420208 := by
    simpa [prefixWord, tailWord_420208, baseEnd_420208] using wordTrace_append hprefix tailTrace_420208
  have hstable : (prefixWord ++ tailWord_420208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420208).length < 2 ^ (prefixWord ++ tailWord_420208).sum := by decide
  have hdescent : baseEnd_420208 < baseStart_420208 := by decide
  rcases family_descends (prefixWord ++ tailWord_420208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420227 : List Nat := [1, 1, 1, 3, 6, 2, 5]
def baseStart_420227 : Nat := 118140960795 + 420227 * 2 ^ 59
def prefixEnd_420227 : Nat := 4983230072969 + 3 ^ 40 * 420227 * 2
def baseEnd_420227 : Nat := 42622900740154586396033

theorem tailTrace_420227 : CollatzResearch.WordTrace tailWord_420227 prefixEnd_420227 42622900740154586396033 := by
  unfold tailWord_420227
  simp only [CollatzResearch.WordTrace]
  refine ⟨15326937848596822902882935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10217958565731215268588623 15326937848596822902882935)
  ·
    refine ⟨22990406772895234354324403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15326937848596822902882935 22990406772895234354324403)
    ·
      refine ⟨34485610159342851531486605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22990406772895234354324403 34485610159342851531486605)
      ·
        refine ⟨12932103809753569324307477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34485610159342851531486605 12932103809753569324307477)
        ·
          refine ⟨606192366082198562076913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12932103809753569324307477 606192366082198562076913)
          ·
            refine ⟨454644274561648921557685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606192366082198562076913 454644274561648921557685)
            ·
              refine ⟨42622900740154586396033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 454644274561648921557685 42622900740154586396033)
              ·
                rfl

theorem cell19_420227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_420227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420227 prefixEnd_420227 := by exact prefixLift 420227
  have htrace : WordTrace (prefixWord ++ tailWord_420227) baseStart_420227 baseEnd_420227 := by
    simpa [prefixWord, tailWord_420227, baseEnd_420227] using wordTrace_append hprefix tailTrace_420227
  have hstable : (prefixWord ++ tailWord_420227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420227).length < 2 ^ (prefixWord ++ tailWord_420227).sum := by decide
  have hdescent : baseEnd_420227 < baseStart_420227 := by decide
  rcases family_descends (prefixWord ++ tailWord_420227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420244 : List Nat := [2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_420244 : Nat := 118140960795 + 420244 * 2 ^ 59
def prefixEnd_420244 : Nat := 4983230072969 + 3 ^ 40 * 420244 * 2
def baseEnd_420244 : Nat := 127873875062612756810275

theorem tailTrace_420244 : CollatzResearch.WordTrace tailWord_420244 prefixEnd_420244 127873875062612756810275 := by
  unfold tailWord_420244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663778944767617403125893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10218371926356823204167857 7663778944767617403125893)
  ·
    refine ⟨1436958552143928263086105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7663778944767617403125893 1436958552143928263086105)
    ·
      refine ⟨1077718914107946197314579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1436958552143928263086105 1077718914107946197314579)
      ·
        refine ⟨1616578371161919295971869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077718914107946197314579 1616578371161919295971869)
        ·
          refine ⟨606216889185719735989451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1616578371161919295971869 606216889185719735989451)
          ·
            refine ⟨909325333778579603984177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606216889185719735989451 909325333778579603984177)
            ·
              refine ⟨681994000333934702988133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909325333778579603984177 681994000333934702988133)
              ·
                refine ⟨127873875062612756810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681994000333934702988133 127873875062612756810275)
                ·
                  rfl

theorem cell19_420244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_420244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420244 prefixEnd_420244 := by exact prefixLift 420244
  have htrace : WordTrace (prefixWord ++ tailWord_420244) baseStart_420244 baseEnd_420244 := by
    simpa [prefixWord, tailWord_420244, baseEnd_420244] using wordTrace_append hprefix tailTrace_420244
  have hstable : (prefixWord ++ tailWord_420244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420244).length < 2 ^ (prefixWord ++ tailWord_420244).sum := by decide
  have hdescent : baseEnd_420244 < baseStart_420244 := by decide
  rcases family_descends (prefixWord ++ tailWord_420244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420362 : List Nat := [3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_420362 : Nat := 118140960795 + 420362 * 2 ^ 59
def prefixEnd_420362 : Nat := 4983230072969 + 3 ^ 40 * 420362 * 2
def baseEnd_420362 : Nat := 127909780672823446187731

theorem tailTrace_420362 : CollatzResearch.WordTrace tailWord_420362 prefixEnd_420362 127909780672823446187731 := by
  unfold tailWord_420362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3832965425776935239761835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10221241135405160639364893 3832965425776935239761835)
  ·
    refine ⟨5749448138665402859642753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3832965425776935239761835 5749448138665402859642753)
    ·
      refine ⟨4312086103999052144732065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749448138665402859642753 4312086103999052144732065)
      ·
        refine ⟨3234064577999289108549049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4312086103999052144732065 3234064577999289108549049)
        ·
          refine ⟨2425548433499466831411787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234064577999289108549049 2425548433499466831411787)
          ·
            refine ⟨3638322650249200247117681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425548433499466831411787 3638322650249200247117681)
            ·
              refine ⟨2728741987686900185338261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3638322650249200247117681 2728741987686900185338261)
              ·
                refine ⟨127909780672823446187731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2728741987686900185338261 127909780672823446187731)
                ·
                  rfl

theorem cell19_420362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_420362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420362 prefixEnd_420362 := by exact prefixLift 420362
  have htrace : WordTrace (prefixWord ++ tailWord_420362) baseStart_420362 baseEnd_420362 := by
    simpa [prefixWord, tailWord_420362, baseEnd_420362] using wordTrace_append hprefix tailTrace_420362
  have hstable : (prefixWord ++ tailWord_420362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420362).length < 2 ^ (prefixWord ++ tailWord_420362).sum := by decide
  have hdescent : baseEnd_420362 < baseStart_420362 := by decide
  rcases family_descends (prefixWord ++ tailWord_420362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420375 : List Nat := [1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_420375 : Nat := 118140960795 + 420375 * 2 ^ 59
def prefixEnd_420375 : Nat := 4983230072969 + 3 ^ 40 * 420375 * 2
def baseEnd_420375 : Nat := 127913736375643267898807

theorem tailTrace_420375 : CollatzResearch.WordTrace tailWord_420375 prefixEnd_420375 127913736375643267898807 := by
  unfold tailWord_420375
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332335852060644179270579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10221557234707096119513719 15332335852060644179270579)
  ·
    refine ⟨22998503778090966268905869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15332335852060644179270579 22998503778090966268905869)
    ·
      refine ⟨8624438916784112350839701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22998503778090966268905869 8624438916784112350839701)
      ·
        refine ⟨404270574224255266445611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8624438916784112350839701 404270574224255266445611)
        ·
          refine ⟨606405861336382899668417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404270574224255266445611 606405861336382899668417)
          ·
            refine ⟨454804396002287174751313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606405861336382899668417 454804396002287174751313)
            ·
              refine ⟨341103297001715381063485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454804396002287174751313 341103297001715381063485)
              ·
                refine ⟨127913736375643267898807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341103297001715381063485 127913736375643267898807)
                ·
                  rfl

theorem cell19_420375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_420375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420375 prefixEnd_420375 := by exact prefixLift 420375
  have htrace : WordTrace (prefixWord ++ tailWord_420375) baseStart_420375 baseEnd_420375 := by
    simpa [prefixWord, tailWord_420375, baseEnd_420375] using wordTrace_append hprefix tailTrace_420375
  have hstable : (prefixWord ++ tailWord_420375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420375).length < 2 ^ (prefixWord ++ tailWord_420375).sum := by decide
  have hdescent : baseEnd_420375 < baseStart_420375 := by decide
  rcases family_descends (prefixWord ++ tailWord_420375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420417 : List Nat := [1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_420417 : Nat := 118140960795 + 420417 * 2 ^ 59
def prefixEnd_420417 : Nat := 4983230072969 + 3 ^ 40 * 420417 * 2
def baseEnd_420417 : Nat := 127926516338599614965359

theorem tailTrace_420417 : CollatzResearch.WordTrace tailWord_420417 prefixEnd_420417 127926516338599614965359 := by
  unfold tailWord_420417
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333867717908485352299505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10222578478605656901533003 15333867717908485352299505)
  ·
    refine ⟨11500400788431364014224629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15333867717908485352299505 11500400788431364014224629)
    ·
      refine ⟨1078162573915440376333559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11500400788431364014224629 1078162573915440376333559)
      ·
        refine ⟨1617243860873160564500339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078162573915440376333559 1617243860873160564500339)
        ·
          refine ⟨2425865791309740846750509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617243860873160564500339 2425865791309740846750509)
          ·
            refine ⟨909699671741152817531441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2425865791309740846750509 909699671741152817531441)
            ·
              refine ⟨682274753805864613148581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909699671741152817531441 682274753805864613148581)
              ·
                refine ⟨127926516338599614965359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682274753805864613148581 127926516338599614965359)
                ·
                  rfl

theorem cell19_420417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_420417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420417 prefixEnd_420417 := by exact prefixLift 420417
  have htrace : WordTrace (prefixWord ++ tailWord_420417) baseStart_420417 baseEnd_420417 := by
    simpa [prefixWord, tailWord_420417, baseEnd_420417] using wordTrace_append hprefix tailTrace_420417
  have hstable : (prefixWord ++ tailWord_420417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420417).length < 2 ^ (prefixWord ++ tailWord_420417).sum := by decide
  have hdescent : baseEnd_420417 < baseStart_420417 := by decide
  rcases family_descends (prefixWord ++ tailWord_420417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420470 : List Nat := [5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_420470 : Nat := 118140960795 + 420470 * 2 ^ 59
def prefixEnd_420470 : Nat := 4983230072969 + 3 ^ 40 * 420470 * 2
def baseEnd_420470 : Nat := 127942643434711195787437

theorem tailTrace_420470 : CollatzResearch.WordTrace tailWord_420470 prefixEnd_420470 127942643434711195787437 := by
  unfold tailWord_420470
  simp only [CollatzResearch.WordTrace]
  refine ⟨958487549169779712748679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10223867191144316935985909 958487549169779712748679)
  ·
    refine ⟨1437731323754669569123019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958487549169779712748679 1437731323754669569123019)
    ·
      refine ⟨2156596985632004353684529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437731323754669569123019 2156596985632004353684529)
      ·
        refine ⟨1617447739224003265263397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156596985632004353684529 1617447739224003265263397)
        ·
          refine ⟨303271451104500612236887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1617447739224003265263397 303271451104500612236887)
          ·
            refine ⟨454907176656750918355331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303271451104500612236887 454907176656750918355331)
            ·
              refine ⟨682360764985126377532997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454907176656750918355331 682360764985126377532997)
              ·
                refine ⟨127942643434711195787437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682360764985126377532997 127942643434711195787437)
                ·
                  rfl

theorem cell19_420470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_420470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420470 prefixEnd_420470 := by exact prefixLift 420470
  have htrace : WordTrace (prefixWord ++ tailWord_420470) baseStart_420470 baseEnd_420470 := by
    simpa [prefixWord, tailWord_420470, baseEnd_420470] using wordTrace_append hprefix tailTrace_420470
  have hstable : (prefixWord ++ tailWord_420470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420470).length < 2 ^ (prefixWord ++ tailWord_420470).sum := by decide
  have hdescent : baseEnd_420470 < baseStart_420470 := by decide
  rcases family_descends (prefixWord ++ tailWord_420470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420476 : List Nat := [2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_420476 : Nat := 118140960795 + 420476 * 2 ^ 59
def prefixEnd_420476 : Nat := 4983230072969 + 3 ^ 40 * 420476 * 2
def baseEnd_420476 : Nat := 127944469143704959654087

theorem tailTrace_420476 : CollatzResearch.WordTrace tailWord_420476 prefixEnd_420476 127944469143704959654087 := by
  unfold tailWord_420476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668009812347369214348641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10224013083129825619131521 7668009812347369214348641)
  ·
    refine ⟨5751007359260526910761481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7668009812347369214348641 5751007359260526910761481)
    ·
      refine ⟨4313255519445395183071111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5751007359260526910761481 4313255519445395183071111)
      ·
        refine ⟨6469883279168092774606667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4313255519445395183071111 6469883279168092774606667)
        ·
          refine ⟨9704824918752139161910001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6469883279168092774606667 9704824918752139161910001)
          ·
            refine ⟨7278618689064104371432501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9704824918752139161910001 7278618689064104371432501)
            ·
              refine ⟨682370502099759784821797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7278618689064104371432501 682370502099759784821797)
              ·
                refine ⟨127944469143704959654087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682370502099759784821797 127944469143704959654087)
                ·
                  rfl

theorem cell19_420476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_420476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420476 prefixEnd_420476 := by exact prefixLift 420476
  have htrace : WordTrace (prefixWord ++ tailWord_420476) baseStart_420476 baseEnd_420476 := by
    simpa [prefixWord, tailWord_420476, baseEnd_420476] using wordTrace_append hprefix tailTrace_420476
  have hstable : (prefixWord ++ tailWord_420476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420476).length < 2 ^ (prefixWord ++ tailWord_420476).sum := by decide
  have hdescent : baseEnd_420476 < baseStart_420476 := by decide
  rcases family_descends (prefixWord ++ tailWord_420476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420548 : List Nat := [2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_420548 : Nat := 118140960795 + 420548 * 2 ^ 59
def prefixEnd_420548 : Nat := 4983230072969 + 3 ^ 40 * 420548 * 2
def baseEnd_420548 : Nat := 127966377651630126053891

theorem tailTrace_420548 : CollatzResearch.WordTrace tailWord_420548 prefixEnd_420548 127966377651630126053891 := by
  unfold tailWord_420548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669322840216947362659149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10225763786955929816878865 7669322840216947362659149)
  ·
    refine ⟨2875996065081355260997181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7669322840216947362659149 2875996065081355260997181)
    ·
      refine ⟨1078498524405508222873943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2875996065081355260997181 1078498524405508222873943)
      ·
        refine ⟨1617747786608262334310915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078498524405508222873943 1617747786608262334310915)
        ·
          refine ⟨2426621679912393501466373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617747786608262334310915 2426621679912393501466373)
          ·
            refine ⟨454991564983573781524945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2426621679912393501466373 454991564983573781524945)
            ·
              refine ⟨341243673737680336143709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454991564983573781524945 341243673737680336143709)
              ·
                refine ⟨127966377651630126053891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341243673737680336143709 127966377651630126053891)
                ·
                  rfl

theorem cell19_420548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_420548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420548 prefixEnd_420548 := by exact prefixLift 420548
  have htrace : WordTrace (prefixWord ++ tailWord_420548) baseStart_420548 baseEnd_420548 := by
    simpa [prefixWord, tailWord_420548, baseEnd_420548] using wordTrace_append hprefix tailTrace_420548
  have hstable : (prefixWord ++ tailWord_420548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420548).length < 2 ^ (prefixWord ++ tailWord_420548).sum := by decide
  have hdescent : baseEnd_420548 < baseStart_420548 := by decide
  rcases family_descends (prefixWord ++ tailWord_420548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420552 : List Nat := [2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_420552 : Nat := 118140960795 + 420552 * 2 ^ 59
def prefixEnd_420552 : Nat := 4983230072969 + 3 ^ 40 * 420552 * 2
def baseEnd_420552 : Nat := 127967594790959301964991

theorem tailTrace_420552 : CollatzResearch.WordTrace tailWord_420552 prefixEnd_420552 127967594790959301964991 := by
  unfold tailWord_420552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669395786209701704231955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10225861048279602272309273 7669395786209701704231955)
  ·
    refine ⟨11504093679314552556347933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7669395786209701704231955 11504093679314552556347933)
    ·
      refine ⟨4314035129742957208630475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11504093679314552556347933 4314035129742957208630475)
      ·
        refine ⟨6471052694614435812945713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314035129742957208630475 6471052694614435812945713)
        ·
          refine ⟨4853289520960826859709285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6471052694614435812945713 4853289520960826859709285)
          ·
            refine ⟨909991785180155036195491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4853289520960826859709285 909991785180155036195491)
            ·
              refine ⟨1364987677770232554293237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909991785180155036195491 1364987677770232554293237)
              ·
                refine ⟨127967594790959301964991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1364987677770232554293237 127967594790959301964991)
                ·
                  rfl

theorem cell19_420552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_420552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420552 prefixEnd_420552 := by exact prefixLift 420552
  have htrace : WordTrace (prefixWord ++ tailWord_420552) baseStart_420552 baseEnd_420552 := by
    simpa [prefixWord, tailWord_420552, baseEnd_420552] using wordTrace_append hprefix tailTrace_420552
  have hstable : (prefixWord ++ tailWord_420552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420552).length < 2 ^ (prefixWord ++ tailWord_420552).sum := by decide
  have hdescent : baseEnd_420552 < baseStart_420552 := by decide
  rcases family_descends (prefixWord ++ tailWord_420552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420590 : List Nat := [4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_420590 : Nat := 118140960795 + 420590 * 2 ^ 59
def prefixEnd_420590 : Nat := 4983230072969 + 3 ^ 40 * 420590 * 2
def baseEnd_420590 : Nat := 127979157614586473120443

theorem tailTrace_420590 : CollatzResearch.WordTrace tailWord_420590 prefixEnd_420590 127979157614586473120443 := by
  unfold tailWord_420590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917522193285216987293403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10226785030854490598898149 1917522193285216987293403)
  ·
    refine ⟨2876283289927825480940105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1917522193285216987293403 2876283289927825480940105)
    ·
      refine ⟨2157212467445869110705079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2876283289927825480940105 2157212467445869110705079)
      ·
        refine ⟨3235818701168803666057619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2157212467445869110705079 3235818701168803666057619)
        ·
          refine ⟨4853728051753205499086429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235818701168803666057619 4853728051753205499086429)
          ·
            refine ⟨1820148019407452062157411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4853728051753205499086429 1820148019407452062157411)
            ·
              refine ⟨2730222029111178093236117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820148019407452062157411 2730222029111178093236117)
              ·
                refine ⟨127979157614586473120443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2730222029111178093236117 127979157614586473120443)
                ·
                  rfl

theorem cell19_420590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_420590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420590 prefixEnd_420590 := by exact prefixLift 420590
  have htrace : WordTrace (prefixWord ++ tailWord_420590) baseStart_420590 baseEnd_420590 := by
    simpa [prefixWord, tailWord_420590, baseEnd_420590] using wordTrace_append hprefix tailTrace_420590
  have hstable : (prefixWord ++ tailWord_420590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420590).length < 2 ^ (prefixWord ++ tailWord_420590).sum := by decide
  have hdescent : baseEnd_420590 < baseStart_420590 := by decide
  rcases family_descends (prefixWord ++ tailWord_420590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420626 : List Nat := [3, 2, 4, 1, 2, 7]
def baseStart_420626 : Nat := 118140960795 + 420626 * 2 ^ 59
def prefixEnd_420626 : Nat := 4983230072969 + 3 ^ 40 * 420626 * 2
def baseEnd_420626 : Nat := 14221123540949895146705

theorem tailTrace_420626 : CollatzResearch.WordTrace tailWord_420626 prefixEnd_420626 14221123540949895146705 := by
  unfold tailWord_420626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835372643537828511664433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10227660382767542697771821 3835372643537828511664433)
  ·
    refine ⟨2876529482653371383748325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3835372643537828511664433 2876529482653371383748325)
    ·
      refine ⟨539349277997507134452811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2876529482653371383748325 539349277997507134452811)
      ·
        refine ⟨809023916996260701679217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539349277997507134452811 809023916996260701679217)
        ·
          refine ⟨606767937747195526259413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809023916996260701679217 606767937747195526259413)
          ·
            refine ⟨14221123540949895146705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 606767937747195526259413 14221123540949895146705)
            ·
              rfl

theorem cell19_420626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_420626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420626 prefixEnd_420626 := by exact prefixLift 420626
  have htrace : WordTrace (prefixWord ++ tailWord_420626) baseStart_420626 baseEnd_420626 := by
    simpa [prefixWord, tailWord_420626, baseEnd_420626] using wordTrace_append hprefix tailTrace_420626
  have hstable : (prefixWord ++ tailWord_420626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420626).length < 2 ^ (prefixWord ++ tailWord_420626).sum := by decide
  have hdescent : baseEnd_420626 < baseStart_420626 := by decide
  rcases family_descends (prefixWord ++ tailWord_420626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420721 : List Nat := [1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_420721 : Nat := 118140960795 + 420721 * 2 ^ 59
def prefixEnd_420721 : Nat := 4983230072969 + 3 ^ 40 * 420721 * 2
def baseEnd_420721 : Nat := 128019018927616984208975

theorem tailTrace_420721 : CollatzResearch.WordTrace tailWord_420721 prefixEnd_420721 128019018927616984208975 := by
  unfold tailWord_420721
  simp only [CollatzResearch.WordTrace]
  refine ⟨15344955508807145271366017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10229970339204763514244011 15344955508807145271366017)
  ·
    refine ⟨11508716631605358953524513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15344955508807145271366017 11508716631605358953524513)
    ·
      refine ⟨8631537473704019215143385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11508716631605358953524513 8631537473704019215143385)
      ·
        refine ⟨6473653105278014411357539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631537473704019215143385 6473653105278014411357539)
        ·
          refine ⟨9710479657917021617036309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473653105278014411357539 9710479657917021617036309)
          ·
            refine ⟨455178733964860388298577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9710479657917021617036309 455178733964860388298577)
            ·
              refine ⟨341384050473645291223933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455178733964860388298577 341384050473645291223933)
              ·
                refine ⟨128019018927616984208975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341384050473645291223933 128019018927616984208975)
                ·
                  rfl

theorem cell19_420721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_420721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420721 prefixEnd_420721 := by exact prefixLift 420721
  have htrace : WordTrace (prefixWord ++ tailWord_420721) baseStart_420721 baseEnd_420721 := by
    simpa [prefixWord, tailWord_420721, baseEnd_420721] using wordTrace_append hprefix tailTrace_420721
  have hstable : (prefixWord ++ tailWord_420721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420721).length < 2 ^ (prefixWord ++ tailWord_420721).sum := by decide
  have hdescent : baseEnd_420721 < baseStart_420721 := by decide
  rcases family_descends (prefixWord ++ tailWord_420721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420723 : List Nat := [1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_420723 : Nat := 118140960795 + 420723 * 2 ^ 59
def prefixEnd_420723 : Nat := 4983230072969 + 3 ^ 40 * 420723 * 2
def baseEnd_420723 : Nat := 128019627497281572164525

theorem tailTrace_420723 : CollatzResearch.WordTrace tailWord_420723 prefixEnd_420723 128019627497281572164525 := by
  unfold tailWord_420723
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345028454799899612938823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10230018969866599741959215 15345028454799899612938823)
  ·
    refine ⟨23017542682199849419408235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15345028454799899612938823 23017542682199849419408235)
    ·
      refine ⟨34526314023299774129112353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23017542682199849419408235 34526314023299774129112353)
      ·
        refine ⟨25894735517474830596834265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34526314023299774129112353 25894735517474830596834265)
        ·
          refine ⟨19421051638106122947625699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25894735517474830596834265 19421051638106122947625699)
          ·
            refine ⟨29131577457159184421438549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19421051638106122947625699 29131577457159184421438549)
            ·
              refine ⟨341385673326084192438733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 29131577457159184421438549 341385673326084192438733)
              ·
                refine ⟨128019627497281572164525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341385673326084192438733 128019627497281572164525)
                ·
                  rfl

theorem cell19_420723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_420723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420723 prefixEnd_420723 := by exact prefixLift 420723
  have htrace : WordTrace (prefixWord ++ tailWord_420723) baseStart_420723 baseEnd_420723 := by
    simpa [prefixWord, tailWord_420723, baseEnd_420723] using wordTrace_append hprefix tailTrace_420723
  have hstable : (prefixWord ++ tailWord_420723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420723).length < 2 ^ (prefixWord ++ tailWord_420723).sum := by decide
  have hdescent : baseEnd_420723 < baseStart_420723 := by decide
  rcases family_descends (prefixWord ++ tailWord_420723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420968 : List Nat := [2, 1, 4, 4, 2, 6]
def baseStart_420968 : Nat := 118140960795 + 420968 * 2 ^ 59
def prefixEnd_420968 : Nat := 4983230072969 + 3 ^ 40 * 420968 * 2
def baseEnd_420968 : Nat := 14232686364577066302157

theorem tailTrace_420968 : CollatzResearch.WordTrace tailWord_420968 prefixEnd_420968 14232686364577066302157 := by
  unfold tailWord_420968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676982169456153227803779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10235976225941537637071705 7676982169456153227803779)
  ·
    refine ⟨11515473254184229841705669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7676982169456153227803779 11515473254184229841705669)
    ·
      refine ⟨2159151235159543095319813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11515473254184229841705669 2159151235159543095319813)
      ·
        refine ⟨404840856592414330372465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2159151235159543095319813 404840856592414330372465)
        ·
          refine ⟨303630642444310747779349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404840856592414330372465 303630642444310747779349)
          ·
            refine ⟨14232686364577066302157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 303630642444310747779349 14232686364577066302157)
            ·
              rfl

theorem cell19_420968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_420968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_420968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_420968 prefixEnd_420968 := by exact prefixLift 420968
  have htrace : WordTrace (prefixWord ++ tailWord_420968) baseStart_420968 baseEnd_420968 := by
    simpa [prefixWord, tailWord_420968, baseEnd_420968] using wordTrace_append hprefix tailTrace_420968
  have hstable : (prefixWord ++ tailWord_420968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420968).length < 2 ^ (prefixWord ++ tailWord_420968).sum := by decide
  have hdescent : baseEnd_420968 < baseStart_420968 := by decide
  rcases family_descends (prefixWord ++ tailWord_420968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421006 : List Nat := [4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_421006 : Nat := 118140960795 + 421006 * 2 ^ 59
def prefixEnd_421006 : Nat := 4983230072969 + 3 ^ 40 * 421006 * 2
def baseEnd_421006 : Nat := 128105740104820767874865

theorem tailTrace_421006 : CollatzResearch.WordTrace tailWord_421006 prefixEnd_421006 128105740104820767874865 := by
  unfold tailWord_421006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919418789096829868186359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10236900208516425963660581 1919418789096829868186359)
  ·
    refine ⟨2879128183645244802279539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1919418789096829868186359 2879128183645244802279539)
    ·
      refine ⟨4318692275467867203419309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879128183645244802279539 4318692275467867203419309)
      ·
        refine ⟨1619509603300450201282241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4318692275467867203419309 1619509603300450201282241)
        ·
          refine ⟨1214632202475337650961681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619509603300450201282241 1214632202475337650961681)
          ·
            refine ⟨910974151856503238221261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214632202475337650961681 910974151856503238221261)
            ·
              refine ⟨341615306946188714332973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 910974151856503238221261 341615306946188714332973)
              ·
                refine ⟨128105740104820767874865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341615306946188714332973 128105740104820767874865)
                ·
                  rfl

theorem cell19_421006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_421006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421006 prefixEnd_421006 := by exact prefixLift 421006
  have htrace : WordTrace (prefixWord ++ tailWord_421006) baseStart_421006 baseEnd_421006 := by
    simpa [prefixWord, tailWord_421006, baseEnd_421006] using wordTrace_append hprefix tailTrace_421006
  have hstable : (prefixWord ++ tailWord_421006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421006).length < 2 ^ (prefixWord ++ tailWord_421006).sum := by decide
  have hdescent : baseEnd_421006 < baseStart_421006 := by decide
  rcases family_descends (prefixWord ++ tailWord_421006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421029 : List Nat := [1, 3, 1, 2, 1, 5, 6]
def baseStart_421029 : Nat := 118140960795 + 421029 * 2 ^ 59
def prefixEnd_421029 : Nat := 4983230072969 + 3 ^ 40 * 421029 * 2
def baseEnd_421029 : Nat := 42704246218654509787897

theorem tailTrace_421029 : CollatzResearch.WordTrace tailWord_421029 prefixEnd_421029 42704246218654509787897 := by
  unfold tailWord_421029
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356189191691313873578141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10237459461127542582385427 15356189191691313873578141)
  ·
    refine ⟨5758570946884242702591803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15356189191691313873578141 5758570946884242702591803)
    ·
      refine ⟨8637856420326364053887705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758570946884242702591803 8637856420326364053887705)
      ·
        refine ⟨6478392315244773040415779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637856420326364053887705 6478392315244773040415779)
        ·
          refine ⟨9717588472867159560623669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478392315244773040415779 9717588472867159560623669)
          ·
            refine ⟨911023919331296208808469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9717588472867159560623669 911023919331296208808469)
            ·
              refine ⟨42704246218654509787897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 911023919331296208808469 42704246218654509787897)
              ·
                rfl

theorem cell19_421029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_421029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421029 prefixEnd_421029 := by exact prefixLift 421029
  have htrace : WordTrace (prefixWord ++ tailWord_421029) baseStart_421029 baseEnd_421029 := by
    simpa [prefixWord, tailWord_421029, baseEnd_421029] using wordTrace_append hprefix tailTrace_421029
  have hstable : (prefixWord ++ tailWord_421029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421029).length < 2 ^ (prefixWord ++ tailWord_421029).sum := by decide
  have hdescent : baseEnd_421029 < baseStart_421029 := by decide
  rcases family_descends (prefixWord ++ tailWord_421029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421103 : List Nat := [1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_421103 : Nat := 118140960795 + 421103 * 2 ^ 59
def prefixEnd_421103 : Nat := 4983230072969 + 3 ^ 40 * 421103 * 2
def baseEnd_421103 : Nat := 128135255733553283719045

theorem tailTrace_421103 : CollatzResearch.WordTrace tailWord_421103 prefixEnd_421103 128135255733553283719045 := by
  unfold tailWord_421103
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358888193423224511771963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10239258795615483007847975 15358888193423224511771963)
  ·
    refine ⟨23038332290134836767657945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15358888193423224511771963 23038332290134836767657945)
    ·
      refine ⟨17278749217601127575743459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23038332290134836767657945 17278749217601127575743459)
      ·
        refine ⟨25918123826401691363615189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17278749217601127575743459 25918123826401691363615189)
        ·
          refine ⟨607456027181289641334731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25918123826401691363615189 607456027181289641334731)
          ·
            refine ⟨911184040771934462002097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607456027181289641334731 911184040771934462002097)
            ·
              refine ⟨683388030578950846501573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911184040771934462002097 683388030578950846501573)
              ·
                refine ⟨128135255733553283719045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683388030578950846501573 128135255733553283719045)
                ·
                  rfl

theorem cell19_421103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_421103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421103 prefixEnd_421103 := by exact prefixLift 421103
  have htrace : WordTrace (prefixWord ++ tailWord_421103) baseStart_421103 baseEnd_421103 := by
    simpa [prefixWord, tailWord_421103, baseEnd_421103] using wordTrace_append hprefix tailTrace_421103
  have hstable : (prefixWord ++ tailWord_421103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421103).length < 2 ^ (prefixWord ++ tailWord_421103).sum := by decide
  have hdescent : baseEnd_421103 < baseStart_421103 := by decide
  rcases family_descends (prefixWord ++ tailWord_421103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421160 : List Nat := [2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_421160 : Nat := 118140960795 + 421160 * 2 ^ 59
def prefixEnd_421160 : Nat := 4983230072969 + 3 ^ 40 * 421160 * 2
def baseEnd_421160 : Nat := 128152599968994040452223

theorem tailTrace_421160 : CollatzResearch.WordTrace tailWord_421160 prefixEnd_421160 128152599968994040452223 := by
  unfold tailWord_421160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680483577108361623298467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10240644769477815497731289 7680483577108361623298467)
  ·
    refine ⟨11520725365662542434947701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680483577108361623298467 11520725365662542434947701)
    ·
      refine ⟨1080068003030863353276347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11520725365662542434947701 1080068003030863353276347)
      ·
        refine ⟨1620102004546295029914521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080068003030863353276347 1620102004546295029914521)
        ·
          refine ⟨1215076503409721272435891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620102004546295029914521 1215076503409721272435891)
          ·
            refine ⟨1822614755114581908653837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215076503409721272435891 1822614755114581908653837)
            ·
              refine ⟨683480533167968215745189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822614755114581908653837 683480533167968215745189)
              ·
                refine ⟨128152599968994040452223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683480533167968215745189 128152599968994040452223)
                ·
                  rfl

theorem cell19_421160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_421160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421160 prefixEnd_421160 := by exact prefixLift 421160
  have htrace : WordTrace (prefixWord ++ tailWord_421160) baseStart_421160 baseEnd_421160 := by
    simpa [prefixWord, tailWord_421160, baseEnd_421160] using wordTrace_append hprefix tailTrace_421160
  have hstable : (prefixWord ++ tailWord_421160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421160).length < 2 ^ (prefixWord ++ tailWord_421160).sum := by decide
  have hdescent : baseEnd_421160 < baseStart_421160 := by decide
  rcases family_descends (prefixWord ++ tailWord_421160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421177 : List Nat := [1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_421177 : Nat := 118140960795 + 421177 * 2 ^ 59
def prefixEnd_421177 : Nat := 4983230072969 + 3 ^ 40 * 421177 * 2
def baseEnd_421177 : Nat := 128157772811143038074399

theorem tailTrace_421177 : CollatzResearch.WordTrace tailWord_421177 prefixEnd_421177 128157772811143038074399 := by
  unfold tailWord_421177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15361587195155135149965785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10241058130103423433310523 15361587195155135149965785)
  ·
    refine ⟨11521190396366351362474339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15361587195155135149965785 11521190396366351362474339)
    ·
      refine ⟨17281785594549527043711509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521190396366351362474339 17281785594549527043711509)
      ·
        refine ⟨810083699744509080173977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17281785594549527043711509 810083699744509080173977)
        ·
          refine ⟨607562774808381810130483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810083699744509080173977 607562774808381810130483)
          ·
            refine ⟨911344162212572715195725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607562774808381810130483 911344162212572715195725)
            ·
              refine ⟨341754060829714768198397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911344162212572715195725 341754060829714768198397)
              ·
                refine ⟨128157772811143038074399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341754060829714768198397 128157772811143038074399)
                ·
                  rfl

theorem cell19_421177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_421177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421177 prefixEnd_421177 := by exact prefixLift 421177
  have htrace : WordTrace (prefixWord ++ tailWord_421177) baseStart_421177 baseEnd_421177 := by
    simpa [prefixWord, tailWord_421177, baseEnd_421177] using wordTrace_append hprefix tailTrace_421177
  have hstable : (prefixWord ++ tailWord_421177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421177).length < 2 ^ (prefixWord ++ tailWord_421177).sum := by decide
  have hdescent : baseEnd_421177 < baseStart_421177 := by decide
  rcases family_descends (prefixWord ++ tailWord_421177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421230 : List Nat := [4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_421230 : Nat := 118140960795 + 421230 * 2 ^ 59
def prefixEnd_421230 : Nat := 4983230072969 + 3 ^ 40 * 421230 * 2
def baseEnd_421230 : Nat := 128173899907254618896477

theorem tailTrace_421230 : CollatzResearch.WordTrace tailWord_421230 prefixEnd_421230 128173899907254618896477 := by
  unfold tailWord_421230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920440032995390650205643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10242346842642083467763429 1920440032995390650205643)
  ·
    refine ⟨2880660049493085975308465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1920440032995390650205643 2880660049493085975308465)
    ·
      refine ⟨2160495037119814481481349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880660049493085975308465 2160495037119814481481349)
      ·
        refine ⟨405092819459965215277753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2160495037119814481481349 405092819459965215277753)
        ·
          refine ⟨303819614594973911458315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405092819459965215277753 303819614594973911458315)
          ·
            refine ⟨455729421892460867187473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303819614594973911458315 455729421892460867187473)
            ·
              refine ⟨341797066419345650390605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455729421892460867187473 341797066419345650390605)
              ·
                refine ⟨128173899907254618896477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341797066419345650390605 128173899907254618896477)
                ·
                  rfl

theorem cell19_421230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_421230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421230 prefixEnd_421230 := by exact prefixLift 421230
  have htrace : WordTrace (prefixWord ++ tailWord_421230) baseStart_421230 baseEnd_421230 := by
    simpa [prefixWord, tailWord_421230, baseEnd_421230] using wordTrace_append hprefix tailTrace_421230
  have hstable : (prefixWord ++ tailWord_421230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421230).length < 2 ^ (prefixWord ++ tailWord_421230).sum := by decide
  have hdescent : baseEnd_421230 < baseStart_421230 := by decide
  rcases family_descends (prefixWord ++ tailWord_421230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421293 : List Nat := [1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_421293 : Nat := 118140960795 + 421293 * 2 ^ 59
def prefixEnd_421293 : Nat := 4983230072969 + 3 ^ 40 * 421293 * 2
def baseEnd_421293 : Nat := 128193069851689139496305

theorem tailTrace_421293 : CollatzResearch.WordTrace tailWord_421293 prefixEnd_421293 128193069851689139496305 := by
  unfold tailWord_421293
  simp only [CollatzResearch.WordTrace]
  refine ⟨15365818062734886961188533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10243878708489924640792355 15365818062734886961188533)
  ·
    refine ⟨1440545443381395652611425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15365818062734886961188533 1440545443381395652611425)
    ·
      refine ⟨1080409082536046739458569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440545443381395652611425 1080409082536046739458569)
      ·
        refine ⟨810306811902035054593927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080409082536046739458569 810306811902035054593927)
        ·
          refine ⟨1215460217853052581890891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810306811902035054593927 1215460217853052581890891)
          ·
            refine ⟨1823190326779578872836337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215460217853052581890891 1823190326779578872836337)
            ·
              refine ⟨1367392745084684154627253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823190326779578872836337 1367392745084684154627253)
              ·
                refine ⟨128193069851689139496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367392745084684154627253 128193069851689139496305)
                ·
                  rfl

theorem cell19_421293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_421293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421293 prefixEnd_421293 := by exact prefixLift 421293
  have htrace : WordTrace (prefixWord ++ tailWord_421293) baseStart_421293 baseEnd_421293 := by
    simpa [prefixWord, tailWord_421293, baseEnd_421293] using wordTrace_append hprefix tailTrace_421293
  have hstable : (prefixWord ++ tailWord_421293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421293).length < 2 ^ (prefixWord ++ tailWord_421293).sum := by decide
  have hdescent : baseEnd_421293 < baseStart_421293 := by decide
  rcases family_descends (prefixWord ++ tailWord_421293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421409 : List Nat := [1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_421409 : Nat := 118140960795 + 421409 * 2 ^ 59
def prefixEnd_421409 : Nat := 4983230072969 + 3 ^ 40 * 421409 * 2
def baseEnd_421409 : Nat := 128228366892235240918211

theorem tailTrace_421409 : CollatzResearch.WordTrace tailWord_421409 prefixEnd_421409 128228366892235240918211 := by
  unfold tailWord_421409
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370048930314638772411281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10246699286876425848274187 15370048930314638772411281)
  ·
    refine ⟨11527536697735979079308461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15370048930314638772411281 11527536697735979079308461)
    ·
      refine ⟨4322826261650992154740673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11527536697735979079308461 4322826261650992154740673)
      ·
        refine ⟨3242119696238244116055505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4322826261650992154740673 3242119696238244116055505)
        ·
          refine ⟨2431589772178683087041629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242119696238244116055505 2431589772178683087041629)
          ·
            refine ⟨911846164567006157640611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431589772178683087041629 911846164567006157640611)
            ·
              refine ⟨1367769246850509236460917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911846164567006157640611 1367769246850509236460917)
              ·
                refine ⟨128228366892235240918211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367769246850509236460917 128228366892235240918211)
                ·
                  rfl

theorem cell19_421409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_421409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421409 prefixEnd_421409 := by exact prefixLift 421409
  have htrace : WordTrace (prefixWord ++ tailWord_421409) baseStart_421409 baseEnd_421409 := by
    simpa [prefixWord, tailWord_421409, baseEnd_421409] using wordTrace_append hprefix tailTrace_421409
  have hstable : (prefixWord ++ tailWord_421409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421409).length < 2 ^ (prefixWord ++ tailWord_421409).sum := by decide
  have hdescent : baseEnd_421409 < baseStart_421409 := by decide
  rcases family_descends (prefixWord ++ tailWord_421409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421485 : List Nat := [1, 5, 1, 1, 4, 7]
def baseStart_421485 : Nat := 118140960795 + 421485 * 2 ^ 59
def prefixEnd_421485 : Nat := 4983230072969 + 3 ^ 40 * 421485 * 2
def baseEnd_421485 : Nat := 14250165837721064803235

theorem tailTrace_421485 : CollatzResearch.WordTrace tailWord_421485 prefixEnd_421485 14250165837721064803235 := by
  unfold tailWord_421485
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372820878039303752177909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10248547252026202501451939 15372820878039303752177909)
  ·
    refine ⟨1441201957316184726766679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15372820878039303752177909 1441201957316184726766679)
    ·
      refine ⟨2161802935974277090150019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441201957316184726766679 2161802935974277090150019)
      ·
        refine ⟨3242704403961415635225029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161802935974277090150019 3242704403961415635225029)
        ·
          refine ⟨608007075742765431604693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3242704403961415635225029 608007075742765431604693)
          ·
            refine ⟨14250165837721064803235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 608007075742765431604693 14250165837721064803235)
            ·
              rfl

theorem cell19_421485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_421485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421485 prefixEnd_421485 := by exact prefixLift 421485
  have htrace : WordTrace (prefixWord ++ tailWord_421485) baseStart_421485 baseEnd_421485 := by
    simpa [prefixWord, tailWord_421485, baseEnd_421485] using wordTrace_append hprefix tailTrace_421485
  have hstable : (prefixWord ++ tailWord_421485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421485).length < 2 ^ (prefixWord ++ tailWord_421485).sum := by decide
  have hdescent : baseEnd_421485 < baseStart_421485 := by decide
  rcases family_descends (prefixWord ++ tailWord_421485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421525 : List Nat := [1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_421525 : Nat := 118140960795 + 421525 * 2 ^ 59
def prefixEnd_421525 : Nat := 4983230072969 + 3 ^ 40 * 421525 * 2
def baseEnd_421525 : Nat := 128263663932781342340117

theorem tailTrace_421525 : CollatzResearch.WordTrace tailWord_421525 prefixEnd_421525 128263663932781342340117 := by
  unfold tailWord_421525
  simp only [CollatzResearch.WordTrace]
  refine ⟨15374279797894390583634029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10249519865262927055756019 15374279797894390583634029)
  ·
    refine ⟨5765354924210396468862761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15374279797894390583634029 5765354924210396468862761)
    ·
      refine ⟨4324016193157797351647071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5765354924210396468862761 4324016193157797351647071)
      ·
        refine ⟨6486024289736696027470607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4324016193157797351647071 6486024289736696027470607)
        ·
          refine ⟨9729036434605044041205911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486024289736696027470607 9729036434605044041205911)
          ·
            refine ⟨14593554651907566061808867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729036434605044041205911 14593554651907566061808867)
            ·
              refine ⟨21890331977861349092713301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593554651907566061808867 21890331977861349092713301)
              ·
                refine ⟨128263663932781342340117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21890331977861349092713301 128263663932781342340117)
                ·
                  rfl

theorem cell19_421525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_421525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421525 prefixEnd_421525 := by exact prefixLift 421525
  have htrace : WordTrace (prefixWord ++ tailWord_421525) baseStart_421525 baseEnd_421525 := by
    simpa [prefixWord, tailWord_421525, baseEnd_421525] using wordTrace_append hprefix tailTrace_421525
  have hstable : (prefixWord ++ tailWord_421525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421525).length < 2 ^ (prefixWord ++ tailWord_421525).sum := by decide
  have hdescent : baseEnd_421525 < baseStart_421525 := by decide
  rcases family_descends (prefixWord ++ tailWord_421525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421570 : List Nat := [3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_421570 : Nat := 118140960795 + 421570 * 2 ^ 59
def prefixEnd_421570 : Nat := 4983230072969 + 3 ^ 40 * 421570 * 2
def baseEnd_421570 : Nat := 128277356750234571339995

theorem tailTrace_421570 : CollatzResearch.WordTrace tailWord_421570 prefixEnd_421570 128277356750234571339995 := by
  unfold tailWord_421570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843980270682840817255541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10250614055154242179348109 3843980270682840817255541)
  ·
    refine ⟨360373150376516326617707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3843980270682840817255541 360373150376516326617707)
    ·
      refine ⟨540559725564774489926561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360373150376516326617707 540559725564774489926561)
      ·
        refine ⟨405419794173580867444921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540559725564774489926561 405419794173580867444921)
        ·
          refine ⟨304064845630185650583691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405419794173580867444921 304064845630185650583691)
          ·
            refine ⟨456097268445278475875537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304064845630185650583691 456097268445278475875537)
            ·
              refine ⟨342072951333958856906653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456097268445278475875537 342072951333958856906653)
              ·
                refine ⟨128277356750234571339995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342072951333958856906653 128277356750234571339995)
                ·
                  rfl

theorem cell19_421570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_421570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421570 prefixEnd_421570 := by exact prefixLift 421570
  have htrace : WordTrace (prefixWord ++ tailWord_421570) baseStart_421570 baseEnd_421570 := by
    simpa [prefixWord, tailWord_421570, baseEnd_421570] using wordTrace_append hprefix tailTrace_421570
  have hstable : (prefixWord ++ tailWord_421570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421570).length < 2 ^ (prefixWord ++ tailWord_421570).sum := by decide
  have hdescent : baseEnd_421570 < baseStart_421570 := by decide
  rcases family_descends (prefixWord ++ tailWord_421570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421574 : List Nat := [6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_421574 : Nat := 118140960795 + 421574 * 2 ^ 59
def prefixEnd_421574 : Nat := 4983230072969 + 3 ^ 40 * 421574 * 2
def baseEnd_421574 : Nat := 128278573889563747251095

theorem tailTrace_421574 : CollatzResearch.WordTrace tailWord_421574 prefixEnd_421574 128278573889563747251095 := by
  unfold tailWord_421574
  simp only [CollatzResearch.WordTrace]
  refine ⟨480502092959902248505243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10250711316477914634778517 480502092959902248505243)
  ·
    refine ⟨720753139439853372757865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 480502092959902248505243 720753139439853372757865)
    ·
      refine ⟨540564854579890029568399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 720753139439853372757865 540564854579890029568399)
      ·
        refine ⟨810847281869835044352599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540564854579890029568399 810847281869835044352599)
        ·
          refine ⟨1216270922804752566528899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810847281869835044352599 1216270922804752566528899)
          ·
            refine ⟨1824406384207128849793349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216270922804752566528899 1824406384207128849793349)
            ·
              refine ⟨342076197038836659336253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1824406384207128849793349 342076197038836659336253)
              ·
                refine ⟨128278573889563747251095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342076197038836659336253 128278573889563747251095)
                ·
                  rfl

theorem cell19_421574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_421574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421574 prefixEnd_421574 := by exact prefixLift 421574
  have htrace : WordTrace (prefixWord ++ tailWord_421574) baseStart_421574 baseEnd_421574 := by
    simpa [prefixWord, tailWord_421574, baseEnd_421574] using wordTrace_append hprefix tailTrace_421574
  have hstable : (prefixWord ++ tailWord_421574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421574).length < 2 ^ (prefixWord ++ tailWord_421574).sum := by decide
  have hdescent : baseEnd_421574 < baseStart_421574 := by decide
  rcases family_descends (prefixWord ++ tailWord_421574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421618 : List Nat := [3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_421618 : Nat := 118140960795 + 421618 * 2 ^ 59
def prefixEnd_421618 : Nat := 4983230072969 + 3 ^ 40 * 421618 * 2
def baseEnd_421618 : Nat := 128291962422184682273197

theorem tailTrace_421618 : CollatzResearch.WordTrace tailWord_421618 prefixEnd_421618 128291962422184682273197 := by
  unfold tailWord_421618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844417946639366866692377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10251781191038311644513005 3844417946639366866692377)
  ·
    refine ⟨2883313459979525150019283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3844417946639366866692377 2883313459979525150019283)
    ·
      refine ⟨4324970189969287725028925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883313459979525150019283 4324970189969287725028925)
      ·
        refine ⟨1621863821238482896885847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4324970189969287725028925 1621863821238482896885847)
        ·
          refine ⟨2432795731857724345328771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621863821238482896885847 2432795731857724345328771)
          ·
            refine ⟨3649193597786586517993157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432795731857724345328771 3649193597786586517993157)
            ·
              refine ⟨684223799584984972123717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3649193597786586517993157 684223799584984972123717)
              ·
                refine ⟨128291962422184682273197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684223799584984972123717 128291962422184682273197)
                ·
                  rfl

theorem cell19_421618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_421618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421618 prefixEnd_421618 := by exact prefixLift 421618
  have htrace : WordTrace (prefixWord ++ tailWord_421618) baseStart_421618 baseEnd_421618 := by
    simpa [prefixWord, tailWord_421618, baseEnd_421618] using wordTrace_append hprefix tailTrace_421618
  have hstable : (prefixWord ++ tailWord_421618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421618).length < 2 ^ (prefixWord ++ tailWord_421618).sum := by decide
  have hdescent : baseEnd_421618 < baseStart_421618 := by decide
  rcases family_descends (prefixWord ++ tailWord_421618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421652 : List Nat := [2, 4, 4, 1, 1, 7]
def baseStart_421652 : Nat := 118140960795 + 421652 * 2 ^ 59
def prefixEnd_421652 : Nat := 4983230072969 + 3 ^ 40 * 421652 * 2
def baseEnd_421652 : Nat := 14255812011831408613061

theorem tailTrace_421652 : CollatzResearch.WordTrace tailWord_421652 prefixEnd_421652 14255812011831408613061 := by
  unfold tailWord_421652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689455934217145636753605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10252607912289527515671473 7689455934217145636753605)
  ·
    refine ⟨1441772987665714806891301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7689455934217145636753605 1441772987665714806891301)
    ·
      refine ⟨270332435187321526292119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1441772987665714806891301 270332435187321526292119)
      ·
        refine ⟨405498652780982289438179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270332435187321526292119 405498652780982289438179)
        ·
          refine ⟨608247979171473434157269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405498652780982289438179 608247979171473434157269)
          ·
            refine ⟨14255812011831408613061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 608247979171473434157269 14255812011831408613061)
            ·
              rfl

theorem cell19_421652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_421652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421652 prefixEnd_421652 := by exact prefixLift 421652
  have htrace : WordTrace (prefixWord ++ tailWord_421652) baseStart_421652 baseEnd_421652 := by
    simpa [prefixWord, tailWord_421652, baseEnd_421652] using wordTrace_append hprefix tailTrace_421652
  have hstable : (prefixWord ++ tailWord_421652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421652).length < 2 ^ (prefixWord ++ tailWord_421652).sum := by decide
  have hdescent : baseEnd_421652 < baseStart_421652 := by decide
  rcases family_descends (prefixWord ++ tailWord_421652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421658 : List Nat := [3, 1, 1, 3, 2, 9]
def baseStart_421658 : Nat := 118140960795 + 421658 * 2 ^ 59
def prefixEnd_421658 : Nat := 4983230072969 + 3 ^ 40 * 421658 * 2
def baseEnd_421658 : Nat := 14256014868386271264911

theorem tailTrace_421658 : CollatzResearch.WordTrace tailWord_421658 prefixEnd_421658 14256014868386271264911 := by
  unfold tailWord_421658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844782676603138574556407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10252753804275036198817085 3844782676603138574556407)
  ·
    refine ⟨5767174014904707861834611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3844782676603138574556407 5767174014904707861834611)
    ·
      refine ⟨8650761022357061792751917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5767174014904707861834611 8650761022357061792751917)
      ·
        refine ⟨3244035383383898172281969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8650761022357061792751917 3244035383383898172281969)
        ·
          refine ⟨2433026537537923629211477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244035383383898172281969 2433026537537923629211477)
          ·
            refine ⟨14256014868386271264911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2433026537537923629211477 14256014868386271264911)
            ·
              rfl

theorem cell19_421658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_421658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421658 prefixEnd_421658 := by exact prefixLift 421658
  have htrace : WordTrace (prefixWord ++ tailWord_421658) baseStart_421658 baseEnd_421658 := by
    simpa [prefixWord, tailWord_421658, baseEnd_421658] using wordTrace_append hprefix tailTrace_421658
  have hstable : (prefixWord ++ tailWord_421658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421658).length < 2 ^ (prefixWord ++ tailWord_421658).sum := by decide
  have hdescent : baseEnd_421658 < baseStart_421658 := by decide
  rcases family_descends (prefixWord ++ tailWord_421658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421753 : List Nat := [1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_421753 : Nat := 118140960795 + 421753 * 2 ^ 59
def prefixEnd_421753 : Nat := 4983230072969 + 3 ^ 40 * 421753 * 2
def baseEnd_421753 : Nat := 128333040874544369272829

theorem tailTrace_421753 : CollatzResearch.WordTrace tailWord_421753 prefixEnd_421753 128333040874544369272829 := by
  unfold tailWord_421753
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382595641068385522933913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10255063760712257015289275 15382595641068385522933913)
  ·
    refine ⟨11536946730801289142200435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15382595641068385522933913 11536946730801289142200435)
    ·
      refine ⟨17305420096201933713300653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536946730801289142200435 17305420096201933713300653)
      ·
        refine ⟨6489532536075725142487745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17305420096201933713300653 6489532536075725142487745)
        ·
          refine ⟨4867149402056793856865809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6489532536075725142487745 4867149402056793856865809)
          ·
            refine ⟨3650362051542595392649357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867149402056793856865809 3650362051542595392649357)
            ·
              refine ⟨1368885769328473272243509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3650362051542595392649357 1368885769328473272243509)
              ·
                refine ⟨128333040874544369272829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1368885769328473272243509 128333040874544369272829)
                ·
                  rfl

theorem cell19_421753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_421753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421753 prefixEnd_421753 := by exact prefixLift 421753
  have htrace : WordTrace (prefixWord ++ tailWord_421753) baseStart_421753 baseEnd_421753 := by
    simpa [prefixWord, tailWord_421753, baseEnd_421753] using wordTrace_append hprefix tailTrace_421753
  have hstable : (prefixWord ++ tailWord_421753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421753).length < 2 ^ (prefixWord ++ tailWord_421753).sum := by decide
  have hdescent : baseEnd_421753 < baseStart_421753 := by decide
  rcases family_descends (prefixWord ++ tailWord_421753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421768 : List Nat := [2, 1, 3, 3, 4, 1, 5]
def baseStart_421768 : Nat := 118140960795 + 421768 * 2 ^ 59
def prefixEnd_421768 : Nat := 4983230072969 + 3 ^ 40 * 421768 * 2
def baseEnd_421768 : Nat := 42779201715676259646485

theorem tailTrace_421768 : CollatzResearch.WordTrace tailWord_421768 prefixEnd_421768 42779201715676259646485 := by
  unfold tailWord_421768
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691571368007021542364979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10255428490676028723153305 7691571368007021542364979)
  ·
    refine ⟨11537357052010532313547469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7691571368007021542364979 11537357052010532313547469)
    ·
      refine ⟨4326508894503949617580301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11537357052010532313547469 4326508894503949617580301)
      ·
        refine ⟨1622440835438981106592613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4326508894503949617580301 1622440835438981106592613)
        ·
          refine ⟨304207656644808957486115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1622440835438981106592613 304207656644808957486115)
          ·
            refine ⟨456311484967213436229173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304207656644808957486115 456311484967213436229173)
            ·
              refine ⟨42779201715676259646485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456311484967213436229173 42779201715676259646485)
              ·
                rfl

theorem cell19_421768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_421768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421768 prefixEnd_421768 := by exact prefixLift 421768
  have htrace : WordTrace (prefixWord ++ tailWord_421768) baseStart_421768 baseEnd_421768 := by
    simpa [prefixWord, tailWord_421768, baseEnd_421768] using wordTrace_append hprefix tailTrace_421768
  have hstable : (prefixWord ++ tailWord_421768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421768).length < 2 ^ (prefixWord ++ tailWord_421768).sum := by decide
  have hdescent : baseEnd_421768 < baseStart_421768 := by decide
  rcases family_descends (prefixWord ++ tailWord_421768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421789 : List Nat := [1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_421789 : Nat := 118140960795 + 421789 * 2 ^ 59
def prefixEnd_421789 : Nat := 4983230072969 + 3 ^ 40 * 421789 * 2
def baseEnd_421789 : Nat := 128343995128506952472731

theorem tailTrace_421789 : CollatzResearch.WordTrace tailWord_421789 prefixEnd_421789 128343995128506952472731 := by
  unfold tailWord_421789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383908668937963671244421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10255939112625309114162947 15383908668937963671244421)
  ·
    refine ⟨2884482875425868188358329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15383908668937963671244421 2884482875425868188358329)
    ·
      refine ⟨2163362156569401141268747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884482875425868188358329 2163362156569401141268747)
      ·
        refine ⟨3245043234854101711903121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163362156569401141268747 3245043234854101711903121)
        ·
          refine ⟨2433782426140576283927341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3245043234854101711903121 2433782426140576283927341)
          ·
            refine ⟨912668409802716106472753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2433782426140576283927341 912668409802716106472753)
            ·
              refine ⟨684501307352037079854565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912668409802716106472753 684501307352037079854565)
              ·
                refine ⟨128343995128506952472731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684501307352037079854565 128343995128506952472731)
                ·
                  rfl

theorem cell19_421789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_421789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421789 prefixEnd_421789 := by exact prefixLift 421789
  have htrace : WordTrace (prefixWord ++ tailWord_421789) baseStart_421789 baseEnd_421789 := by
    simpa [prefixWord, tailWord_421789, baseEnd_421789] using wordTrace_append hprefix tailTrace_421789
  have hstable : (prefixWord ++ tailWord_421789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421789).length < 2 ^ (prefixWord ++ tailWord_421789).sum := by decide
  have hdescent : baseEnd_421789 < baseStart_421789 := by decide
  rcases family_descends (prefixWord ++ tailWord_421789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421842 : List Nat := [3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_421842 : Nat := 118140960795 + 421842 * 2 ^ 59
def prefixEnd_421842 : Nat := 4983230072969 + 3 ^ 40 * 421842 * 2
def baseEnd_421842 : Nat := 128360122224618533294809

theorem tailTrace_421842 : CollatzResearch.WordTrace tailWord_421842 prefixEnd_421842 128360122224618533294809 := by
  unfold tailWord_421842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3846460434436488430730945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10257227825163969148615853 3846460434436488430730945)
  ·
    refine ⟨2884845325827366323048209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3846460434436488430730945 2884845325827366323048209)
    ·
      refine ⟨2163633994370524742286157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884845325827366323048209 2163633994370524742286157)
      ·
        refine ⟨811362747888946778357309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2163633994370524742286157 811362747888946778357309)
        ·
          refine ⟨304261030458355041883991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811362747888946778357309 304261030458355041883991)
          ·
            refine ⟨456391545687532562825987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304261030458355041883991 456391545687532562825987)
            ·
              refine ⟨684587318531298844238981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456391545687532562825987 684587318531298844238981)
              ·
                refine ⟨128360122224618533294809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684587318531298844238981 128360122224618533294809)
                ·
                  rfl

theorem cell19_421842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_421842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421842 prefixEnd_421842 := by exact prefixLift 421842
  have htrace : WordTrace (prefixWord ++ tailWord_421842) baseStart_421842 baseEnd_421842 := by
    simpa [prefixWord, tailWord_421842, baseEnd_421842] using wordTrace_append hprefix tailTrace_421842
  have hstable : (prefixWord ++ tailWord_421842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421842).length < 2 ^ (prefixWord ++ tailWord_421842).sum := by decide
  have hdescent : baseEnd_421842 < baseStart_421842 := by decide
  rcases family_descends (prefixWord ++ tailWord_421842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421863 : List Nat := [1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_421863 : Nat := 118140960795 + 421863 * 2 ^ 59
def prefixEnd_421863 : Nat := 4983230072969 + 3 ^ 40 * 421863 * 2
def baseEnd_421863 : Nat := 128366512206096706828085

theorem tailTrace_421863 : CollatzResearch.WordTrace tailWord_421863 prefixEnd_421863 128366512206096706828085 := by
  unfold tailWord_421863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386607670669874309438243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10257738447113249539625495 15386607670669874309438243)
  ·
    refine ⟨23079911506004811464157365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15386607670669874309438243 23079911506004811464157365)
    ·
      refine ⟨2163741703687951074764753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23079911506004811464157365 2163741703687951074764753)
      ·
        refine ⟨1622806277765963306073565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163741703687951074764753 1622806277765963306073565)
        ·
          refine ⟨608552354162236239777587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1622806277765963306073565 608552354162236239777587)
          ·
            refine ⟨912828531243354359666381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608552354162236239777587 912828531243354359666381)
            ·
              refine ⟨342310699216257884874893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 912828531243354359666381 342310699216257884874893)
              ·
                refine ⟨128366512206096706828085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342310699216257884874893 128366512206096706828085)
                ·
                  rfl

theorem cell19_421863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_421863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421863 prefixEnd_421863 := by exact prefixLift 421863
  have htrace : WordTrace (prefixWord ++ tailWord_421863) baseStart_421863 baseEnd_421863 := by
    simpa [prefixWord, tailWord_421863, baseEnd_421863] using wordTrace_append hprefix tailTrace_421863
  have hstable : (prefixWord ++ tailWord_421863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421863).length < 2 ^ (prefixWord ++ tailWord_421863).sum := by decide
  have hdescent : baseEnd_421863 < baseStart_421863 := by decide
  rcases family_descends (prefixWord ++ tailWord_421863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
