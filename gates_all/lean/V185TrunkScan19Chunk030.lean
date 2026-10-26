import V185TrunkScan19Chunk029

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_300730 : List Nat := [3, 1, 1, 1, 2, 4, 7]
def baseStart_300730 : Nat := 118140960795 + 300730 * 2 ^ 59
def prefixEnd_300730 : Nat := 4983230072969 + 3 ^ 40 * 300730 * 2
def baseEnd_300730 : Nat := 30502525871943432334217

theorem tailTrace_300730 : CollatzResearch.WordTrace tailWord_300730 prefixEnd_300730 30502525871943432334217 := by
  unfold tailWord_300730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742131050128511360020911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7312349467009363626722429 2742131050128511360020911)
  ·
    refine ⟨4113196575192767040031367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742131050128511360020911 4113196575192767040031367)
    ·
      refine ⟨6169794862789150560047051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4113196575192767040031367 6169794862789150560047051)
      ·
        refine ⟨9254692294183725840070577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169794862789150560047051 9254692294183725840070577)
        ·
          refine ⟨6941019220637794380052933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9254692294183725840070577 6941019220637794380052933)
          ·
            refine ⟨1301441103869586446259925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6941019220637794380052933 1301441103869586446259925)
            ·
              refine ⟨30502525871943432334217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1301441103869586446259925 30502525871943432334217)
              ·
                rfl

theorem cell19_300730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_300730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300730 prefixEnd_300730 := by exact prefixLift 300730
  have htrace : WordTrace (prefixWord ++ tailWord_300730) baseStart_300730 baseEnd_300730 := by
    simpa [prefixWord, tailWord_300730, baseEnd_300730] using wordTrace_append hprefix tailTrace_300730
  have hstable : (prefixWord ++ tailWord_300730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300730).length < 2 ^ (prefixWord ++ tailWord_300730).sum := by decide
  have hdescent : baseEnd_300730 < baseStart_300730 := by decide
  rcases family_descends (prefixWord ++ tailWord_300730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300768 : List Nat := [2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_300768 : Nat := 118140960795 + 300768 * 2 ^ 59
def prefixEnd_300768 : Nat := 4983230072969 + 3 ^ 40 * 300768 * 2
def baseEnd_300768 : Nat := 91519140439457468158103

theorem tailTrace_300768 : CollatzResearch.WordTrace tailWord_300768 prefixEnd_300768 91519140439457468158103 := by
  unfold tailWord_300768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5484955087188188964983479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7313273449584251953311305 5484955087188188964983479)
  ·
    refine ⟨8227432630782283447475219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5484955087188188964983479 8227432630782283447475219)
    ·
      refine ⟨12341148946173425171212829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8227432630782283447475219 12341148946173425171212829)
      ·
        refine ⟨4627930854815034439204811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12341148946173425171212829 4627930854815034439204811)
        ·
          refine ⟨6941896282222551658807217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627930854815034439204811 6941896282222551658807217)
          ·
            refine ⟨5206422211666913744105413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6941896282222551658807217 5206422211666913744105413)
            ·
              refine ⟨976204164687546327019765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5206422211666913744105413 976204164687546327019765)
              ·
                refine ⟨91519140439457468158103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 976204164687546327019765 91519140439457468158103)
                ·
                  rfl

theorem cell19_300768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_300768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300768 prefixEnd_300768 := by exact prefixLift 300768
  have htrace : WordTrace (prefixWord ++ tailWord_300768) baseStart_300768 baseEnd_300768 := by
    simpa [prefixWord, tailWord_300768, baseEnd_300768] using wordTrace_append hprefix tailTrace_300768
  have hstable : (prefixWord ++ tailWord_300768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300768).length < 2 ^ (prefixWord ++ tailWord_300768).sum := by decide
  have hdescent : baseEnd_300768 < baseStart_300768 := by decide
  rcases family_descends (prefixWord ++ tailWord_300768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300804 : List Nat := [2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_300804 : Nat := 118140960795 + 300804 * 2 ^ 59
def prefixEnd_300804 : Nat := 4983230072969 + 3 ^ 40 * 300804 * 2
def baseEnd_300804 : Nat := 91530094693420051358005

theorem tailTrace_300804 : CollatzResearch.WordTrace tailWord_300804 prefixEnd_300804 91530094693420051358005 := by
  unfold tailWord_300804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5485611601122978039138733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7314148801497304052184977 5485611601122978039138733)
  ·
    refine ⟨2057104350421116764677025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5485611601122978039138733 2057104350421116764677025)
    ·
      refine ⟨1542828262815837573507769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2057104350421116764677025 1542828262815837573507769)
      ·
        refine ⟨1157121197111878180130827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1542828262815837573507769 1157121197111878180130827)
        ·
          refine ⟨1735681795667817270196241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157121197111878180130827 1735681795667817270196241)
          ·
            refine ⟨1301761346750862952647181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735681795667817270196241 1301761346750862952647181)
            ·
              refine ⟨488160505031573607242693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1301761346750862952647181 488160505031573607242693)
              ·
                refine ⟨91530094693420051358005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488160505031573607242693 91530094693420051358005)
                ·
                  rfl

theorem cell19_300804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_300804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300804 prefixEnd_300804 := by exact prefixLift 300804
  have htrace : WordTrace (prefixWord ++ tailWord_300804) baseStart_300804 baseEnd_300804 := by
    simpa [prefixWord, tailWord_300804, baseEnd_300804] using wordTrace_append hprefix tailTrace_300804
  have hstable : (prefixWord ++ tailWord_300804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300804).length < 2 ^ (prefixWord ++ tailWord_300804).sum := by decide
  have hdescent : baseEnd_300804 < baseStart_300804 := by decide
  rcases family_descends (prefixWord ++ tailWord_300804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300844 : List Nat := [2, 2, 1, 1, 1, 6, 6]
def baseStart_300844 : Nat := 118140960795 + 300844 * 2 ^ 59
def prefixEnd_300844 : Nat := 4983230072969 + 3 ^ 40 * 300844 * 2
def baseEnd_300844 : Nat := 30514088695570603489669

theorem tailTrace_300844 : CollatzResearch.WordTrace tailWord_300844 prefixEnd_300844 30514088695570603489669 := by
  unfold tailWord_300844
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486341061050521454866793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7315121414734028606489057 5486341061050521454866793)
  ·
    refine ⟨4114755795787891091150095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5486341061050521454866793 4114755795787891091150095)
    ·
      refine ⟨6172133693681836636725143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4114755795787891091150095 6172133693681836636725143)
      ·
        refine ⟨9258200540522754955087715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172133693681836636725143 9258200540522754955087715)
        ·
          refine ⟨13887300810784132432631573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9258200540522754955087715 13887300810784132432631573)
          ·
            refine ⟨650967225505506207779605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13887300810784132432631573 650967225505506207779605)
            ·
              refine ⟨30514088695570603489669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 650967225505506207779605 30514088695570603489669)
              ·
                rfl

theorem cell19_300844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_300844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300844 prefixEnd_300844 := by exact prefixLift 300844
  have htrace : WordTrace (prefixWord ++ tailWord_300844) baseStart_300844 baseEnd_300844 := by
    simpa [prefixWord, tailWord_300844, baseEnd_300844] using wordTrace_append hprefix tailTrace_300844
  have hstable : (prefixWord ++ tailWord_300844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300844).length < 2 ^ (prefixWord ++ tailWord_300844).sum := by decide
  have hdescent : baseEnd_300844 < baseStart_300844 := by decide
  rcases family_descends (prefixWord ++ tailWord_300844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300876 : List Nat := [2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_300876 : Nat := 118140960795 + 300876 * 2 ^ 59
def prefixEnd_300876 : Nat := 4983230072969 + 3 ^ 40 * 300876 * 2
def baseEnd_300876 : Nat := 91552003201345217757809

theorem tailTrace_300876 : CollatzResearch.WordTrace tailWord_300876 prefixEnd_300876 91552003201345217757809 := by
  unfold tailWord_300876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486924628992556187449241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7315899505323408249932321 5486924628992556187449241)
  ·
    refine ⟨4115193471744417140586931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5486924628992556187449241 4115193471744417140586931)
    ·
      refine ⟨6172790207616625710880397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115193471744417140586931 6172790207616625710880397)
      ·
        refine ⟨2314796327856234641580149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6172790207616625710880397 2314796327856234641580149)
        ·
          refine ⟨217012155736521997648139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2314796327856234641580149 217012155736521997648139)
          ·
            refine ⟨325518233604782996472209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217012155736521997648139 325518233604782996472209)
            ·
              refine ⟨244138675203587247354157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325518233604782996472209 244138675203587247354157)
              ·
                refine ⟨91552003201345217757809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244138675203587247354157 91552003201345217757809)
                ·
                  rfl

theorem cell19_300876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_300876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300876 prefixEnd_300876 := by exact prefixLift 300876
  have htrace : WordTrace (prefixWord ++ tailWord_300876) baseStart_300876 baseEnd_300876 := by
    simpa [prefixWord, tailWord_300876, baseEnd_300876] using wordTrace_append hprefix tailTrace_300876
  have hstable : (prefixWord ++ tailWord_300876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300876).length < 2 ^ (prefixWord ++ tailWord_300876).sum := by decide
  have hdescent : baseEnd_300876 < baseStart_300876 := by decide
  rcases family_descends (prefixWord ++ tailWord_300876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300899 : List Nat := [1, 1, 1, 5, 4, 2, 5]
def baseStart_300899 : Nat := 118140960795 + 300899 * 2 ^ 59
def prefixEnd_300899 : Nat := 4983230072969 + 3 ^ 40 * 300899 * 2
def baseEnd_300899 : Nat := 30519667250829326415545

theorem tailTrace_300899 : CollatzResearch.WordTrace tailWord_300899 prefixEnd_300899 30519667250829326415545 := by
  unfold tailWord_300899
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974688136901787302985751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7316458757934524868657167 10974688136901787302985751)
  ·
    refine ⟨16462032205352680954478627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974688136901787302985751 16462032205352680954478627)
    ·
      refine ⟨24693048308029021431717941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462032205352680954478627 24693048308029021431717941)
      ·
        refine ⟨2314973278877720759223557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24693048308029021431717941 2314973278877720759223557)
        ·
          refine ⟨434057489789572642354417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2314973278877720759223557 434057489789572642354417)
          ·
            refine ⟨325543117342179481765813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434057489789572642354417 325543117342179481765813)
            ·
              refine ⟨30519667250829326415545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 325543117342179481765813 30519667250829326415545)
              ·
                rfl

theorem cell19_300899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_300899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300899 prefixEnd_300899 := by exact prefixLift 300899
  have htrace : WordTrace (prefixWord ++ tailWord_300899) baseStart_300899 baseEnd_300899 := by
    simpa [prefixWord, tailWord_300899, baseEnd_300899] using wordTrace_append hprefix tailTrace_300899
  have hstable : (prefixWord ++ tailWord_300899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300899).length < 2 ^ (prefixWord ++ tailWord_300899).sum := by decide
  have hdescent : baseEnd_300899 < baseStart_300899 := by decide
  rcases family_descends (prefixWord ++ tailWord_300899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301034 : List Nat := [3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_301034 : Nat := 118140960795 + 301034 * 2 ^ 59
def prefixEnd_301034 : Nat := 4983230072969 + 3 ^ 40 * 301034 * 2
def baseEnd_301034 : Nat := 91600080204847666246267

theorem tailTrace_301034 : CollatzResearch.WordTrace tailWord_301034 prefixEnd_301034 91600080204847666246267 := by
  unfold tailWord_301034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744902997853176339787539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7319741327608470239433437 2744902997853176339787539)
  ·
    refine ⟨4117354496779764509681309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744902997853176339787539 4117354496779764509681309)
    ·
      refine ⟨1544007936292411691130491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4117354496779764509681309 1544007936292411691130491)
      ·
        refine ⟨2316011904438617536695737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544007936292411691130491 2316011904438617536695737)
        ·
          refine ⟨1737008928328963152521803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316011904438617536695737 1737008928328963152521803)
          ·
            refine ⟨2605513392493444728782705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737008928328963152521803 2605513392493444728782705)
            ·
              refine ⟨1954135044370083546587029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605513392493444728782705 1954135044370083546587029)
              ·
                refine ⟨91600080204847666246267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1954135044370083546587029 91600080204847666246267)
                ·
                  rfl

theorem cell19_301034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_301034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301034 prefixEnd_301034 := by exact prefixLift 301034
  have htrace : WordTrace (prefixWord ++ tailWord_301034) baseStart_301034 baseEnd_301034 := by
    simpa [prefixWord, tailWord_301034, baseEnd_301034] using wordTrace_append hprefix tailTrace_301034
  have hstable : (prefixWord ++ tailWord_301034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301034).length < 2 ^ (prefixWord ++ tailWord_301034).sum := by decide
  have hdescent : baseEnd_301034 < baseStart_301034 := by decide
  rcases family_descends (prefixWord ++ tailWord_301034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301062 : List Nat := [6, 2, 1, 2, 2, 1, 5]
def baseStart_301062 : Nat := 118140960795 + 301062 * 2 ^ 59
def prefixEnd_301062 : Nat := 4983230072969 + 3 ^ 40 * 301062 * 2
def baseEnd_301062 : Nat := 30536200060050632541323

theorem tailTrace_301062 : CollatzResearch.WordTrace tailWord_301062 prefixEnd_301062 30536200060050632541323 := by
  unfold tailWord_301062
  simp only [CollatzResearch.WordTrace]
  refine ⟨343144788603477066911545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7320422156874177427446293 343144788603477066911545)
  ·
    refine ⟨257358591452607800183659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 343144788603477066911545 257358591452607800183659)
    ·
      refine ⟨386037887178911700275489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257358591452607800183659 386037887178911700275489)
      ·
        refine ⟨289528415384183775206617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386037887178911700275489 289528415384183775206617)
        ·
          refine ⟨217146311538137831404963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289528415384183775206617 217146311538137831404963)
          ·
            refine ⟨325719467307206747107445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217146311538137831404963 325719467307206747107445)
            ·
              refine ⟨30536200060050632541323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 325719467307206747107445 30536200060050632541323)
              ·
                rfl

theorem cell19_301062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_301062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301062 prefixEnd_301062 := by exact prefixLift 301062
  have htrace : WordTrace (prefixWord ++ tailWord_301062) baseStart_301062 baseEnd_301062 := by
    simpa [prefixWord, tailWord_301062, baseEnd_301062] using wordTrace_append hprefix tailTrace_301062
  have hstable : (prefixWord ++ tailWord_301062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301062).length < 2 ^ (prefixWord ++ tailWord_301062).sum := by decide
  have hdescent : baseEnd_301062 < baseStart_301062 := by decide
  rcases family_descends (prefixWord ++ tailWord_301062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301089 : List Nat := [1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_301089 : Nat := 118140960795 + 301089 * 2 ^ 59
def prefixEnd_301089 : Nat := 4983230072969 + 3 ^ 40 * 301089 * 2
def baseEnd_301089 : Nat := 91616815870623835023895

theorem tailTrace_301089 : CollatzResearch.WordTrace tailWord_301089 prefixEnd_301089 91616815870623835023895 := by
  unfold tailWord_301089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981618006213449752402321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7321078670808966501601547 10981618006213449752402321)
  ·
    refine ⟨8236213504660087314301741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10981618006213449752402321 8236213504660087314301741)
    ·
      refine ⟨3088580064247532742863153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8236213504660087314301741 3088580064247532742863153)
      ·
        refine ⟨2316435048185649557147365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088580064247532742863153 2316435048185649557147365)
        ·
          refine ⟨434331571534809291965131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2316435048185649557147365 434331571534809291965131)
          ·
            refine ⟨651497357302213937947697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434331571534809291965131 651497357302213937947697)
            ·
              refine ⟨488623017976660453460773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651497357302213937947697 488623017976660453460773)
              ·
                refine ⟨91616815870623835023895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488623017976660453460773 91616815870623835023895)
                ·
                  rfl

theorem cell19_301089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_301089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301089 prefixEnd_301089 := by exact prefixLift 301089
  have htrace : WordTrace (prefixWord ++ tailWord_301089) baseStart_301089 baseEnd_301089 := by
    simpa [prefixWord, tailWord_301089, baseEnd_301089] using wordTrace_append hprefix tailTrace_301089
  have hstable : (prefixWord ++ tailWord_301089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301089).length < 2 ^ (prefixWord ++ tailWord_301089).sum := by decide
  have hdescent : baseEnd_301089 < baseStart_301089 := by decide
  rcases family_descends (prefixWord ++ tailWord_301089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301091 : List Nat := [1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_301091 : Nat := 118140960795 + 301091 * 2 ^ 59
def prefixEnd_301091 : Nat := 4983230072969 + 3 ^ 40 * 301091 * 2
def baseEnd_301091 : Nat := 91617424440288422979445

theorem tailTrace_301091 : CollatzResearch.WordTrace tailWord_301091 prefixEnd_301091 91617424440288422979445 := by
  unfold tailWord_301091
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981690952206204093975127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7321127301470802729316751 10981690952206204093975127)
  ·
    refine ⟨16472536428309306140962691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10981690952206204093975127 16472536428309306140962691)
    ·
      refine ⟨24708804642463959211444037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16472536428309306140962691 24708804642463959211444037)
      ·
        refine ⟨4632900870461992352145757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24708804642463959211444037 4632900870461992352145757)
        ·
          refine ⟨1737337826423247132054659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4632900870461992352145757 1737337826423247132054659)
          ·
            refine ⟨2606006739634870698081989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737337826423247132054659 2606006739634870698081989)
            ·
              refine ⟨488626263681538255890373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2606006739634870698081989 488626263681538255890373)
              ·
                refine ⟨91617424440288422979445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488626263681538255890373 91617424440288422979445)
                ·
                  rfl

theorem cell19_301091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_301091 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301091 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301091 prefixEnd_301091 := by exact prefixLift 301091
  have htrace : WordTrace (prefixWord ++ tailWord_301091) baseStart_301091 baseEnd_301091 := by
    simpa [prefixWord, tailWord_301091, baseEnd_301091] using wordTrace_append hprefix tailTrace_301091
  have hstable : (prefixWord ++ tailWord_301091).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301091).length < 2 ^ (prefixWord ++ tailWord_301091).sum := by decide
  have hdescent : baseEnd_301091 < baseStart_301091 := by decide
  rcases family_descends (prefixWord ++ tailWord_301091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301142 : List Nat := [5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_301142 : Nat := 118140960795 + 301142 * 2 ^ 59
def prefixEnd_301142 : Nat := 4983230072969 + 3 ^ 40 * 301142 * 2
def baseEnd_301142 : Nat := 91632942966735415845973

theorem tailTrace_301142 : CollatzResearch.WordTrace tailWord_301142 prefixEnd_301142 91632942966735415845973 := by
  unfold tailWord_301142
  simp only [CollatzResearch.WordTrace]
  refine ⟨686471942188839987755105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7322367383347626536054453 686471942188839987755105)
  ·
    refine ⟨514853956641629990816329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 686471942188839987755105 514853956641629990816329)
    ·
      refine ⟨386140467481222493112247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514853956641629990816329 386140467481222493112247)
      ·
        refine ⟨579210701221833739668371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386140467481222493112247 579210701221833739668371)
        ·
          refine ⟨868816051832750609502557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579210701221833739668371 868816051832750609502557)
          ·
            refine ⟨325806019437281478563459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 868816051832750609502557 325806019437281478563459)
            ·
              refine ⟨488709029155922217845189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325806019437281478563459 488709029155922217845189)
              ·
                refine ⟨91632942966735415845973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488709029155922217845189 91632942966735415845973)
                ·
                  rfl

theorem cell19_301142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_301142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301142 prefixEnd_301142 := by exact prefixLift 301142
  have htrace : WordTrace (prefixWord ++ tailWord_301142) baseStart_301142 baseEnd_301142 := by
    simpa [prefixWord, tailWord_301142, baseEnd_301142] using wordTrace_append hprefix tailTrace_301142
  have hstable : (prefixWord ++ tailWord_301142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301142).length < 2 ^ (prefixWord ++ tailWord_301142).sum := by decide
  have hdescent : baseEnd_301142 < baseStart_301142 := by decide
  rcases family_descends (prefixWord ++ tailWord_301142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301165 : List Nat := [1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_301165 : Nat := 118140960795 + 301165 * 2 ^ 59
def prefixEnd_301165 : Nat := 4983230072969 + 3 ^ 40 * 301165 * 2
def baseEnd_301165 : Nat := 91639941517878177334799

theorem tailTrace_301165 : CollatzResearch.WordTrace tailWord_301165 prefixEnd_301165 91639941517878177334799 := by
  unfold tailWord_301165
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984389953938114732168949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7322926635958743154779299 10984389953938114732168949)
  ·
    refine ⟨1029786558181698256140839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10984389953938114732168949 1029786558181698256140839)
    ·
      refine ⟨1544679837272547384211259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029786558181698256140839 1544679837272547384211259)
      ·
        refine ⟨2317019755908821076316889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544679837272547384211259 2317019755908821076316889)
        ·
          refine ⟨1737764816931615807237667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2317019755908821076316889 1737764816931615807237667)
          ·
            refine ⟨2606647225397423710856501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737764816931615807237667 2606647225397423710856501)
            ·
              refine ⟨244373177381008472892797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2606647225397423710856501 244373177381008472892797)
              ·
                refine ⟨91639941517878177334799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244373177381008472892797 91639941517878177334799)
                ·
                  rfl

theorem cell19_301165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_301165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301165 prefixEnd_301165 := by exact prefixLift 301165
  have htrace : WordTrace (prefixWord ++ tailWord_301165) baseStart_301165 baseEnd_301165 := by
    simpa [prefixWord, tailWord_301165, baseEnd_301165] using wordTrace_append hprefix tailTrace_301165
  have hstable : (prefixWord ++ tailWord_301165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301165).length < 2 ^ (prefixWord ++ tailWord_301165).sum := by decide
  have hdescent : baseEnd_301165 < baseStart_301165 := by decide
  rcases family_descends (prefixWord ++ tailWord_301165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301220 : List Nat := [2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_301220 : Nat := 118140960795 + 301220 * 2 ^ 59
def prefixEnd_301220 : Nat := 4983230072969 + 3 ^ 40 * 301220 * 2
def baseEnd_301220 : Nat := 91656677183654346112427

theorem tailTrace_301220 : CollatzResearch.WordTrace tailWord_301220 prefixEnd_301220 91656677183654346112427 := by
  unfold tailWord_301220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493197984369429562710557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7324263979159239416947409 5493197984369429562710557)
  ·
    refine ⟨2059949244138536086016459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5493197984369429562710557 2059949244138536086016459)
    ·
      refine ⟨3089923866207804129024689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059949244138536086016459 3089923866207804129024689)
      ·
        refine ⟨2317442899655853096768517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3089923866207804129024689 2317442899655853096768517)
        ·
          refine ⟨434520543685472455644097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2317442899655853096768517 434520543685472455644097)
          ·
            refine ⟨325890407764104341733073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434520543685472455644097 325890407764104341733073)
            ·
              refine ⟨244417805823078256299805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325890407764104341733073 244417805823078256299805)
              ·
                refine ⟨91656677183654346112427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244417805823078256299805 91656677183654346112427)
                ·
                  rfl

theorem cell19_301220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_301220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301220 prefixEnd_301220 := by exact prefixLift 301220
  have htrace : WordTrace (prefixWord ++ tailWord_301220) baseStart_301220 baseEnd_301220 := by
    simpa [prefixWord, tailWord_301220, baseEnd_301220] using wordTrace_append hprefix tailTrace_301220
  have hstable : (prefixWord ++ tailWord_301220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301220).length < 2 ^ (prefixWord ++ tailWord_301220).sum := by decide
  have hdescent : baseEnd_301220 < baseStart_301220 := by decide
  rcases family_descends (prefixWord ++ tailWord_301220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301262 : List Nat := [4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_301262 : Nat := 118140960795 + 301262 * 2 ^ 59
def prefixEnd_301262 : Nat := 4983230072969 + 3 ^ 40 * 301262 * 2
def baseEnd_301262 : Nat := 91669457146610693178979

theorem tailTrace_301262 : CollatzResearch.WordTrace tailWord_301262 prefixEnd_301262 91669457146610693178979 := by
  unfold tailWord_301262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373490979323337537306255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7325285223057800198966693 1373490979323337537306255)
  ·
    refine ⟨2060236468985006305959383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373490979323337537306255 2060236468985006305959383)
    ·
      refine ⟨3090354703477509458939075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060236468985006305959383 3090354703477509458939075)
      ·
        refine ⟨4635532055216264188408613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090354703477509458939075 4635532055216264188408613)
        ·
          refine ⟨869162260353049535326615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4635532055216264188408613 869162260353049535326615)
          ·
            refine ⟨1303743390529574302989923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869162260353049535326615 1303743390529574302989923)
            ·
              refine ⟨1955615085794361454484885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303743390529574302989923 1955615085794361454484885)
              ·
                refine ⟨91669457146610693178979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1955615085794361454484885 91669457146610693178979)
                ·
                  rfl

theorem cell19_301262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_301262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301262 prefixEnd_301262 := by exact prefixLift 301262
  have htrace : WordTrace (prefixWord ++ tailWord_301262) baseStart_301262 baseEnd_301262 := by
    simpa [prefixWord, tailWord_301262, baseEnd_301262] using wordTrace_append hprefix tailTrace_301262
  have hstable : (prefixWord ++ tailWord_301262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301262).length < 2 ^ (prefixWord ++ tailWord_301262).sum := by decide
  have hdescent : baseEnd_301262 < baseStart_301262 := by decide
  rcases family_descends (prefixWord ++ tailWord_301262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301393 : List Nat := [1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_301393 : Nat := 118140960795 + 301393 * 2 ^ 59
def prefixEnd_301393 : Nat := 4983230072969 + 3 ^ 40 * 301393 * 2
def baseEnd_301393 : Nat := 91709318459641204267511

theorem tailTrace_301393 : CollatzResearch.WordTrace tailWord_301393 prefixEnd_301393 91709318459641204267511 := by
  unfold tailWord_301393
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992705797112109671468833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7328470531408073114312555 10992705797112109671468833)
  ·
    refine ⟨8244529347834082253601625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10992705797112109671468833 8244529347834082253601625)
    ·
      refine ⟨6183397010875561690201219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8244529347834082253601625 6183397010875561690201219)
      ·
        refine ⟨9275095516313342535301829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183397010875561690201219 9275095516313342535301829)
        ·
          refine ⟨1739080409308751725369093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9275095516313342535301829 1739080409308751725369093)
          ·
            refine ⟨326077576745390948506705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1739080409308751725369093 326077576745390948506705)
            ·
              refine ⟨244558182559043211380029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326077576745390948506705 244558182559043211380029)
              ·
                refine ⟨91709318459641204267511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244558182559043211380029 91709318459641204267511)
                ·
                  rfl

theorem cell19_301393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_301393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301393 prefixEnd_301393 := by exact prefixLift 301393
  have htrace : WordTrace (prefixWord ++ tailWord_301393) baseStart_301393 baseEnd_301393 := by
    simpa [prefixWord, tailWord_301393, baseEnd_301393] using wordTrace_append hprefix tailTrace_301393
  have hstable : (prefixWord ++ tailWord_301393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301393).length < 2 ^ (prefixWord ++ tailWord_301393).sum := by decide
  have hdescent : baseEnd_301393 < baseStart_301393 := by decide
  rcases family_descends (prefixWord ++ tailWord_301393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301406 : List Nat := [4, 4, 2, 1, 1, 2, 5]
def baseStart_301406 : Nat := 118140960795 + 301406 * 2 ^ 59
def prefixEnd_301406 : Nat := 4983230072969 + 3 ^ 40 * 301406 * 2
def baseEnd_301406 : Nat := 30571091387487008659529

theorem tailTrace_301406 : CollatzResearch.WordTrace tailWord_301406 prefixEnd_301406 30571091387487008659529 := by
  unfold tailWord_301406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374147493258126611461509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7328786630710008594461381 1374147493258126611461509)
  ·
    refine ⟨257652654985898739649033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1374147493258126611461509 257652654985898739649033)
    ·
      refine ⟨193239491239424054736775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257652654985898739649033 193239491239424054736775)
      ·
        refine ⟨289859236859136082105163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193239491239424054736775 289859236859136082105163)
        ·
          refine ⟨434788855288704123157745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289859236859136082105163 434788855288704123157745)
          ·
            refine ⟨326091641466528092368309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434788855288704123157745 326091641466528092368309)
            ·
              refine ⟨30571091387487008659529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326091641466528092368309 30571091387487008659529)
              ·
                rfl

theorem cell19_301406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_301406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301406 prefixEnd_301406 := by exact prefixLift 301406
  have htrace : WordTrace (prefixWord ++ tailWord_301406) baseStart_301406 baseEnd_301406 := by
    simpa [prefixWord, tailWord_301406, baseEnd_301406] using wordTrace_append hprefix tailTrace_301406
  have hstable : (prefixWord ++ tailWord_301406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301406).length < 2 ^ (prefixWord ++ tailWord_301406).sum := by decide
  have hdescent : baseEnd_301406 < baseStart_301406 := by decide
  rcases family_descends (prefixWord ++ tailWord_301406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301435 : List Nat := [1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_301435 : Nat := 118140960795 + 301435 * 2 ^ 59
def prefixEnd_301435 : Nat := 4983230072969 + 3 ^ 40 * 301435 * 2
def baseEnd_301435 : Nat := 91722098422597551334063

theorem tailTrace_301435 : CollatzResearch.WordTrace tailWord_301435 prefixEnd_301435 91722098422597551334063 := by
  unfold tailWord_301435
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994237662959950844497759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7329491775306633896331839 10994237662959950844497759)
  ·
    refine ⟨16491356494439926266746639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10994237662959950844497759 16491356494439926266746639)
    ·
      refine ⟨24737034741659889400119959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16491356494439926266746639 24737034741659889400119959)
      ·
        refine ⟨37105552112489834100179939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24737034741659889400119959 37105552112489834100179939)
        ·
          refine ⟨55658328168734751150269909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37105552112489834100179939 55658328168734751150269909)
          ·
            refine ⟨1304492066454720730084451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55658328168734751150269909 1304492066454720730084451)
            ·
              refine ⟨1956738099682081095126677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304492066454720730084451 1956738099682081095126677)
              ·
                refine ⟨91722098422597551334063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1956738099682081095126677 91722098422597551334063)
                ·
                  rfl

theorem cell19_301435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_301435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301435 prefixEnd_301435 := by exact prefixLift 301435
  have htrace : WordTrace (prefixWord ++ tailWord_301435) baseStart_301435 baseEnd_301435 := by
    simpa [prefixWord, tailWord_301435, baseEnd_301435] using wordTrace_append hprefix tailTrace_301435
  have hstable : (prefixWord ++ tailWord_301435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301435).length < 2 ^ (prefixWord ++ tailWord_301435).sum := by decide
  have hdescent : baseEnd_301435 < baseStart_301435 := by decide
  rcases family_descends (prefixWord ++ tailWord_301435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301482 : List Nat := [3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_301482 : Nat := 118140960795 + 301482 * 2 ^ 59
def prefixEnd_301482 : Nat := 4983230072969 + 3 ^ 40 * 301482 * 2
def baseEnd_301482 : Nat := 91736399809715368289491

theorem tailTrace_301482 : CollatzResearch.WordTrace tailWord_301482 prefixEnd_301482 91736399809715368289491 := by
  unfold tailWord_301482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748987973447419467864675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7330634595859785247639133 2748987973447419467864675)
  ·
    refine ⟨4123481960171129201797013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748987973447419467864675 4123481960171129201797013)
    ·
      refine ⟨193288216883021681334235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4123481960171129201797013 193288216883021681334235)
      ·
        refine ⟨289932325324532522001353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193288216883021681334235 289932325324532522001353)
        ·
          refine ⟨217449243993399391501015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289932325324532522001353 217449243993399391501015)
          ·
            refine ⟨326173865990099087251523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217449243993399391501015 326173865990099087251523)
            ·
              refine ⟨489260798985148630877285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326173865990099087251523 489260798985148630877285)
              ·
                refine ⟨91736399809715368289491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489260798985148630877285 91736399809715368289491)
                ·
                  rfl

theorem cell19_301482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_301482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301482 prefixEnd_301482 := by exact prefixLift 301482
  have htrace : WordTrace (prefixWord ++ tailWord_301482) baseStart_301482 baseEnd_301482 := by
    simpa [prefixWord, tailWord_301482, baseEnd_301482] using wordTrace_append hprefix tailTrace_301482
  have hstable : (prefixWord ++ tailWord_301482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301482).length < 2 ^ (prefixWord ++ tailWord_301482).sum := by decide
  have hdescent : baseEnd_301482 < baseStart_301482 := by decide
  rcases family_descends (prefixWord ++ tailWord_301482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301530 : List Nat := [3, 1, 1, 2, 3, 1, 8]
def baseStart_301530 : Nat := 118140960795 + 301530 * 2 ^ 59
def prefixEnd_301530 : Nat := 4983230072969 + 3 ^ 40 * 301530 * 2
def baseEnd_301530 : Nat := 30583668493888493074231

theorem tailTrace_301530 : CollatzResearch.WordTrace tailWord_301530 prefixEnd_301530 30583668493888493074231 := by
  unfold tailWord_301530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749425649403945517301511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7331801731743854712804029 2749425649403945517301511)
  ·
    refine ⟨4124138474105918275952267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2749425649403945517301511 4124138474105918275952267)
    ·
      refine ⟨6186207711158877413928401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4124138474105918275952267 6186207711158877413928401)
      ·
        refine ⟨4639655783369158060446301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6186207711158877413928401 4639655783369158060446301)
        ·
          refine ⟨1739870918763434272667363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4639655783369158060446301 1739870918763434272667363)
          ·
            refine ⟨2609806378145151409001045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739870918763434272667363 2609806378145151409001045)
            ·
              refine ⟨30583668493888493074231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2609806378145151409001045 30583668493888493074231)
              ·
                rfl

theorem cell19_301530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_301530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301530 prefixEnd_301530 := by exact prefixLift 301530
  have htrace : WordTrace (prefixWord ++ tailWord_301530) baseStart_301530 baseEnd_301530 := by
    simpa [prefixWord, tailWord_301530, baseEnd_301530] using wordTrace_append hprefix tailTrace_301530
  have hstable : (prefixWord ++ tailWord_301530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301530).length < 2 ^ (prefixWord ++ tailWord_301530).sum := by decide
  have hdescent : baseEnd_301530 < baseStart_301530 := by decide
  rcases family_descends (prefixWord ++ tailWord_301530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301581 : List Nat := [1, 7, 1, 1, 1, 3, 5]
def baseStart_301581 : Nat := 118140960795 + 301581 * 2 ^ 59
def prefixEnd_301581 : Nat := 4983230072969 + 3 ^ 40 * 301581 * 2
def baseEnd_301581 : Nat := 30588841336037490696407

theorem tailTrace_301581 : CollatzResearch.WordTrace tailWord_301581 prefixEnd_301581 30588841336037490696407 := by
  unfold tailWord_301581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999562720431017779312597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7333041813620678519541731 10999562720431017779312597)
  ·
    refine ⟨257802251260101979202639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10999562720431017779312597 257802251260101979202639)
    ·
      refine ⟨386703376890152968803959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257802251260101979202639 386703376890152968803959)
      ·
        refine ⟨580055065335229453205939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386703376890152968803959 580055065335229453205939)
        ·
          refine ⟨870082598002844179808909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580055065335229453205939 870082598002844179808909)
          ·
            refine ⟨326280974251066567428341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 870082598002844179808909 326280974251066567428341)
            ·
              refine ⟨30588841336037490696407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326280974251066567428341 30588841336037490696407)
              ·
                rfl

theorem cell19_301581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_301581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301581 prefixEnd_301581 := by exact prefixLift 301581
  have htrace : WordTrace (prefixWord ++ tailWord_301581) baseStart_301581 baseEnd_301581 := by
    simpa [prefixWord, tailWord_301581, baseEnd_301581] using wordTrace_append hprefix tailTrace_301581
  have hstable : (prefixWord ++ tailWord_301581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301581).length < 2 ^ (prefixWord ++ tailWord_301581).sum := by decide
  have hdescent : baseEnd_301581 < baseStart_301581 := by decide
  rcases family_descends (prefixWord ++ tailWord_301581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301625 : List Nat := [1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_301625 : Nat := 118140960795 + 301625 * 2 ^ 59
def prefixEnd_301625 : Nat := 4983230072969 + 3 ^ 40 * 301625 * 2
def baseEnd_301625 : Nat := 91779912540733407111323

theorem tailTrace_301625 : CollatzResearch.WordTrace tailWord_301625 prefixEnd_301625 91779912540733407111323 := by
  unfold tailWord_301625
  simp only [CollatzResearch.WordTrace]
  refine ⟨11001167532271613293914329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7334111688181075529276219 11001167532271613293914329)
  ·
    refine ⟨8250875649203709970435747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11001167532271613293914329 8250875649203709970435747)
    ·
      refine ⟨12376313473805564955653621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250875649203709970435747 12376313473805564955653621)
      ·
        refine ⟨1160279388169271714592527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12376313473805564955653621 1160279388169271714592527)
        ·
          refine ⟨1740419082253907571888791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160279388169271714592527 1740419082253907571888791)
          ·
            refine ⟨2610628623380861357833187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740419082253907571888791 2610628623380861357833187)
            ·
              refine ⟨3915942935071292036749781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610628623380861357833187 3915942935071292036749781)
              ·
                refine ⟨91779912540733407111323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3915942935071292036749781 91779912540733407111323)
                ·
                  rfl

theorem cell19_301625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_301625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301625 prefixEnd_301625 := by exact prefixLift 301625
  have htrace : WordTrace (prefixWord ++ tailWord_301625) baseStart_301625 baseEnd_301625 := by
    simpa [prefixWord, tailWord_301625, baseEnd_301625] using wordTrace_append hprefix tailTrace_301625
  have hstable : (prefixWord ++ tailWord_301625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301625).length < 2 ^ (prefixWord ++ tailWord_301625).sum := by decide
  have hdescent : baseEnd_301625 < baseStart_301625 := by decide
  rcases family_descends (prefixWord ++ tailWord_301625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301678 : List Nat := [4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_301678 : Nat := 118140960795 + 301678 * 2 ^ 59
def prefixEnd_301678 : Nat := 4983230072969 + 3 ^ 40 * 301678 * 2
def baseEnd_301678 : Nat := 91796039636844987933401

theorem tailTrace_301678 : CollatzResearch.WordTrace tailWord_301678 prefixEnd_301678 91796039636844987933401 := by
  unfold tailWord_301678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375387575134950418199211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7335400400719735563729125 1375387575134950418199211)
  ·
    refine ⟨2063081362702425627298817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1375387575134950418199211 2063081362702425627298817)
    ·
      refine ⟨1547311022026819220474113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2063081362702425627298817 1547311022026819220474113)
      ·
        refine ⟨1160483266520114415355585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1547311022026819220474113 1160483266520114415355585)
        ·
          refine ⟨870362449890085811516689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160483266520114415355585 870362449890085811516689)
          ·
            refine ⟨652771837417564358637517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870362449890085811516689 652771837417564358637517)
            ·
              refine ⟨244789439031586634489069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652771837417564358637517 244789439031586634489069)
              ·
                refine ⟨91796039636844987933401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244789439031586634489069 91796039636844987933401)
                ·
                  rfl

theorem cell19_301678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_301678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301678 prefixEnd_301678 := by exact prefixLift 301678
  have htrace : WordTrace (prefixWord ++ tailWord_301678) baseStart_301678 baseEnd_301678 := by
    simpa [prefixWord, tailWord_301678, baseEnd_301678] using wordTrace_append hprefix tailTrace_301678
  have hstable : (prefixWord ++ tailWord_301678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301678).length < 2 ^ (prefixWord ++ tailWord_301678).sum := by decide
  have hdescent : baseEnd_301678 < baseStart_301678 := by decide
  rcases family_descends (prefixWord ++ tailWord_301678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301701 : List Nat := [1, 3, 1, 1, 4, 3, 6]
def baseStart_301701 : Nat := 118140960795 + 301701 * 2 ^ 59
def prefixEnd_301701 : Nat := 4983230072969 + 3 ^ 40 * 301701 * 2
def baseEnd_301701 : Nat := 30601012729329249807409

theorem tailTrace_301701 : CollatzResearch.WordTrace tailWord_301701 prefixEnd_301701 30601012729329249807409 := by
  unfold tailWord_301701
  simp only [CollatzResearch.WordTrace]
  refine ⟨11003939479996278273680957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7335959653330852182453971 11003939479996278273680957)
  ·
    refine ⟨4126477304998604352630359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11003939479996278273680957 4126477304998604352630359)
    ·
      refine ⟨6189715957497906528945539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126477304998604352630359 6189715957497906528945539)
      ·
        refine ⟨9284573936246859793418309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189715957497906528945539 9284573936246859793418309)
        ·
          refine ⟨1740857613046286211265933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9284573936246859793418309 1740857613046286211265933)
          ·
            refine ⟨652821604892357329224725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1740857613046286211265933 652821604892357329224725)
            ·
              refine ⟨30601012729329249807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 652821604892357329224725 30601012729329249807409)
              ·
                rfl

theorem cell19_301701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_301701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301701 prefixEnd_301701 := by exact prefixLift 301701
  have htrace : WordTrace (prefixWord ++ tailWord_301701) baseStart_301701 baseEnd_301701 := by
    simpa [prefixWord, tailWord_301701, baseEnd_301701] using wordTrace_append hprefix tailTrace_301701
  have hstable : (prefixWord ++ tailWord_301701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301701).length < 2 ^ (prefixWord ++ tailWord_301701).sum := by decide
  have hdescent : baseEnd_301701 < baseStart_301701 := by decide
  rcases family_descends (prefixWord ++ tailWord_301701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301720 : List Nat := [2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_301720 : Nat := 118140960795 + 301720 * 2 ^ 59
def prefixEnd_301720 : Nat := 4983230072969 + 3 ^ 40 * 301720 * 2
def baseEnd_301720 : Nat := 91808819599801334999953

theorem tailTrace_301720 : CollatzResearch.WordTrace tailWord_301720 prefixEnd_301720 91808819599801334999953 := by
  unfold tailWord_301720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502316233463722259311307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7336421644618296345748409 5502316233463722259311307)
  ·
    refine ⟨8253474350195583388966961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5502316233463722259311307 8253474350195583388966961)
    ·
      refine ⟨6190105762646687541725221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8253474350195583388966961 6190105762646687541725221)
      ·
        refine ⟨1160644830496253914073479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6190105762646687541725221 1160644830496253914073479)
        ·
          refine ⟨1740967245744380871110219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160644830496253914073479 1740967245744380871110219)
          ·
            refine ⟨2611450868616571306665329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740967245744380871110219 2611450868616571306665329)
            ·
              refine ⟨1958588151462428479998997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611450868616571306665329 1958588151462428479998997)
              ·
                refine ⟨91808819599801334999953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1958588151462428479998997 91808819599801334999953)
                ·
                  rfl

theorem cell19_301720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_301720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301720 prefixEnd_301720 := by exact prefixLift 301720
  have htrace : WordTrace (prefixWord ++ tailWord_301720) baseStart_301720 baseEnd_301720 := by
    simpa [prefixWord, tailWord_301720, baseEnd_301720] using wordTrace_append hprefix tailTrace_301720
  have hstable : (prefixWord ++ tailWord_301720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301720).length < 2 ^ (prefixWord ++ tailWord_301720).sum := by decide
  have hdescent : baseEnd_301720 < baseStart_301720 := by decide
  rcases family_descends (prefixWord ++ tailWord_301720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301735 : List Nat := [1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_301735 : Nat := 118140960795 + 301735 * 2 ^ 59
def prefixEnd_301735 : Nat := 4983230072969 + 3 ^ 40 * 301735 * 2
def baseEnd_301735 : Nat := 91813383872285744666579

theorem tailTrace_301735 : CollatzResearch.WordTrace tailWord_301735 prefixEnd_301735 91813383872285744666579 := by
  unfold tailWord_301735
  simp only [CollatzResearch.WordTrace]
  refine ⟨11005179561873102080418659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7336786374582068053612439 11005179561873102080418659)
  ·
    refine ⟨16507769342809653120627989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11005179561873102080418659 16507769342809653120627989)
    ·
      refine ⟨773801687944202490029437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16507769342809653120627989 773801687944202490029437)
      ·
        refine ⟨290175632979075933761039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 773801687944202490029437 290175632979075933761039)
        ·
          refine ⟨435263449468613900641559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290175632979075933761039 435263449468613900641559)
          ·
            refine ⟨652895174202920850962339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435263449468613900641559 652895174202920850962339)
            ·
              refine ⟨979342761304381276443509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652895174202920850962339 979342761304381276443509)
              ·
                refine ⟨91813383872285744666579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 979342761304381276443509 91813383872285744666579)
                ·
                  rfl

theorem cell19_301735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_301735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301735 prefixEnd_301735 := by exact prefixLift 301735
  have htrace : WordTrace (prefixWord ++ tailWord_301735) baseStart_301735 baseEnd_301735 := by
    simpa [prefixWord, tailWord_301735, baseEnd_301735] using wordTrace_append hprefix tailTrace_301735
  have hstable : (prefixWord ++ tailWord_301735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301735).length < 2 ^ (prefixWord ++ tailWord_301735).sum := by decide
  have hdescent : baseEnd_301735 < baseStart_301735 := by decide
  rcases family_descends (prefixWord ++ tailWord_301735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301777 : List Nat := [1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_301777 : Nat := 118140960795 + 301777 * 2 ^ 59
def prefixEnd_301777 : Nat := 4983230072969 + 3 ^ 40 * 301777 * 2
def baseEnd_301777 : Nat := 91826163835242091733131

theorem tailTrace_301777 : CollatzResearch.WordTrace tailWord_301777 prefixEnd_301777 91826163835242091733131 := by
  unfold tailWord_301777
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006711427720943253447585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7337807618480628835631723 11006711427720943253447585)
  ·
    refine ⟨8255033570790707440085689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11006711427720943253447585 8255033570790707440085689)
    ·
      refine ⟨6191275178093030580064267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8255033570790707440085689 6191275178093030580064267)
      ·
        refine ⟨9286912767139545870096401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6191275178093030580064267 9286912767139545870096401)
        ·
          refine ⟨6965184575354659402572301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9286912767139545870096401 6965184575354659402572301)
          ·
            refine ⟨2611944215757997275964613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6965184575354659402572301 2611944215757997275964613)
            ·
              refine ⟨489739540454624489243365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2611944215757997275964613 489739540454624489243365)
              ·
                refine ⟨91826163835242091733131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489739540454624489243365 91826163835242091733131)
                ·
                  rfl

theorem cell19_301777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_301777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301777 prefixEnd_301777 := by exact prefixLift 301777
  have htrace : WordTrace (prefixWord ++ tailWord_301777) baseStart_301777 baseEnd_301777 := by
    simpa [prefixWord, tailWord_301777, baseEnd_301777] using wordTrace_append hprefix tailTrace_301777
  have hstable : (prefixWord ++ tailWord_301777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301777).length < 2 ^ (prefixWord ++ tailWord_301777).sum := by decide
  have hdescent : baseEnd_301777 < baseStart_301777 := by decide
  rcases family_descends (prefixWord ++ tailWord_301777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301796 : List Nat := [2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_301796 : Nat := 118140960795 + 301796 * 2 ^ 59
def prefixEnd_301796 : Nat := 4983230072969 + 3 ^ 40 * 301796 * 2
def baseEnd_301796 : Nat := 91831945247055677310857

theorem tailTrace_301796 : CollatzResearch.WordTrace tailWord_301796 prefixEnd_301796 91831945247055677310857 := by
  unfold tailWord_301796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503702207326054749194621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7338269609768072998926161 5503702207326054749194621)
  ·
    refine ⟨2063888327747270530947983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5503702207326054749194621 2063888327747270530947983)
    ·
      refine ⟨3095832491620905796421975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063888327747270530947983 3095832491620905796421975)
      ·
        refine ⟨4643748737431358694632963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095832491620905796421975 4643748737431358694632963)
        ·
          refine ⟨6965623106147038041949445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643748737431358694632963 6965623106147038041949445)
          ·
            refine ⟨1306054332402569632865521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6965623106147038041949445 1306054332402569632865521)
            ·
              refine ⟨979540749301927224649141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306054332402569632865521 979540749301927224649141)
              ·
                refine ⟨91831945247055677310857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 979540749301927224649141 91831945247055677310857)
                ·
                  rfl

theorem cell19_301796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_301796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301796 prefixEnd_301796 := by exact prefixLift 301796
  have htrace : WordTrace (prefixWord ++ tailWord_301796) baseStart_301796 baseEnd_301796 := by
    simpa [prefixWord, tailWord_301796, baseEnd_301796] using wordTrace_append hprefix tailTrace_301796
  have hstable : (prefixWord ++ tailWord_301796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301796).length < 2 ^ (prefixWord ++ tailWord_301796).sum := by decide
  have hdescent : baseEnd_301796 < baseStart_301796 := by decide
  rcases family_descends (prefixWord ++ tailWord_301796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301832 : List Nat := [2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_301832 : Nat := 118140960795 + 301832 * 2 ^ 59
def prefixEnd_301832 : Nat := 4983230072969 + 3 ^ 40 * 301832 * 2
def baseEnd_301832 : Nat := 91842899501018260510759

theorem tailTrace_301832 : CollatzResearch.WordTrace tailWord_301832 prefixEnd_301832 91842899501018260510759 := by
  unfold tailWord_301832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504358721260843823349875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7339144961681125097799833 5504358721260843823349875)
  ·
    refine ⟨8256538081891265735024813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5504358721260843823349875 8256538081891265735024813)
    ·
      refine ⟨3096201780709224650634305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8256538081891265735024813 3096201780709224650634305)
      ·
        refine ⟨2322151335531918487975729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3096201780709224650634305 2322151335531918487975729)
        ·
          refine ⟨1741613501648938865981797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322151335531918487975729 1741613501648938865981797)
          ·
            refine ⟨326552531559176037371587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1741613501648938865981797 326552531559176037371587)
            ·
              refine ⟨489828797338764056057381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326552531559176037371587 489828797338764056057381)
              ·
                refine ⟨91842899501018260510759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489828797338764056057381 91842899501018260510759)
                ·
                  rfl

theorem cell19_301832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_301832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301832 prefixEnd_301832 := by exact prefixLift 301832
  have htrace : WordTrace (prefixWord ++ tailWord_301832) baseStart_301832 baseEnd_301832 := by
    simpa [prefixWord, tailWord_301832, baseEnd_301832] using wordTrace_append hprefix tailTrace_301832
  have hstable : (prefixWord ++ tailWord_301832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301832).length < 2 ^ (prefixWord ++ tailWord_301832).sum := by decide
  have hdescent : baseEnd_301832 < baseStart_301832 := by decide
  rcases family_descends (prefixWord ++ tailWord_301832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301870 : List Nat := [4, 1, 3, 2, 1, 2, 6]
def baseStart_301870 : Nat := 118140960795 + 301870 * 2 ^ 59
def prefixEnd_301870 : Nat := 4983230072969 + 3 ^ 40 * 301870 * 2
def baseEnd_301870 : Nat := 30618154108215143888737

theorem tailTrace_301870 : CollatzResearch.WordTrace tailWord_301870 prefixEnd_301870 30618154108215143888737 := by
  unfold tailWord_301870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376262927048002517072883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7340068944256013424388709 1376262927048002517072883)
  ·
    refine ⟨2064394390572003775609325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376262927048002517072883 2064394390572003775609325)
    ·
      refine ⟨774147896464501415853497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2064394390572003775609325 774147896464501415853497)
      ·
        refine ⟨580610922348376061890123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774147896464501415853497 580610922348376061890123)
        ·
          refine ⟨870916383522564092835185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580610922348376061890123 870916383522564092835185)
          ·
            refine ⟨653187287641923069626389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870916383522564092835185 653187287641923069626389)
            ·
              refine ⟨30618154108215143888737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 653187287641923069626389 30618154108215143888737)
              ·
                rfl

theorem cell19_301870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_301870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301870 prefixEnd_301870 := by exact prefixLift 301870
  have htrace : WordTrace (prefixWord ++ tailWord_301870) baseStart_301870 baseEnd_301870 := by
    simpa [prefixWord, tailWord_301870, baseEnd_301870] using wordTrace_append hprefix tailTrace_301870
  have hstable : (prefixWord ++ tailWord_301870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301870).length < 2 ^ (prefixWord ++ tailWord_301870).sum := by decide
  have hdescent : baseEnd_301870 < baseStart_301870 := by decide
  rcases family_descends (prefixWord ++ tailWord_301870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301908 : List Nat := [2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_301908 : Nat := 118140960795 + 301908 * 2 ^ 59
def prefixEnd_301908 : Nat := 4983230072969 + 3 ^ 40 * 301908 * 2
def baseEnd_301908 : Nat := 91866025148272602821663

theorem tailTrace_301908 : CollatzResearch.WordTrace tailWord_301908 prefixEnd_301908 91866025148272602821663 := by
  unfold tailWord_301908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5505744695123176313233189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7340992926830901750977585 5505744695123176313233189)
  ·
    refine ⟨1032327130335595558731223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5505744695123176313233189 1032327130335595558731223)
    ·
      refine ⟨1548490695503393338096835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1032327130335595558731223 1548490695503393338096835)
      ·
        refine ⟨2322736043255090007145253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548490695503393338096835 2322736043255090007145253)
        ·
          refine ⟨435513008110329376339735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2322736043255090007145253 435513008110329376339735)
          ·
            refine ⟨653269512165494064509603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435513008110329376339735 653269512165494064509603)
            ·
              refine ⟨979904268248241096764405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653269512165494064509603 979904268248241096764405)
              ·
                refine ⟨91866025148272602821663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 979904268248241096764405 91866025148272602821663)
                ·
                  rfl

theorem cell19_301908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_301908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301908 prefixEnd_301908 := by exact prefixLift 301908
  have htrace : WordTrace (prefixWord ++ tailWord_301908) baseStart_301908 baseEnd_301908 := by
    simpa [prefixWord, tailWord_301908, baseEnd_301908] using wordTrace_append hprefix tailTrace_301908
  have hstable : (prefixWord ++ tailWord_301908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301908).length < 2 ^ (prefixWord ++ tailWord_301908).sum := by decide
  have hdescent : baseEnd_301908 < baseStart_301908 := by decide
  rcases family_descends (prefixWord ++ tailWord_301908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301931 : List Nat := [1, 1, 1, 1, 2, 2, 11]
def baseStart_301931 : Nat := 118140960795 + 301931 * 2 ^ 59
def prefixEnd_301931 : Nat := 4983230072969 + 3 ^ 40 * 301931 * 2
def baseEnd_301931 : Nat := 30624341233138454770163

theorem tailTrace_301931 : CollatzResearch.WordTrace tailWord_301931 prefixEnd_301931 30624341233138454770163 := by
  unfold tailWord_301931
  simp only [CollatzResearch.WordTrace]
  refine ⟨11012328269163027554553647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7341552179442018369702431 11012328269163027554553647)
  ·
    refine ⟨16518492403744541331830471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11012328269163027554553647 16518492403744541331830471)
    ·
      refine ⟨24777738605616811997745707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16518492403744541331830471 24777738605616811997745707)
      ·
        refine ⟨37166607908425217996618561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24777738605616811997745707 37166607908425217996618561)
        ·
          refine ⟨27874955931318913497463921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37166607908425217996618561 27874955931318913497463921)
          ·
            refine ⟨20906216948489185123097941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27874955931318913497463921 20906216948489185123097941)
            ·
              refine ⟨30624341233138454770163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20906216948489185123097941 30624341233138454770163)
              ·
                rfl

theorem cell19_301931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_301931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301931 prefixEnd_301931 := by exact prefixLift 301931
  have htrace : WordTrace (prefixWord ++ tailWord_301931) baseStart_301931 baseEnd_301931 := by
    simpa [prefixWord, tailWord_301931, baseEnd_301931] using wordTrace_append hprefix tailTrace_301931
  have hstable : (prefixWord ++ tailWord_301931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301931).length < 2 ^ (prefixWord ++ tailWord_301931).sum := by decide
  have hdescent : baseEnd_301931 < baseStart_301931 := by decide
  rcases family_descends (prefixWord ++ tailWord_301931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301986 : List Nat := [3, 3, 1, 2, 2, 8]
def baseStart_301986 : Nat := 118140960795 + 301986 * 2 ^ 59
def prefixEnd_301986 : Nat := 4983230072969 + 3 ^ 40 * 301986 * 2
def baseEnd_301986 : Nat := 10209973262799059232013

theorem tailTrace_301986 : CollatzResearch.WordTrace tailWord_301986 prefixEnd_301986 10209973262799059232013 := by
  unfold tailWord_301986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753583570990942986951453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7342889522642514631870541 2753583570990942986951453)
  ·
    refine ⟨1032593839121603620106795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2753583570990942986951453 1032593839121603620106795)
    ·
      refine ⟨1548890758682405430160193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1032593839121603620106795 1548890758682405430160193)
      ·
        refine ⟨1161668069011804072620145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1548890758682405430160193 1161668069011804072620145)
        ·
          refine ⟨871251051758853054465109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161668069011804072620145 871251051758853054465109)
          ·
            refine ⟨10209973262799059232013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 871251051758853054465109 10209973262799059232013)
            ·
              rfl

theorem cell19_301986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_301986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_301986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_301986 prefixEnd_301986 := by exact prefixLift 301986
  have htrace : WordTrace (prefixWord ++ tailWord_301986) baseStart_301986 baseEnd_301986 := by
    simpa [prefixWord, tailWord_301986, baseEnd_301986] using wordTrace_append hprefix tailTrace_301986
  have hstable : (prefixWord ++ tailWord_301986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301986).length < 2 ^ (prefixWord ++ tailWord_301986).sum := by decide
  have hdescent : baseEnd_301986 < baseStart_301986 := by decide
  rcases family_descends (prefixWord ++ tailWord_301986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302001 : List Nat := [1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_302001 : Nat := 118140960795 + 302001 * 2 ^ 59
def prefixEnd_302001 : Nat := 4983230072969 + 3 ^ 40 * 302001 * 2
def baseEnd_302001 : Nat := 91894323637675942754743

theorem tailTrace_302001 : CollatzResearch.WordTrace tailWord_302001 prefixEnd_302001 91894323637675942754743 := by
  unfold tailWord_302001
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014881378909429509601857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7343254252606286339734571 11014881378909429509601857)
  ·
    refine ⟨8261161034182072132201393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11014881378909429509601857 8261161034182072132201393)
    ·
      refine ⟨6195870775636554099151045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8261161034182072132201393 6195870775636554099151045)
      ·
        refine ⟨1161725770431853893590821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6195870775636554099151045 1161725770431853893590821)
        ·
          refine ⟨217823581955972605048279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1161725770431853893590821 217823581955972605048279)
          ·
            refine ⟨326735372933958907572419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217823581955972605048279 326735372933958907572419)
            ·
              refine ⟨490103059400938361358629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326735372933958907572419 490103059400938361358629)
              ·
                refine ⟨91894323637675942754743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490103059400938361358629 91894323637675942754743)
                ·
                  rfl

theorem cell19_302001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_302001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302001 prefixEnd_302001 := by exact prefixLift 302001
  have htrace : WordTrace (prefixWord ++ tailWord_302001) baseStart_302001 baseEnd_302001 := by
    simpa [prefixWord, tailWord_302001, baseEnd_302001] using wordTrace_append hprefix tailTrace_302001
  have hstable : (prefixWord ++ tailWord_302001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302001).length < 2 ^ (prefixWord ++ tailWord_302001).sum := by decide
  have hdescent : baseEnd_302001 < baseStart_302001 := by decide
  rcases family_descends (prefixWord ++ tailWord_302001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302064 : List Nat := [2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_302064 : Nat := 118140960795 + 302064 * 2 ^ 59
def prefixEnd_302064 : Nat := 4983230072969 + 3 ^ 40 * 302064 * 2
def baseEnd_302064 : Nat := 91913493582110463354571

theorem tailTrace_302064 : CollatzResearch.WordTrace tailWord_302064 prefixEnd_302064 91913493582110463354571 := by
  unfold tailWord_302064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508589588840595634572623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7344786118454127512763497 5508589588840595634572623)
  ·
    refine ⟨8262884383260893451858935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5508589588840595634572623 8262884383260893451858935)
    ·
      refine ⟨12394326574891340177788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8262884383260893451858935 12394326574891340177788403)
      ·
        refine ⟨18591489862337010266682605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12394326574891340177788403 18591489862337010266682605)
        ·
          refine ⟨6971808698376378850005977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18591489862337010266682605 6971808698376378850005977)
          ·
            refine ⟨5228856523782284137504483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6971808698376378850005977 5228856523782284137504483)
            ·
              refine ⟨7843284785673426206256725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228856523782284137504483 7843284785673426206256725)
              ·
                refine ⟨91913493582110463354571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7843284785673426206256725 91913493582110463354571)
                ·
                  rfl

theorem cell19_302064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_302064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302064 prefixEnd_302064 := by exact prefixLift 302064
  have htrace : WordTrace (prefixWord ++ tailWord_302064) baseStart_302064 baseEnd_302064 := by
    simpa [prefixWord, tailWord_302064, baseEnd_302064] using wordTrace_append hprefix tailTrace_302064
  have hstable : (prefixWord ++ tailWord_302064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302064).length < 2 ^ (prefixWord ++ tailWord_302064).sum := by decide
  have hdescent : baseEnd_302064 < baseStart_302064 := by decide
  rcases family_descends (prefixWord ++ tailWord_302064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302081 : List Nat := [1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_302081 : Nat := 118140960795 + 302081 * 2 ^ 59
def prefixEnd_302081 : Nat := 4983230072969 + 3 ^ 40 * 302081 * 2
def baseEnd_302081 : Nat := 91918666424259460976747

theorem tailTrace_302081 : CollatzResearch.WordTrace tailWord_302081 prefixEnd_302081 91918666424259460976747 := by
  unfold tailWord_302081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11017799218619603172514097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7345199479079735448342731 11017799218619603172514097)
  ·
    refine ⟨8263349413964702379385573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11017799218619603172514097 8263349413964702379385573)
    ·
      refine ⟨1549378015118381696134795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8263349413964702379385573 1549378015118381696134795)
      ·
        refine ⟨2324067022677572544202193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549378015118381696134795 2324067022677572544202193)
        ·
          refine ⟨1743050267008179408151645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324067022677572544202193 1743050267008179408151645)
          ·
            refine ⟨653643850128067278056867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1743050267008179408151645 653643850128067278056867)
            ·
              refine ⟨980465775192100917085301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653643850128067278056867 980465775192100917085301)
              ·
                refine ⟨91918666424259460976747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 980465775192100917085301 91918666424259460976747)
                ·
                  rfl

theorem cell19_302081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_302081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302081 prefixEnd_302081 := by exact prefixLift 302081
  have htrace : WordTrace (prefixWord ++ tailWord_302081) baseStart_302081 baseEnd_302081 := by
    simpa [prefixWord, tailWord_302081, baseEnd_302081] using wordTrace_append hprefix tailTrace_302081
  have hstable : (prefixWord ++ tailWord_302081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302081).length < 2 ^ (prefixWord ++ tailWord_302081).sum := by decide
  have hdescent : baseEnd_302081 < baseStart_302081 := by decide
  rcases family_descends (prefixWord ++ tailWord_302081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302157 : List Nat := [1, 6, 1, 1, 1, 9]
def baseStart_302157 : Nat := 118140960795 + 302157 * 2 ^ 59
def prefixEnd_302157 : Nat := 4983230072969 + 3 ^ 40 * 302157 * 2
def baseEnd_302157 : Nat := 10215754674612644809739

theorem tailTrace_302157 : CollatzResearch.WordTrace tailWord_302157 prefixEnd_302157 10215754674612644809739 := by
  unfold tailWord_302157
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020571166344268152280725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7347047444229512101520483 11020571166344268152280725)
  ·
    refine ⟨516589273422387569638159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11020571166344268152280725 516589273422387569638159)
    ·
      refine ⟨774883910133581354457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516589273422387569638159 774883910133581354457239)
      ·
        refine ⟨1162325865200372031685859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774883910133581354457239 1162325865200372031685859)
        ·
          refine ⟨1743488797800558047528789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162325865200372031685859 1743488797800558047528789)
          ·
            refine ⟨10215754674612644809739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1743488797800558047528789 10215754674612644809739)
            ·
              rfl

theorem cell19_302157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_302157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302157 prefixEnd_302157 := by exact prefixLift 302157
  have htrace : WordTrace (prefixWord ++ tailWord_302157) baseStart_302157 baseEnd_302157 := by
    simpa [prefixWord, tailWord_302157, baseEnd_302157] using wordTrace_append hprefix tailTrace_302157
  have hstable : (prefixWord ++ tailWord_302157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302157).length < 2 ^ (prefixWord ++ tailWord_302157).sum := by decide
  have hdescent : baseEnd_302157 < baseStart_302157 := by decide
  rcases family_descends (prefixWord ++ tailWord_302157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302250 : List Nat := [3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_302250 : Nat := 118140960795 + 302250 * 2 ^ 59
def prefixEnd_302250 : Nat := 4983230072969 + 3 ^ 40 * 302250 * 2
def baseEnd_302250 : Nat := 91970090560917143220731

theorem tailTrace_302250 : CollatzResearch.WordTrace tailWord_302250 prefixEnd_302250 91970090560917143220731 := by
  unfold tailWord_302250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755990788751836258854051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7349308770004896690277469 2755990788751836258854051)
  ·
    refine ⟨4133986183127754388281077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755990788751836258854051 4133986183127754388281077)
    ·
      refine ⟨387561204668226973901351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4133986183127754388281077 387561204668226973901351)
      ·
        refine ⟨581341807002340460852027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387561204668226973901351 581341807002340460852027)
        ·
          refine ⟨872012710503510691278041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581341807002340460852027 872012710503510691278041)
          ·
            refine ⟨654009532877633018458531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872012710503510691278041 654009532877633018458531)
            ·
              refine ⟨981014299316449527687797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654009532877633018458531 981014299316449527687797)
              ·
                refine ⟨91970090560917143220731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 981014299316449527687797 91970090560917143220731)
                ·
                  rfl

theorem cell19_302250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_302250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302250 prefixEnd_302250 := by exact prefixLift 302250
  have htrace : WordTrace (prefixWord ++ tailWord_302250) baseStart_302250 baseEnd_302250 := by
    simpa [prefixWord, tailWord_302250, baseEnd_302250] using wordTrace_append hprefix tailTrace_302250
  have hstable : (prefixWord ++ tailWord_302250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302250).length < 2 ^ (prefixWord ++ tailWord_302250).sum := by decide
  have hdescent : baseEnd_302250 < baseStart_302250 := by decide
  rcases family_descends (prefixWord ++ tailWord_302250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302290 : List Nat := [3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_302290 : Nat := 118140960795 + 302290 * 2 ^ 59
def prefixEnd_302290 : Nat := 4983230072969 + 3 ^ 40 * 302290 * 2
def baseEnd_302290 : Nat := 91982261954208902331733

theorem tailTrace_302290 : CollatzResearch.WordTrace tailWord_302290 prefixEnd_302290 91982261954208902331733 := by
  unfold tailWord_302290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756355518715607966718081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7350281383241621244581549 2756355518715607966718081)
  ·
    refine ⟨2067266639036705975038561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2756355518715607966718081 2067266639036705975038561)
    ·
      refine ⟨1550449979277529481278921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2067266639036705975038561 1550449979277529481278921)
      ·
        refine ⟨1162837484458147110959191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1550449979277529481278921 1162837484458147110959191)
        ·
          refine ⟨1744256226687220666438787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162837484458147110959191 1744256226687220666438787)
          ·
            refine ⟨2616384340030830999658181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744256226687220666438787 2616384340030830999658181)
            ·
              refine ⟨490572063755780812435909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2616384340030830999658181 490572063755780812435909)
              ·
                refine ⟨91982261954208902331733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490572063755780812435909 91982261954208902331733)
                ·
                  rfl

theorem cell19_302290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_302290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302290 prefixEnd_302290 := by exact prefixLift 302290
  have htrace : WordTrace (prefixWord ++ tailWord_302290) baseStart_302290 baseEnd_302290 := by
    simpa [prefixWord, tailWord_302290, baseEnd_302290] using wordTrace_append hprefix tailTrace_302290
  have hstable : (prefixWord ++ tailWord_302290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302290).length < 2 ^ (prefixWord ++ tailWord_302290).sum := by decide
  have hdescent : baseEnd_302290 < baseStart_302290 := by decide
  rcases family_descends (prefixWord ++ tailWord_302290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302324 : List Nat := [2, 6, 1, 2, 1, 7]
def baseStart_302324 : Nat := 118140960795 + 302324 * 2 ^ 59
def prefixEnd_302324 : Nat := 4983230072969 + 3 ^ 40 * 302324 * 2
def baseEnd_302324 : Nat := 10221400848722988619565

theorem tailTrace_302324 : CollatzResearch.WordTrace tailWord_302324 prefixEnd_302324 10221400848722988619565 := by
  unfold tailWord_302324
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513331078369627836805013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7351108104492837115740017 5513331078369627836805013)
  ·
    refine ⟨258437394298576304850235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5513331078369627836805013 258437394298576304850235)
    ·
      refine ⟨387656091447864457275353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258437394298576304850235 387656091447864457275353)
      ·
        refine ⟨290742068585898342956515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387656091447864457275353 290742068585898342956515)
        ·
          refine ⟨436113102878847514434773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290742068585898342956515 436113102878847514434773)
          ·
            refine ⟨10221400848722988619565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 436113102878847514434773 10221400848722988619565)
            ·
              rfl

theorem cell19_302324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_302324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302324 prefixEnd_302324 := by exact prefixLift 302324
  have htrace : WordTrace (prefixWord ++ tailWord_302324) baseStart_302324 baseEnd_302324 := by
    simpa [prefixWord, tailWord_302324, baseEnd_302324] using wordTrace_append hprefix tailTrace_302324
  have hstable : (prefixWord ++ tailWord_302324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302324).length < 2 ^ (prefixWord ++ tailWord_302324).sum := by decide
  have hdescent : baseEnd_302324 < baseStart_302324 := by decide
  rcases family_descends (prefixWord ++ tailWord_302324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302347 : List Nat := [1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_302347 : Nat := 118140960795 + 302347 * 2 ^ 59
def prefixEnd_302347 : Nat := 4983230072969 + 3 ^ 40 * 302347 * 2
def baseEnd_302347 : Nat := 91999606189649659064911

theorem tailTrace_302347 : CollatzResearch.WordTrace tailWord_302347 prefixEnd_302347 91999606189649659064911 := by
  unfold tailWord_302347
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027501035655930601697295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7351667357103953734464863 11027501035655930601697295)
  ·
    refine ⟨16541251553483895902545943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11027501035655930601697295 16541251553483895902545943)
    ·
      refine ⟨24811877330225843853818915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16541251553483895902545943 24811877330225843853818915)
      ·
        refine ⟨37217815995338765780728373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24811877330225843853818915 37217815995338765780728373)
        ·
          refine ⟨3489170249563009291943285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37217815995338765780728373 3489170249563009291943285)
          ·
            refine ⟨327109710896532121119683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3489170249563009291943285 327109710896532121119683)
            ·
              refine ⟨490664566344798181679525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327109710896532121119683 490664566344798181679525)
              ·
                refine ⟨91999606189649659064911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490664566344798181679525 91999606189649659064911)
                ·
                  rfl

theorem cell19_302347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_302347 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302347 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302347 prefixEnd_302347 := by exact prefixLift 302347
  have htrace : WordTrace (prefixWord ++ tailWord_302347) baseStart_302347 baseEnd_302347 := by
    simpa [prefixWord, tailWord_302347, baseEnd_302347] using wordTrace_append hprefix tailTrace_302347
  have hstable : (prefixWord ++ tailWord_302347).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302347).length < 2 ^ (prefixWord ++ tailWord_302347).sum := by decide
  have hdescent : baseEnd_302347 < baseStart_302347 := by decide
  rcases family_descends (prefixWord ++ tailWord_302347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302387 : List Nat := [1, 1, 1, 2, 5, 3, 6]
def baseStart_302387 : Nat := 118140960795 + 302387 * 2 ^ 59
def prefixEnd_302387 : Nat := 4983230072969 + 3 ^ 40 * 302387 * 2
def baseEnd_302387 : Nat := 30670592527647139391971

theorem tailTrace_302387 : CollatzResearch.WordTrace tailWord_302387 prefixEnd_302387 30670592527647139391971 := by
  unfold tailWord_302387
  simp only [CollatzResearch.WordTrace]
  refine ⟨11028959955511017433153415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7352639970340678288768943 11028959955511017433153415)
  ·
    refine ⟨16543439933266526149730123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11028959955511017433153415 16543439933266526149730123)
    ·
      refine ⟨24815159899899789224595185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16543439933266526149730123 24815159899899789224595185)
      ·
        refine ⟨18611369924924841918446389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24815159899899789224595185 18611369924924841918446389)
        ·
          refine ⟨1744815930461703929854349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18611369924924841918446389 1744815930461703929854349)
          ·
            refine ⟨654305973923138973695381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1744815930461703929854349 654305973923138973695381)
            ·
              refine ⟨30670592527647139391971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 654305973923138973695381 30670592527647139391971)
              ·
                rfl

theorem cell19_302387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_302387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302387 prefixEnd_302387 := by exact prefixLift 302387
  have htrace : WordTrace (prefixWord ++ tailWord_302387) baseStart_302387 baseEnd_302387 := by
    simpa [prefixWord, tailWord_302387, baseEnd_302387] using wordTrace_append hprefix tailTrace_302387
  have hstable : (prefixWord ++ tailWord_302387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302387).length < 2 ^ (prefixWord ++ tailWord_302387).sum := by decide
  have hdescent : baseEnd_302387 < baseStart_302387 := by decide
  rcases family_descends (prefixWord ++ tailWord_302387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302421 : List Nat := [1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_302421 : Nat := 118140960795 + 302421 * 2 ^ 59
def prefixEnd_302421 : Nat := 4983230072969 + 3 ^ 40 * 302421 * 2
def baseEnd_302421 : Nat := 92022123267239413420265

theorem tailTrace_302421 : CollatzResearch.WordTrace tailWord_302421 prefixEnd_302421 92022123267239413420265 := by
  unfold tailWord_302421
  simp only [CollatzResearch.WordTrace]
  refine ⟨11030200037387841239891117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7353466691591894159927411 11030200037387841239891117)
  ·
    refine ⟨4136325014020440464959169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11030200037387841239891117 4136325014020440464959169)
    ·
      refine ⟨3102243760515330348719377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4136325014020440464959169 3102243760515330348719377)
      ·
        refine ⟨2326682820386497761539533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3102243760515330348719377 2326682820386497761539533)
        ·
          refine ⟨872506057644936660577325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2326682820386497761539533 872506057644936660577325)
          ·
            refine ⟨327189771616851247716497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872506057644936660577325 327189771616851247716497)
            ·
              refine ⟨245392328712638435787373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327189771616851247716497 245392328712638435787373)
              ·
                refine ⟨92022123267239413420265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245392328712638435787373 92022123267239413420265)
                ·
                  rfl

theorem cell19_302421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_302421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302421 prefixEnd_302421 := by exact prefixLift 302421
  have htrace : WordTrace (prefixWord ++ tailWord_302421) baseStart_302421 baseEnd_302421 := by
    simpa [prefixWord, tailWord_302421, baseEnd_302421] using wordTrace_append hprefix tailTrace_302421
  have hstable : (prefixWord ++ tailWord_302421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302421).length < 2 ^ (prefixWord ++ tailWord_302421).sum := by decide
  have hdescent : baseEnd_302421 < baseStart_302421 := by decide
  rcases family_descends (prefixWord ++ tailWord_302421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302423 : List Nat := [1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_302423 : Nat := 118140960795 + 302423 * 2 ^ 59
def prefixEnd_302423 : Nat := 4983230072969 + 3 ^ 40 * 302423 * 2
def baseEnd_302423 : Nat := 92022731836904001375815

theorem tailTrace_302423 : CollatzResearch.WordTrace tailWord_302423 prefixEnd_302423 92022731836904001375815 := by
  unfold tailWord_302423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11030272983380595581463923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7353515322253730387642615 11030272983380595581463923)
  ·
    refine ⟨16545409475070893372195885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11030272983380595581463923 16545409475070893372195885)
    ·
      refine ⟨6204528553151585014573457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16545409475070893372195885 6204528553151585014573457)
      ·
        refine ⟨4653396414863688760930093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6204528553151585014573457 4653396414863688760930093)
        ·
          refine ⟨1745023655573883285348785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4653396414863688760930093 1745023655573883285348785)
          ·
            refine ⟨1308767741680412464011589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1745023655573883285348785 1308767741680412464011589)
            ·
              refine ⟨245393951565077337002173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1308767741680412464011589 245393951565077337002173)
              ·
                refine ⟨92022731836904001375815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245393951565077337002173 92022731836904001375815)
                ·
                  rfl

theorem cell19_302423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_302423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302423 prefixEnd_302423 := by exact prefixLift 302423
  have htrace : WordTrace (prefixWord ++ tailWord_302423) baseStart_302423 baseEnd_302423 := by
    simpa [prefixWord, tailWord_302423, baseEnd_302423] using wordTrace_append hprefix tailTrace_302423
  have hstable : (prefixWord ++ tailWord_302423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302423).length < 2 ^ (prefixWord ++ tailWord_302423).sum := by decide
  have hdescent : baseEnd_302423 < baseStart_302423 := by decide
  rcases family_descends (prefixWord ++ tailWord_302423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302440 : List Nat := [2, 1, 4, 2, 4, 1, 5]
def baseStart_302440 : Nat := 118140960795 + 302440 * 2 ^ 59
def prefixEnd_302440 : Nat := 4983230072969 + 3 ^ 40 * 302440 * 2
def baseEnd_302440 : Nat := 30675968226350999665997

theorem tailTrace_302440 : CollatzResearch.WordTrace tailWord_302440 prefixEnd_302440 30675968226350999665997 := by
  unfold tailWord_302440
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515446512159503742416387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7353928682879338323221849 5515446512159503742416387)
  ·
    refine ⟨8273169768239255613624581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5515446512159503742416387 8273169768239255613624581)
    ·
      refine ⟨1551219331544860427554609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8273169768239255613624581 1551219331544860427554609)
      ·
        refine ⟨1163414498658645320665957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1551219331544860427554609 1163414498658645320665957)
        ·
          refine ⟨218140218498495997624867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1163414498658645320665957 218140218498495997624867)
          ·
            refine ⟨327210327747743996437301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218140218498495997624867 327210327747743996437301)
            ·
              refine ⟨30675968226350999665997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 327210327747743996437301 30675968226350999665997)
              ·
                rfl

theorem cell19_302440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_302440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302440 prefixEnd_302440 := by exact prefixLift 302440
  have htrace : WordTrace (prefixWord ++ tailWord_302440) baseStart_302440 baseEnd_302440 := by
    simpa [prefixWord, tailWord_302440, baseEnd_302440] using wordTrace_append hprefix tailTrace_302440
  have hstable : (prefixWord ++ tailWord_302440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302440).length < 2 ^ (prefixWord ++ tailWord_302440).sum := by decide
  have hdescent : baseEnd_302440 < baseStart_302440 := by decide
  rcases family_descends (prefixWord ++ tailWord_302440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302444 : List Nat := [2, 2, 1, 1, 5, 1, 7]
def baseStart_302444 : Nat := 118140960795 + 302444 * 2 ^ 59
def prefixEnd_302444 : Nat := 4983230072969 + 3 ^ 40 * 302444 * 2
def baseEnd_302444 : Nat := 30676373939460724969697

theorem tailTrace_302444 : CollatzResearch.WordTrace tailWord_302444 prefixEnd_302444 30676373939460724969697 := by
  unfold tailWord_302444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515519458152258083989193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7354025944203010778652257 5515519458152258083989193)
  ·
    refine ⟨4136639593614193562991895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5515519458152258083989193 4136639593614193562991895)
    ·
      refine ⟨6204959390421290344487843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4136639593614193562991895 6204959390421290344487843)
      ·
        refine ⟨9307439085631935516731765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204959390421290344487843 9307439085631935516731765)
        ·
          refine ⟨872572414277993954693603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9307439085631935516731765 872572414277993954693603)
          ·
            refine ⟨1308858621416990932040405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872572414277993954693603 1308858621416990932040405)
            ·
              refine ⟨30676373939460724969697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1308858621416990932040405 30676373939460724969697)
              ·
                rfl

theorem cell19_302444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_302444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302444 prefixEnd_302444 := by exact prefixLift 302444
  have htrace : WordTrace (prefixWord ++ tailWord_302444) baseStart_302444 baseEnd_302444 := by
    simpa [prefixWord, tailWord_302444, baseEnd_302444] using wordTrace_append hprefix tailTrace_302444
  have hstable : (prefixWord ++ tailWord_302444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302444).length < 2 ^ (prefixWord ++ tailWord_302444).sum := by decide
  have hdescent : baseEnd_302444 < baseStart_302444 := by decide
  rcases family_descends (prefixWord ++ tailWord_302444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302520 : List Nat := [2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_302520 : Nat := 118140960795 + 302520 * 2 ^ 59
def prefixEnd_302520 : Nat := 4983230072969 + 3 ^ 40 * 302520 * 2
def baseEnd_302520 : Nat := 92052247465636517219995

theorem tailTrace_302520 : CollatzResearch.WordTrace tailWord_302520 prefixEnd_302520 92052247465636517219995 := by
  unfold tailWord_302520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516905432014590573872507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7355873909352787431830009 5516905432014590573872507)
  ·
    refine ⟨8275358148021885860808761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5516905432014590573872507 8275358148021885860808761)
    ·
      refine ⟨6206518611016414395606571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8275358148021885860808761 6206518611016414395606571)
      ·
        refine ⟨9309777916524621593409857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206518611016414395606571 9309777916524621593409857)
        ·
          refine ⟨6982333437393466195057393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9309777916524621593409857 6982333437393466195057393)
          ·
            refine ⟨5236750078045099646293045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6982333437393466195057393 5236750078045099646293045)
            ·
              refine ⟨490945319816728091839973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5236750078045099646293045 490945319816728091839973)
              ·
                refine ⟨92052247465636517219995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490945319816728091839973 92052247465636517219995)
                ·
                  rfl

theorem cell19_302520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_302520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302520 prefixEnd_302520 := by exact prefixLift 302520
  have htrace : WordTrace (prefixWord ++ tailWord_302520) baseStart_302520 baseEnd_302520 := by
    simpa [prefixWord, tailWord_302520, baseEnd_302520] using wordTrace_append hprefix tailTrace_302520
  have hstable : (prefixWord ++ tailWord_302520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302520).length < 2 ^ (prefixWord ++ tailWord_302520).sum := by decide
  have hdescent : baseEnd_302520 < baseStart_302520 := by decide
  rcases family_descends (prefixWord ++ tailWord_302520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302685 : List Nat := [1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_302685 : Nat := 118140960795 + 302685 * 2 ^ 59
def prefixEnd_302685 : Nat := 4983230072969 + 3 ^ 40 * 302685 * 2
def baseEnd_302685 : Nat := 92102454462965023552879

theorem tailTrace_302685 : CollatzResearch.WordTrace tailWord_302685 prefixEnd_302685 92102454462965023552879 := by
  unfold tailWord_302685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039828908431414327501509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7359885938954276218334339 11039828908431414327501509)
  ·
    refine ⟨2069967920330890186406533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11039828908431414327501509 2069967920330890186406533)
    ·
      refine ⟨388118985062041909951225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2069967920330890186406533 388118985062041909951225)
      ·
        refine ⟨291089238796531432463419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388118985062041909951225 291089238796531432463419)
        ·
          refine ⟨436633858194797148695129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291089238796531432463419 436633858194797148695129)
          ·
            refine ⟨327475393646097861521347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436633858194797148695129 327475393646097861521347)
            ·
              refine ⟨491213090469146792282021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327475393646097861521347 491213090469146792282021)
              ·
                refine ⟨92102454462965023552879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 491213090469146792282021 92102454462965023552879)
                ·
                  rfl

theorem cell19_302685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_302685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302685 prefixEnd_302685 := by exact prefixLift 302685
  have htrace : WordTrace (prefixWord ++ tailWord_302685) baseStart_302685 baseEnd_302685 := by
    simpa [prefixWord, tailWord_302685, baseEnd_302685] using wordTrace_append hprefix tailTrace_302685
  have hstable : (prefixWord ++ tailWord_302685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302685).length < 2 ^ (prefixWord ++ tailWord_302685).sum := by decide
  have hdescent : baseEnd_302685 < baseStart_302685 := by decide
  rcases family_descends (prefixWord ++ tailWord_302685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302691 : List Nat := [1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_302691 : Nat := 118140960795 + 302691 * 2 ^ 59
def prefixEnd_302691 : Nat := 4983230072969 + 3 ^ 40 * 302691 * 2
def baseEnd_302691 : Nat := 92104280171958787419529

theorem tailTrace_302691 : CollatzResearch.WordTrace tailWord_302691 prefixEnd_302691 92104280171958787419529 := by
  unfold tailWord_302691
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040047746409677352219927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7360031830939784901479951 11040047746409677352219927)
  ·
    refine ⟨16560071619614516028329891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11040047746409677352219927 16560071619614516028329891)
    ·
      refine ⟨24840107429421774042494837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16560071619614516028329891 24840107429421774042494837)
      ·
        refine ⟨2328760071508291316483891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24840107429421774042494837 2328760071508291316483891)
        ·
          refine ⟨3493140107262436974725837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328760071508291316483891 3493140107262436974725837)
          ·
            refine ⟨1309927540223413865522189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3493140107262436974725837 1309927540223413865522189)
            ·
              refine ⟨491222827583780199570821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309927540223413865522189 491222827583780199570821)
              ·
                refine ⟨92104280171958787419529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 491222827583780199570821 92104280171958787419529)
                ·
                  rfl

theorem cell19_302691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_302691 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302691 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302691 prefixEnd_302691 := by exact prefixLift 302691
  have htrace : WordTrace (prefixWord ++ tailWord_302691) baseStart_302691 baseEnd_302691 := by
    simpa [prefixWord, tailWord_302691, baseEnd_302691] using wordTrace_append hprefix tailTrace_302691
  have hstable : (prefixWord ++ tailWord_302691).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302691).length < 2 ^ (prefixWord ++ tailWord_302691).sum := by decide
  have hdescent : baseEnd_302691 < baseStart_302691 := by decide
  rcases family_descends (prefixWord ++ tailWord_302691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302731 : List Nat := [1, 1, 1, 1, 4, 1, 10]
def baseStart_302731 : Nat := 118140960795 + 302731 * 2 ^ 59
def prefixEnd_302731 : Nat := 4983230072969 + 3 ^ 40 * 302731 * 2
def baseEnd_302731 : Nat := 30705483855083515510177

theorem tailTrace_302731 : CollatzResearch.WordTrace tailWord_302731 prefixEnd_302731 30705483855083515510177 := by
  unfold tailWord_302731
  simp only [CollatzResearch.WordTrace]
  refine ⟨11041506666264764183676047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7361004444176509455784031 11041506666264764183676047)
  ·
    refine ⟨16562259999397146275514071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11041506666264764183676047 16562259999397146275514071)
    ·
      refine ⟨24843389999095719413271107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16562259999397146275514071 24843389999095719413271107)
      ·
        refine ⟨37265084998643579119906661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24843389999095719413271107 37265084998643579119906661)
        ·
          refine ⟨6987203437245671084982499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37265084998643579119906661 6987203437245671084982499)
          ·
            refine ⟨10480805155868506627473749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6987203437245671084982499 10480805155868506627473749)
            ·
              refine ⟨30705483855083515510177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10480805155868506627473749 30705483855083515510177)
              ·
                rfl

theorem cell19_302731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_302731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302731 prefixEnd_302731 := by exact prefixLift 302731
  have htrace : WordTrace (prefixWord ++ tailWord_302731) baseStart_302731 baseEnd_302731 := by
    simpa [prefixWord, tailWord_302731, baseEnd_302731] using wordTrace_append hprefix tailTrace_302731
  have hstable : (prefixWord ++ tailWord_302731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302731).length < 2 ^ (prefixWord ++ tailWord_302731).sum := by decide
  have hdescent : baseEnd_302731 < baseStart_302731 := by decide
  rcases family_descends (prefixWord ++ tailWord_302731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302824 : List Nat := [2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_302824 : Nat := 118140960795 + 302824 * 2 ^ 59
def prefixEnd_302824 : Nat := 4983230072969 + 3 ^ 40 * 302824 * 2
def baseEnd_302824 : Nat := 92144750054653886463611

theorem tailTrace_302824 : CollatzResearch.WordTrace tailWord_302824 prefixEnd_302824 92144750054653886463611 := by
  unfold tailWord_302824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522449327463920533405763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7363265769951894044541017 5522449327463920533405763)
  ·
    refine ⟨8283673991195880800108645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5522449327463920533405763 8283673991195880800108645)
    ·
      refine ⟨1553188873349227650020371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8283673991195880800108645 1553188873349227650020371)
      ·
        refine ⟨2329783310023841475030557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553188873349227650020371 2329783310023841475030557)
        ·
          refine ⟨873668741258940553136459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2329783310023841475030557 873668741258940553136459)
          ·
            refine ⟨1310503111888410829704689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873668741258940553136459 1310503111888410829704689)
            ·
              refine ⟨982877333916308122278517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310503111888410829704689 982877333916308122278517)
              ·
                refine ⟨92144750054653886463611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 982877333916308122278517 92144750054653886463611)
                ·
                  rfl

theorem cell19_302824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_302824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302824 prefixEnd_302824 := by exact prefixLift 302824
  have htrace : WordTrace (prefixWord ++ tailWord_302824) baseStart_302824 baseEnd_302824 := by
    simpa [prefixWord, tailWord_302824, baseEnd_302824] using wordTrace_append hprefix tailTrace_302824
  have hstable : (prefixWord ++ tailWord_302824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302824).length < 2 ^ (prefixWord ++ tailWord_302824).sum := by decide
  have hdescent : baseEnd_302824 < baseStart_302824 := by decide
  rcases family_descends (prefixWord ++ tailWord_302824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302862 : List Nat := [4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_302862 : Nat := 118140960795 + 302862 * 2 ^ 59
def prefixEnd_302862 : Nat := 4983230072969 + 3 ^ 40 * 302862 * 2
def baseEnd_302862 : Nat := 92156312878281057619063

theorem tailTrace_302862 : CollatzResearch.WordTrace tailWord_302862 prefixEnd_302862 92156312878281057619063 := by
  unfold tailWord_302862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380785578598771694586855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7364189752526782371129893 1380785578598771694586855)
  ·
    refine ⟨2071178367898157541880283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380785578598771694586855 2071178367898157541880283)
    ·
      refine ⟨3106767551847236312820425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071178367898157541880283 3106767551847236312820425)
      ·
        refine ⟨2330075663885427234615319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3106767551847236312820425 2330075663885427234615319)
        ·
          refine ⟨3495113495828140851922979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330075663885427234615319 3495113495828140851922979)
          ·
            refine ⟨5242670243742211277884469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495113495828140851922979 5242670243742211277884469)
            ·
              refine ⟨491500335350832307301669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5242670243742211277884469 491500335350832307301669)
              ·
                refine ⟨92156312878281057619063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 491500335350832307301669 92156312878281057619063)
                ·
                  rfl

theorem cell19_302862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_302862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302862 prefixEnd_302862 := by exact prefixLift 302862
  have htrace : WordTrace (prefixWord ++ tailWord_302862) baseStart_302862 baseEnd_302862 := by
    simpa [prefixWord, tailWord_302862, baseEnd_302862] using wordTrace_append hprefix tailTrace_302862
  have hstable : (prefixWord ++ tailWord_302862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302862).length < 2 ^ (prefixWord ++ tailWord_302862).sum := by decide
  have hdescent : baseEnd_302862 < baseStart_302862 := by decide
  rcases family_descends (prefixWord ++ tailWord_302862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302883 : List Nat := [1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_302883 : Nat := 118140960795 + 302883 * 2 ^ 59
def prefixEnd_302883 : Nat := 4983230072969 + 3 ^ 40 * 302883 * 2
def baseEnd_302883 : Nat := 92162702859759231152339

theorem tailTrace_302883 : CollatzResearch.WordTrace tailWord_302883 prefixEnd_302883 92162702859759231152339 := by
  unfold tailWord_302883
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047050561714094143209303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7364700374476062762139535 11047050561714094143209303)
  ·
    refine ⟨16570575842571141214813955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11047050561714094143209303 16570575842571141214813955)
    ·
      refine ⟨24855863763856711822220933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16570575842571141214813955 24855863763856711822220933)
      ·
        refine ⟨4660474455723133466666425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24855863763856711822220933 4660474455723133466666425)
        ·
          refine ⟨3495355841792350099999819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4660474455723133466666425 3495355841792350099999819)
          ·
            refine ⟨5243033762688525149999729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495355841792350099999819 5243033762688525149999729)
            ·
              refine ⟨3932275322016393862499797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5243033762688525149999729 3932275322016393862499797)
              ·
                refine ⟨92162702859759231152339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3932275322016393862499797 92162702859759231152339)
                ·
                  rfl

theorem cell19_302883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_302883 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302883 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302883 prefixEnd_302883 := by exact prefixLift 302883
  have htrace : WordTrace (prefixWord ++ tailWord_302883) baseStart_302883 baseEnd_302883 := by
    simpa [prefixWord, tailWord_302883, baseEnd_302883] using wordTrace_append hprefix tailTrace_302883
  have hstable : (prefixWord ++ tailWord_302883).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302883).length < 2 ^ (prefixWord ++ tailWord_302883).sum := by decide
  have hdescent : baseEnd_302883 < baseStart_302883 := by decide
  rcases family_descends (prefixWord ++ tailWord_302883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302921 : List Nat := [1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_302921 : Nat := 118140960795 + 302921 * 2 ^ 59
def prefixEnd_302921 : Nat := 4983230072969 + 3 ^ 40 * 302921 * 2
def baseEnd_302921 : Nat := 92174265683386402307791

theorem tailTrace_302921 : CollatzResearch.WordTrace tailWord_302921 prefixEnd_302921 92174265683386402307791 := by
  unfold tailWord_302921
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048436535576426633092617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7365624357050951088728411 11048436535576426633092617)
  ·
    refine ⟨8286327401682319974819463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11048436535576426633092617 8286327401682319974819463)
    ·
      refine ⟨12429491102523479962229195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8286327401682319974819463 12429491102523479962229195)
      ·
        refine ⟨18644236653785219943343793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429491102523479962229195 18644236653785219943343793)
        ·
          refine ⟨13983177490338914957507845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18644236653785219943343793 13983177490338914957507845)
          ·
            refine ⟨2621845779438546554532721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13983177490338914957507845 2621845779438546554532721)
            ·
              refine ⟨1966384334578909915899541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621845779438546554532721 1966384334578909915899541)
              ·
                refine ⟨92174265683386402307791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1966384334578909915899541 92174265683386402307791)
                ·
                  rfl

theorem cell19_302921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_302921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302921 prefixEnd_302921 := by exact prefixLift 302921
  have htrace : WordTrace (prefixWord ++ tailWord_302921) baseStart_302921 baseEnd_302921 := by
    simpa [prefixWord, tailWord_302921, baseEnd_302921] using wordTrace_append hprefix tailTrace_302921
  have hstable : (prefixWord ++ tailWord_302921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302921).length < 2 ^ (prefixWord ++ tailWord_302921).sum := by decide
  have hdescent : baseEnd_302921 < baseStart_302921 := by decide
  rcases family_descends (prefixWord ++ tailWord_302921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302974 : List Nat := [4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_302974 : Nat := 118140960795 + 302974 * 2 ^ 59
def prefixEnd_302974 : Nat := 4983230072969 + 3 ^ 40 * 302974 * 2
def baseEnd_302974 : Nat := 92190392779497983129869

theorem tailTrace_302974 : CollatzResearch.WordTrace tailWord_302974 prefixEnd_302974 92190392779497983129869 := by
  unfold tailWord_302974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381296200548052085596497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7366913069589611123181317 1381296200548052085596497)
  ·
    refine ⟨1035972150411039064197373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1381296200548052085596497 1035972150411039064197373)
    ·
      refine ⟨388489556404139649074015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1035972150411039064197373 388489556404139649074015)
      ·
        refine ⟨582734334606209473611023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388489556404139649074015 582734334606209473611023)
        ·
          refine ⟨874101501909314210416535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582734334606209473611023 874101501909314210416535)
          ·
            refine ⟨1311152252863971315624803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874101501909314210416535 1311152252863971315624803)
            ·
              refine ⟨1966728379295956973437205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311152252863971315624803 1966728379295956973437205)
              ·
                refine ⟨92190392779497983129869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1966728379295956973437205 92190392779497983129869)
                ·
                  rfl

theorem cell19_302974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_302974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302974 prefixEnd_302974 := by exact prefixLift 302974
  have htrace : WordTrace (prefixWord ++ tailWord_302974) baseStart_302974 baseEnd_302974 := by
    simpa [prefixWord, tailWord_302974, baseEnd_302974] using wordTrace_append hprefix tailTrace_302974
  have hstable : (prefixWord ++ tailWord_302974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302974).length < 2 ^ (prefixWord ++ tailWord_302974).sum := by decide
  have hdescent : baseEnd_302974 < baseStart_302974 := by decide
  rcases family_descends (prefixWord ++ tailWord_302974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302997 : List Nat := [1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_302997 : Nat := 118140960795 + 302997 * 2 ^ 59
def prefixEnd_302997 : Nat := 4983230072969 + 3 ^ 40 * 302997 * 2
def baseEnd_302997 : Nat := 92197391330640744618695

theorem tailTrace_302997 : CollatzResearch.WordTrace tailWord_302997 prefixEnd_302997 92197391330640744618695 := by
  unfold tailWord_302997
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051208483301091612859245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7367472322200727741906163 11051208483301091612859245)
  ·
    refine ⟨4144203181237909354822217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11051208483301091612859245 4144203181237909354822217)
    ·
      refine ⟨3108152385928432016116663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4144203181237909354822217 3108152385928432016116663)
      ·
        refine ⟨4662228578892648024174995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108152385928432016116663 4662228578892648024174995)
        ·
          refine ⟨6993342868338972036262493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662228578892648024174995 6993342868338972036262493)
          ·
            refine ⟨2622503575627114513598435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6993342868338972036262493 2622503575627114513598435)
            ·
              refine ⟨3933755363440671770397653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622503575627114513598435 3933755363440671770397653)
              ·
                refine ⟨92197391330640744618695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3933755363440671770397653 92197391330640744618695)
                ·
                  rfl

theorem cell19_302997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_302997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_302997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_302997 prefixEnd_302997 := by exact prefixLift 302997
  have htrace : WordTrace (prefixWord ++ tailWord_302997) baseStart_302997 baseEnd_302997 := by
    simpa [prefixWord, tailWord_302997, baseEnd_302997] using wordTrace_append hprefix tailTrace_302997
  have hstable : (prefixWord ++ tailWord_302997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302997).length < 2 ^ (prefixWord ++ tailWord_302997).sum := by decide
  have hdescent : baseEnd_302997 < baseStart_302997 := by decide
  rcases family_descends (prefixWord ++ tailWord_302997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303109 : List Nat := [1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_303109 : Nat := 118140960795 + 303109 * 2 ^ 59
def prefixEnd_303109 : Nat := 4983230072969 + 3 ^ 40 * 303109 * 2
def baseEnd_303109 : Nat := 92231471231857670129501

theorem tailTrace_303109 : CollatzResearch.WordTrace tailWord_303109 prefixEnd_303109 92231471231857670129501 := by
  unfold tailWord_303109
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055293458895334740936381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7370195639263556493957587 11055293458895334740936381)
  ·
    refine ⟨4145735047085750527851143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11055293458895334740936381 4145735047085750527851143)
    ·
      refine ⟨6218602570628625791776715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145735047085750527851143 6218602570628625791776715)
      ·
        refine ⟨9327903855942938687665073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6218602570628625791776715 9327903855942938687665073)
        ·
          refine ⟨6995927891957204015748805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9327903855942938687665073 6995927891957204015748805)
          ·
            refine ⟨1311736479741975752952901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6995927891957204015748805 1311736479741975752952901)
            ·
              refine ⟨245950589951620453678669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1311736479741975752952901 245950589951620453678669)
              ·
                refine ⟨92231471231857670129501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245950589951620453678669 92231471231857670129501)
                ·
                  rfl

theorem cell19_303109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_303109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303109 prefixEnd_303109 := by exact prefixLift 303109
  have htrace : WordTrace (prefixWord ++ tailWord_303109) baseStart_303109 baseEnd_303109 := by
    simpa [prefixWord, tailWord_303109, baseEnd_303109] using wordTrace_append hprefix tailTrace_303109
  have hstable : (prefixWord ++ tailWord_303109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303109).length < 2 ^ (prefixWord ++ tailWord_303109).sum := by decide
  have hdescent : baseEnd_303109 < baseStart_303109 := by decide
  rcases family_descends (prefixWord ++ tailWord_303109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303124 : List Nat := [2, 4, 3, 2, 1, 2, 5]
def baseStart_303124 : Nat := 118140960795 + 303124 * 2 ^ 59
def prefixEnd_303124 : Nat := 4983230072969 + 3 ^ 40 * 303124 * 2
def baseEnd_303124 : Nat := 30745345168114026598709

theorem tailTrace_303124 : CollatzResearch.WordTrace tailWord_303124 prefixEnd_303124 30745345168114026598709 := by
  unfold tailWord_303124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527920276920496151366213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7370560369227328201821617 5527920276920496151366213)
  ·
    refine ⟨1036485051922593028381165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5527920276920496151366213 1036485051922593028381165)
    ·
      refine ⟨388681894470972385642937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1036485051922593028381165 388681894470972385642937)
      ·
        refine ⟨291511420853229289232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388681894470972385642937 291511420853229289232203)
        ·
          refine ⟨437267131279843933848305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291511420853229289232203 437267131279843933848305)
          ·
            refine ⟨327950348459882950386229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437267131279843933848305 327950348459882950386229)
            ·
              refine ⟨30745345168114026598709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 327950348459882950386229 30745345168114026598709)
              ·
                rfl

theorem cell19_303124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_303124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303124 prefixEnd_303124 := by exact prefixLift 303124
  have htrace : WordTrace (prefixWord ++ tailWord_303124) baseStart_303124 baseEnd_303124 := by
    simpa [prefixWord, tailWord_303124, baseEnd_303124] using wordTrace_append hprefix tailTrace_303124
  have hstable : (prefixWord ++ tailWord_303124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303124).length < 2 ^ (prefixWord ++ tailWord_303124).sum := by decide
  have hdescent : baseEnd_303124 < baseStart_303124 := by decide
  rcases family_descends (prefixWord ++ tailWord_303124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303130 : List Nat := [3, 1, 1, 3, 1, 3, 7]
def baseStart_303130 : Nat := 118140960795 + 303130 * 2 ^ 59
def prefixEnd_303130 : Nat := 4983230072969 + 3 ^ 40 * 303130 * 2
def baseEnd_303130 : Nat := 30745953737778614554259

theorem tailTrace_303130 : CollatzResearch.WordTrace tailWord_303130 prefixEnd_303130 30745953737778614554259 := by
  unfold tailWord_303130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764014847954813831862711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7370706261212836884967229 2764014847954813831862711)
  ·
    refine ⟨4146022271932220747794067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764014847954813831862711 4146022271932220747794067)
    ·
      refine ⟨6219033407898331121691101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4146022271932220747794067 6219033407898331121691101)
      ·
        refine ⟨2332137527961874170634163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6219033407898331121691101 2332137527961874170634163)
        ·
          refine ⟨3498206291942811255951245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332137527961874170634163 3498206291942811255951245)
          ·
            refine ⟨1311827359478554220981717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3498206291942811255951245 1311827359478554220981717)
            ·
              refine ⟨30745953737778614554259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1311827359478554220981717 30745953737778614554259)
              ·
                rfl

theorem cell19_303130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_303130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303130 prefixEnd_303130 := by exact prefixLift 303130
  have htrace : WordTrace (prefixWord ++ tailWord_303130) baseStart_303130 baseEnd_303130 := by
    simpa [prefixWord, tailWord_303130, baseEnd_303130] using wordTrace_append hprefix tailTrace_303130
  have hstable : (prefixWord ++ tailWord_303130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303130).length < 2 ^ (prefixWord ++ tailWord_303130).sum := by decide
  have hdescent : baseEnd_303130 < baseStart_303130 := by decide
  rcases family_descends (prefixWord ++ tailWord_303130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303168 : List Nat := [2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_303168 : Nat := 118140960795 + 303168 * 2 ^ 59
def prefixEnd_303168 : Nat := 4983230072969 + 3 ^ 40 * 303168 * 2
def baseEnd_303168 : Nat := 92249424036963014818229

theorem tailTrace_303168 : CollatzResearch.WordTrace tailWord_303168 prefixEnd_303168 92249424036963014818229 := by
  unfold tailWord_303168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528722682840793908667079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7371630243787725211556105 5528722682840793908667079)
  ·
    refine ⟨8293084024261190863000619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528722682840793908667079 8293084024261190863000619)
    ·
      refine ⟨12439626036391786294500929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8293084024261190863000619 12439626036391786294500929)
      ·
        refine ⟨9329719527293839720875697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12439626036391786294500929 9329719527293839720875697)
        ·
          refine ⟨6997289645470379790656773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9329719527293839720875697 6997289645470379790656773)
          ·
            refine ⟨1311991808525696210748145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6997289645470379790656773 1311991808525696210748145)
            ·
              refine ⟨983993856394272158061109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311991808525696210748145 983993856394272158061109)
              ·
                refine ⟨92249424036963014818229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 983993856394272158061109 92249424036963014818229)
                ·
                  rfl

theorem cell19_303168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_303168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303168 prefixEnd_303168 := by exact prefixLift 303168
  have htrace : WordTrace (prefixWord ++ tailWord_303168) baseStart_303168 baseEnd_303168 := by
    simpa [prefixWord, tailWord_303168, baseEnd_303168] using wordTrace_append hprefix tailTrace_303168
  have hstable : (prefixWord ++ tailWord_303168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303168).length < 2 ^ (prefixWord ++ tailWord_303168).sum := by decide
  have hdescent : baseEnd_303168 < baseStart_303168 := by decide
  rcases family_descends (prefixWord ++ tailWord_303168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303198 : List Nat := [4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_303198 : Nat := 118140960795 + 303198 * 2 ^ 59
def prefixEnd_303198 : Nat := 4983230072969 + 3 ^ 40 * 303198 * 2
def baseEnd_303198 : Nat := 92258552581931834151481

theorem tailTrace_303198 : CollatzResearch.WordTrace tailWord_303198 prefixEnd_303198 92258552581931834151481 := by
  unfold tailWord_303198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382317444446612867615781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7372359703715268627284165 1382317444446612867615781)
  ·
    refine ⟨259184520833739912677959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1382317444446612867615781 259184520833739912677959)
    ·
      refine ⟨388776781250609869016939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259184520833739912677959 388776781250609869016939)
      ·
        refine ⟨583165171875914803525409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388776781250609869016939 583165171875914803525409)
        ·
          refine ⟨437373878906936102644057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583165171875914803525409 437373878906936102644057)
          ·
            refine ⟨328030409180202076983043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437373878906936102644057 328030409180202076983043)
            ·
              refine ⟨492045613770303115474565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328030409180202076983043 492045613770303115474565)
              ·
                refine ⟨92258552581931834151481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492045613770303115474565 92258552581931834151481)
                ·
                  rfl

theorem cell19_303198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_303198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303198 prefixEnd_303198 := by exact prefixLift 303198
  have htrace : WordTrace (prefixWord ++ tailWord_303198) baseStart_303198 baseEnd_303198 := by
    simpa [prefixWord, tailWord_303198, baseEnd_303198] using wordTrace_append hprefix tailTrace_303198
  have hstable : (prefixWord ++ tailWord_303198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303198).length < 2 ^ (prefixWord ++ tailWord_303198).sum := by decide
  have hdescent : baseEnd_303198 < baseStart_303198 := by decide
  rcases family_descends (prefixWord ++ tailWord_303198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303223 : List Nat := [1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_303223 : Nat := 118140960795 + 303223 * 2 ^ 59
def prefixEnd_303223 : Nat := 4983230072969 + 3 ^ 40 * 303223 * 2
def baseEnd_303223 : Nat := 92266159702739183595857

theorem tailTrace_303223 : CollatzResearch.WordTrace tailWord_303223 prefixEnd_303223 92266159702739183595857 := by
  unfold tailWord_303223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11059451380482332210586323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7372967586988221473724215 11059451380482332210586323)
  ·
    refine ⟨16589177070723498315879485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11059451380482332210586323 16589177070723498315879485)
    ·
      refine ⟨6220941401521311868454807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16589177070723498315879485 6220941401521311868454807)
      ·
        refine ⟨9331412102281967802682211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220941401521311868454807 9331412102281967802682211)
        ·
          refine ⟨13997118153422951704023317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9331412102281967802682211 13997118153422951704023317)
          ·
            refine ⟨656114913441700861126093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13997118153422951704023317 656114913441700861126093)
            ·
              refine ⟨246043092540637822922285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656114913441700861126093 246043092540637822922285)
              ·
                refine ⟨92266159702739183595857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246043092540637822922285 92266159702739183595857)
                ·
                  rfl

theorem cell19_303223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_303223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303223 prefixEnd_303223 := by exact prefixLift 303223
  have htrace : WordTrace (prefixWord ++ tailWord_303223) baseStart_303223 baseEnd_303223 := by
    simpa [prefixWord, tailWord_303223, baseEnd_303223] using wordTrace_append hprefix tailTrace_303223
  have hstable : (prefixWord ++ tailWord_303223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303223).length < 2 ^ (prefixWord ++ tailWord_303223).sum := by decide
  have hdescent : baseEnd_303223 < baseStart_303223 := by decide
  rcases family_descends (prefixWord ++ tailWord_303223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303274 : List Nat := [3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_303274 : Nat := 118140960795 + 303274 * 2 ^ 59
def prefixEnd_303274 : Nat := 4983230072969 + 3 ^ 40 * 303274 * 2
def baseEnd_303274 : Nat := 92281678229186176462385

theorem tailTrace_303274 : CollatzResearch.WordTrace tailWord_303274 prefixEnd_303274 92281678229186176462385 := by
  unfold tailWord_303274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765327875824391980173219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7374207668865045280461917 2765327875824391980173219)
  ·
    refine ⟨4147991813736587970259829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2765327875824391980173219 4147991813736587970259829)
    ·
      refine ⟨388874232537805122211859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4147991813736587970259829 388874232537805122211859)
      ·
        refine ⟨583311348806707683317789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388874232537805122211859 583311348806707683317789)
        ·
          refine ⟨218741755802515381244171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 583311348806707683317789 218741755802515381244171)
          ·
            refine ⟨328112633703773071866257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218741755802515381244171 328112633703773071866257)
            ·
              refine ⟨246084475277829803899693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328112633703773071866257 246084475277829803899693)
              ·
                refine ⟨92281678229186176462385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246084475277829803899693 92281678229186176462385)
                ·
                  rfl

theorem cell19_303274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_303274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303274 prefixEnd_303274 := by exact prefixLift 303274
  have htrace : WordTrace (prefixWord ++ tailWord_303274) baseStart_303274 baseEnd_303274 := by
    simpa [prefixWord, tailWord_303274, baseEnd_303274] using wordTrace_append hprefix tailTrace_303274
  have hstable : (prefixWord ++ tailWord_303274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303274).length < 2 ^ (prefixWord ++ tailWord_303274).sum := by decide
  have hdescent : baseEnd_303274 < baseStart_303274 := by decide
  rcases family_descends (prefixWord ++ tailWord_303274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303282 : List Nat := [3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_303282 : Nat := 118140960795 + 303282 * 2 ^ 59
def prefixEnd_303282 : Nat := 4983230072969 + 3 ^ 40 * 303282 * 2
def baseEnd_303282 : Nat := 92284112507844528284585

theorem tailTrace_303282 : CollatzResearch.WordTrace tailWord_303282 prefixEnd_303282 92284112507844528284585 := by
  unfold tailWord_303282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765400821817146321746025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7374402191512390191322733 2765400821817146321746025)
  ·
    refine ⟨2074050616362859741309519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2765400821817146321746025 2074050616362859741309519)
    ·
      refine ⟨3111075924544289611964279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074050616362859741309519 3111075924544289611964279)
      ·
        refine ⟨4666613886816434417946419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111075924544289611964279 4666613886816434417946419)
        ·
          refine ⟨6999920830224651626919629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666613886816434417946419 6999920830224651626919629)
          ·
            refine ⟨2624970311334244360094861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6999920830224651626919629 2624970311334244360094861)
            ·
              refine ⟨984363866750341635035573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2624970311334244360094861 984363866750341635035573)
              ·
                refine ⟨92284112507844528284585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 984363866750341635035573 92284112507844528284585)
                ·
                  rfl

theorem cell19_303282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_303282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303282 prefixEnd_303282 := by exact prefixLift 303282
  have htrace : WordTrace (prefixWord ++ tailWord_303282) baseStart_303282 baseEnd_303282 := by
    simpa [prefixWord, tailWord_303282, baseEnd_303282] using wordTrace_append hprefix tailTrace_303282
  have hstable : (prefixWord ++ tailWord_303282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303282).length < 2 ^ (prefixWord ++ tailWord_303282).sum := by decide
  have hdescent : baseEnd_303282 < baseStart_303282 := by decide
  rcases family_descends (prefixWord ++ tailWord_303282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303297 : List Nat := [1, 2, 6, 1, 2, 2, 5]
def baseStart_303297 : Nat := 118140960795 + 303297 * 2 ^ 59
def prefixEnd_303297 : Nat := 4983230072969 + 3 ^ 40 * 303297 * 2
def baseEnd_303297 : Nat := 30762892260109645983737

theorem tailTrace_303297 : CollatzResearch.WordTrace tailWord_303297 prefixEnd_303297 30762892260109645983737 := by
  unfold tailWord_303297
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062150382214242848780145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7374766921476161899186763 11062150382214242848780145)
  ·
    refine ⟨8296612786660682136585109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11062150382214242848780145 8296612786660682136585109)
    ·
      refine ⟨388903724374719475152427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8296612786660682136585109 388903724374719475152427)
      ·
        refine ⟨583355586562079212728641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388903724374719475152427 583355586562079212728641)
        ·
          refine ⟨437516689921559409546481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583355586562079212728641 437516689921559409546481)
          ·
            refine ⟨328137517441169557159861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437516689921559409546481 328137517441169557159861)
            ·
              refine ⟨30762892260109645983737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 328137517441169557159861 30762892260109645983737)
              ·
                rfl

theorem cell19_303297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_303297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303297 prefixEnd_303297 := by exact prefixLift 303297
  have htrace : WordTrace (prefixWord ++ tailWord_303297) baseStart_303297 baseEnd_303297 := by
    simpa [prefixWord, tailWord_303297, baseEnd_303297] using wordTrace_append hprefix tailTrace_303297
  have hstable : (prefixWord ++ tailWord_303297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303297).length < 2 ^ (prefixWord ++ tailWord_303297).sum := by decide
  have hdescent : baseEnd_303297 < baseStart_303297 := by decide
  rcases family_descends (prefixWord ++ tailWord_303297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303320 : List Nat := [2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_303320 : Nat := 118140960795 + 303320 * 2 ^ 59
def prefixEnd_303320 : Nat := 4983230072969 + 3 ^ 40 * 303320 * 2
def baseEnd_303320 : Nat := 92295675331471699440037

theorem tailTrace_303320 : CollatzResearch.WordTrace tailWord_303320 prefixEnd_303320 92295675331471699440037 := by
  unfold tailWord_303320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531494630565458888433707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7375326174087278517911609 5531494630565458888433707)
  ·
    refine ⟨8297241945848188332650561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5531494630565458888433707 8297241945848188332650561)
    ·
      refine ⟨6222931459386141249487921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8297241945848188332650561 6222931459386141249487921)
      ·
        refine ⟨4667198594539605937115941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6222931459386141249487921 4667198594539605937115941)
        ·
          refine ⟨875099736476176113209239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4667198594539605937115941 875099736476176113209239)
          ·
            refine ⟨1312649604714264169813859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875099736476176113209239 1312649604714264169813859)
            ·
              refine ⟨1968974407071396254720789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312649604714264169813859 1968974407071396254720789)
              ·
                refine ⟨92295675331471699440037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1968974407071396254720789 92295675331471699440037)
                ·
                  rfl

theorem cell19_303320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_303320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303320 prefixEnd_303320 := by exact prefixLift 303320
  have htrace : WordTrace (prefixWord ++ tailWord_303320) baseStart_303320 baseEnd_303320 := by
    simpa [prefixWord, tailWord_303320, baseEnd_303320] using wordTrace_append hprefix tailTrace_303320
  have hstable : (prefixWord ++ tailWord_303320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303320).length < 2 ^ (prefixWord ++ tailWord_303320).sum := by decide
  have hdescent : baseEnd_303320 < baseStart_303320 := by decide
  rcases family_descends (prefixWord ++ tailWord_303320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303377 : List Nat := [1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_303377 : Nat := 118140960795 + 303377 * 2 ^ 59
def prefixEnd_303377 : Nat := 4983230072969 + 3 ^ 40 * 303377 * 2
def baseEnd_303377 : Nat := 92313019566912456173215

theorem tailTrace_303377 : CollatzResearch.WordTrace tailWord_303377 prefixEnd_303377 92313019566912456173215 := by
  unfold tailWord_303377
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065068221924416511692385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7376712147949611007794923 11065068221924416511692385)
  ·
    refine ⟨8298801166443312383769289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11065068221924416511692385 8298801166443312383769289)
    ·
      refine ⟨6224100874832484287826967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8298801166443312383769289 6224100874832484287826967)
      ·
        refine ⟨9336151312248726431740451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224100874832484287826967 9336151312248726431740451)
        ·
          refine ⟨14004226968373089647610677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336151312248726431740451 14004226968373089647610677)
          ·
            refine ⟨1312896278284977154463501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14004226968373089647610677 1312896278284977154463501)
            ·
              refine ⟨492336104356866432923813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1312896278284977154463501 492336104356866432923813)
              ·
                refine ⟨92313019566912456173215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492336104356866432923813 92313019566912456173215)
                ·
                  rfl

theorem cell19_303377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_303377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303377 prefixEnd_303377 := by exact prefixLift 303377
  have htrace : WordTrace (prefixWord ++ tailWord_303377) baseStart_303377 baseEnd_303377 := by
    simpa [prefixWord, tailWord_303377, baseEnd_303377] using wordTrace_append hprefix tailTrace_303377
  have hstable : (prefixWord ++ tailWord_303377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303377).length < 2 ^ (prefixWord ++ tailWord_303377).sum := by decide
  have hdescent : baseEnd_303377 < baseStart_303377 := by decide
  rcases family_descends (prefixWord ++ tailWord_303377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303390 : List Nat := [4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_303390 : Nat := 118140960795 + 303390 * 2 ^ 59
def prefixEnd_303390 : Nat := 4983230072969 + 3 ^ 40 * 303390 * 2
def baseEnd_303390 : Nat := 92316975269732277884291

theorem tailTrace_303390 : CollatzResearch.WordTrace tailWord_303390 prefixEnd_303390 92316975269732277884291 := by
  unfold tailWord_303390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383192796359664966489453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7377028247251546487943749 1383192796359664966489453)
  ·
    refine ⟨518697298634874362433545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1383192796359664966489453 518697298634874362433545)
    ·
      refine ⟨389022973976155771825159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518697298634874362433545 389022973976155771825159)
      ·
        refine ⟨583534460964233657737739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389022973976155771825159 583534460964233657737739)
        ·
          refine ⟨875301691446350486606609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583534460964233657737739 875301691446350486606609)
          ·
            refine ⟨656476268584762864954957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875301691446350486606609 656476268584762864954957)
            ·
              refine ⟨246178600719286074358109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656476268584762864954957 246178600719286074358109)
              ·
                refine ⟨92316975269732277884291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246178600719286074358109 92316975269732277884291)
                ·
                  rfl

theorem cell19_303390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_303390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303390 prefixEnd_303390 := by exact prefixLift 303390
  have htrace : WordTrace (prefixWord ++ tailWord_303390) baseStart_303390 baseEnd_303390 := by
    simpa [prefixWord, tailWord_303390, baseEnd_303390] using wordTrace_append hprefix tailTrace_303390
  have hstable : (prefixWord ++ tailWord_303390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303390).length < 2 ^ (prefixWord ++ tailWord_303390).sum := by decide
  have hdescent : baseEnd_303390 < baseStart_303390 := by decide
  rcases family_descends (prefixWord ++ tailWord_303390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303472 : List Nat := [2, 1, 1, 1, 4, 5, 5]
def baseStart_303472 : Nat := 118140960795 + 303472 * 2 ^ 59
def prefixEnd_303472 : Nat := 4983230072969 + 3 ^ 40 * 303472 * 2
def baseEnd_303472 : Nat := 30780642208660128020615

theorem tailTrace_303472 : CollatzResearch.WordTrace tailWord_303472 prefixEnd_303472 30780642208660128020615 := by
  unfold tailWord_303472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534266578290123868200335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7379022104386831824267113 5534266578290123868200335)
  ·
    refine ⟨8301399867435185802300503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534266578290123868200335 8301399867435185802300503)
    ·
      refine ⟨12452099801152778703450755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301399867435185802300503 12452099801152778703450755)
      ·
        refine ⟨18678149701729168055176133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12452099801152778703450755 18678149701729168055176133)
        ·
          refine ⟨3502153069074219010345525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18678149701729168055176133 3502153069074219010345525)
          ·
            refine ⟨328326850225708032219893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3502153069074219010345525 328326850225708032219893)
            ·
              refine ⟨30780642208660128020615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 328326850225708032219893 30780642208660128020615)
              ·
                rfl

theorem cell19_303472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_303472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303472 prefixEnd_303472 := by exact prefixLift 303472
  have htrace : WordTrace (prefixWord ++ tailWord_303472) baseStart_303472 baseEnd_303472 := by
    simpa [prefixWord, tailWord_303472, baseEnd_303472] using wordTrace_append hprefix tailTrace_303472
  have hstable : (prefixWord ++ tailWord_303472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303472).length < 2 ^ (prefixWord ++ tailWord_303472).sum := by decide
  have hdescent : baseEnd_303472 < baseStart_303472 := by decide
  rcases family_descends (prefixWord ++ tailWord_303472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303489 : List Nat := [1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_303489 : Nat := 118140960795 + 303489 * 2 ^ 59
def prefixEnd_303489 : Nat := 4983230072969 + 3 ^ 40 * 303489 * 2
def baseEnd_303489 : Nat := 92347099468129381684021

theorem tailTrace_303489 : CollatzResearch.WordTrace tailWord_303489 prefixEnd_303489 92347099468129381684021 := by
  unfold tailWord_303489
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069153197518659639769521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7379435465012439759846347 11069153197518659639769521)
  ·
    refine ⟨8301864898138994729827141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11069153197518659639769521 8301864898138994729827141)
    ·
      refine ⟨1556599668401061511842589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8301864898138994729827141 1556599668401061511842589)
      ·
        refine ⟨583724875650398066940971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1556599668401061511842589 583724875650398066940971)
        ·
          refine ⟨875587313475597100411457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583724875650398066940971 875587313475597100411457)
          ·
            refine ⟨656690485106697825308593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875587313475597100411457 656690485106697825308593)
            ·
              refine ⟨492517863830023368981445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656690485106697825308593 492517863830023368981445)
              ·
                refine ⟨92347099468129381684021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492517863830023368981445 92347099468129381684021)
                ·
                  rfl

theorem cell19_303489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_303489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303489 prefixEnd_303489 := by exact prefixLift 303489
  have htrace : WordTrace (prefixWord ++ tailWord_303489) baseStart_303489 baseEnd_303489 := by
    simpa [prefixWord, tailWord_303489, baseEnd_303489] using wordTrace_append hprefix tailTrace_303489
  have hstable : (prefixWord ++ tailWord_303489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303489).length < 2 ^ (prefixWord ++ tailWord_303489).sum := by decide
  have hdescent : baseEnd_303489 < baseStart_303489 := by decide
  rcases family_descends (prefixWord ++ tailWord_303489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303540 : List Nat := [2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_303540 : Nat := 118140960795 + 303540 * 2 ^ 59
def prefixEnd_303540 : Nat := 4983230072969 + 3 ^ 40 * 303540 * 2
def baseEnd_303540 : Nat := 92362617994576374550549

theorem tailTrace_303540 : CollatzResearch.WordTrace tailWord_303540 prefixEnd_303540 92362617994576374550549 := by
  unfold tailWord_303540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535506660166947674938037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7380675546889263566584049 5535506660166947674938037)
  ·
    refine ⟨518953749390651344525441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5535506660166947674938037 518953749390651344525441)
    ·
      refine ⟨389215312042988508394081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518953749390651344525441 389215312042988508394081)
      ·
        refine ⟨291911484032241381295561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389215312042988508394081 291911484032241381295561)
        ·
          refine ⟨218933613024181035971671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291911484032241381295561 218933613024181035971671)
          ·
            refine ⟨328400419536271553957507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218933613024181035971671 328400419536271553957507)
            ·
              refine ⟨492600629304407330936261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328400419536271553957507 492600629304407330936261)
              ·
                refine ⟨92362617994576374550549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492600629304407330936261 92362617994576374550549)
                ·
                  rfl

theorem cell19_303540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_303540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303540 prefixEnd_303540 := by exact prefixLift 303540
  have htrace : WordTrace (prefixWord ++ tailWord_303540) baseStart_303540 baseEnd_303540 := by
    simpa [prefixWord, tailWord_303540, baseEnd_303540] using wordTrace_append hprefix tailTrace_303540
  have hstable : (prefixWord ++ tailWord_303540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303540).length < 2 ^ (prefixWord ++ tailWord_303540).sum := by decide
  have hdescent : baseEnd_303540 < baseStart_303540 := by decide
  rcases family_descends (prefixWord ++ tailWord_303540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303569 : List Nat := [1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_303569 : Nat := 118140960795 + 303569 * 2 ^ 59
def prefixEnd_303569 : Nat := 4983230072969 + 3 ^ 40 * 303569 * 2
def baseEnd_303569 : Nat := 92371442254712899906025

theorem tailTrace_303569 : CollatzResearch.WordTrace tailWord_303569 prefixEnd_303569 92371442254712899906025 := by
  unfold tailWord_303569
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072071037228833302681761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7381380691485888868454507 11072071037228833302681761)
  ·
    refine ⟨8304053277921624977011321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11072071037228833302681761 8304053277921624977011321)
    ·
      refine ⟨6228039958441218732758491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8304053277921624977011321 6228039958441218732758491)
      ·
        refine ⟨9342059937661828099137737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228039958441218732758491 9342059937661828099137737)
        ·
          refine ⟨7006544953246371074353303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9342059937661828099137737 7006544953246371074353303)
          ·
            refine ⟨10509817429869556611529955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7006544953246371074353303 10509817429869556611529955)
            ·
              refine ⟨15764726144804334917294933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10509817429869556611529955 15764726144804334917294933)
              ·
                refine ⟨92371442254712899906025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15764726144804334917294933 92371442254712899906025)
                ·
                  rfl

theorem cell19_303569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_303569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303569 prefixEnd_303569 := by exact prefixLift 303569
  have htrace : WordTrace (prefixWord ++ tailWord_303569) baseStart_303569 baseEnd_303569 := by
    simpa [prefixWord, tailWord_303569, baseEnd_303569] using wordTrace_append hprefix tailTrace_303569
  have hstable : (prefixWord ++ tailWord_303569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303569).length < 2 ^ (prefixWord ++ tailWord_303569).sum := by decide
  have hdescent : baseEnd_303569 < baseStart_303569 := by decide
  rcases family_descends (prefixWord ++ tailWord_303569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303618 : List Nat := [3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_303618 : Nat := 118140960795 + 303618 * 2 ^ 59
def prefixEnd_303618 : Nat := 4983230072969 + 3 ^ 40 * 303618 * 2
def baseEnd_303618 : Nat := 92386352211495304817003

theorem tailTrace_303618 : CollatzResearch.WordTrace tailWord_303618 prefixEnd_303618 92386352211495304817003 := by
  unfold tailWord_303618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768464553512828667803877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7382572142700876447477005 2768464553512828667803877)
  ·
    refine ⟨519087103783655375213227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2768464553512828667803877 519087103783655375213227)
    ·
      refine ⟨778630655675483062819841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519087103783655375213227 778630655675483062819841)
      ·
        refine ⟨583972991756612297114881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 778630655675483062819841 583972991756612297114881)
        ·
          refine ⟨437979743817459222836161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583972991756612297114881 437979743817459222836161)
          ·
            refine ⟨328484807863094417127121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437979743817459222836161 328484807863094417127121)
            ·
              refine ⟨246363605897320812845341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328484807863094417127121 246363605897320812845341)
              ·
                refine ⟨92386352211495304817003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246363605897320812845341 92386352211495304817003)
                ·
                  rfl

theorem cell19_303618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_303618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303618 prefixEnd_303618 := by exact prefixLift 303618
  have htrace : WordTrace (prefixWord ++ tailWord_303618) baseStart_303618 baseEnd_303618 := by
    simpa [prefixWord, tailWord_303618, baseEnd_303618] using wordTrace_append hprefix tailTrace_303618
  have hstable : (prefixWord ++ tailWord_303618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303618).length < 2 ^ (prefixWord ++ tailWord_303618).sum := by decide
  have hdescent : baseEnd_303618 < baseStart_303618 := by decide
  rcases family_descends (prefixWord ++ tailWord_303618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303620 : List Nat := [2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_303620 : Nat := 118140960795 + 303620 * 2 ^ 59
def prefixEnd_303620 : Nat := 4983230072969 + 3 ^ 40 * 303620 * 2
def baseEnd_303620 : Nat := 92386960781159892772553

theorem tailTrace_303620 : CollatzResearch.WordTrace tailWord_303620 prefixEnd_303620 92386960781159892772553 := by
  unfold tailWord_303620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536965580022034506394157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7382620773362712675192209 5536965580022034506394157)
  ·
    refine ⟨2076362092508262939897809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5536965580022034506394157 2076362092508262939897809)
    ·
      refine ⟨1557271569381197204923357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2076362092508262939897809 1557271569381197204923357)
      ·
        refine ⟨583976838517948951846259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1557271569381197204923357 583976838517948951846259)
        ·
          refine ⟨875965257776923427769389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583976838517948951846259 875965257776923427769389)
          ·
            refine ⟨328486971666346285413521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 875965257776923427769389 328486971666346285413521)
            ·
              refine ⟨246365228749759714060141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328486971666346285413521 246365228749759714060141)
              ·
                refine ⟨92386960781159892772553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246365228749759714060141 92386960781159892772553)
                ·
                  rfl

theorem cell19_303620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_303620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303620 prefixEnd_303620 := by exact prefixLift 303620
  have htrace : WordTrace (prefixWord ++ tailWord_303620) baseStart_303620 baseEnd_303620 := by
    simpa [prefixWord, tailWord_303620, baseEnd_303620] using wordTrace_append hprefix tailTrace_303620
  have hstable : (prefixWord ++ tailWord_303620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303620).length < 2 ^ (prefixWord ++ tailWord_303620).sum := by decide
  have hdescent : baseEnd_303620 < baseStart_303620 := by decide
  rcases family_descends (prefixWord ++ tailWord_303620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303639 : List Nat := [1, 1, 3, 6, 2, 1, 5]
def baseStart_303639 : Nat := 118140960795 + 303639 * 2 ^ 59
def prefixEnd_303639 : Nat := 4983230072969 + 3 ^ 40 * 303639 * 2
def baseEnd_303639 : Nat := 30797580730991159450093

theorem tailTrace_303639 : CollatzResearch.WordTrace tailWord_303639 prefixEnd_303639 30797580730991159450093 := by
  unfold tailWord_303639
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074624146975235257729971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7383082764650156838486647 11074624146975235257729971)
  ·
    refine ⟨16611936220462852886594957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074624146975235257729971 16611936220462852886594957)
    ·
      refine ⟨6229476082673569832473109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16611936220462852886594957 6229476082673569832473109)
      ·
        refine ⟨292006691375323585897177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6229476082673569832473109 292006691375323585897177)
        ·
          refine ⟨219005018531492689422883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292006691375323585897177 219005018531492689422883)
          ·
            refine ⟨328507527797239034134325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219005018531492689422883 328507527797239034134325)
            ·
              refine ⟨30797580730991159450093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 328507527797239034134325 30797580730991159450093)
              ·
                rfl

theorem cell19_303639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_303639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303639 prefixEnd_303639 := by exact prefixLift 303639
  have htrace : WordTrace (prefixWord ++ tailWord_303639) baseStart_303639 baseEnd_303639 := by
    simpa [prefixWord, tailWord_303639, baseEnd_303639] using wordTrace_append hprefix tailTrace_303639
  have hstable : (prefixWord ++ tailWord_303639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303639).length < 2 ^ (prefixWord ++ tailWord_303639).sum := by decide
  have hdescent : baseEnd_303639 < baseStart_303639 := by decide
  rcases family_descends (prefixWord ++ tailWord_303639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303664 : List Nat := [2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_303664 : Nat := 118140960795 + 303664 * 2 ^ 59
def prefixEnd_303664 : Nat := 4983230072969 + 3 ^ 40 * 303664 * 2
def baseEnd_303664 : Nat := 92400349313780827794655

theorem tailTrace_303664 : CollatzResearch.WordTrace tailWord_303664 prefixEnd_303664 92400349313780827794655 := by
  unfold tailWord_303664
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537767985942332263695023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7383690647923109684926697 5537767985942332263695023)
  ·
    refine ⟨8306651978913498395542535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5537767985942332263695023 8306651978913498395542535)
    ·
      refine ⟨12459977968370247593313803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8306651978913498395542535 12459977968370247593313803)
      ·
        refine ⟨18689966952555371389970705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459977968370247593313803 18689966952555371389970705)
        ·
          refine ⟨14017475214416528542478029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18689966952555371389970705 14017475214416528542478029)
          ·
            refine ⟨5256553205406198203429261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14017475214416528542478029 5256553205406198203429261)
            ·
              refine ⟨1971207452027324326285973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5256553205406198203429261 1971207452027324326285973)
              ·
                refine ⟨92400349313780827794655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1971207452027324326285973 92400349313780827794655)
                ·
                  rfl

theorem cell19_303664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_303664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303664 prefixEnd_303664 := by exact prefixLift 303664
  have htrace : WordTrace (prefixWord ++ tailWord_303664) baseStart_303664 baseEnd_303664 := by
    simpa [prefixWord, tailWord_303664, baseEnd_303664] using wordTrace_append hprefix tailTrace_303664
  have hstable : (prefixWord ++ tailWord_303664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303664).length < 2 ^ (prefixWord ++ tailWord_303664).sum := by decide
  have hdescent : baseEnd_303664 < baseStart_303664 := by decide
  rcases family_descends (prefixWord ++ tailWord_303664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303681 : List Nat := [1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_303681 : Nat := 118140960795 + 303681 * 2 ^ 59
def prefixEnd_303681 : Nat := 4983230072969 + 3 ^ 40 * 303681 * 2
def baseEnd_303681 : Nat := 92405522155929825416831

theorem tailTrace_303681 : CollatzResearch.WordTrace tailWord_303681 prefixEnd_303681 92405522155929825416831 := by
  unfold tailWord_303681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076156012823076430758897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7384104008548717620505931 11076156012823076430758897)
  ·
    refine ⟨8307117009617307323069173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11076156012823076430758897 8307117009617307323069173)
    ·
      refine ⟨778792219651622561537735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8307117009617307323069173 778792219651622561537735)
      ·
        refine ⟨1168188329477433842306603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778792219651622561537735 1168188329477433842306603)
        ·
          refine ⟨1752282494216150763459905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168188329477433842306603 1752282494216150763459905)
          ·
            refine ⟨1314211870662113072594929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752282494216150763459905 1314211870662113072594929)
            ·
              refine ⟨985658902996584804446197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314211870662113072594929 985658902996584804446197)
              ·
                refine ⟨92405522155929825416831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 985658902996584804446197 92405522155929825416831)
                ·
                  rfl

theorem cell19_303681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_303681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303681 prefixEnd_303681 := by exact prefixLift 303681
  have htrace : WordTrace (prefixWord ++ tailWord_303681) baseStart_303681 baseEnd_303681 := by
    simpa [prefixWord, tailWord_303681, baseEnd_303681] using wordTrace_append hprefix tailTrace_303681
  have hstable : (prefixWord ++ tailWord_303681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303681).length < 2 ^ (prefixWord ++ tailWord_303681).sum := by decide
  have hdescent : baseEnd_303681 < baseStart_303681 := by decide
  rcases family_descends (prefixWord ++ tailWord_303681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303717 : List Nat := [1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_303717 : Nat := 118140960795 + 303717 * 2 ^ 59
def prefixEnd_303717 : Nat := 4983230072969 + 3 ^ 40 * 303717 * 2
def baseEnd_303717 : Nat := 92416476409892408616733

theorem tailTrace_303717 : CollatzResearch.WordTrace tailWord_303717 prefixEnd_303717 92416476409892408616733 := by
  unfold tailWord_303717
  simp only [CollatzResearch.WordTrace]
  refine ⟨11077469040692654579069405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7384979360461769719379603 11077469040692654579069405)
  ·
    refine ⟨4154050890259745467151027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11077469040692654579069405 4154050890259745467151027)
    ·
      refine ⟨6231076335389618200726541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154050890259745467151027 6231076335389618200726541)
      ·
        refine ⟨2336653625771106825272453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6231076335389618200726541 2336653625771106825272453)
        ·
          refine ⟨438122554832082529738585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2336653625771106825272453 438122554832082529738585)
          ·
            refine ⟨328591916124061897303939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438122554832082529738585 328591916124061897303939)
            ·
              refine ⟨492887874186092845955909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328591916124061897303939 492887874186092845955909)
              ·
                refine ⟨92416476409892408616733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492887874186092845955909 92416476409892408616733)
                ·
                  rfl

theorem cell19_303717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_303717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303717 prefixEnd_303717 := by exact prefixLift 303717
  have htrace : WordTrace (prefixWord ++ tailWord_303717) baseStart_303717 baseEnd_303717 := by
    simpa [prefixWord, tailWord_303717, baseEnd_303717] using wordTrace_append hprefix tailTrace_303717
  have hstable : (prefixWord ++ tailWord_303717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303717).length < 2 ^ (prefixWord ++ tailWord_303717).sum := by decide
  have hdescent : baseEnd_303717 < baseStart_303717 := by decide
  rcases family_descends (prefixWord ++ tailWord_303717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303734 : List Nat := [5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_303734 : Nat := 118140960795 + 303734 * 2 ^ 59
def prefixEnd_303734 : Nat := 4983230072969 + 3 ^ 40 * 303734 * 2
def baseEnd_303734 : Nat := 92421649252041406238909

theorem tailTrace_303734 : CollatzResearch.WordTrace tailWord_303734 prefixEnd_303734 92421649252041406238909 := by
  unfold tailWord_303734
  simp only [CollatzResearch.WordTrace]
  refine ⟨692380567601941655152391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7385392721087377654958837 692380567601941655152391)
  ·
    refine ⟨1038570851402912482728587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692380567601941655152391 1038570851402912482728587)
    ·
      refine ⟨1557856277104368724092881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038570851402912482728587 1557856277104368724092881)
      ·
        refine ⟨1168392207828276543069661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1557856277104368724092881 1168392207828276543069661)
        ·
          refine ⟨438147077935603703651123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168392207828276543069661 438147077935603703651123)
          ·
            refine ⟨657220616903405555476685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438147077935603703651123 657220616903405555476685)
            ·
              refine ⟨246457731338777083303757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657220616903405555476685 246457731338777083303757)
              ·
                refine ⟨92421649252041406238909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246457731338777083303757 92421649252041406238909)
                ·
                  rfl

theorem cell19_303734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_303734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303734 prefixEnd_303734 := by exact prefixLift 303734
  have htrace : WordTrace (prefixWord ++ tailWord_303734) baseStart_303734 baseEnd_303734 := by
    simpa [prefixWord, tailWord_303734, baseEnd_303734] using wordTrace_append hprefix tailTrace_303734
  have hstable : (prefixWord ++ tailWord_303734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303734).length < 2 ^ (prefixWord ++ tailWord_303734).sum := by decide
  have hdescent : baseEnd_303734 < baseStart_303734 := by decide
  rcases family_descends (prefixWord ++ tailWord_303734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303740 : List Nat := [2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_303740 : Nat := 118140960795 + 303740 * 2 ^ 59
def prefixEnd_303740 : Nat := 4983230072969 + 3 ^ 40 * 303740 * 2
def baseEnd_303740 : Nat := 92423474961035170105559

theorem tailTrace_303740 : CollatzResearch.WordTrace tailWord_303740 prefixEnd_303740 92423474961035170105559 := by
  unfold tailWord_303740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539153959804664753578337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7385538613072886338104449 5539153959804664753578337)
  ·
    refine ⟨4154365469853498565183753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5539153959804664753578337 4154365469853498565183753)
    ·
      refine ⟨3115774102390123923887815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4154365469853498565183753 3115774102390123923887815)
      ·
        refine ⟨4673661153585185885831723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115774102390123923887815 4673661153585185885831723)
        ·
          refine ⟨7010491730377778828747585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673661153585185885831723 7010491730377778828747585)
          ·
            refine ⟨5257868797783334121560689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7010491730377778828747585 5257868797783334121560689)
            ·
              refine ⟨3943401598337500591170517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257868797783334121560689 3943401598337500591170517)
              ·
                refine ⟨92423474961035170105559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3943401598337500591170517 92423474961035170105559)
                ·
                  rfl

theorem cell19_303740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_303740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303740 prefixEnd_303740 := by exact prefixLift 303740
  have htrace : WordTrace (prefixWord ++ tailWord_303740) baseStart_303740 baseEnd_303740 := by
    simpa [prefixWord, tailWord_303740, baseEnd_303740] using wordTrace_append hprefix tailTrace_303740
  have hstable : (prefixWord ++ tailWord_303740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303740).length < 2 ^ (prefixWord ++ tailWord_303740).sum := by decide
  have hdescent : baseEnd_303740 < baseStart_303740 := by decide
  rcases family_descends (prefixWord ++ tailWord_303740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303793 : List Nat := [1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_303793 : Nat := 118140960795 + 303793 * 2 ^ 59
def prefixEnd_303793 : Nat := 4983230072969 + 3 ^ 40 * 303793 * 2
def baseEnd_303793 : Nat := 92439602057146750927637

theorem tailTrace_303793 : CollatzResearch.WordTrace tailWord_303793 prefixEnd_303793 92439602057146750927637 := by
  unfold tailWord_303793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080240988417319558836033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7386827325611546372557355 11080240988417319558836033)
  ·
    refine ⟨8310180741312989669127025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11080240988417319558836033 8310180741312989669127025)
    ·
      refine ⟨6232635555984742251845269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8310180741312989669127025 6232635555984742251845269)
      ·
        refine ⟨292154791686784793055247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6232635555984742251845269 292154791686784793055247)
        ·
          refine ⟨438232187530177189582871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292154791686784793055247 438232187530177189582871)
          ·
            refine ⟨657348281295265784374307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438232187530177189582871 657348281295265784374307)
            ·
              refine ⟨986022421942898676561461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657348281295265784374307 986022421942898676561461)
              ·
                refine ⟨92439602057146750927637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 986022421942898676561461 92439602057146750927637)
                ·
                  rfl

theorem cell19_303793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_303793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303793 prefixEnd_303793 := by exact prefixLift 303793
  have htrace : WordTrace (prefixWord ++ tailWord_303793) baseStart_303793 baseEnd_303793 := by
    simpa [prefixWord, tailWord_303793, baseEnd_303793] using wordTrace_append hprefix tailTrace_303793
  have hstable : (prefixWord ++ tailWord_303793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303793).length < 2 ^ (prefixWord ++ tailWord_303793).sum := by decide
  have hdescent : baseEnd_303793 < baseStart_303793 := by decide
  rcases family_descends (prefixWord ++ tailWord_303793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303795 : List Nat := [1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_303795 : Nat := 118140960795 + 303795 * 2 ^ 59
def prefixEnd_303795 : Nat := 4983230072969 + 3 ^ 40 * 303795 * 2
def baseEnd_303795 : Nat := 92440210626811338883187

theorem tailTrace_303795 : CollatzResearch.WordTrace tailWord_303795 prefixEnd_303795 92440210626811338883187 := by
  unfold tailWord_303795
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080313934410073900408839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7386875956273382600272559 11080313934410073900408839)
  ·
    refine ⟨16620470901615110850613259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11080313934410073900408839 16620470901615110850613259)
    ·
      refine ⟨24930706352422666275919889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16620470901615110850613259 24930706352422666275919889)
      ·
        refine ⟨18698029764316999706939917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24930706352422666275919889 18698029764316999706939917)
        ·
          refine ⟨7011761161618874890102469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18698029764316999706939917 7011761161618874890102469)
          ·
            refine ⟨1314705217803539041894213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7011761161618874890102469 1314705217803539041894213)
            ·
              refine ⟨246507228338163570355165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1314705217803539041894213 246507228338163570355165)
              ·
                refine ⟨92440210626811338883187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246507228338163570355165 92440210626811338883187)
                ·
                  rfl

theorem cell19_303795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_303795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303795 prefixEnd_303795 := by exact prefixLift 303795
  have htrace : WordTrace (prefixWord ++ tailWord_303795) baseStart_303795 baseEnd_303795 := by
    simpa [prefixWord, tailWord_303795, baseEnd_303795] using wordTrace_append hprefix tailTrace_303795
  have hstable : (prefixWord ++ tailWord_303795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303795).length < 2 ^ (prefixWord ++ tailWord_303795).sum := by decide
  have hdescent : baseEnd_303795 < baseStart_303795 := by decide
  rcases family_descends (prefixWord ++ tailWord_303795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303816 : List Nat := [2, 1, 3, 1, 2, 3, 7]
def baseStart_303816 : Nat := 118140960795 + 303816 * 2 ^ 59
def prefixEnd_303816 : Nat := 4983230072969 + 3 ^ 40 * 303816 * 2
def baseEnd_303816 : Nat := 30815533536096504138821

theorem tailTrace_303816 : CollatzResearch.WordTrace tailWord_303816 prefixEnd_303816 30815533536096504138821 := by
  unfold tailWord_303816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540539933666997243461651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7387386578222662991282201 5540539933666997243461651)
  ·
    refine ⟨8310809900500495865192477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5540539933666997243461651 8310809900500495865192477)
    ·
      refine ⟨3116553712687685949447179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8310809900500495865192477 3116553712687685949447179)
      ·
        refine ⟨4674830569031528924170769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116553712687685949447179 4674830569031528924170769)
        ·
          refine ⟨3506122926773646693128077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4674830569031528924170769 3506122926773646693128077)
          ·
            refine ⟨1314796097540117509923029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3506122926773646693128077 1314796097540117509923029)
            ·
              refine ⟨30815533536096504138821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1314796097540117509923029 30815533536096504138821)
              ·
                rfl

theorem cell19_303816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_303816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303816 prefixEnd_303816 := by exact prefixLift 303816
  have htrace : WordTrace (prefixWord ++ tailWord_303816) baseStart_303816 baseEnd_303816 := by
    simpa [prefixWord, tailWord_303816, baseEnd_303816] using wordTrace_append hprefix tailTrace_303816
  have hstable : (prefixWord ++ tailWord_303816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303816).length < 2 ^ (prefixWord ++ tailWord_303816).sum := by decide
  have hdescent : baseEnd_303816 < baseStart_303816 := by decide
  rcases family_descends (prefixWord ++ tailWord_303816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303909 : List Nat := [1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_303909 : Nat := 118140960795 + 303909 * 2 ^ 59
def prefixEnd_303909 : Nat := 4983230072969 + 3 ^ 40 * 303909 * 2
def baseEnd_303909 : Nat := 92474899097692852349543

theorem tailTrace_303909 : CollatzResearch.WordTrace tailWord_303909 prefixEnd_303909 92474899097692852349543 := by
  unfold tailWord_303909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084471855997071370058781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7389647903998047580039187 11084471855997071370058781)
  ·
    refine ⟨4156676945998901763772043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11084471855997071370058781 4156676945998901763772043)
    ·
      refine ⟨6235015418998352645658065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156676945998901763772043 6235015418998352645658065)
      ·
        refine ⟨4676261564248764484243549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6235015418998352645658065 4676261564248764484243549)
        ·
          refine ⟨1753598086593286681591331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4676261564248764484243549 1753598086593286681591331)
          ·
            refine ⟨2630397129889930022386997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753598086593286681591331 2630397129889930022386997)
            ·
              refine ⟨246599730927180939598781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2630397129889930022386997 246599730927180939598781)
              ·
                refine ⟨92474899097692852349543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246599730927180939598781 92474899097692852349543)
                ·
                  rfl

theorem cell19_303909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_303909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303909 prefixEnd_303909 := by exact prefixLift 303909
  have htrace : WordTrace (prefixWord ++ tailWord_303909) baseStart_303909 baseEnd_303909 := by
    simpa [prefixWord, tailWord_303909, baseEnd_303909] using wordTrace_append hprefix tailTrace_303909
  have hstable : (prefixWord ++ tailWord_303909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303909).length < 2 ^ (prefixWord ++ tailWord_303909).sum := by decide
  have hdescent : baseEnd_303909 < baseStart_303909 := by decide
  rcases family_descends (prefixWord ++ tailWord_303909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303926 : List Nat := [5, 1, 2, 2, 2, 1, 6]
def baseStart_303926 : Nat := 118140960795 + 303926 * 2 ^ 59
def prefixEnd_303926 : Nat := 4983230072969 + 3 ^ 40 * 303926 * 2
def baseEnd_303926 : Nat := 30826690646613949990573

theorem tailTrace_303926 : CollatzResearch.WordTrace tailWord_303926 prefixEnd_303926 30826690646613949990573 := by
  unfold tailWord_303926
  simp only [CollatzResearch.WordTrace]
  refine ⟨692818243558467704589227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7390061264623655515618421 692818243558467704589227)
  ·
    refine ⟨1039227365337701556883841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692818243558467704589227 1039227365337701556883841)
    ·
      refine ⟨779420524003276167662881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1039227365337701556883841 779420524003276167662881)
      ·
        refine ⟨584565393002457125747161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779420524003276167662881 584565393002457125747161)
        ·
          refine ⟨438424044751842844310371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584565393002457125747161 438424044751842844310371)
          ·
            refine ⟨657636067127764266465557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438424044751842844310371 657636067127764266465557)
            ·
              refine ⟨30826690646613949990573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 657636067127764266465557 30826690646613949990573)
              ·
                rfl

theorem cell19_303926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_303926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303926 prefixEnd_303926 := by exact prefixLift 303926
  have htrace : WordTrace (prefixWord ++ tailWord_303926) baseStart_303926 baseEnd_303926 := by
    simpa [prefixWord, tailWord_303926, baseEnd_303926] using wordTrace_append hprefix tailTrace_303926
  have hstable : (prefixWord ++ tailWord_303926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303926).length < 2 ^ (prefixWord ++ tailWord_303926).sum := by decide
  have hdescent : baseEnd_303926 < baseStart_303926 := by decide
  rcases family_descends (prefixWord ++ tailWord_303926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303964 : List Nat := [2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_303964 : Nat := 118140960795 + 303964 * 2 ^ 59
def prefixEnd_303964 : Nat := 4983230072969 + 3 ^ 40 * 303964 * 2
def baseEnd_303964 : Nat := 92491634763469021127171

theorem tailTrace_303964 : CollatzResearch.WordTrace tailWord_303964 prefixEnd_303964 92491634763469021127171 := by
  unfold tailWord_303964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543238935398907881655473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7390985247198543842207297 5543238935398907881655473)
  ·
    refine ⟨4157429201549180911241605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5543238935398907881655473 4157429201549180911241605)
    ·
      refine ⟨779517975290471420857801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4157429201549180911241605 779517975290471420857801)
      ·
        refine ⟨584638481467853565643351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779517975290471420857801 584638481467853565643351)
        ·
          refine ⟨876957722201780348465027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584638481467853565643351 876957722201780348465027)
          ·
            refine ⟨1315436583302670522697541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876957722201780348465027 1315436583302670522697541)
            ·
              refine ⟨246644359369250723005789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1315436583302670522697541 246644359369250723005789)
              ·
                refine ⟨92491634763469021127171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246644359369250723005789 92491634763469021127171)
                ·
                  rfl

theorem cell19_303964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_303964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303964 prefixEnd_303964 := by exact prefixLift 303964
  have htrace : WordTrace (prefixWord ++ tailWord_303964) baseStart_303964 baseEnd_303964 := by
    simpa [prefixWord, tailWord_303964, baseEnd_303964] using wordTrace_append hprefix tailTrace_303964
  have hstable : (prefixWord ++ tailWord_303964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303964).length < 2 ^ (prefixWord ++ tailWord_303964).sum := by decide
  have hdescent : baseEnd_303964 < baseStart_303964 := by decide
  rcases family_descends (prefixWord ++ tailWord_303964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303968 : List Nat := [2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_303968 : Nat := 118140960795 + 303968 * 2 ^ 59
def prefixEnd_303968 : Nat := 4983230072969 + 3 ^ 40 * 303968 * 2
def baseEnd_303968 : Nat := 92492851902798197038271

theorem tailTrace_303968 : CollatzResearch.WordTrace tailWord_303968 prefixEnd_303968 92492851902798197038271 := by
  unfold tailWord_303968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543311881391662223228279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7391082508522216297637705 5543311881391662223228279)
  ·
    refine ⟨8314967822087493334842419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5543311881391662223228279 8314967822087493334842419)
    ·
      refine ⟨12472451733131240002263629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8314967822087493334842419 12472451733131240002263629)
      ·
        refine ⟨4677169399924215000848861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12472451733131240002263629 4677169399924215000848861)
        ·
          refine ⟨1753938524971580625318323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4677169399924215000848861 1753938524971580625318323)
          ·
            refine ⟨2630907787457370937977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753938524971580625318323 2630907787457370937977485)
            ·
              refine ⟨986590420296514101741557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2630907787457370937977485 986590420296514101741557)
              ·
                refine ⟨92492851902798197038271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 986590420296514101741557 92492851902798197038271)
                ·
                  rfl

theorem cell19_303968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_303968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_303968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_303968 prefixEnd_303968 := by exact prefixLift 303968
  have htrace : WordTrace (prefixWord ++ tailWord_303968) baseStart_303968 baseEnd_303968 := by
    simpa [prefixWord, tailWord_303968, baseEnd_303968] using wordTrace_append hprefix tailTrace_303968
  have hstable : (prefixWord ++ tailWord_303968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303968).length < 2 ^ (prefixWord ++ tailWord_303968).sum := by decide
  have hdescent : baseEnd_303968 < baseStart_303968 := by decide
  rcases family_descends (prefixWord ++ tailWord_303968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304139 : List Nat := [1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_304139 : Nat := 118140960795 + 304139 * 2 ^ 59
def prefixEnd_304139 : Nat := 4983230072969 + 3 ^ 40 * 304139 * 2
def baseEnd_304139 : Nat := 92544884609120467237805

theorem tailTrace_304139 : CollatzResearch.WordTrace tailWord_304139 prefixEnd_304139 92544884609120467237805 := by
  unfold tailWord_304139
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092860645163820650931471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7395240430109213767287647 11092860645163820650931471)
  ·
    refine ⟨16639290967745730976397207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11092860645163820650931471 16639290967745730976397207)
    ·
      refine ⟨24958936451618596464595811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16639290967745730976397207 24958936451618596464595811)
      ·
        refine ⟨37438404677427894696893717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24958936451618596464595811 37438404677427894696893717)
        ·
          refine ⟨1754925219254432563916893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37438404677427894696893717 1754925219254432563916893)
          ·
            refine ⟨658096957220412211468835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1754925219254432563916893 658096957220412211468835)
            ·
              refine ⟨987145435830618317203253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658096957220412211468835 987145435830618317203253)
              ·
                refine ⟨92544884609120467237805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 987145435830618317203253 92544884609120467237805)
                ·
                  rfl

theorem cell19_304139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_304139 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304139 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304139 prefixEnd_304139 := by exact prefixLift 304139
  have htrace : WordTrace (prefixWord ++ tailWord_304139) baseStart_304139 baseEnd_304139 := by
    simpa [prefixWord, tailWord_304139, baseEnd_304139] using wordTrace_append hprefix tailTrace_304139
  have hstable : (prefixWord ++ tailWord_304139).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304139).length < 2 ^ (prefixWord ++ tailWord_304139).sum := by decide
  have hdescent : baseEnd_304139 < baseStart_304139 := by decide
  rcases family_descends (prefixWord ++ tailWord_304139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304156 : List Nat := [2, 2, 3, 1, 4, 2, 5]
def baseStart_304156 : Nat := 118140960795 + 304156 * 2 ^ 59
def prefixEnd_304156 : Nat := 4983230072969 + 3 ^ 40 * 304156 * 2
def baseEnd_304156 : Nat := 30850019150423154953327

theorem tailTrace_304156 : CollatzResearch.WordTrace tailWord_304156 prefixEnd_304156 30850019150423154953327 := by
  unfold tailWord_304156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546740343051116277150161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7395653790734821702866881 5546740343051116277150161)
  ·
    refine ⟨4160055257288337207862621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5546740343051116277150161 4160055257288337207862621)
    ·
      refine ⟨1560020721483126452948483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4160055257288337207862621 1560020721483126452948483)
      ·
        refine ⟨2340031082224689679422725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560020721483126452948483 2340031082224689679422725)
        ·
          refine ⟨438755827917129314891761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2340031082224689679422725 438755827917129314891761)
          ·
            refine ⟨329066870937846986168821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438755827917129314891761 329066870937846986168821)
            ·
              refine ⟨30850019150423154953327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329066870937846986168821 30850019150423154953327)
              ·
                rfl

theorem cell19_304156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_304156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304156 prefixEnd_304156 := by exact prefixLift 304156
  have htrace : WordTrace (prefixWord ++ tailWord_304156) baseStart_304156 baseEnd_304156 := by
    simpa [prefixWord, tailWord_304156, baseEnd_304156] using wordTrace_append hprefix tailTrace_304156
  have hstable : (prefixWord ++ tailWord_304156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304156).length < 2 ^ (prefixWord ++ tailWord_304156).sum := by decide
  have hdescent : baseEnd_304156 < baseStart_304156 := by decide
  rcases family_descends (prefixWord ++ tailWord_304156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304177 : List Nat := [1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_304177 : Nat := 118140960795 + 304177 * 2 ^ 59
def prefixEnd_304177 : Nat := 4983230072969 + 3 ^ 40 * 304177 * 2
def baseEnd_304177 : Nat := 92556447432747638393257

theorem tailTrace_304177 : CollatzResearch.WordTrace tailWord_304177 prefixEnd_304177 92556447432747638393257 := by
  unfold tailWord_304177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11094246619026153140814785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7396164412684102093876523 11094246619026153140814785)
  ·
    refine ⟨8320684964269614855611089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11094246619026153140814785 8320684964269614855611089)
    ·
      refine ⟨6240513723202211141708317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8320684964269614855611089 6240513723202211141708317)
      ·
        refine ⟨2340192646200829178140619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6240513723202211141708317 2340192646200829178140619)
        ·
          refine ⟨3510288969301243767210929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340192646200829178140619 3510288969301243767210929)
          ·
            refine ⟨2632716726975932825408197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510288969301243767210929 2632716726975932825408197)
            ·
              refine ⟨493634386307987404764037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2632716726975932825408197 493634386307987404764037)
              ·
                refine ⟨92556447432747638393257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493634386307987404764037 92556447432747638393257)
                ·
                  rfl

theorem cell19_304177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_304177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304177 prefixEnd_304177 := by exact prefixLift 304177
  have htrace : WordTrace (prefixWord ++ tailWord_304177) baseStart_304177 baseEnd_304177 := by
    simpa [prefixWord, tailWord_304177, baseEnd_304177] using wordTrace_append hprefix tailTrace_304177
  have hstable : (prefixWord ++ tailWord_304177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304177).length < 2 ^ (prefixWord ++ tailWord_304177).sum := by decide
  have hdescent : baseEnd_304177 < baseStart_304177 := by decide
  rcases family_descends (prefixWord ++ tailWord_304177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304386 : List Nat := [3, 4, 1, 1, 10]
def baseStart_304386 : Nat := 118140960795 + 304386 * 2 ^ 59
def prefixEnd_304386 : Nat := 4983230072969 + 3 ^ 40 * 304386 * 2
def baseEnd_304386 : Nat := 3430371961581373324009

theorem tailTrace_304386 : CollatzResearch.WordTrace tailWord_304386 prefixEnd_304386 3430371961581373324009 := by
  unfold tailWord_304386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775467368817245458793253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7401246316845987890115341 2775467368817245458793253)
  ·
    refine ⟨520400131653233523523735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2775467368817245458793253 520400131653233523523735)
    ·
      refine ⟨780600197479850285285603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 520400131653233523523735 780600197479850285285603)
      ·
        refine ⟨1170900296219775427928405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780600197479850285285603 1170900296219775427928405)
        ·
          refine ⟨3430371961581373324009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1170900296219775427928405 3430371961581373324009)
          ·
            rfl

theorem cell19_304386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 10].length) (baseStart_304386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304386 prefixEnd_304386 := by exact prefixLift 304386
  have htrace : WordTrace (prefixWord ++ tailWord_304386) baseStart_304386 baseEnd_304386 := by
    simpa [prefixWord, tailWord_304386, baseEnd_304386] using wordTrace_append hprefix tailTrace_304386
  have hstable : (prefixWord ++ tailWord_304386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304386).length < 2 ^ (prefixWord ++ tailWord_304386).sum := by decide
  have hdescent : baseEnd_304386 < baseStart_304386 := by decide
  rcases family_descends (prefixWord ++ tailWord_304386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304464 : List Nat := [2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_304464 : Nat := 118140960795 + 304464 * 2 ^ 59
def prefixEnd_304464 : Nat := 4983230072969 + 3 ^ 40 * 304464 * 2
def baseEnd_304464 : Nat := 92643777179616010014697

theorem tailTrace_304464 : CollatzResearch.WordTrace tailWord_304464 prefixEnd_304464 92643777179616010014697 := by
  unfold tailWord_304464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552357184493200578256223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7403142912657600771008297 5552357184493200578256223)
  ·
    refine ⟨8328535776739800867384335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5552357184493200578256223 8328535776739800867384335)
    ·
      refine ⟨12492803665109701301076503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8328535776739800867384335 12492803665109701301076503)
      ·
        refine ⟨18739205497664551951614755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12492803665109701301076503 18739205497664551951614755)
        ·
          refine ⟨28108808246496827927422133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18739205497664551951614755 28108808246496827927422133)
          ·
            refine ⟨2635200773109077618195825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28108808246496827927422133 2635200773109077618195825)
            ·
              refine ⟨1976400579831808213646869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2635200773109077618195825 1976400579831808213646869)
              ·
                refine ⟨92643777179616010014697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1976400579831808213646869 92643777179616010014697)
                ·
                  rfl

theorem cell19_304464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_304464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304464 prefixEnd_304464 := by exact prefixLift 304464
  have htrace : WordTrace (prefixWord ++ tailWord_304464) baseStart_304464 baseEnd_304464 := by
    simpa [prefixWord, tailWord_304464, baseEnd_304464] using wordTrace_append hprefix tailTrace_304464
  have hstable : (prefixWord ++ tailWord_304464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304464).length < 2 ^ (prefixWord ++ tailWord_304464).sum := by decide
  have hdescent : baseEnd_304464 < baseStart_304464 := by decide
  rcases family_descends (prefixWord ++ tailWord_304464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304519 : List Nat := [1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_304519 : Nat := 118140960795 + 304519 * 2 ^ 59
def prefixEnd_304519 : Nat := 4983230072969 + 3 ^ 40 * 304519 * 2
def baseEnd_304519 : Nat := 92660512845392178792325

theorem tailTrace_304519 : CollatzResearch.WordTrace tailWord_304519 prefixEnd_304519 92660512845392178792325 := by
  unfold tailWord_304519
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106720383787145549764611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7404480255858097033176407 11106720383787145549764611)
  ·
    refine ⟨16660080575680718324646917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11106720383787145549764611 16660080575680718324646917)
    ·
      refine ⟨3123765107940134685871297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16660080575680718324646917 3123765107940134685871297)
      ·
        refine ⟨2342823830955101014403473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123765107940134685871297 2342823830955101014403473)
        ·
          refine ⟨1757117873216325760802605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2342823830955101014403473 1757117873216325760802605)
          ·
            refine ⟨658919202456122160300977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1757117873216325760802605 658919202456122160300977)
            ·
              refine ⟨494189401842091620225733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658919202456122160300977 494189401842091620225733)
              ·
                refine ⟨92660512845392178792325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494189401842091620225733 92660512845392178792325)
                ·
                  rfl

theorem cell19_304519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_304519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304519 prefixEnd_304519 := by exact prefixLift 304519
  have htrace : WordTrace (prefixWord ++ tailWord_304519) baseStart_304519 baseEnd_304519 := by
    simpa [prefixWord, tailWord_304519, baseEnd_304519] using wordTrace_append hprefix tailTrace_304519
  have hstable : (prefixWord ++ tailWord_304519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304519).length < 2 ^ (prefixWord ++ tailWord_304519).sum := by decide
  have hdescent : baseEnd_304519 < baseStart_304519 := by decide
  rcases family_descends (prefixWord ++ tailWord_304519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304557 : List Nat := [1, 5, 2, 2, 1, 8]
def baseStart_304557 : Nat := 118140960795 + 304557 * 2 ^ 59
def prefixEnd_304557 : Nat := 4983230072969 + 3 ^ 40 * 304557 * 2
def baseEnd_304557 : Nat := 10296897296557705549753

theorem tailTrace_304557 : CollatzResearch.WordTrace tailWord_304557 prefixEnd_304557 10296897296557705549753 := by
  unfold tailWord_304557
  simp only [CollatzResearch.WordTrace]
  refine ⟨11108106357649478039647925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7405404238432985359765283 11108106357649478039647925)
  ·
    refine ⟨1041384971029638566216993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11108106357649478039647925 1041384971029638566216993)
    ·
      refine ⟨781038728272228924662745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1041384971029638566216993 781038728272228924662745)
      ·
        refine ⟨585779046204171693497059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781038728272228924662745 585779046204171693497059)
        ·
          refine ⟨878668569306257540245589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585779046204171693497059 878668569306257540245589)
          ·
            refine ⟨10296897296557705549753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 878668569306257540245589 10296897296557705549753)
            ·
              rfl

theorem cell19_304557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_304557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304557 prefixEnd_304557 := by exact prefixLift 304557
  have htrace : WordTrace (prefixWord ++ tailWord_304557) baseStart_304557 baseEnd_304557 := by
    simpa [prefixWord, tailWord_304557, baseEnd_304557] using wordTrace_append hprefix tailTrace_304557
  have hstable : (prefixWord ++ tailWord_304557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304557).length < 2 ^ (prefixWord ++ tailWord_304557).sum := by decide
  have hdescent : baseEnd_304557 < baseStart_304557 := by decide
  rcases family_descends (prefixWord ++ tailWord_304557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304572 : List Nat := [2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_304572 : Nat := 118140960795 + 304572 * 2 ^ 59
def prefixEnd_304572 : Nat := 4983230072969 + 3 ^ 40 * 304572 * 2
def baseEnd_304572 : Nat := 92676639941503759614403

theorem tailTrace_304572 : CollatzResearch.WordTrace tailWord_304572 prefixEnd_304572 92676639941503759614403 := by
  unfold tailWord_304572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554326726297567800721985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7405768968396757067629313 5554326726297567800721985)
  ·
    refine ⟨4165745044723175850541489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5554326726297567800721985 4165745044723175850541489)
    ·
      refine ⟨3124308783542381887906117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4165745044723175850541489 3124308783542381887906117)
      ·
        refine ⟨585807896914196603982397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3124308783542381887906117 585807896914196603982397)
        ·
          refine ⟨219677961342823726493399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 585807896914196603982397 219677961342823726493399)
          ·
            refine ⟨329516942014235589740099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219677961342823726493399 329516942014235589740099)
            ·
              refine ⟨494275413021353384610149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329516942014235589740099 494275413021353384610149)
              ·
                refine ⟨92676639941503759614403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494275413021353384610149 92676639941503759614403)
                ·
                  rfl

theorem cell19_304572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_304572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304572 prefixEnd_304572 := by exact prefixLift 304572
  have htrace : WordTrace (prefixWord ++ tailWord_304572) baseStart_304572 baseEnd_304572 := by
    simpa [prefixWord, tailWord_304572, baseEnd_304572] using wordTrace_append hprefix tailTrace_304572
  have hstable : (prefixWord ++ tailWord_304572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304572).length < 2 ^ (prefixWord ++ tailWord_304572).sum := by decide
  have hdescent : baseEnd_304572 < baseStart_304572 := by decide
  rcases family_descends (prefixWord ++ tailWord_304572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304616 : List Nat := [2, 1, 4, 1, 1, 2, 8]
def baseStart_304616 : Nat := 118140960795 + 304616 * 2 ^ 59
def prefixEnd_304616 : Nat := 4983230072969 + 3 ^ 40 * 304616 * 2
def baseEnd_304616 : Nat := 30896676158041564878835

theorem tailTrace_304616 : CollatzResearch.WordTrace tailWord_304616 prefixEnd_304616 30896676158041564878835 := by
  unfold tailWord_304616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555129132217865558022851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7406838842957154077363801 5555129132217865558022851)
  ·
    refine ⟨8332693698326798337034277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5555129132217865558022851 8332693698326798337034277)
    ·
      refine ⟨1562380068436274688193927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8332693698326798337034277 1562380068436274688193927)
      ·
        refine ⟨2343570102654412032290891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562380068436274688193927 2343570102654412032290891)
        ·
          refine ⟨3515355153981618048436337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343570102654412032290891 3515355153981618048436337)
          ·
            refine ⟨2636516365486213536327253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3515355153981618048436337 2636516365486213536327253)
            ·
              refine ⟨30896676158041564878835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2636516365486213536327253 30896676158041564878835)
              ·
                rfl

theorem cell19_304616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_304616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304616 prefixEnd_304616 := by exact prefixLift 304616
  have htrace : WordTrace (prefixWord ++ tailWord_304616) baseStart_304616 baseEnd_304616 := by
    simpa [prefixWord, tailWord_304616, baseEnd_304616] using wordTrace_append hprefix tailTrace_304616
  have hstable : (prefixWord ++ tailWord_304616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304616).length < 2 ^ (prefixWord ++ tailWord_304616).sum := by decide
  have hdescent : baseEnd_304616 < baseStart_304616 := by decide
  rcases family_descends (prefixWord ++ tailWord_304616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304646 : List Nat := [6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_304646 : Nat := 118140960795 + 304646 * 2 ^ 59
def prefixEnd_304646 : Nat := 4983230072969 + 3 ^ 40 * 304646 * 2
def baseEnd_304646 : Nat := 92699157019093513969757

theorem tailTrace_304646 : CollatzResearch.WordTrace tailWord_304646 prefixEnd_304646 92699157019093513969757 := by
  unfold tailWord_304646
  simp only [CollatzResearch.WordTrace]
  refine ⟨347229764197720194988681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7407568302884697493091861 347229764197720194988681)
  ·
    refine ⟨260422323148290146241511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 347229764197720194988681 260422323148290146241511)
    ·
      refine ⟨390633484722435219362267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260422323148290146241511 390633484722435219362267)
      ·
        refine ⟨585950227083652829043401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390633484722435219362267 585950227083652829043401)
        ·
          refine ⟨439462670312739621782551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585950227083652829043401 439462670312739621782551)
          ·
            refine ⟨659194005469109432673827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439462670312739621782551 659194005469109432673827)
            ·
              refine ⟨988791008203664149010741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659194005469109432673827 988791008203664149010741)
              ·
                refine ⟨92699157019093513969757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988791008203664149010741 92699157019093513969757)
                ·
                  rfl

theorem cell19_304646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_304646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304646 prefixEnd_304646 := by exact prefixLift 304646
  have htrace : WordTrace (prefixWord ++ tailWord_304646) baseStart_304646 baseEnd_304646 := by
    simpa [prefixWord, tailWord_304646, baseEnd_304646] using wordTrace_append hprefix tailTrace_304646
  have hstable : (prefixWord ++ tailWord_304646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304646).length < 2 ^ (prefixWord ++ tailWord_304646).sum := by decide
  have hdescent : baseEnd_304646 < baseStart_304646 := by decide
  rcases family_descends (prefixWord ++ tailWord_304646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304650 : List Nat := [3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_304650 : Nat := 118140960795 + 304650 * 2 ^ 59
def prefixEnd_304650 : Nat := 4983230072969 + 3 ^ 40 * 304650 * 2
def baseEnd_304650 : Nat := 92700374158422689880857

theorem tailTrace_304650 : CollatzResearch.WordTrace tailWord_304650 prefixEnd_304650 92700374158422689880857 := by
  unfold tailWord_304650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777874586578138730695851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7407665564208369948522269 2777874586578138730695851)
  ·
    refine ⟨4166811879867208096043777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777874586578138730695851 4166811879867208096043777)
    ·
      refine ⟨3125108909900406072032833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4166811879867208096043777 3125108909900406072032833)
      ·
        refine ⟨2343831682425304554024625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3125108909900406072032833 2343831682425304554024625)
        ·
          refine ⟨1757873761818978415518469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343831682425304554024625 1757873761818978415518469)
          ·
            refine ⟨329601330341058452909713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1757873761818978415518469 329601330341058452909713)
            ·
              refine ⟨247200997755793839682285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329601330341058452909713 247200997755793839682285)
              ·
                refine ⟨92700374158422689880857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247200997755793839682285 92700374158422689880857)
                ·
                  rfl

theorem cell19_304650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_304650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304650 prefixEnd_304650 := by exact prefixLift 304650
  have htrace : WordTrace (prefixWord ++ tailWord_304650) baseStart_304650 baseEnd_304650 := by
    simpa [prefixWord, tailWord_304650, baseEnd_304650] using wordTrace_append hprefix tailTrace_304650
  have hstable : (prefixWord ++ tailWord_304650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304650).length < 2 ^ (prefixWord ++ tailWord_304650).sum := by decide
  have hdescent : baseEnd_304650 < baseStart_304650 := by decide
  rcases family_descends (prefixWord ++ tailWord_304650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304652 : List Nat := [2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_304652 : Nat := 118140960795 + 304652 * 2 ^ 59
def prefixEnd_304652 : Nat := 4983230072969 + 3 ^ 40 * 304652 * 2
def baseEnd_304652 : Nat := 92700982728087277836407

theorem tailTrace_304652 : CollatzResearch.WordTrace tailWord_304652 prefixEnd_304652 92700982728087277836407 := by
  unfold tailWord_304652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555785646152654632178105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7407714194870206176237473 5555785646152654632178105)
  ·
    refine ⟨4166839234614490974133579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5555785646152654632178105 4166839234614490974133579)
    ·
      refine ⟨6250258851921736461200369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166839234614490974133579 6250258851921736461200369)
      ·
        refine ⟨4687694138941302345900277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6250258851921736461200369 4687694138941302345900277)
        ·
          refine ⟨439471325525747094928151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4687694138941302345900277 439471325525747094928151)
          ·
            refine ⟨659206988288620642392227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439471325525747094928151 659206988288620642392227)
            ·
              refine ⟨988810482432930963588341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659206988288620642392227 988810482432930963588341)
              ·
                refine ⟨92700982728087277836407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988810482432930963588341 92700982728087277836407)
                ·
                  rfl

theorem cell19_304652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_304652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304652 prefixEnd_304652 := by exact prefixLift 304652
  have htrace : WordTrace (prefixWord ++ tailWord_304652) baseStart_304652 baseEnd_304652 := by
    simpa [prefixWord, tailWord_304652, baseEnd_304652] using wordTrace_append hprefix tailTrace_304652
  have hstable : (prefixWord ++ tailWord_304652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304652).length < 2 ^ (prefixWord ++ tailWord_304652).sum := by decide
  have hdescent : baseEnd_304652 < baseStart_304652 := by decide
  rcases family_descends (prefixWord ++ tailWord_304652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304673 : List Nat := [1, 2, 3, 2, 2, 2, 7]
def baseStart_304673 : Nat := 118140960795 + 304673 * 2 ^ 59
def prefixEnd_304673 : Nat := 4983230072969 + 3 ^ 40 * 304673 * 2
def baseEnd_304673 : Nat := 30902457569855150456561

theorem tailTrace_304673 : CollatzResearch.WordTrace tailWord_304673 prefixEnd_304673 30902457569855150456561 := by
  unfold tailWord_304673
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112337225229229850870673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7408224816819486567247115 11112337225229229850870673)
  ·
    refine ⟨8334252918921922388153005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11112337225229229850870673 8334252918921922388153005)
    ·
      refine ⟨3125344844595720895557377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8334252918921922388153005 3125344844595720895557377)
      ·
        refine ⟨2344008633446790671668033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3125344844595720895557377 2344008633446790671668033)
        ·
          refine ⟨1758006475085093003751025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344008633446790671668033 1758006475085093003751025)
          ·
            refine ⟨1318504856313819752813269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758006475085093003751025 1318504856313819752813269)
            ·
              refine ⟨30902457569855150456561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1318504856313819752813269 30902457569855150456561)
              ·
                rfl

theorem cell19_304673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_304673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304673 prefixEnd_304673 := by exact prefixLift 304673
  have htrace : WordTrace (prefixWord ++ tailWord_304673) baseStart_304673 baseEnd_304673 := by
    simpa [prefixWord, tailWord_304673, baseEnd_304673] using wordTrace_append hprefix tailTrace_304673
  have hstable : (prefixWord ++ tailWord_304673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304673).length < 2 ^ (prefixWord ++ tailWord_304673).sum := by decide
  have hdescent : baseEnd_304673 < baseStart_304673 := by decide
  rcases family_descends (prefixWord ++ tailWord_304673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304726 : List Nat := [5, 2, 2, 2, 8]
def baseStart_304726 : Nat := 118140960795 + 304726 * 2 ^ 59
def prefixEnd_304726 : Nat := 4983230072969 + 3 ^ 40 * 304726 * 2
def baseEnd_304726 : Nat := 3434203696506556747843

theorem tailTrace_304726 : CollatzResearch.WordTrace tailWord_304726 prefixEnd_304726 3434203696506556747843 := by
  unfold tailWord_304726
  simp only [CollatzResearch.WordTrace]
  refine ⟨694641893377326243909377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7409513529358146601700021 694641893377326243909377)
  ·
    refine ⟨520981420032994682932033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 694641893377326243909377 520981420032994682932033)
    ·
      refine ⟨390736065024746012199025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520981420032994682932033 390736065024746012199025)
      ·
        refine ⟨293052048768559509149269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390736065024746012199025 293052048768559509149269)
        ·
          refine ⟨3434203696506556747843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 293052048768559509149269 3434203696506556747843)
          ·
            rfl

theorem cell19_304726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 8].length) (baseStart_304726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304726 prefixEnd_304726 := by exact prefixLift 304726
  have htrace : WordTrace (prefixWord ++ tailWord_304726) baseStart_304726 baseEnd_304726 := by
    simpa [prefixWord, tailWord_304726, baseEnd_304726] using wordTrace_append hprefix tailTrace_304726
  have hstable : (prefixWord ++ tailWord_304726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304726).length < 2 ^ (prefixWord ++ tailWord_304726).sum := by decide
  have hdescent : baseEnd_304726 < baseStart_304726 := by decide
  rcases family_descends (prefixWord ++ tailWord_304726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304823 : List Nat := [1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_304823 : Nat := 118140960795 + 304823 * 2 ^ 59
def prefixEnd_304823 : Nat := 4983230072969 + 3 ^ 40 * 304823 * 2
def baseEnd_304823 : Nat := 92753015434409548035941

theorem tailTrace_304823 : CollatzResearch.WordTrace tailWord_304823 prefixEnd_304823 92753015434409548035941 := by
  unfold tailWord_304823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11117808174685805468831123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7411872116457203645887415 11117808174685805468831123)
  ·
    refine ⟨16676712262028708203246685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11117808174685805468831123 16676712262028708203246685)
    ·
      refine ⟨6253767098260765576217507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16676712262028708203246685 6253767098260765576217507)
      ·
        refine ⟨9380650647391148364326261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6253767098260765576217507 9380650647391148364326261)
        ·
          refine ⟨879435998192920159155587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9380650647391148364326261 879435998192920159155587)
          ·
            refine ⟨1319153997289380238733381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879435998192920159155587 1319153997289380238733381)
            ·
              refine ⟨247341374491758794762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1319153997289380238733381 247341374491758794762509)
              ·
                refine ⟨92753015434409548035941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247341374491758794762509 92753015434409548035941)
                ·
                  rfl

theorem cell19_304823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_304823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304823 prefixEnd_304823 := by exact prefixLift 304823
  have htrace : WordTrace (prefixWord ++ tailWord_304823) baseStart_304823 baseEnd_304823 := by
    simpa [prefixWord, tailWord_304823, baseEnd_304823] using wordTrace_append hprefix tailTrace_304823
  have hstable : (prefixWord ++ tailWord_304823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304823).length < 2 ^ (prefixWord ++ tailWord_304823).sum := by decide
  have hdescent : baseEnd_304823 < baseStart_304823 := by decide
  rcases family_descends (prefixWord ++ tailWord_304823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304838 : List Nat := [6, 1, 2, 1, 1, 3, 5]
def baseStart_304838 : Nat := 118140960795 + 304838 * 2 ^ 59
def prefixEnd_304838 : Nat := 4983230072969 + 3 ^ 40 * 304838 * 2
def baseEnd_304838 : Nat := 30919193235631319234189

theorem tailTrace_304838 : CollatzResearch.WordTrace tailWord_304838 prefixEnd_304838 30919193235631319234189 := by
  unfold tailWord_304838
  simp only [CollatzResearch.WordTrace]
  refine ⟨347448602175983219707099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7412236846420975353751445 347448602175983219707099)
  ·
    refine ⟨521172903263974829560649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347448602175983219707099 521172903263974829560649)
    ·
      refine ⟨390879677447981122170487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521172903263974829560649 390879677447981122170487)
      ·
        refine ⟨586319516171971683255731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390879677447981122170487 586319516171971683255731)
        ·
          refine ⟨879479274257957524883597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586319516171971683255731 879479274257957524883597)
          ·
            refine ⟨329804727846734071831349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 879479274257957524883597 329804727846734071831349)
            ·
              refine ⟨30919193235631319234189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329804727846734071831349 30919193235631319234189)
              ·
                rfl

theorem cell19_304838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_304838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304838 prefixEnd_304838 := by exact prefixLift 304838
  have htrace : WordTrace (prefixWord ++ tailWord_304838) baseStart_304838 baseEnd_304838 := by
    simpa [prefixWord, tailWord_304838, baseEnd_304838] using wordTrace_append hprefix tailTrace_304838
  have hstable : (prefixWord ++ tailWord_304838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304838).length < 2 ^ (prefixWord ++ tailWord_304838).sum := by decide
  have hdescent : baseEnd_304838 < baseStart_304838 := by decide
  rcases family_descends (prefixWord ++ tailWord_304838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304842 : List Nat := [3, 1, 2, 1, 5, 2, 5]
def baseStart_304842 : Nat := 118140960795 + 304842 * 2 ^ 59
def prefixEnd_304842 : Nat := 4983230072969 + 3 ^ 40 * 304842 * 2
def baseEnd_304842 : Nat := 30919598948741044537889

theorem tailTrace_304842 : CollatzResearch.WordTrace tailWord_304842 prefixEnd_304842 30919598948741044537889 := by
  unfold tailWord_304842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779625290404242928443195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7412334107744647809181853 2779625290404242928443195)
  ·
    refine ⟨4169437935606364392664793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779625290404242928443195 4169437935606364392664793)
    ·
      refine ⟨3127078451704773294498595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4169437935606364392664793 3127078451704773294498595)
      ·
        refine ⟨4690617677557159941747893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127078451704773294498595 4690617677557159941747893)
        ·
          refine ⟨439745407270983744538865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4690617677557159941747893 439745407270983744538865)
          ·
            refine ⟨329809055453237808404149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439745407270983744538865 329809055453237808404149)
            ·
              refine ⟨30919598948741044537889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329809055453237808404149 30919598948741044537889)
              ·
                rfl

theorem cell19_304842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_304842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304842 prefixEnd_304842 := by exact prefixLift 304842
  have htrace : WordTrace (prefixWord ++ tailWord_304842) baseStart_304842 baseEnd_304842 := by
    simpa [prefixWord, tailWord_304842, baseEnd_304842] using wordTrace_append hprefix tailTrace_304842
  have hstable : (prefixWord ++ tailWord_304842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304842).length < 2 ^ (prefixWord ++ tailWord_304842).sum := by decide
  have hdescent : baseEnd_304842 < baseStart_304842 := by decide
  rcases family_descends (prefixWord ++ tailWord_304842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304863 : List Nat := [1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_304863 : Nat := 118140960795 + 304863 * 2 ^ 59
def prefixEnd_304863 : Nat := 4983230072969 + 3 ^ 40 * 304863 * 2
def baseEnd_304863 : Nat := 92765186827701307146943

theorem tailTrace_304863 : CollatzResearch.WordTrace tailWord_304863 prefixEnd_304863 92765186827701307146943 := by
  unfold tailWord_304863
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119267094540892300287243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7412844729693928200191495 11119267094540892300287243)
  ·
    refine ⟨16678900641811338450430865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11119267094540892300287243 16678900641811338450430865)
    ·
      refine ⟨12509175481358503837823149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16678900641811338450430865 12509175481358503837823149)
      ·
        refine ⟨4690940805509438939183681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12509175481358503837823149 4690940805509438939183681)
        ·
          refine ⟨3518205604132079204387761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4690940805509438939183681 3518205604132079204387761)
          ·
            refine ⟨2638654203099059403290821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518205604132079204387761 2638654203099059403290821)
            ·
              refine ⟨494747663081073638117029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2638654203099059403290821 494747663081073638117029)
              ·
                refine ⟨92765186827701307146943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494747663081073638117029 92765186827701307146943)
                ·
                  rfl

theorem cell19_304863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_304863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304863 prefixEnd_304863 := by exact prefixLift 304863
  have htrace : WordTrace (prefixWord ++ tailWord_304863) baseStart_304863 baseEnd_304863 := by
    simpa [prefixWord, tailWord_304863, baseEnd_304863] using wordTrace_append hprefix tailTrace_304863
  have hstable : (prefixWord ++ tailWord_304863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304863).length < 2 ^ (prefixWord ++ tailWord_304863).sum := by decide
  have hdescent : baseEnd_304863 < baseStart_304863 := by decide
  rcases family_descends (prefixWord ++ tailWord_304863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304882 : List Nat := [3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_304882 : Nat := 118140960795 + 304882 * 2 ^ 59
def prefixEnd_304882 : Nat := 4983230072969 + 3 ^ 40 * 304882 * 2
def baseEnd_304882 : Nat := 92770968239514892724669

theorem tailTrace_304882 : CollatzResearch.WordTrace tailWord_304882 prefixEnd_304882 92770968239514892724669 := by
  unfold tailWord_304882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779990020368014636307225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7413306720981372363485933 2779990020368014636307225)
  ·
    refine ⟨2084992515276010977230419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2779990020368014636307225 2084992515276010977230419)
    ·
      refine ⟨3127488772914016465845629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2084992515276010977230419 3127488772914016465845629)
      ·
        refine ⟨1172808289842756174692111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3127488772914016465845629 1172808289842756174692111)
        ·
          refine ⟨1759212434764134262038167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172808289842756174692111 1759212434764134262038167)
          ·
            refine ⟨2638818652146201393057251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759212434764134262038167 2638818652146201393057251)
            ·
              refine ⟨3958227978219302089585877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638818652146201393057251 3958227978219302089585877)
              ·
                refine ⟨92770968239514892724669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3958227978219302089585877 92770968239514892724669)
                ·
                  rfl

theorem cell19_304882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_304882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304882 prefixEnd_304882 := by exact prefixLift 304882
  have htrace : WordTrace (prefixWord ++ tailWord_304882) baseStart_304882 baseEnd_304882 := by
    simpa [prefixWord, tailWord_304882, baseEnd_304882] using wordTrace_append hprefix tailTrace_304882
  have hstable : (prefixWord ++ tailWord_304882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304882).length < 2 ^ (prefixWord ++ tailWord_304882).sum := by decide
  have hdescent : baseEnd_304882 < baseStart_304882 := by decide
  rcases family_descends (prefixWord ++ tailWord_304882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304920 : List Nat := [2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_304920 : Nat := 118140960795 + 304920 * 2 ^ 59
def prefixEnd_304920 : Nat := 4983230072969 + 3 ^ 40 * 304920 * 2
def baseEnd_304920 : Nat := 92782531063142063880121

theorem tailTrace_304920 : CollatzResearch.WordTrace tailWord_304920 prefixEnd_304920 92782531063142063880121 := by
  unfold tailWord_304920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560673027667195517556107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7414230703556260690074809 5560673027667195517556107)
  ·
    refine ⟨8341009541500793276334161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5560673027667195517556107 8341009541500793276334161)
    ·
      refine ⟨6255757156125594957250621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8341009541500793276334161 6255757156125594957250621)
      ·
        refine ⟨2345908933547098108968983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6255757156125594957250621 2345908933547098108968983)
        ·
          refine ⟨3518863400320647163453475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345908933547098108968983 3518863400320647163453475)
          ·
            refine ⟨5278295100480970745180213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518863400320647163453475 5278295100480970745180213)
            ·
              refine ⟨494840165670091007360645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5278295100480970745180213 494840165670091007360645)
              ·
                refine ⟨92782531063142063880121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494840165670091007360645 92782531063142063880121)
                ·
                  rfl

theorem cell19_304920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_304920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304920 prefixEnd_304920 := by exact prefixLift 304920
  have htrace : WordTrace (prefixWord ++ tailWord_304920) baseStart_304920 baseEnd_304920 := by
    simpa [prefixWord, tailWord_304920, baseEnd_304920] using wordTrace_append hprefix tailTrace_304920
  have hstable : (prefixWord ++ tailWord_304920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304920).length < 2 ^ (prefixWord ++ tailWord_304920).sum := by decide
  have hdescent : baseEnd_304920 < baseStart_304920 := by decide
  rcases family_descends (prefixWord ++ tailWord_304920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304994 : List Nat := [3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_304994 : Nat := 118140960795 + 304994 * 2 ^ 59
def prefixEnd_304994 : Nat := 4983230072969 + 3 ^ 40 * 304994 * 2
def baseEnd_304994 : Nat := 92805048140731818235475

theorem tailTrace_304994 : CollatzResearch.WordTrace tailWord_304994 prefixEnd_304994 92805048140731818235475 := by
  unfold tailWord_304994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781011264266575418326509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7416030038044201115537357 2781011264266575418326509)
  ·
    refine ⟨1042879224099965781872441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2781011264266575418326509 1042879224099965781872441)
    ·
      refine ⟨782159418074974336404331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1042879224099965781872441 782159418074974336404331)
      ·
        refine ⟨1173239127112461504606497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782159418074974336404331 1173239127112461504606497)
        ·
          refine ⟨879929345334346128454873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173239127112461504606497 879929345334346128454873)
          ·
            refine ⟨659947009000759596341155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879929345334346128454873 659947009000759596341155)
            ·
              refine ⟨989920513501139394511733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659947009000759596341155 989920513501139394511733)
              ·
                refine ⟨92805048140731818235475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 989920513501139394511733 92805048140731818235475)
                ·
                  rfl

theorem cell19_304994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_304994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_304994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_304994 prefixEnd_304994 := by exact prefixLift 304994
  have htrace : WordTrace (prefixWord ++ tailWord_304994) baseStart_304994 baseEnd_304994 := by
    simpa [prefixWord, tailWord_304994, baseEnd_304994] using wordTrace_append hprefix tailTrace_304994
  have hstable : (prefixWord ++ tailWord_304994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304994).length < 2 ^ (prefixWord ++ tailWord_304994).sum := by decide
  have hdescent : baseEnd_304994 < baseStart_304994 := by decide
  rcases family_descends (prefixWord ++ tailWord_304994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305032 : List Nat := [2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_305032 : Nat := 118140960795 + 305032 * 2 ^ 59
def prefixEnd_305032 : Nat := 4983230072969 + 3 ^ 40 * 305032 * 2
def baseEnd_305032 : Nat := 92816610964358989390927

theorem tailTrace_305032 : CollatzResearch.WordTrace tailWord_305032 prefixEnd_305032 92816610964358989390927 := by
  unfold tailWord_305032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562715515464317081594675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7416954020619089442126233 5562715515464317081594675)
  ·
    refine ⟨8344073273196475622392013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5562715515464317081594675 8344073273196475622392013)
    ·
      refine ⟨3129027477448678358397005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8344073273196475622392013 3129027477448678358397005)
      ·
        refine ⟨1173385304043254384398877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3129027477448678358397005 1173385304043254384398877)
        ·
          refine ⟨440019489016220394149579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1173385304043254384398877 440019489016220394149579)
          ·
            refine ⟨660029233524330591224369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440019489016220394149579 660029233524330591224369)
            ·
              refine ⟨495021925143247943418277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660029233524330591224369 495021925143247943418277)
              ·
                refine ⟨92816610964358989390927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495021925143247943418277 92816610964358989390927)
                ·
                  rfl

theorem cell19_305032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_305032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305032 prefixEnd_305032 := by exact prefixLift 305032
  have htrace : WordTrace (prefixWord ++ tailWord_305032) baseStart_305032 baseEnd_305032 := by
    simpa [prefixWord, tailWord_305032, baseEnd_305032] using wordTrace_append hprefix tailTrace_305032
  have hstable : (prefixWord ++ tailWord_305032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305032).length < 2 ^ (prefixWord ++ tailWord_305032).sum := by decide
  have hdescent : baseEnd_305032 < baseStart_305032 := by decide
  rcases family_descends (prefixWord ++ tailWord_305032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305053 : List Nat := [1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_305053 : Nat := 118140960795 + 305053 * 2 ^ 59
def prefixEnd_305053 : Nat := 4983230072969 + 3 ^ 40 * 305053 * 2
def baseEnd_305053 : Nat := 92823000945837162924203

theorem tailTrace_305053 : CollatzResearch.WordTrace tailWord_305053 prefixEnd_305053 92823000945837162924203 := by
  unfold tailWord_305053
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126196963852554749703813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7417464642568369833135875 11126196963852554749703813)
  ·
    refine ⟨2086161930722354015569465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11126196963852554749703813 2086161930722354015569465)
    ·
      refine ⟨1564621448041765511677099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2086161930722354015569465 1564621448041765511677099)
      ·
        refine ⟨2346932172062648267515649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564621448041765511677099 2346932172062648267515649)
        ·
          refine ⟨1760199129046986200636737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346932172062648267515649 1760199129046986200636737)
          ·
            refine ⟨1320149346785239650477553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760199129046986200636737 1320149346785239650477553)
            ·
              refine ⟨990112010088929737858165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320149346785239650477553 990112010088929737858165)
              ·
                refine ⟨92823000945837162924203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 990112010088929737858165 92823000945837162924203)
                ·
                  rfl

theorem cell19_305053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_305053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305053 prefixEnd_305053 := by exact prefixLift 305053
  have htrace : WordTrace (prefixWord ++ tailWord_305053) baseStart_305053 baseEnd_305053 := by
    simpa [prefixWord, tailWord_305053, baseEnd_305053] using wordTrace_append hprefix tailTrace_305053
  have hstable : (prefixWord ++ tailWord_305053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305053).length < 2 ^ (prefixWord ++ tailWord_305053).sum := by decide
  have hdescent : baseEnd_305053 < baseStart_305053 := by decide
  rcases family_descends (prefixWord ++ tailWord_305053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305093 : List Nat := [1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_305093 : Nat := 118140960795 + 305093 * 2 ^ 59
def prefixEnd_305093 : Nat := 4983230072969 + 3 ^ 40 * 305093 * 2
def baseEnd_305093 : Nat := 92835172339128922035205

theorem tailTrace_305093 : CollatzResearch.WordTrace tailWord_305093 prefixEnd_305093 92835172339128922035205 := by
  unfold tailWord_305093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127655883707641581159933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7418437255805094387439955 11127655883707641581159933)
  ·
    refine ⟨4172870956390365592934975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11127655883707641581159933 4172870956390365592934975)
    ·
      refine ⟨6259306434585548389402463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172870956390365592934975 6259306434585548389402463)
      ·
        refine ⟨9388959651878322584103695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6259306434585548389402463 9388959651878322584103695)
        ·
          refine ⟨14083439477817483876155543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388959651878322584103695 14083439477817483876155543)
          ·
            refine ⟨21125159216726225814233315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14083439477817483876155543 21125159216726225814233315)
            ·
              refine ⟨31687738825089338721349973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21125159216726225814233315 31687738825089338721349973)
              ·
                refine ⟨92835172339128922035205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31687738825089338721349973 92835172339128922035205)
                ·
                  rfl

theorem cell19_305093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_305093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305093 prefixEnd_305093 := by exact prefixLift 305093
  have htrace : WordTrace (prefixWord ++ tailWord_305093) baseStart_305093 baseEnd_305093 := by
    simpa [prefixWord, tailWord_305093, baseEnd_305093] using wordTrace_append hprefix tailTrace_305093
  have hstable : (prefixWord ++ tailWord_305093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305093).length < 2 ^ (prefixWord ++ tailWord_305093).sum := by decide
  have hdescent : baseEnd_305093 < baseStart_305093 := by decide
  rcases family_descends (prefixWord ++ tailWord_305093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305106 : List Nat := [3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_305106 : Nat := 118140960795 + 305106 * 2 ^ 59
def prefixEnd_305106 : Nat := 4983230072969 + 3 ^ 40 * 305106 * 2
def baseEnd_305106 : Nat := 92839128041948743746281

theorem tailTrace_305106 : CollatzResearch.WordTrace tailWord_305106 prefixEnd_305106 92839128041948743746281 := by
  unfold tailWord_305106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782032508165136200345793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7418753355107029867588781 2782032508165136200345793)
  ·
    refine ⟨2086524381123852150259345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2782032508165136200345793 2086524381123852150259345)
    ·
      refine ⟨1564893285842889112694509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2086524381123852150259345 1564893285842889112694509)
      ·
        refine ⟨586834982191083417260441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1564893285842889112694509 586834982191083417260441)
        ·
          refine ⟨440126236643312562945331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586834982191083417260441 440126236643312562945331)
          ·
            refine ⟨660189354964968844417997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440126236643312562945331 660189354964968844417997)
            ·
              refine ⟨247571008111863316656749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660189354964968844417997 247571008111863316656749)
              ·
                refine ⟨92839128041948743746281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247571008111863316656749 92839128041948743746281)
                ·
                  rfl

theorem cell19_305106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_305106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305106 prefixEnd_305106 := by exact prefixLift 305106
  have htrace : WordTrace (prefixWord ++ tailWord_305106) baseStart_305106 baseEnd_305106 := by
    simpa [prefixWord, tailWord_305106, baseEnd_305106] using wordTrace_append hprefix tailTrace_305106
  have hstable : (prefixWord ++ tailWord_305106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305106).length < 2 ^ (prefixWord ++ tailWord_305106).sum := by decide
  have hdescent : baseEnd_305106 < baseStart_305106 := by decide
  rcases family_descends (prefixWord ++ tailWord_305106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305108 : List Nat := [2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_305108 : Nat := 118140960795 + 305108 * 2 ^ 59
def prefixEnd_305108 : Nat := 4983230072969 + 3 ^ 40 * 305108 * 2
def baseEnd_305108 : Nat := 92839736611613331701831

theorem tailTrace_305108 : CollatzResearch.WordTrace tailWord_305108 prefixEnd_305108 92839736611613331701831 := by
  unfold tailWord_305108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5564101489326649571477989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7418801985768866095303985 5564101489326649571477989)
  ·
    refine ⟨1043269029248746794652123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5564101489326649571477989 1043269029248746794652123)
    ·
      refine ⟨1564903543873120191978185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043269029248746794652123 1564903543873120191978185)
      ·
        refine ⟨1173677657904840143983639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1564903543873120191978185 1173677657904840143983639)
        ·
          refine ⟨1760516486857260215975459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173677657904840143983639 1760516486857260215975459)
          ·
            refine ⟨2640774730285890323963189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760516486857260215975459 2640774730285890323963189)
            ·
              refine ⟨247572630964302217871549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2640774730285890323963189 247572630964302217871549)
              ·
                refine ⟨92839736611613331701831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247572630964302217871549 92839736611613331701831)
                ·
                  rfl

theorem cell19_305108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_305108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305108 prefixEnd_305108 := by exact prefixLift 305108
  have htrace : WordTrace (prefixWord ++ tailWord_305108) baseStart_305108 baseEnd_305108 := by
    simpa [prefixWord, tailWord_305108, baseEnd_305108] using wordTrace_append hprefix tailTrace_305108
  have hstable : (prefixWord ++ tailWord_305108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305108).length < 2 ^ (prefixWord ++ tailWord_305108).sum := by decide
  have hdescent : baseEnd_305108 < baseStart_305108 := by decide
  rcases family_descends (prefixWord ++ tailWord_305108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305207 : List Nat := [1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_305207 : Nat := 118140960795 + 305207 * 2 ^ 59
def prefixEnd_305207 : Nat := 4983230072969 + 3 ^ 40 * 305207 * 2
def baseEnd_305207 : Nat := 92869860810010435501561

theorem tailTrace_305207 : CollatzResearch.WordTrace tailWord_305207 prefixEnd_305207 92869860810010435501561 := by
  unfold tailWord_305207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131813805294639050809875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7421209203529759367206583 11131813805294639050809875)
  ·
    refine ⟨16697720707941958576214813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11131813805294639050809875 16697720707941958576214813)
    ·
      refine ⟨6261645265478234466080555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16697720707941958576214813 6261645265478234466080555)
      ·
        refine ⟨9392467898217351699120833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261645265478234466080555 9392467898217351699120833)
        ·
          refine ⟨7044350923663013774340625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9392467898217351699120833 7044350923663013774340625)
          ·
            refine ⟨5283263192747260330755469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7044350923663013774340625 5283263192747260330755469)
            ·
              refine ⟨1981223697280222624033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5283263192747260330755469 1981223697280222624033301)
              ·
                refine ⟨92869860810010435501561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1981223697280222624033301 92869860810010435501561)
                ·
                  rfl

theorem cell19_305207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_305207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305207 prefixEnd_305207 := by exact prefixLift 305207
  have htrace : WordTrace (prefixWord ++ tailWord_305207) baseStart_305207 baseEnd_305207 := by
    simpa [prefixWord, tailWord_305207, baseEnd_305207] using wordTrace_append hprefix tailTrace_305207
  have hstable : (prefixWord ++ tailWord_305207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305207).length < 2 ^ (prefixWord ++ tailWord_305207).sum := by decide
  have hdescent : baseEnd_305207 < baseStart_305207 := by decide
  rcases family_descends (prefixWord ++ tailWord_305207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305222 : List Nat := [6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_305222 : Nat := 118140960795 + 305222 * 2 ^ 59
def prefixEnd_305222 : Nat := 4983230072969 + 3 ^ 40 * 305222 * 2
def baseEnd_305222 : Nat := 92874425082494845168187

theorem tailTrace_305222 : CollatzResearch.WordTrace tailWord_305222 prefixEnd_305222 92874425082494845168187 := by
  unfold tailWord_305222
  simp only [CollatzResearch.WordTrace]
  refine ⟨347886278132509269143935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7421573933493531075070613 347886278132509269143935)
  ·
    refine ⟨521829417198763903715903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347886278132509269143935 521829417198763903715903)
    ·
      refine ⟨782744125798145855573855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521829417198763903715903 782744125798145855573855)
      ·
        refine ⟨1174116188697218783360783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782744125798145855573855 1174116188697218783360783)
        ·
          refine ⟨1761174283045828175041175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174116188697218783360783 1761174283045828175041175)
          ·
            refine ⟨2641761424568742262561763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761174283045828175041175 2641761424568742262561763)
            ·
              refine ⟨3962642136853113393842645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641761424568742262561763 3962642136853113393842645)
              ·
                refine ⟨92874425082494845168187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3962642136853113393842645 92874425082494845168187)
                ·
                  rfl

theorem cell19_305222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_305222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305222 prefixEnd_305222 := by exact prefixLift 305222
  have htrace : WordTrace (prefixWord ++ tailWord_305222) baseStart_305222 baseEnd_305222 := by
    simpa [prefixWord, tailWord_305222, baseEnd_305222] using wordTrace_append hprefix tailTrace_305222
  have hstable : (prefixWord ++ tailWord_305222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305222).length < 2 ^ (prefixWord ++ tailWord_305222).sum := by decide
  have hdescent : baseEnd_305222 < baseStart_305222 := by decide
  rcases family_descends (prefixWord ++ tailWord_305222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305258 : List Nat := [3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_305258 : Nat := 118140960795 + 305258 * 2 ^ 59
def prefixEnd_305258 : Nat := 4983230072969 + 3 ^ 40 * 305258 * 2
def baseEnd_305258 : Nat := 92885379336457428368089

theorem tailTrace_305258 : CollatzResearch.WordTrace tailWord_305258 prefixEnd_305258 92885379336457428368089 := by
  unfold tailWord_305258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783418482027468690229107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7422449285406583173944285 2783418482027468690229107)
  ·
    refine ⟨4175127723041203035343661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783418482027468690229107 4175127723041203035343661)
    ·
      refine ⟨1565672896140451138253873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4175127723041203035343661 1565672896140451138253873)
      ·
        refine ⟨1174254672105338353690405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1565672896140451138253873 1174254672105338353690405)
        ·
          refine ⟨220172751019750941316951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1174254672105338353690405 220172751019750941316951)
          ·
            refine ⟨330259126529626411975427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220172751019750941316951 330259126529626411975427)
            ·
              refine ⟨495388689794439617963141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330259126529626411975427 495388689794439617963141)
              ·
                refine ⟨92885379336457428368089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495388689794439617963141 92885379336457428368089)
                ·
                  rfl

theorem cell19_305258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_305258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305258 prefixEnd_305258 := by exact prefixLift 305258
  have htrace : WordTrace (prefixWord ++ tailWord_305258) baseStart_305258 baseEnd_305258 := by
    simpa [prefixWord, tailWord_305258, baseEnd_305258] using wordTrace_append hprefix tailTrace_305258
  have hstable : (prefixWord ++ tailWord_305258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305258).length < 2 ^ (prefixWord ++ tailWord_305258).sum := by decide
  have hdescent : baseEnd_305258 < baseStart_305258 := by decide
  rcases family_descends (prefixWord ++ tailWord_305258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305332 : List Nat := [2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_305332 : Nat := 118140960795 + 305332 * 2 ^ 59
def prefixEnd_305332 : Nat := 4983230072969 + 3 ^ 40 * 305332 * 2
def baseEnd_305332 : Nat := 92907896414047182723443

theorem tailTrace_305332 : CollatzResearch.WordTrace tailWord_305332 prefixEnd_305332 92907896414047182723443 := by
  unfold tailWord_305332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568186464920892699555125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7424248619894523599406833 5568186464920892699555125)
  ·
    refine ⟨522017481086333690583293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5568186464920892699555125 522017481086333690583293)
    ·
      refine ⟨195756555407375133968735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 522017481086333690583293 195756555407375133968735)
      ·
        refine ⟨293634833111062700953103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195756555407375133968735 293634833111062700953103)
        ·
          refine ⟨440452249666594051429655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293634833111062700953103 440452249666594051429655)
          ·
            refine ⟨660678374499891077144483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440452249666594051429655 660678374499891077144483)
            ·
              refine ⟨991017561749836615716725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660678374499891077144483 991017561749836615716725)
              ·
                refine ⟨92907896414047182723443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 991017561749836615716725 92907896414047182723443)
                ·
                  rfl

theorem cell19_305332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_305332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305332 prefixEnd_305332 := by exact prefixLift 305332
  have htrace : WordTrace (prefixWord ++ tailWord_305332) baseStart_305332 baseEnd_305332 := by
    simpa [prefixWord, tailWord_305332, baseEnd_305332] using wordTrace_append hprefix tailTrace_305332
  have hstable : (prefixWord ++ tailWord_305332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305332).length < 2 ^ (prefixWord ++ tailWord_305332).sum := by decide
  have hdescent : baseEnd_305332 < baseStart_305332 := by decide
  rcases family_descends (prefixWord ++ tailWord_305332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305338 : List Nat := [3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_305338 : Nat := 118140960795 + 305338 * 2 ^ 59
def prefixEnd_305338 : Nat := 4983230072969 + 3 ^ 40 * 305338 * 2
def baseEnd_305338 : Nat := 92909722123040946590093

theorem tailTrace_305338 : CollatzResearch.WordTrace tailWord_305338 prefixEnd_305338 92909722123040946590093 := by
  unfold tailWord_305338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784147941955012105957167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7424394511880032282552445 2784147941955012105957167)
  ·
    refine ⟨4176221912932518158935751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784147941955012105957167 4176221912932518158935751)
    ·
      refine ⟨6264332869398777238403627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176221912932518158935751 6264332869398777238403627)
      ·
        refine ⟨9396499304098165857605441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264332869398777238403627 9396499304098165857605441)
        ·
          refine ⟨7047374478073624393204081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9396499304098165857605441 7047374478073624393204081)
          ·
            refine ⟨5285530858555218294903061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7047374478073624393204081 5285530858555218294903061)
            ·
              refine ⟨247759258994775857573581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5285530858555218294903061 247759258994775857573581)
              ·
                refine ⟨92909722123040946590093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247759258994775857573581 92909722123040946590093)
                ·
                  rfl

theorem cell19_305338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_305338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305338 prefixEnd_305338 := by exact prefixLift 305338
  have htrace : WordTrace (prefixWord ++ tailWord_305338) baseStart_305338 baseEnd_305338 := by
    simpa [prefixWord, tailWord_305338, baseEnd_305338] using wordTrace_append hprefix tailTrace_305338
  have hstable : (prefixWord ++ tailWord_305338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305338).length < 2 ^ (prefixWord ++ tailWord_305338).sum := by decide
  have hdescent : baseEnd_305338 < baseStart_305338 := by decide
  rcases family_descends (prefixWord ++ tailWord_305338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305372 : List Nat := [2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_305372 : Nat := 118140960795 + 305372 * 2 ^ 59
def prefixEnd_305372 : Nat := 4983230072969 + 3 ^ 40 * 305372 * 2
def baseEnd_305372 : Nat := 92920067807338941834445

theorem tailTrace_305372 : CollatzResearch.WordTrace tailWord_305372 prefixEnd_305372 92920067807338941834445 := by
  unfold tailWord_305372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568915924848436115283185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7425221233131248153710913 5568915924848436115283185)
  ·
    refine ⟨4176686943636327086462389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5568915924848436115283185 4176686943636327086462389)
    ·
      refine ⟨391564400965905664355849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4176686943636327086462389 391564400965905664355849)
      ·
        refine ⟨293673300724429248266887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391564400965905664355849 293673300724429248266887)
        ·
          refine ⟨440509951086643872400331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293673300724429248266887 440509951086643872400331)
          ·
            refine ⟨660764926629965808600497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440509951086643872400331 660764926629965808600497)
            ·
              refine ⟨495573694972474356450373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660764926629965808600497 495573694972474356450373)
              ·
                refine ⟨92920067807338941834445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495573694972474356450373 92920067807338941834445)
                ·
                  rfl

theorem cell19_305372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_305372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305372 prefixEnd_305372 := by exact prefixLift 305372
  have htrace : WordTrace (prefixWord ++ tailWord_305372) baseStart_305372 baseEnd_305372 := by
    simpa [prefixWord, tailWord_305372, baseEnd_305372] using wordTrace_append hprefix tailTrace_305372
  have hstable : (prefixWord ++ tailWord_305372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305372).length < 2 ^ (prefixWord ++ tailWord_305372).sum := by decide
  have hdescent : baseEnd_305372 < baseStart_305372 := by decide
  rcases family_descends (prefixWord ++ tailWord_305372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305416 : List Nat := [2, 1, 3, 2, 3, 8]
def baseStart_305416 : Nat := 118140960795 + 305416 * 2 ^ 59
def prefixEnd_305416 : Nat := 4983230072969 + 3 ^ 40 * 305416 * 2
def baseEnd_305416 : Nat := 10325939593328875206283

theorem tailTrace_305416 : CollatzResearch.WordTrace tailWord_305416 prefixEnd_305416 10325939593328875206283 := by
  unfold tailWord_305416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5569718330768733872584051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7426291107691645163445401 5569718330768733872584051)
  ·
    refine ⟨8354577496153100808876077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5569718330768733872584051 8354577496153100808876077)
    ·
      refine ⟨3132966561057412803328529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8354577496153100808876077 3132966561057412803328529)
      ·
        refine ⟨2349724920793059602496397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3132966561057412803328529 2349724920793059602496397)
        ·
          refine ⟨881146845297397350936149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2349724920793059602496397 881146845297397350936149)
          ·
            refine ⟨10325939593328875206283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 881146845297397350936149 10325939593328875206283)
            ·
              rfl

theorem cell19_305416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_305416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305416 prefixEnd_305416 := by exact prefixLift 305416
  have htrace : WordTrace (prefixWord ++ tailWord_305416) baseStart_305416 baseEnd_305416 := by
    simpa [prefixWord, tailWord_305416, baseEnd_305416] using wordTrace_append hprefix tailTrace_305416
  have hstable : (prefixWord ++ tailWord_305416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305416).length < 2 ^ (prefixWord ++ tailWord_305416).sum := by decide
  have hdescent : baseEnd_305416 < baseStart_305416 := by decide
  rcases family_descends (prefixWord ++ tailWord_305416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305435 : List Nat := [1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_305435 : Nat := 118140960795 + 305435 * 2 ^ 59
def prefixEnd_305435 : Nat := 4983230072969 + 3 ^ 40 * 305435 * 2
def baseEnd_305435 : Nat := 92939237751773462434273

theorem tailTrace_305435 : CollatzResearch.WordTrace tailWord_305435 prefixEnd_305435 92939237751773462434273 := by
  unfold tailWord_305435
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140129648468633990109759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7426753098979089326739839 11140129648468633990109759)
  ·
    refine ⟨16710194472702950985164639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11140129648468633990109759 16710194472702950985164639)
    ·
      refine ⟨25065291709054426477746959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16710194472702950985164639 25065291709054426477746959)
      ·
        refine ⟨37597937563581639716620439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25065291709054426477746959 37597937563581639716620439)
        ·
          refine ⟨56396906345372459574930659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37597937563581639716620439 56396906345372459574930659)
          ·
            refine ⟨84595359518058689362395989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56396906345372459574930659 84595359518058689362395989)
            ·
              refine ⟨495675934676125132982789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 84595359518058689362395989 495675934676125132982789)
              ·
                refine ⟨92939237751773462434273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495675934676125132982789 92939237751773462434273)
                ·
                  rfl

theorem cell19_305435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_305435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305435 prefixEnd_305435 := by exact prefixLift 305435
  have htrace : WordTrace (prefixWord ++ tailWord_305435) baseStart_305435 baseEnd_305435 := by
    simpa [prefixWord, tailWord_305435, baseEnd_305435] using wordTrace_append hprefix tailTrace_305435
  have hstable : (prefixWord ++ tailWord_305435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305435).length < 2 ^ (prefixWord ++ tailWord_305435).sum := by decide
  have hdescent : baseEnd_305435 < baseStart_305435 := by decide
  rcases family_descends (prefixWord ++ tailWord_305435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305509 : List Nat := [1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_305509 : Nat := 118140960795 + 305509 * 2 ^ 59
def prefixEnd_305509 : Nat := 4983230072969 + 3 ^ 40 * 305509 * 2
def baseEnd_305509 : Nat := 92961754829363216789627

theorem tailTrace_305509 : CollatzResearch.WordTrace tailWord_305509 prefixEnd_305509 92961754829363216789627 := by
  unfold tailWord_305509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142828650200544628303581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7428552433467029752202387 11142828650200544628303581)
  ·
    refine ⟨4178560743825204235613843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11142828650200544628303581 4178560743825204235613843)
    ·
      refine ⟨6267841115737806353420765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178560743825204235613843 6267841115737806353420765)
      ·
        refine ⟨2350440418401677382532787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6267841115737806353420765 2350440418401677382532787)
        ·
          refine ⟨3525660627602516073799181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350440418401677382532787 3525660627602516073799181)
          ·
            refine ⟨1322122735350943527674693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3525660627602516073799181 1322122735350943527674693)
            ·
              refine ⟨247898012878301911439005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1322122735350943527674693 247898012878301911439005)
              ·
                refine ⟨92961754829363216789627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247898012878301911439005 92961754829363216789627)
                ·
                  rfl

theorem cell19_305509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_305509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305509 prefixEnd_305509 := by exact prefixLift 305509
  have htrace : WordTrace (prefixWord ++ tailWord_305509) baseStart_305509 baseEnd_305509 := by
    simpa [prefixWord, tailWord_305509, baseEnd_305509] using wordTrace_append hprefix tailTrace_305509
  have hstable : (prefixWord ++ tailWord_305509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305509).length < 2 ^ (prefixWord ++ tailWord_305509).sum := by decide
  have hdescent : baseEnd_305509 < baseStart_305509 := by decide
  rcases family_descends (prefixWord ++ tailWord_305509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305568 : List Nat := [2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_305568 : Nat := 118140960795 + 305568 * 2 ^ 59
def prefixEnd_305568 : Nat := 4983230072969 + 3 ^ 40 * 305568 * 2
def baseEnd_305568 : Nat := 92979707634468561478355

theorem tailTrace_305568 : CollatzResearch.WordTrace tailWord_305568 prefixEnd_305568 92979707634468561478355 := by
  unfold tailWord_305568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572490278493398852350679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7429987037991198469800905 5572490278493398852350679)
  ·
    refine ⟨8358735417740098278526019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5572490278493398852350679 8358735417740098278526019)
    ·
      refine ⟨12538103126610147417789029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8358735417740098278526019 12538103126610147417789029)
      ·
        refine ⟨2350894336239402640835443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12538103126610147417789029 2350894336239402640835443)
        ·
          refine ⟨3526341504359103961253165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350894336239402640835443 3526341504359103961253165)
          ·
            refine ⟨1322378064134663985469937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3526341504359103961253165 1322378064134663985469937)
            ·
              refine ⟨991783548100997989102453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322378064134663985469937 991783548100997989102453)
              ·
                refine ⟨92979707634468561478355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 991783548100997989102453 92979707634468561478355)
                ·
                  rfl

theorem cell19_305568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_305568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305568 prefixEnd_305568 := by exact prefixLift 305568
  have htrace : WordTrace (prefixWord ++ tailWord_305568) baseStart_305568 baseEnd_305568 := by
    simpa [prefixWord, tailWord_305568, baseEnd_305568] using wordTrace_append hprefix tailTrace_305568
  have hstable : (prefixWord ++ tailWord_305568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305568).length < 2 ^ (prefixWord ++ tailWord_305568).sum := by decide
  have hdescent : baseEnd_305568 < baseStart_305568 := by decide
  rcases family_descends (prefixWord ++ tailWord_305568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305678 : List Nat := [4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_305678 : Nat := 118140960795 + 305678 * 2 ^ 59
def prefixEnd_305678 : Nat := 4983230072969 + 3 ^ 40 * 305678 * 2
def baseEnd_305678 : Nat := 93013178966020899033611

theorem tailTrace_305678 : CollatzResearch.WordTrace tailWord_305678 prefixEnd_305678 93013178966020899033611 := by
  unfold tailWord_305678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393624073323535811400711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7432661724392190994137125 1393624073323535811400711)
  ·
    refine ⟨2090436109985303717101067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393624073323535811400711 2090436109985303717101067)
    ·
      refine ⟨3135654164977955575651601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090436109985303717101067 3135654164977955575651601)
      ·
        refine ⟨2351740623733466681738701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3135654164977955575651601 2351740623733466681738701)
        ·
          refine ⟨881902733900050005652013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351740623733466681738701 881902733900050005652013)
          ·
            refine ⟨330713525212518752119505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 881902733900050005652013 330713525212518752119505)
            ·
              refine ⟨248035143909389064089629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330713525212518752119505 248035143909389064089629)
              ·
                refine ⟨93013178966020899033611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248035143909389064089629 93013178966020899033611)
                ·
                  rfl

theorem cell19_305678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_305678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305678 prefixEnd_305678 := by exact prefixLift 305678
  have htrace : WordTrace (prefixWord ++ tailWord_305678) baseStart_305678 baseEnd_305678 := by
    simpa [prefixWord, tailWord_305678, baseEnd_305678] using wordTrace_append hprefix tailTrace_305678
  have hstable : (prefixWord ++ tailWord_305678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305678).length < 2 ^ (prefixWord ++ tailWord_305678).sum := by decide
  have hdescent : baseEnd_305678 < baseStart_305678 := by decide
  rcases family_descends (prefixWord ++ tailWord_305678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305718 : List Nat := [5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_305718 : Nat := 118140960795 + 305718 * 2 ^ 59
def prefixEnd_305718 : Nat := 4983230072969 + 3 ^ 40 * 305718 * 2
def baseEnd_305718 : Nat := 93025350359312658144613

theorem tailTrace_305718 : CollatzResearch.WordTrace tailWord_305718 prefixEnd_305718 93025350359312658144613 := by
  unfold tailWord_305718
  simp only [CollatzResearch.WordTrace]
  refine ⟨696903219152710832666363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7433634337628915548441205 696903219152710832666363)
  ·
    refine ⟨1045354828729066248999545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696903219152710832666363 1045354828729066248999545)
    ·
      refine ⟨784016121546799686749659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1045354828729066248999545 784016121546799686749659)
      ·
        refine ⟨1176024182320199530124489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784016121546799686749659 1176024182320199530124489)
        ·
          refine ⟨882018136740149647593367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176024182320199530124489 882018136740149647593367)
          ·
            refine ⟨1323027205110224471390051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882018136740149647593367 1323027205110224471390051)
            ·
              refine ⟨1984540807665336707085077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323027205110224471390051 1984540807665336707085077)
              ·
                refine ⟨93025350359312658144613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1984540807665336707085077 93025350359312658144613)
                ·
                  rfl

theorem cell19_305718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_305718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305718 prefixEnd_305718 := by exact prefixLift 305718
  have htrace : WordTrace (prefixWord ++ tailWord_305718) baseStart_305718 baseEnd_305718 := by
    simpa [prefixWord, tailWord_305718, baseEnd_305718] using wordTrace_append hprefix tailTrace_305718
  have hstable : (prefixWord ++ tailWord_305718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305718).length < 2 ^ (prefixWord ++ tailWord_305718).sum := by decide
  have hdescent : baseEnd_305718 < baseStart_305718 := by decide
  rcases family_descends (prefixWord ++ tailWord_305718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305720 : List Nat := [2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_305720 : Nat := 118140960795 + 305720 * 2 ^ 59
def prefixEnd_305720 : Nat := 4983230072969 + 3 ^ 40 * 305720 * 2
def baseEnd_305720 : Nat := 93025958928977246100163

theorem tailTrace_305720 : CollatzResearch.WordTrace tailWord_305720 prefixEnd_305720 93025958928977246100163 := by
  unfold tailWord_305720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575262226218063832117307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7433682968290751776156409 5575262226218063832117307)
  ·
    refine ⟨8362893339327095748175961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5575262226218063832117307 8362893339327095748175961)
    ·
      refine ⟨6272170004495321811131971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8362893339327095748175961 6272170004495321811131971)
      ·
        refine ⟨9408255006742982716697957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272170004495321811131971 9408255006742982716697957)
        ·
          refine ⟨1764047813764309259380867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9408255006742982716697957 1764047813764309259380867)
          ·
            refine ⟨2646071720646463889071301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764047813764309259380867 2646071720646463889071301)
            ·
              refine ⟨496138447621211979200869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2646071720646463889071301 496138447621211979200869)
              ·
                refine ⟨93025958928977246100163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496138447621211979200869 93025958928977246100163)
                ·
                  rfl

theorem cell19_305720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_305720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305720 prefixEnd_305720 := by exact prefixLift 305720
  have htrace : WordTrace (prefixWord ++ tailWord_305720) baseStart_305720 baseEnd_305720 := by
    simpa [prefixWord, tailWord_305720, baseEnd_305720] using wordTrace_append hprefix tailTrace_305720
  have hstable : (prefixWord ++ tailWord_305720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305720).length < 2 ^ (prefixWord ++ tailWord_305720).sum := by decide
  have hdescent : baseEnd_305720 < baseStart_305720 := by decide
  rcases family_descends (prefixWord ++ tailWord_305720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305756 : List Nat := [2, 2, 4, 1, 4, 6]
def baseStart_305756 : Nat := 118140960795 + 305756 * 2 ^ 59
def prefixEnd_305756 : Nat := 4983230072969 + 3 ^ 40 * 305756 * 2
def baseEnd_305756 : Nat := 10337434798104425477785

theorem tailTrace_305756 : CollatzResearch.WordTrace tailWord_305756 prefixEnd_305756 10337434798104425477785 := by
  unfold tailWord_305756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575918740152852906272561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7434558320203803875030081 5575918740152852906272561)
  ·
    refine ⟨4181939055114639679704421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5575918740152852906272561 4181939055114639679704421)
    ·
      refine ⟨784113572833994939944579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4181939055114639679704421 784113572833994939944579)
      ·
        refine ⟨1176170359250992409916869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784113572833994939944579 1176170359250992409916869)
        ·
          refine ⟨220531942359561076859413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1176170359250992409916869 220531942359561076859413)
          ·
            refine ⟨10337434798104425477785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220531942359561076859413 10337434798104425477785)
            ·
              rfl

theorem cell19_305756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_305756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305756 prefixEnd_305756 := by exact prefixLift 305756
  have htrace : WordTrace (prefixWord ++ tailWord_305756) baseStart_305756 baseEnd_305756 := by
    simpa [prefixWord, tailWord_305756, baseEnd_305756] using wordTrace_append hprefix tailTrace_305756
  have hstable : (prefixWord ++ tailWord_305756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305756).length < 2 ^ (prefixWord ++ tailWord_305756).sum := by decide
  have hdescent : baseEnd_305756 < baseStart_305756 := by decide
  rcases family_descends (prefixWord ++ tailWord_305756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305779 : List Nat := [1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_305779 : Nat := 118140960795 + 305779 * 2 ^ 59
def prefixEnd_305779 : Nat := 4983230072969 + 3 ^ 40 * 305779 * 2
def baseEnd_305779 : Nat := 93043911734082590788891

theorem tailTrace_305779 : CollatzResearch.WordTrace tailWord_305779 prefixEnd_305779 93043911734082590788891 := by
  unfold tailWord_305779
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152676359222380740632391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7435117572814920493754927 11152676359222380740632391)
  ·
    refine ⟨16729014538833571110948587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11152676359222380740632391 16729014538833571110948587)
    ·
      refine ⟨25093521808250356666422881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16729014538833571110948587 25093521808250356666422881)
      ·
        refine ⟨18820141356187767499817161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25093521808250356666422881 18820141356187767499817161)
        ·
          refine ⟨14115106017140825624862871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18820141356187767499817161 14115106017140825624862871)
          ·
            refine ⟨21172659025711238437294307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14115106017140825624862871 21172659025711238437294307)
            ·
              refine ⟨31758988538566857655941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21172659025711238437294307 31758988538566857655941461)
              ·
                refine ⟨93043911734082590788891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31758988538566857655941461 93043911734082590788891)
                ·
                  rfl

theorem cell19_305779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_305779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305779 prefixEnd_305779 := by exact prefixLift 305779
  have htrace : WordTrace (prefixWord ++ tailWord_305779) baseStart_305779 baseEnd_305779 := by
    simpa [prefixWord, tailWord_305779, baseEnd_305779] using wordTrace_append hprefix tailTrace_305779
  have hstable : (prefixWord ++ tailWord_305779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305779).length < 2 ^ (prefixWord ++ tailWord_305779).sum := by decide
  have hdescent : baseEnd_305779 < baseStart_305779 := by decide
  rcases family_descends (prefixWord ++ tailWord_305779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305817 : List Nat := [1, 2, 1, 2, 1, 2, 10]
def baseStart_305817 : Nat := 118140960795 + 305817 * 2 ^ 59
def prefixEnd_305817 : Nat := 4983230072969 + 3 ^ 40 * 305817 * 2
def baseEnd_305817 : Nat := 31018491519236587314781

theorem tailTrace_305817 : CollatzResearch.WordTrace tailWord_305817 prefixEnd_305817 31018491519236587314781 := by
  unfold tailWord_305817
  simp only [CollatzResearch.WordTrace]
  refine ⟨11154062333084713230515705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7436041555389808820343803 11154062333084713230515705)
  ·
    refine ⟨8365546749813534922886779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11154062333084713230515705 8365546749813534922886779)
    ·
      refine ⟨12548320124720302384330169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8365546749813534922886779 12548320124720302384330169)
      ·
        refine ⟨9411240093540226788247627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12548320124720302384330169 9411240093540226788247627)
        ·
          refine ⟨14116860140310340182371441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9411240093540226788247627 14116860140310340182371441)
          ·
            refine ⟨10587645105232755136778581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14116860140310340182371441 10587645105232755136778581)
            ·
              refine ⟨31018491519236587314781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10587645105232755136778581 31018491519236587314781)
              ·
                rfl

theorem cell19_305817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_305817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305817 prefixEnd_305817 := by exact prefixLift 305817
  have htrace : WordTrace (prefixWord ++ tailWord_305817) baseStart_305817 baseEnd_305817 := by
    simpa [prefixWord, tailWord_305817, baseEnd_305817] using wordTrace_append hprefix tailTrace_305817
  have hstable : (prefixWord ++ tailWord_305817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305817).length < 2 ^ (prefixWord ++ tailWord_305817).sum := by decide
  have hdescent : baseEnd_305817 < baseStart_305817 := by decide
  rcases family_descends (prefixWord ++ tailWord_305817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305853 : List Nat := [1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_305853 : Nat := 118140960795 + 305853 * 2 ^ 59
def prefixEnd_305853 : Nat := 4983230072969 + 3 ^ 40 * 305853 * 2
def baseEnd_305853 : Nat := 93066428811672345144245

theorem tailTrace_305853 : CollatzResearch.WordTrace tailWord_305853 prefixEnd_305853 93066428811672345144245 := by
  unfold tailWord_305853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155375360954291378826213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7436916907302860919217475 11155375360954291378826213)
  ·
    refine ⟨2091632880178929633529915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11155375360954291378826213 2091632880178929633529915)
    ·
      refine ⟨3137449320268394450294873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2091632880178929633529915 3137449320268394450294873)
      ·
        refine ⟨2353086990201295837721155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3137449320268394450294873 2353086990201295837721155)
        ·
          refine ⟨3529630485301943756581733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353086990201295837721155 3529630485301943756581733)
          ·
            refine ⟨661805715994114454359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3529630485301943756581733 661805715994114454359075)
            ·
              refine ⟨992708573991171681538613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661805715994114454359075 992708573991171681538613)
              ·
                refine ⟨93066428811672345144245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 992708573991171681538613 93066428811672345144245)
                ·
                  rfl

theorem cell19_305853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_305853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305853 prefixEnd_305853 := by exact prefixLift 305853
  have htrace : WordTrace (prefixWord ++ tailWord_305853) baseStart_305853 baseEnd_305853 := by
    simpa [prefixWord, tailWord_305853, baseEnd_305853] using wordTrace_append hprefix tailTrace_305853
  have hstable : (prefixWord ++ tailWord_305853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305853).length < 2 ^ (prefixWord ++ tailWord_305853).sum := by decide
  have hdescent : baseEnd_305853 < baseStart_305853 := by decide
  rcases family_descends (prefixWord ++ tailWord_305853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305891 : List Nat := [1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_305891 : Nat := 118140960795 + 305891 * 2 ^ 59
def prefixEnd_305891 : Nat := 4983230072969 + 3 ^ 40 * 305891 * 2
def baseEnd_305891 : Nat := 93077991635299516299697

theorem tailTrace_305891 : CollatzResearch.WordTrace tailWord_305891 prefixEnd_305891 93077991635299516299697 := by
  unfold tailWord_305891
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156761334816623868709527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7437840889877749245806351 11156761334816623868709527)
  ·
    refine ⟨16735142002224935803064291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156761334816623868709527 16735142002224935803064291)
    ·
      refine ⟨25102713003337403704596437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16735142002224935803064291 25102713003337403704596437)
      ·
        refine ⟨588344836015720399326479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25102713003337403704596437 588344836015720399326479)
        ·
          refine ⟨882517254023580598989719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588344836015720399326479 882517254023580598989719)
          ·
            refine ⟨1323775881035370898484579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882517254023580598989719 1323775881035370898484579)
            ·
              refine ⟨1985663821553056347726869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323775881035370898484579 1985663821553056347726869)
              ·
                refine ⟨93077991635299516299697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1985663821553056347726869 93077991635299516299697)
                ·
                  rfl

theorem cell19_305891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_305891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305891 prefixEnd_305891 := by exact prefixLift 305891
  have htrace : WordTrace (prefixWord ++ tailWord_305891) baseStart_305891 baseEnd_305891 := by
    simpa [prefixWord, tailWord_305891, baseEnd_305891] using wordTrace_append hprefix tailTrace_305891
  have hstable : (prefixWord ++ tailWord_305891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305891).length < 2 ^ (prefixWord ++ tailWord_305891).sum := by decide
  have hdescent : baseEnd_305891 < baseStart_305891 := by decide
  rcases family_descends (prefixWord ++ tailWord_305891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305910 : List Nat := [5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_305910 : Nat := 118140960795 + 305910 * 2 ^ 59
def prefixEnd_305910 : Nat := 4983230072969 + 3 ^ 40 * 305910 * 2
def baseEnd_305910 : Nat := 93083773047113101877423

theorem tailTrace_305910 : CollatzResearch.WordTrace tailWord_305910 prefixEnd_305910 93083773047113101877423 := by
  unfold tailWord_305910
  simp only [CollatzResearch.WordTrace]
  refine ⟨697340895109236882103199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7438302881165193409100789 697340895109236882103199)
  ·
    refine ⟨1046011342663855323154799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697340895109236882103199 1046011342663855323154799)
    ·
      refine ⟨1569017013995782984732199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046011342663855323154799 1569017013995782984732199)
      ·
        refine ⟨2353525520993674477098299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569017013995782984732199 2353525520993674477098299)
        ·
          refine ⟨3530288281490511715647449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353525520993674477098299 3530288281490511715647449)
          ·
            refine ⟨2647716211117883786735587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530288281490511715647449 2647716211117883786735587)
            ·
              refine ⟨3971574316676825680103381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647716211117883786735587 3971574316676825680103381)
              ·
                refine ⟨93083773047113101877423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3971574316676825680103381 93083773047113101877423)
                ·
                  rfl

theorem cell19_305910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_305910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305910 prefixEnd_305910 := by exact prefixLift 305910
  have htrace : WordTrace (prefixWord ++ tailWord_305910) baseStart_305910 baseEnd_305910 := by
    simpa [prefixWord, tailWord_305910, baseEnd_305910] using wordTrace_append hprefix tailTrace_305910
  have hstable : (prefixWord ++ tailWord_305910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305910).length < 2 ^ (prefixWord ++ tailWord_305910).sum := by decide
  have hdescent : baseEnd_305910 < baseStart_305910 := by decide
  rcases family_descends (prefixWord ++ tailWord_305910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305912 : List Nat := [2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_305912 : Nat := 118140960795 + 305912 * 2 ^ 59
def prefixEnd_305912 : Nat := 4983230072969 + 3 ^ 40 * 305912 * 2
def baseEnd_305912 : Nat := 93084381616777689832973

theorem tailTrace_305912 : CollatzResearch.WordTrace tailWord_305912 prefixEnd_305912 93084381616777689832973 := by
  unfold tailWord_305912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578763633870272227611995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7438351511827029636815993 5578763633870272227611995)
  ·
    refine ⟨8368145450805408341417993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5578763633870272227611995 8368145450805408341417993)
    ·
      refine ⟨6276109088104056256063495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8368145450805408341417993 6276109088104056256063495)
      ·
        refine ⟨9414163632156084384095243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276109088104056256063495 9414163632156084384095243)
        ·
          refine ⟨14121245448234126576142865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9414163632156084384095243 14121245448234126576142865)
          ·
            refine ⟨10590934086175594932107149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14121245448234126576142865 10590934086175594932107149)
            ·
              refine ⟨3971600282315848099540181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10590934086175594932107149 3971600282315848099540181)
              ·
                refine ⟨93084381616777689832973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3971600282315848099540181 93084381616777689832973)
                ·
                  rfl

theorem cell19_305912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_305912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305912 prefixEnd_305912 := by exact prefixLift 305912
  have htrace : WordTrace (prefixWord ++ tailWord_305912) baseStart_305912 baseEnd_305912 := by
    simpa [prefixWord, tailWord_305912, baseEnd_305912] using wordTrace_append hprefix tailTrace_305912
  have hstable : (prefixWord ++ tailWord_305912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305912).length < 2 ^ (prefixWord ++ tailWord_305912).sum := by decide
  have hdescent : baseEnd_305912 < baseStart_305912 := by decide
  rcases family_descends (prefixWord ++ tailWord_305912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305948 : List Nat := [2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_305948 : Nat := 118140960795 + 305948 * 2 ^ 59
def prefixEnd_305948 : Nat := 4983230072969 + 3 ^ 40 * 305948 * 2
def baseEnd_305948 : Nat := 93095335870740273032875

theorem tailTrace_305948 : CollatzResearch.WordTrace tailWord_305948 prefixEnd_305948 93095335870740273032875 := by
  unfold tailWord_305948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5579420147805061301767249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7439226863740081735689665 5579420147805061301767249)
  ·
    refine ⟨4184565110853795976325437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5579420147805061301767249 4184565110853795976325437)
    ·
      refine ⟨1569211916570173491122039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4184565110853795976325437 1569211916570173491122039)
      ·
        refine ⟨2353817874855260236683059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569211916570173491122039 2353817874855260236683059)
        ·
          refine ⟨3530726812282890355024589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353817874855260236683059 3530726812282890355024589)
          ·
            refine ⟨1324022554606083883134221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3530726812282890355024589 1324022554606083883134221)
            ·
              refine ⟨496508457977281456175333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1324022554606083883134221 496508457977281456175333)
              ·
                refine ⟨93095335870740273032875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496508457977281456175333 93095335870740273032875)
                ·
                  rfl

theorem cell19_305948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_305948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_305948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_305948 prefixEnd_305948 := by exact prefixLift 305948
  have htrace : WordTrace (prefixWord ++ tailWord_305948) baseStart_305948 baseEnd_305948 := by
    simpa [prefixWord, tailWord_305948, baseEnd_305948] using wordTrace_append hprefix tailTrace_305948
  have hstable : (prefixWord ++ tailWord_305948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305948).length < 2 ^ (prefixWord ++ tailWord_305948).sum := by decide
  have hdescent : baseEnd_305948 < baseStart_305948 := by decide
  rcases family_descends (prefixWord ++ tailWord_305948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306018 : List Nat := [3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_306018 : Nat := 118140960795 + 306018 * 2 ^ 59
def prefixEnd_306018 : Nat := 4983230072969 + 3 ^ 40 * 306018 * 2
def baseEnd_306018 : Nat := 93116635809000851477129

theorem tailTrace_306018 : CollatzResearch.WordTrace tailWord_306018 prefixEnd_306018 93116635809000851477129 := by
  unfold tailWord_306018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790348351339131139645677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7440928936904349705721805 2790348351339131139645677)
  ·
    refine ⟨1046380631752174177367129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2790348351339131139645677 1046380631752174177367129)
    ·
      refine ⟨784785473814130633025347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1046380631752174177367129 784785473814130633025347)
      ·
        refine ⟨1177178210721195949538021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784785473814130633025347 1177178210721195949538021)
        ·
          refine ⟨220720914510224240538379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1177178210721195949538021 220720914510224240538379)
          ·
            refine ⟨331081371765336360807569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220720914510224240538379 331081371765336360807569)
            ·
              refine ⟨248311028824002270605677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331081371765336360807569 248311028824002270605677)
              ·
                refine ⟨93116635809000851477129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248311028824002270605677 93116635809000851477129)
                ·
                  rfl

theorem cell19_306018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_306018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306018 prefixEnd_306018 := by exact prefixLift 306018
  have htrace : WordTrace (prefixWord ++ tailWord_306018) baseStart_306018 baseEnd_306018 := by
    simpa [prefixWord, tailWord_306018, baseEnd_306018] using wordTrace_append hprefix tailTrace_306018
  have hstable : (prefixWord ++ tailWord_306018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306018).length < 2 ^ (prefixWord ++ tailWord_306018).sum := by decide
  have hdescent : baseEnd_306018 < baseStart_306018 := by decide
  rcases family_descends (prefixWord ++ tailWord_306018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306024 : List Nat := [2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_306024 : Nat := 118140960795 + 306024 * 2 ^ 59
def prefixEnd_306024 : Nat := 4983230072969 + 3 ^ 40 * 306024 * 2
def baseEnd_306024 : Nat := 93118461517994615343779

theorem tailTrace_306024 : CollatzResearch.WordTrace tailWord_306024 prefixEnd_306024 93118461517994615343779 := by
  unfold tailWord_306024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580806121667393791650563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7441074828889858388867417 5580806121667393791650563)
  ·
    refine ⟨8371209182501090687475845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580806121667393791650563 8371209182501090687475845)
    ·
      refine ⟨1569601721718954503901721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8371209182501090687475845 1569601721718954503901721)
      ·
        refine ⟨1177201291289215877926291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1569601721718954503901721 1177201291289215877926291)
        ·
          refine ⟨1765801936933823816889437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177201291289215877926291 1765801936933823816889437)
          ·
            refine ⟨662175726350183931333539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1765801936933823816889437 662175726350183931333539)
            ·
              refine ⟨993263589525275897000309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662175726350183931333539 993263589525275897000309)
              ·
                refine ⟨93118461517994615343779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 993263589525275897000309 93118461517994615343779)
                ·
                  rfl

theorem cell19_306024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_306024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306024 prefixEnd_306024 := by exact prefixLift 306024
  have htrace : WordTrace (prefixWord ++ tailWord_306024) baseStart_306024 baseEnd_306024 := by
    simpa [prefixWord, tailWord_306024, baseEnd_306024] using wordTrace_append hprefix tailTrace_306024
  have hstable : (prefixWord ++ tailWord_306024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306024).length < 2 ^ (prefixWord ++ tailWord_306024).sum := by decide
  have hdescent : baseEnd_306024 < baseStart_306024 := by decide
  rcases family_descends (prefixWord ++ tailWord_306024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306045 : List Nat := [1, 4, 1, 1, 2, 1, 9]
def baseStart_306045 : Nat := 118140960795 + 306045 * 2 ^ 59
def prefixEnd_306045 : Nat := 4983230072969 + 3 ^ 40 * 306045 * 2
def baseEnd_306045 : Nat := 31041617166490929625685

theorem tailTrace_306045 : CollatzResearch.WordTrace tailWord_306045 prefixEnd_306045 31041617166490929625685 := by
  unfold tailWord_306045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162378176258708169815589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441585450839138779877059 11162378176258708169815589)
  ·
    refine ⟨2092945908048507781840423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11162378176258708169815589 2092945908048507781840423)
    ·
      refine ⟨3139418862072761672760635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092945908048507781840423 3139418862072761672760635)
      ·
        refine ⟨4709128293109142509140953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139418862072761672760635 4709128293109142509140953)
        ·
          refine ⟨3531846219831856881855715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4709128293109142509140953 3531846219831856881855715)
          ·
            refine ⟨5297769329747785322783573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531846219831856881855715 5297769329747785322783573)
            ·
              refine ⟨31041617166490929625685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5297769329747785322783573 31041617166490929625685)
              ·
                rfl

theorem cell19_306045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_306045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306045 prefixEnd_306045 := by exact prefixLift 306045
  have htrace : WordTrace (prefixWord ++ tailWord_306045) baseStart_306045 baseEnd_306045 := by
    simpa [prefixWord, tailWord_306045, baseEnd_306045] using wordTrace_append hprefix tailTrace_306045
  have hstable : (prefixWord ++ tailWord_306045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306045).length < 2 ^ (prefixWord ++ tailWord_306045).sum := by decide
  have hdescent : baseEnd_306045 < baseStart_306045 := by decide
  rcases family_descends (prefixWord ++ tailWord_306045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306081 : List Nat := [1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_306081 : Nat := 118140960795 + 306081 * 2 ^ 59
def prefixEnd_306081 : Nat := 4983230072969 + 3 ^ 40 * 306081 * 2
def baseEnd_306081 : Nat := 93135805753435372076957

theorem tailTrace_306081 : CollatzResearch.WordTrace tailWord_306081 prefixEnd_306081 93135805753435372076957 := by
  unfold tailWord_306081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163691204128286318126097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7442460802752190878750731 11163691204128286318126097)
  ·
    refine ⟨8372768403096214738594573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11163691204128286318126097 8372768403096214738594573)
    ·
      refine ⟨3139788151161080526972965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8372768403096214738594573 3139788151161080526972965)
      ·
        refine ⟨588710278342702598807431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3139788151161080526972965 588710278342702598807431)
        ·
          refine ⟨883065417514053898211147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588710278342702598807431 883065417514053898211147)
          ·
            refine ⟨1324598126271080847316721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883065417514053898211147 1324598126271080847316721)
            ·
              refine ⟨993448594703310635487541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324598126271080847316721 993448594703310635487541)
              ·
                refine ⟨93135805753435372076957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 993448594703310635487541 93135805753435372076957)
                ·
                  rfl

theorem cell19_306081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_306081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306081 prefixEnd_306081 := by exact prefixLift 306081
  have htrace : WordTrace (prefixWord ++ tailWord_306081) baseStart_306081 baseEnd_306081 := by
    simpa [prefixWord, tailWord_306081, baseEnd_306081] using wordTrace_append hprefix tailTrace_306081
  have hstable : (prefixWord ++ tailWord_306081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306081).length < 2 ^ (prefixWord ++ tailWord_306081).sum := by decide
  have hdescent : baseEnd_306081 < baseStart_306081 := by decide
  rcases family_descends (prefixWord ++ tailWord_306081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306083 : List Nat := [1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_306083 : Nat := 118140960795 + 306083 * 2 ^ 59
def prefixEnd_306083 : Nat := 4983230072969 + 3 ^ 40 * 306083 * 2
def baseEnd_306083 : Nat := 93136414323099960032507

theorem tailTrace_306083 : CollatzResearch.WordTrace tailWord_306083 prefixEnd_306083 93136414323099960032507 := by
  unfold tailWord_306083
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163764150121040659698903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7442509433414027106465935 11163764150121040659698903)
  ·
    refine ⟨16745646225181560989548355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163764150121040659698903 16745646225181560989548355)
    ·
      refine ⟨25118469337772341484322533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16745646225181560989548355 25118469337772341484322533)
      ·
        refine ⟨4709713000832314028310475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25118469337772341484322533 4709713000832314028310475)
        ·
          refine ⟨7064569501248471042465713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709713000832314028310475 7064569501248471042465713)
          ·
            refine ⟨5298427125936353281849285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7064569501248471042465713 5298427125936353281849285)
            ·
              refine ⟨993455086113066240346741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5298427125936353281849285 993455086113066240346741)
              ·
                refine ⟨93136414323099960032507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 993455086113066240346741 93136414323099960032507)
                ·
                  rfl

theorem cell19_306083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_306083 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306083 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306083 prefixEnd_306083 := by exact prefixLift 306083
  have htrace : WordTrace (prefixWord ++ tailWord_306083) baseStart_306083 baseEnd_306083 := by
    simpa [prefixWord, tailWord_306083, baseEnd_306083] using wordTrace_append hprefix tailTrace_306083
  have hstable : (prefixWord ++ tailWord_306083).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306083).length < 2 ^ (prefixWord ++ tailWord_306083).sum := by decide
  have hdescent : baseEnd_306083 < baseStart_306083 := by decide
  rcases family_descends (prefixWord ++ tailWord_306083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306134 : List Nat := [5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_306134 : Nat := 118140960795 + 306134 * 2 ^ 59
def prefixEnd_306134 : Nat := 4983230072969 + 3 ^ 40 * 306134 * 2
def baseEnd_306134 : Nat := 93151932849546952899035

theorem tailTrace_306134 : CollatzResearch.WordTrace tailWord_306134 prefixEnd_306134 93151932849546952899035 := by
  unfold tailWord_306134
  simp only [CollatzResearch.WordTrace]
  refine ⟨697851517058517273112841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7443749515290850913203637 697851517058517273112841)
  ·
    refine ⟨523388637793887954834631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 697851517058517273112841 523388637793887954834631)
    ·
      refine ⟨785082956690831932251947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523388637793887954834631 785082956690831932251947)
      ·
        refine ⟨1177624435036247898377921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785082956690831932251947 1177624435036247898377921)
        ·
          refine ⟨883218326277185923783441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1177624435036247898377921 883218326277185923783441)
          ·
            refine ⟨662413744707889442837581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883218326277185923783441 662413744707889442837581)
            ·
              refine ⟨248405154265458541064093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662413744707889442837581 248405154265458541064093)
              ·
                refine ⟨93151932849546952899035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248405154265458541064093 93151932849546952899035)
                ·
                  rfl

theorem cell19_306134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_306134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306134 prefixEnd_306134 := by exact prefixLift 306134
  have htrace : WordTrace (prefixWord ++ tailWord_306134) baseStart_306134 baseEnd_306134 := by
    simpa [prefixWord, tailWord_306134, baseEnd_306134] using wordTrace_append hprefix tailTrace_306134
  have hstable : (prefixWord ++ tailWord_306134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306134).length < 2 ^ (prefixWord ++ tailWord_306134).sum := by decide
  have hdescent : baseEnd_306134 < baseStart_306134 := by decide
  rcases family_descends (prefixWord ++ tailWord_306134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306159 : List Nat := [1, 1, 2, 1, 4, 4, 6]
def baseStart_306159 : Nat := 118140960795 + 306159 * 2 ^ 59
def prefixEnd_306159 : Nat := 4983230072969 + 3 ^ 40 * 306159 * 2
def baseEnd_306159 : Nat := 31053179990118100781137

theorem tailTrace_306159 : CollatzResearch.WordTrace tailWord_306159 prefixEnd_306159 31053179990118100781137 := by
  unfold tailWord_306159
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166536097845705639465531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7444357398563803759643687 11166536097845705639465531)
  ·
    refine ⟨16749804146768558459198297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11166536097845705639465531 16749804146768558459198297)
    ·
      refine ⟨12562353110076418844398723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16749804146768558459198297 12562353110076418844398723)
      ·
        refine ⟨18843529665114628266598085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12562353110076418844398723 18843529665114628266598085)
        ·
          refine ⟨3533161812208992799987141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18843529665114628266598085 3533161812208992799987141)
          ·
            refine ⟨662467839789186149997589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3533161812208992799987141 662467839789186149997589)
            ·
              refine ⟨31053179990118100781137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 662467839789186149997589 31053179990118100781137)
              ·
                rfl

theorem cell19_306159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_306159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306159 prefixEnd_306159 := by exact prefixLift 306159
  have htrace : WordTrace (prefixWord ++ tailWord_306159) baseStart_306159 baseEnd_306159 := by
    simpa [prefixWord, tailWord_306159, baseEnd_306159] using wordTrace_append hprefix tailTrace_306159
  have hstable : (prefixWord ++ tailWord_306159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306159).length < 2 ^ (prefixWord ++ tailWord_306159).sum := by decide
  have hdescent : baseEnd_306159 < baseStart_306159 := by decide
  rcases family_descends (prefixWord ++ tailWord_306159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306233 : List Nat := [1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_306233 : Nat := 118140960795 + 306233 * 2 ^ 59
def prefixEnd_306233 : Nat := 4983230072969 + 3 ^ 40 * 306233 * 2
def baseEnd_306233 : Nat := 93182057047944056698765

theorem tailTrace_306233 : CollatzResearch.WordTrace tailWord_306233 prefixEnd_306233 93182057047944056698765 := by
  unfold tailWord_306233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169235099577616277659353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7446156733051744185106235 11169235099577616277659353)
  ·
    refine ⟨8376926324683212208244515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11169235099577616277659353 8376926324683212208244515)
    ·
      refine ⟨12565389487024818312366773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8376926324683212208244515 12565389487024818312366773)
      ·
        refine ⟨1178005264408576716784385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12565389487024818312366773 1178005264408576716784385)
        ·
          refine ⟨883503948306432537588289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178005264408576716784385 883503948306432537588289)
          ·
            refine ⟨662627961229824403191217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883503948306432537588289 662627961229824403191217)
            ·
              refine ⟨496970970922368302393413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662627961229824403191217 496970970922368302393413)
              ·
                refine ⟨93182057047944056698765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496970970922368302393413 93182057047944056698765)
                ·
                  rfl

theorem cell19_306233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_306233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306233 prefixEnd_306233 := by exact prefixLift 306233
  have htrace : WordTrace (prefixWord ++ tailWord_306233) baseStart_306233 baseEnd_306233 := by
    simpa [prefixWord, tailWord_306233, baseEnd_306233] using wordTrace_append hprefix tailTrace_306233
  have hstable : (prefixWord ++ tailWord_306233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306233).length < 2 ^ (prefixWord ++ tailWord_306233).sum := by decide
  have hdescent : baseEnd_306233 < baseStart_306233 := by decide
  rcases family_descends (prefixWord ++ tailWord_306233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306254 : List Nat := [4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_306254 : Nat := 118140960795 + 306254 * 2 ^ 59
def prefixEnd_306254 : Nat := 4983230072969 + 3 ^ 40 * 306254 * 2
def baseEnd_306254 : Nat := 93188447029422230232041

theorem tailTrace_306254 : CollatzResearch.WordTrace tailWord_306254 prefixEnd_306254 93188447029422230232041 := by
  unfold tailWord_306254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396250129062692108021727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7446667355001024576115877 1396250129062692108021727)
  ·
    refine ⟨2094375193594038162032591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1396250129062692108021727 2094375193594038162032591)
    ·
      refine ⟨3141562790391057243048887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094375193594038162032591 3141562790391057243048887)
      ·
        refine ⟨4712344185586585864573331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3141562790391057243048887 4712344185586585864573331)
        ·
          refine ⟨7068516278379878796859997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712344185586585864573331 7068516278379878796859997)
          ·
            refine ⟨2650693604392454548822499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7068516278379878796859997 2650693604392454548822499)
            ·
              refine ⟨3976040406588681823233749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650693604392454548822499 3976040406588681823233749)
              ·
                refine ⟨93188447029422230232041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3976040406588681823233749 93188447029422230232041)
                ·
                  rfl

theorem cell19_306254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_306254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306254 prefixEnd_306254 := by exact prefixLift 306254
  have htrace : WordTrace (prefixWord ++ tailWord_306254) baseStart_306254 baseEnd_306254 := by
    simpa [prefixWord, tailWord_306254, baseEnd_306254] using wordTrace_append hprefix tailTrace_306254
  have hstable : (prefixWord ++ tailWord_306254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306254).length < 2 ^ (prefixWord ++ tailWord_306254).sum := by decide
  have hdescent : baseEnd_306254 < baseStart_306254 := by decide
  rcases family_descends (prefixWord ++ tailWord_306254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306269 : List Nat := [1, 4, 4, 1, 3, 6]
def baseStart_306269 : Nat := 118140960795 + 306269 * 2 ^ 59
def prefixEnd_306269 : Nat := 4983230072969 + 3 ^ 40 * 306269 * 2
def baseEnd_306269 : Nat := 10354779033545182210963

theorem tailTrace_306269 : CollatzResearch.WordTrace tailWord_306269 prefixEnd_306269 10354779033545182210963 := by
  unfold tailWord_306269
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170548127447194425969861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7447032084964796283979907 11170548127447194425969861)
  ·
    refine ⟨2094477773896348954869349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11170548127447194425969861 2094477773896348954869349)
    ·
      refine ⟨392714582605565429038003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2094477773896348954869349 392714582605565429038003)
      ·
        refine ⟨589071873908348143557005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392714582605565429038003 589071873908348143557005)
        ·
          refine ⟨220901952715630553833877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589071873908348143557005 220901952715630553833877)
          ·
            refine ⟨10354779033545182210963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220901952715630553833877 10354779033545182210963)
            ·
              rfl

theorem cell19_306269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_306269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306269 prefixEnd_306269 := by exact prefixLift 306269
  have htrace : WordTrace (prefixWord ++ tailWord_306269) baseStart_306269 baseEnd_306269 := by
    simpa [prefixWord, tailWord_306269, baseEnd_306269] using wordTrace_append hprefix tailTrace_306269
  have hstable : (prefixWord ++ tailWord_306269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306269).length < 2 ^ (prefixWord ++ tailWord_306269).sum := by decide
  have hdescent : baseEnd_306269 < baseStart_306269 := by decide
  rcases family_descends (prefixWord ++ tailWord_306269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306358 : List Nat := [5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_306358 : Nat := 118140960795 + 306358 * 2 ^ 59
def prefixEnd_306358 : Nat := 4983230072969 + 3 ^ 40 * 306358 * 2
def baseEnd_306358 : Nat := 93220092651980803920647

theorem tailTrace_306358 : CollatzResearch.WordTrace tailWord_306358 prefixEnd_306358 93220092651980803920647 := by
  unfold tailWord_306358
  simp only [CollatzResearch.WordTrace]
  refine ⟨698362139007797664122483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7449196149416508417306485 698362139007797664122483)
  ·
    refine ⟨1047543208511696496183725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698362139007797664122483 1047543208511696496183725)
    ·
      refine ⟨392828703191886186068897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1047543208511696496183725 392828703191886186068897)
      ·
        refine ⟨294621527393914639551673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392828703191886186068897 294621527393914639551673)
        ·
          refine ⟨220966145545435979663755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294621527393914639551673 220966145545435979663755)
          ·
            refine ⟨331449218318153969495633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220966145545435979663755 331449218318153969495633)
            ·
              refine ⟨248586913738615477121725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331449218318153969495633 248586913738615477121725)
              ·
                refine ⟨93220092651980803920647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248586913738615477121725 93220092651980803920647)
                ·
                  rfl

theorem cell19_306358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_306358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306358 prefixEnd_306358 := by exact prefixLift 306358
  have htrace : WordTrace (prefixWord ++ tailWord_306358) baseStart_306358 baseEnd_306358 := by
    simpa [prefixWord, tailWord_306358, baseEnd_306358] using wordTrace_append hprefix tailTrace_306358
  have hstable : (prefixWord ++ tailWord_306358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306358).length < 2 ^ (prefixWord ++ tailWord_306358).sum := by decide
  have hdescent : baseEnd_306358 < baseStart_306358 := by decide
  rcases family_descends (prefixWord ++ tailWord_306358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306364 : List Nat := [2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_306364 : Nat := 118140960795 + 306364 * 2 ^ 59
def prefixEnd_306364 : Nat := 4983230072969 + 3 ^ 40 * 306364 * 2
def baseEnd_306364 : Nat := 93221918360974567787297

theorem tailTrace_306364 : CollatzResearch.WordTrace tailWord_306364 prefixEnd_306364 93221918360974567787297 := by
  unfold tailWord_306364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587006531051512825339073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7449342041402017100452097 5587006531051512825339073)
  ·
    refine ⟨4190254898288634619004305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5587006531051512825339073 4190254898288634619004305)
    ·
      refine ⟨3142691173716475964253229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4190254898288634619004305 3142691173716475964253229)
      ·
        refine ⟨1178509190143678486594961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3142691173716475964253229 1178509190143678486594961)
        ·
          refine ⟨883881892607758864946221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178509190143678486594961 883881892607758864946221)
          ·
            refine ⟨331455709727909574354833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 883881892607758864946221 331455709727909574354833)
            ·
              refine ⟨248591782295932180766125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331455709727909574354833 248591782295932180766125)
              ·
                refine ⟨93221918360974567787297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248591782295932180766125 93221918360974567787297)
                ·
                  rfl

theorem cell19_306364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_306364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306364 prefixEnd_306364 := by exact prefixLift 306364
  have htrace : WordTrace (prefixWord ++ tailWord_306364) baseStart_306364 baseEnd_306364 := by
    simpa [prefixWord, tailWord_306364, baseEnd_306364] using wordTrace_append hprefix tailTrace_306364
  have hstable : (prefixWord ++ tailWord_306364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306364).length < 2 ^ (prefixWord ++ tailWord_306364).sum := by decide
  have hdescent : baseEnd_306364 < baseStart_306364 := by decide
  rcases family_descends (prefixWord ++ tailWord_306364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306366 : List Nat := [4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_306366 : Nat := 118140960795 + 306366 * 2 ^ 59
def prefixEnd_306366 : Nat := 4983230072969 + 3 ^ 40 * 306366 * 2
def baseEnd_306366 : Nat := 93222526930639155742847

theorem tailTrace_306366 : CollatzResearch.WordTrace tailWord_306366 prefixEnd_306366 93222526930639155742847 := by
  unfold tailWord_306366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396760751011972499031369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7449390672063853328167301 1396760751011972499031369)
  ·
    refine ⟨1047570563258979374273527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1396760751011972499031369 1047570563258979374273527)
    ·
      refine ⟨1571355844888469061410291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047570563258979374273527 1571355844888469061410291)
      ·
        refine ⟨2357033767332703592115437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571355844888469061410291 2357033767332703592115437)
        ·
          refine ⟨883887662749763847043289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2357033767332703592115437 883887662749763847043289)
          ·
            refine ⟨662915747062322885282467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883887662749763847043289 662915747062322885282467)
            ·
              refine ⟨994373620593484327923701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662915747062322885282467 994373620593484327923701)
              ·
                refine ⟨93222526930639155742847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 994373620593484327923701 93222526930639155742847)
                ·
                  rfl

theorem cell19_306366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_306366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306366 prefixEnd_306366 := by exact prefixLift 306366
  have htrace : WordTrace (prefixWord ++ tailWord_306366) baseStart_306366 baseEnd_306366 := by
    simpa [prefixWord, tailWord_306366, baseEnd_306366] using wordTrace_append hprefix tailTrace_306366
  have hstable : (prefixWord ++ tailWord_306366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306366).length < 2 ^ (prefixWord ++ tailWord_306366).sum := by decide
  have hdescent : baseEnd_306366 < baseStart_306366 := by decide
  rcases family_descends (prefixWord ++ tailWord_306366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306381 : List Nat := [1, 6, 2, 2, 1, 2, 5]
def baseStart_306381 : Nat := 118140960795 + 306381 * 2 ^ 59
def prefixEnd_306381 : Nat := 4983230072969 + 3 ^ 40 * 306381 * 2
def baseEnd_306381 : Nat := 31075697067707855136491

theorem tailTrace_306381 : CollatzResearch.WordTrace tailWord_306381 prefixEnd_306381 31075697067707855136491 := by
  unfold tailWord_306381
  simp only [CollatzResearch.WordTrace]
  refine ⟨11174633103041437554046997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7449755402027625036031331 11174633103041437554046997)
  ·
    refine ⟨523810926705067385345953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11174633103041437554046997 523810926705067385345953)
    ·
      refine ⟨392858195028800539009465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 523810926705067385345953 392858195028800539009465)
      ·
        refine ⟨294643646271600404257099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392858195028800539009465 294643646271600404257099)
        ·
          refine ⟨441965469407400606385649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294643646271600404257099 441965469407400606385649)
          ·
            refine ⟨331474102055550454789237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441965469407400606385649 331474102055550454789237)
            ·
              refine ⟨31075697067707855136491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 331474102055550454789237 31075697067707855136491)
              ·
                rfl

theorem cell19_306381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_306381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306381 prefixEnd_306381 := by exact prefixLift 306381
  have htrace : WordTrace (prefixWord ++ tailWord_306381) baseStart_306381 baseEnd_306381 := by
    simpa [prefixWord, tailWord_306381, baseEnd_306381] using wordTrace_append hprefix tailTrace_306381
  have hstable : (prefixWord ++ tailWord_306381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306381).length < 2 ^ (prefixWord ++ tailWord_306381).sum := by decide
  have hdescent : baseEnd_306381 < baseStart_306381 := by decide
  rcases family_descends (prefixWord ++ tailWord_306381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306461 : List Nat := [1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_306461 : Nat := 118140960795 + 306461 * 2 ^ 59
def prefixEnd_306461 : Nat := 4983230072969 + 3 ^ 40 * 306461 * 2
def baseEnd_306461 : Nat := 93251433989707083631477

theorem tailTrace_306461 : CollatzResearch.WordTrace tailWord_306461 prefixEnd_306461 93251433989707083631477 := by
  unfold tailWord_306461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177550942751611216959237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7451700628501074144639491 11177550942751611216959237)
  ·
    refine ⟨2095790801765927103179857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11177550942751611216959237 2095790801765927103179857)
    ·
      refine ⟨1571843101324445327384893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2095790801765927103179857 1571843101324445327384893)
      ·
        refine ⟨589441162996666997769335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1571843101324445327384893 589441162996666997769335)
        ·
          refine ⟨884161744495000496654003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589441162996666997769335 884161744495000496654003)
          ·
            refine ⟨1326242616742500744981005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884161744495000496654003 1326242616742500744981005)
            ·
              refine ⟨497340981278437779367877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1326242616742500744981005 497340981278437779367877)
              ·
                refine ⟨93251433989707083631477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497340981278437779367877 93251433989707083631477)
                ·
                  rfl

theorem cell19_306461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_306461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306461 prefixEnd_306461 := by exact prefixLift 306461
  have htrace : WordTrace (prefixWord ++ tailWord_306461) baseStart_306461 baseEnd_306461 := by
    simpa [prefixWord, tailWord_306461, baseEnd_306461] using wordTrace_append hprefix tailTrace_306461
  have hstable : (prefixWord ++ tailWord_306461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306461).length < 2 ^ (prefixWord ++ tailWord_306461).sum := by decide
  have hdescent : baseEnd_306461 < baseStart_306461 := by decide
  rcases family_descends (prefixWord ++ tailWord_306461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306535 : List Nat := [1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_306535 : Nat := 118140960795 + 306535 * 2 ^ 59
def prefixEnd_306535 : Nat := 4983230072969 + 3 ^ 40 * 306535 * 2
def baseEnd_306535 : Nat := 93273951067296837986831

theorem tailTrace_306535 : CollatzResearch.WordTrace tailWord_306535 prefixEnd_306535 93273951067296837986831 := by
  unfold tailWord_306535
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180249944483521855153059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7453499962989014570102039 11180249944483521855153059)
  ·
    refine ⟨16770374916725282782729589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11180249944483521855153059 16770374916725282782729589)
    ·
      refine ⟨1572222648442995260880899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16770374916725282782729589 1572222648442995260880899)
      ·
        refine ⟨2358333972664492891321349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572222648442995260880899 2358333972664492891321349)
        ·
          refine ⟨442187619874592417122753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2358333972664492891321349 442187619874592417122753)
          ·
            refine ⟨331640714905944312842065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442187619874592417122753 331640714905944312842065)
            ·
              refine ⟨248730536179458234631549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331640714905944312842065 248730536179458234631549)
              ·
                refine ⟨93273951067296837986831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248730536179458234631549 93273951067296837986831)
                ·
                  rfl

theorem cell19_306535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_306535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306535 prefixEnd_306535 := by exact prefixLift 306535
  have htrace : WordTrace (prefixWord ++ tailWord_306535) baseStart_306535 baseEnd_306535 := by
    simpa [prefixWord, tailWord_306535, baseEnd_306535] using wordTrace_append hprefix tailTrace_306535
  have hstable : (prefixWord ++ tailWord_306535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306535).length < 2 ^ (prefixWord ++ tailWord_306535).sum := by decide
  have hdescent : baseEnd_306535 < baseStart_306535 := by decide
  rcases family_descends (prefixWord ++ tailWord_306535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306617 : List Nat := [1, 2, 1, 4, 11]
def baseStart_306617 : Nat := 118140960795 + 306617 * 2 ^ 59
def prefixEnd_306617 : Nat := 4983230072969 + 3 ^ 40 * 306617 * 2
def baseEnd_306617 : Nat := 3455514904575738672755

theorem tailTrace_306617 : CollatzResearch.WordTrace tailWord_306617 prefixEnd_306617 3455514904575738672755 := by
  unfold tailWord_306617
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183240730186449859638105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7455493820124299906425403 11183240730186449859638105)
  ·
    refine ⟨8387430547639837394728579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11183240730186449859638105 8387430547639837394728579)
    ·
      refine ⟨12581145821459756092092869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8387430547639837394728579 12581145821459756092092869)
      ·
        refine ⟨2358964841523704267267413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12581145821459756092092869 2358964841523704267267413)
        ·
          refine ⟨3455514904575738672755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2358964841523704267267413 3455514904575738672755)
          ·
            rfl

theorem cell19_306617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 11].length) (baseStart_306617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306617 prefixEnd_306617 := by exact prefixLift 306617
  have htrace : WordTrace (prefixWord ++ tailWord_306617) baseStart_306617 baseEnd_306617 := by
    simpa [prefixWord, tailWord_306617, baseEnd_306617] using wordTrace_append hprefix tailTrace_306617
  have hstable : (prefixWord ++ tailWord_306617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306617).length < 2 ^ (prefixWord ++ tailWord_306617).sum := by decide
  have hdescent : baseEnd_306617 < baseStart_306617 := by decide
  rcases family_descends (prefixWord ++ tailWord_306617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306634 : List Nat := [3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_306634 : Nat := 118140960795 + 306634 * 2 ^ 59
def prefixEnd_306634 : Nat := 4983230072969 + 3 ^ 40 * 306634 * 2
def baseEnd_306634 : Nat := 93304075265693941786561

theorem tailTrace_306634 : CollatzResearch.WordTrace tailWord_306634 prefixEnd_306634 93304075265693941786561 := by
  unfold tailWord_306634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795965192781215440751739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7455907180749907842004637 2795965192781215440751739)
  ·
    refine ⟨4193947789171823161127609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2795965192781215440751739 4193947789171823161127609)
    ·
      refine ⟨3145460841878867370845707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193947789171823161127609 3145460841878867370845707)
      ·
        refine ⟨4718191262818301056268561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145460841878867370845707 4718191262818301056268561)
        ·
          refine ⟨3538643447113725792201421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4718191262818301056268561 3538643447113725792201421)
          ·
            refine ⟨1326991292667647172075533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3538643447113725792201421 1326991292667647172075533)
            ·
              refine ⟨497621734750367689528325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1326991292667647172075533 497621734750367689528325)
              ·
                refine ⟨93304075265693941786561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497621734750367689528325 93304075265693941786561)
                ·
                  rfl

theorem cell19_306634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_306634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306634 prefixEnd_306634 := by exact prefixLift 306634
  have htrace : WordTrace (prefixWord ++ tailWord_306634) baseStart_306634 baseEnd_306634 := by
    simpa [prefixWord, tailWord_306634, baseEnd_306634] using wordTrace_append hprefix tailTrace_306634
  have hstable : (prefixWord ++ tailWord_306634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306634).length < 2 ^ (prefixWord ++ tailWord_306634).sum := by decide
  have hdescent : baseEnd_306634 < baseStart_306634 := by decide
  rcases family_descends (prefixWord ++ tailWord_306634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306693 : List Nat := [1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_306693 : Nat := 118140960795 + 306693 * 2 ^ 59
def prefixEnd_306693 : Nat := 4983230072969 + 3 ^ 40 * 306693 * 2
def baseEnd_306693 : Nat := 93322028070799286475289

theorem tailTrace_306693 : CollatzResearch.WordTrace tailWord_306693 prefixEnd_306693 93322028070799286475289 := by
  unfold tailWord_306693
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186012677911114839404733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7457341785274076559603155 11186012677911114839404733)
  ·
    refine ⟨4194754754216668064776775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11186012677911114839404733 4194754754216668064776775)
    ·
      refine ⟨6292132131325002097165163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4194754754216668064776775 6292132131325002097165163)
      ·
        refine ⟨9438198196987503145747745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292132131325002097165163 9438198196987503145747745)
        ·
          refine ⟨7078648647740627359310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9438198196987503145747745 7078648647740627359310809)
          ·
            refine ⟨5308986485805470519483107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7078648647740627359310809 5308986485805470519483107)
            ·
              refine ⟨7963479728708205779224661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5308986485805470519483107 7963479728708205779224661)
              ·
                refine ⟨93322028070799286475289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7963479728708205779224661 93322028070799286475289)
                ·
                  rfl

theorem cell19_306693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_306693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306693 prefixEnd_306693 := by exact prefixLift 306693
  have htrace : WordTrace (prefixWord ++ tailWord_306693) baseStart_306693 baseEnd_306693 := by
    simpa [prefixWord, tailWord_306693, baseEnd_306693] using wordTrace_append hprefix tailTrace_306693
  have hstable : (prefixWord ++ tailWord_306693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306693).length < 2 ^ (prefixWord ++ tailWord_306693).sum := by decide
  have hdescent : baseEnd_306693 < baseStart_306693 := by decide
  rcases family_descends (prefixWord ++ tailWord_306693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306769 : List Nat := [1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_306769 : Nat := 118140960795 + 306769 * 2 ^ 59
def prefixEnd_306769 : Nat := 4983230072969 + 3 ^ 40 * 306769 * 2
def baseEnd_306769 : Nat := 93345153718053628786193

theorem tailTrace_306769 : CollatzResearch.WordTrace tailWord_306769 prefixEnd_306769 93345153718053628786193 := by
  unfold tailWord_306769
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188784625635779819171361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7459189750423853212780907 11188784625635779819171361)
  ·
    refine ⟨8391588469226834864378521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11188784625635779819171361 8391588469226834864378521)
    ·
      refine ⟨6293691351920126148283891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8391588469226834864378521 6293691351920126148283891)
      ·
        refine ⟨9440537027880189222425837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293691351920126148283891 9440537027880189222425837)
        ·
          refine ⟨3540201385455070958409689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9440537027880189222425837 3540201385455070958409689)
          ·
            refine ⟨2655151039091303218807267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3540201385455070958409689 2655151039091303218807267)
            ·
              refine ⟨3982726558636954828210901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655151039091303218807267 3982726558636954828210901)
              ·
                refine ⟨93345153718053628786193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3982726558636954828210901 93345153718053628786193)
                ·
                  rfl

theorem cell19_306769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_306769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306769 prefixEnd_306769 := by exact prefixLift 306769
  have htrace : WordTrace (prefixWord ++ tailWord_306769) baseStart_306769 baseEnd_306769 := by
    simpa [prefixWord, tailWord_306769, baseEnd_306769] using wordTrace_append hprefix tailTrace_306769
  have hstable : (prefixWord ++ tailWord_306769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306769).length < 2 ^ (prefixWord ++ tailWord_306769).sum := by decide
  have hdescent : baseEnd_306769 < baseStart_306769 := by decide
  rcases family_descends (prefixWord ++ tailWord_306769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306788 : List Nat := [2, 3, 1, 1, 2, 10]
def baseStart_306788 : Nat := 118140960795 + 306788 * 2 ^ 59
def prefixEnd_306788 : Nat := 4983230072969 + 3 ^ 40 * 306788 * 2
def baseEnd_306788 : Nat := 10372326125540801595991

theorem tailTrace_306788 : CollatzResearch.WordTrace tailWord_306788 prefixEnd_306788 10372326125540801595991 := by
  unfold tailWord_306788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594738806283473032056509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7459651741711297376075345 5594738806283473032056509)
  ·
    refine ⟨2098027052356302387021191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5594738806283473032056509 2098027052356302387021191)
    ·
      refine ⟨3147040578534453580531787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098027052356302387021191 3147040578534453580531787)
      ·
        refine ⟨4720560867801680370797681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147040578534453580531787 4720560867801680370797681)
        ·
          refine ⟨3540420650851260278098261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4720560867801680370797681 3540420650851260278098261)
          ·
            refine ⟨10372326125540801595991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3540420650851260278098261 10372326125540801595991)
            ·
              rfl

theorem cell19_306788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_306788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306788 prefixEnd_306788 := by exact prefixLift 306788
  have htrace : WordTrace (prefixWord ++ tailWord_306788) baseStart_306788 baseEnd_306788 := by
    simpa [prefixWord, tailWord_306788, baseEnd_306788] using wordTrace_append hprefix tailTrace_306788
  have hstable : (prefixWord ++ tailWord_306788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306788).length < 2 ^ (prefixWord ++ tailWord_306788).sum := by decide
  have hdescent : baseEnd_306788 < baseStart_306788 := by decide
  rcases family_descends (prefixWord ++ tailWord_306788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306900 : List Nat := [2, 4, 1, 3, 1, 1, 7]
def baseStart_306900 : Nat := 118140960795 + 306900 * 2 ^ 59
def prefixEnd_306900 : Nat := 4983230072969 + 3 ^ 40 * 306900 * 2
def baseEnd_306900 : Nat := 31128338343694713291575

theorem tailTrace_306900 : CollatzResearch.WordTrace tailWord_306900 prefixEnd_306900 31128338343694713291575 := by
  unfold tailWord_306900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596781294080594596095077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7462375058774126128126769 5596781294080594596095077)
  ·
    refine ⟨1049396492640111486767827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5596781294080594596095077 1049396492640111486767827)
    ·
      refine ⟨1574094738960167230151741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049396492640111486767827 1574094738960167230151741)
      ·
        refine ⟨590285527110062711306903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1574094738960167230151741 590285527110062711306903)
        ·
          refine ⟨885428290665094066960355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590285527110062711306903 885428290665094066960355)
          ·
            refine ⟨1328142435997641100440533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885428290665094066960355 1328142435997641100440533)
            ·
              refine ⟨31128338343694713291575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1328142435997641100440533 31128338343694713291575)
              ·
                rfl

theorem cell19_306900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_306900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306900 prefixEnd_306900 := by exact prefixLift 306900
  have htrace : WordTrace (prefixWord ++ tailWord_306900) baseStart_306900 baseEnd_306900 := by
    simpa [prefixWord, tailWord_306900, baseEnd_306900] using wordTrace_append hprefix tailTrace_306900
  have hstable : (prefixWord ++ tailWord_306900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306900).length < 2 ^ (prefixWord ++ tailWord_306900).sum := by decide
  have hdescent : baseEnd_306900 < baseStart_306900 := by decide
  rcases family_descends (prefixWord ++ tailWord_306900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306940 : List Nat := [2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_306940 : Nat := 118140960795 + 306940 * 2 ^ 59
def prefixEnd_306940 : Nat := 4983230072969 + 3 ^ 40 * 306940 * 2
def baseEnd_306940 : Nat := 93397186424375898985727

theorem tailTrace_306940 : CollatzResearch.WordTrace tailWord_306940 prefixEnd_306940 93397186424375898985727 := by
  unfold tailWord_306940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597510754008138011823137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7463347672010850682430849 5597510754008138011823137)
  ·
    refine ⟨4198133065506103508867353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5597510754008138011823137 4198133065506103508867353)
    ·
      refine ⟨3148599799129577631650515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4198133065506103508867353 3148599799129577631650515)
      ·
        refine ⟨4722899698694366447475773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3148599799129577631650515 4722899698694366447475773)
        ·
          refine ⟨1771087387010387417803415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4722899698694366447475773 1771087387010387417803415)
          ·
            refine ⟨2656631080515581126705123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771087387010387417803415 2656631080515581126705123)
            ·
              refine ⟨3984946620773371690057685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656631080515581126705123 3984946620773371690057685)
              ·
                refine ⟨93397186424375898985727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3984946620773371690057685 93397186424375898985727)
                ·
                  rfl

theorem cell19_306940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_306940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_306940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_306940 prefixEnd_306940 := by exact prefixLift 306940
  have htrace : WordTrace (prefixWord ++ tailWord_306940) baseStart_306940 baseEnd_306940 := by
    simpa [prefixWord, tailWord_306940, baseEnd_306940] using wordTrace_append hprefix tailTrace_306940
  have hstable : (prefixWord ++ tailWord_306940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306940).length < 2 ^ (prefixWord ++ tailWord_306940).sum := by decide
  have hdescent : baseEnd_306940 < baseStart_306940 := by decide
  rcases family_descends (prefixWord ++ tailWord_306940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307016 : List Nat := [2, 1, 3, 1, 1, 5, 6]
def baseStart_307016 : Nat := 118140960795 + 307016 * 2 ^ 59
def prefixEnd_307016 : Nat := 4983230072969 + 3 ^ 40 * 307016 * 2
def baseEnd_307016 : Nat := 31140104023876747098877

theorem tailTrace_307016 : CollatzResearch.WordTrace tailWord_307016 prefixEnd_307016 31140104023876747098877 := by
  unfold tailWord_307016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5598896727870470501706451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7465195637160627335608601 5598896727870470501706451)
  ·
    refine ⟨8398345091805705752559677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5598896727870470501706451 8398345091805705752559677)
    ·
      refine ⟨3149379409427139657209879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8398345091805705752559677 3149379409427139657209879)
      ·
        refine ⟨4724069114140709485814819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149379409427139657209879 4724069114140709485814819)
        ·
          refine ⟨7086103671211064228722229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724069114140709485814819 7086103671211064228722229)
          ·
            refine ⟨664322219176037271442709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7086103671211064228722229 664322219176037271442709)
            ·
              refine ⟨31140104023876747098877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 664322219176037271442709 31140104023876747098877)
              ·
                rfl

theorem cell19_307016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_307016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307016 prefixEnd_307016 := by exact prefixLift 307016
  have htrace : WordTrace (prefixWord ++ tailWord_307016) baseStart_307016 baseEnd_307016 := by
    simpa [prefixWord, tailWord_307016, baseEnd_307016] using wordTrace_append hprefix tailTrace_307016
  have hstable : (prefixWord ++ tailWord_307016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307016).length < 2 ^ (prefixWord ++ tailWord_307016).sum := by decide
  have hdescent : baseEnd_307016 < baseStart_307016 := by decide
  rcases family_descends (prefixWord ++ tailWord_307016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307050 : List Nat := [3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_307050 : Nat := 118140960795 + 307050 * 2 ^ 59
def prefixEnd_307050 : Nat := 4983230072969 + 3 ^ 40 * 307050 * 2
def baseEnd_307050 : Nat := 93430657755928236540983

theorem tailTrace_307050 : CollatzResearch.WordTrace tailWord_307050 prefixEnd_307050 93430657755928236540983 := by
  unfold tailWord_307050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799758384404441202537651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7466022358411843206767069 2799758384404441202537651)
  ·
    refine ⟨4199637576606661803806477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799758384404441202537651 4199637576606661803806477)
    ·
      refine ⟨1574864091227498176427429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4199637576606661803806477 1574864091227498176427429)
      ·
        refine ⟨295287017105155908080143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1574864091227498176427429 295287017105155908080143)
        ·
          refine ⟨442930525657733862120215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295287017105155908080143 442930525657733862120215)
          ·
            refine ⟨664395788486600793180323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442930525657733862120215 664395788486600793180323)
            ·
              refine ⟨996593682729901189770485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664395788486600793180323 996593682729901189770485)
              ·
                refine ⟨93430657755928236540983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 996593682729901189770485 93430657755928236540983)
                ·
                  rfl

theorem cell19_307050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_307050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307050 prefixEnd_307050 := by exact prefixLift 307050
  have htrace : WordTrace (prefixWord ++ tailWord_307050) baseStart_307050 baseEnd_307050 := by
    simpa [prefixWord, tailWord_307050, baseEnd_307050] using wordTrace_append hprefix tailTrace_307050
  have hstable : (prefixWord ++ tailWord_307050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307050).length < 2 ^ (prefixWord ++ tailWord_307050).sum := by decide
  have hdescent : baseEnd_307050 < baseStart_307050 := by decide
  rcases family_descends (prefixWord ++ tailWord_307050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307052 : List Nat := [2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_307052 : Nat := 118140960795 + 307052 * 2 ^ 59
def prefixEnd_307052 : Nat := 4983230072969 + 3 ^ 40 * 307052 * 2
def baseEnd_307052 : Nat := 93431266325592824496533

theorem tailTrace_307052 : CollatzResearch.WordTrace tailWord_307052 prefixEnd_307052 93431266325592824496533 := by
  unfold tailWord_307052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599553241805259575861705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7466070989073679434482273 5599553241805259575861705)
  ·
    refine ⟨4199664931353944681896279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5599553241805259575861705 4199664931353944681896279)
    ·
      refine ⟨6299497397030917022844419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199664931353944681896279 6299497397030917022844419)
      ·
        refine ⟨9449246095546375534266629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6299497397030917022844419 9449246095546375534266629)
        ·
          refine ⟨1771733642914945412674993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9449246095546375534266629 1771733642914945412674993)
          ·
            refine ⟨1328800232186209059506245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771733642914945412674993 1328800232186209059506245)
            ·
              refine ⟨249150043534914198657421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1328800232186209059506245 249150043534914198657421)
              ·
                refine ⟨93431266325592824496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249150043534914198657421 93431266325592824496533)
                ·
                  rfl

theorem cell19_307052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_307052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307052 prefixEnd_307052 := by exact prefixLift 307052
  have htrace : WordTrace (prefixWord ++ tailWord_307052) baseStart_307052 baseEnd_307052 := by
    simpa [prefixWord, tailWord_307052, baseEnd_307052] using wordTrace_append hprefix tailTrace_307052
  have hstable : (prefixWord ++ tailWord_307052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307052).length < 2 ^ (prefixWord ++ tailWord_307052).sum := by decide
  have hdescent : baseEnd_307052 < baseStart_307052 := by decide
  rcases family_descends (prefixWord ++ tailWord_307052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307090 : List Nat := [3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_307090 : Nat := 118140960795 + 307090 * 2 ^ 59
def prefixEnd_307090 : Nat := 4983230072969 + 3 ^ 40 * 307090 * 2
def baseEnd_307090 : Nat := 93442829149219995651985

theorem tailTrace_307090 : CollatzResearch.WordTrace tailWord_307090 prefixEnd_307090 93442829149219995651985 := by
  unfold tailWord_307090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800123114368212910401681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7466994971648567761071149 2800123114368212910401681)
  ·
    refine ⟨2100092335776159682801261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2800123114368212910401681 2100092335776159682801261)
    ·
      refine ⟨787534625916059881050473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2100092335776159682801261 787534625916059881050473)
      ·
        refine ⟨590650969437044910787855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787534625916059881050473 590650969437044910787855)
        ·
          refine ⟨885976454155567366181783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590650969437044910787855 885976454155567366181783)
          ·
            refine ⟨1328964681233351049272675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885976454155567366181783 1328964681233351049272675)
            ·
              refine ⟨1993447021850026573909013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328964681233351049272675 1993447021850026573909013)
              ·
                refine ⟨93442829149219995651985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1993447021850026573909013 93442829149219995651985)
                ·
                  rfl

theorem cell19_307090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_307090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307090 prefixEnd_307090 := by exact prefixLift 307090
  have htrace : WordTrace (prefixWord ++ tailWord_307090) baseStart_307090 baseEnd_307090 := by
    simpa [prefixWord, tailWord_307090, baseEnd_307090] using wordTrace_append hprefix tailTrace_307090
  have hstable : (prefixWord ++ tailWord_307090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307090).length < 2 ^ (prefixWord ++ tailWord_307090).sum := by decide
  have hdescent : baseEnd_307090 < baseStart_307090 := by decide
  rcases family_descends (prefixWord ++ tailWord_307090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307221 : List Nat := [1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_307221 : Nat := 118140960795 + 307221 * 2 ^ 59
def prefixEnd_307221 : Nat := 4983230072969 + 3 ^ 40 * 307221 * 2
def baseEnd_307221 : Nat := 93482690462250506740517

theorem tailTrace_307221 : CollatzResearch.WordTrace tailWord_307221 prefixEnd_307221 93482690462250506740517 := by
  unfold tailWord_307221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205270419998261014625517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7470180279998840676417011 11205270419998261014625517)
  ·
    refine ⟨4201976407499347880484569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11205270419998261014625517 4201976407499347880484569)
    ·
      refine ⟨3151482305624510910363427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4201976407499347880484569 3151482305624510910363427)
      ·
        refine ⟨4727223458436766365545141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151482305624510910363427 4727223458436766365545141)
        ·
          refine ⟨443177199228446846769857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4727223458436766365545141 443177199228446846769857)
          ·
            refine ⟨332382899421335135077393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443177199228446846769857 332382899421335135077393)
            ·
              refine ⟨249287174566001351308045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332382899421335135077393 249287174566001351308045)
              ·
                refine ⟨93482690462250506740517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249287174566001351308045 93482690462250506740517)
                ·
                  rfl

theorem cell19_307221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_307221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307221 prefixEnd_307221 := by exact prefixLift 307221
  have htrace : WordTrace (prefixWord ++ tailWord_307221) baseStart_307221 baseEnd_307221 := by
    simpa [prefixWord, tailWord_307221, baseEnd_307221] using wordTrace_append hprefix tailTrace_307221
  have hstable : (prefixWord ++ tailWord_307221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307221).length < 2 ^ (prefixWord ++ tailWord_307221).sum := by decide
  have hdescent : baseEnd_307221 < baseStart_307221 := by decide
  rcases family_descends (prefixWord ++ tailWord_307221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307223 : List Nat := [1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_307223 : Nat := 118140960795 + 307223 * 2 ^ 59
def prefixEnd_307223 : Nat := 4983230072969 + 3 ^ 40 * 307223 * 2
def baseEnd_307223 : Nat := 93483299031915094696067

theorem tailTrace_307223 : CollatzResearch.WordTrace tailWord_307223 prefixEnd_307223 93483299031915094696067 := by
  unfold tailWord_307223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205343365991015356198323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7470228910660676904132215 11205343365991015356198323)
  ·
    refine ⟨16808015048986523034297485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11205343365991015356198323 16808015048986523034297485)
    ·
      refine ⟨6303005643369946137861557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16808015048986523034297485 6303005643369946137861557)
      ·
        refine ⟨590906779065932450424521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6303005643369946137861557 590906779065932450424521)
        ·
          refine ⟨443180084299449337818391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590906779065932450424521 443180084299449337818391)
          ·
            refine ⟨664770126449174006727587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443180084299449337818391 664770126449174006727587)
            ·
              refine ⟨997155189673761010091381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664770126449174006727587 997155189673761010091381)
              ·
                refine ⟨93483299031915094696067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 997155189673761010091381 93483299031915094696067)
                ·
                  rfl

theorem cell19_307223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_307223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307223 prefixEnd_307223 := by exact prefixLift 307223
  have htrace : WordTrace (prefixWord ++ tailWord_307223) baseStart_307223 baseEnd_307223 := by
    simpa [prefixWord, tailWord_307223, baseEnd_307223] using wordTrace_append hprefix tailTrace_307223
  have hstable : (prefixWord ++ tailWord_307223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307223).length < 2 ^ (prefixWord ++ tailWord_307223).sum := by decide
  have hdescent : baseEnd_307223 < baseStart_307223 := by decide
  rcases family_descends (prefixWord ++ tailWord_307223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307240 : List Nat := [2, 1, 5, 3, 1, 2, 5]
def baseStart_307240 : Nat := 118140960795 + 307240 * 2 ^ 59
def prefixEnd_307240 : Nat := 4983230072969 + 3 ^ 40 * 307240 * 2
def baseEnd_307240 : Nat := 31162823958021364106081

theorem tailTrace_307240 : CollatzResearch.WordTrace tailWord_307240 prefixEnd_307240 31162823958021364106081 := by
  unfold tailWord_307240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602981703464713629783587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7470642271286284839711449 5602981703464713629783587)
  ·
    refine ⟨8404472555197070444675381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5602981703464713629783587 8404472555197070444675381)
    ·
      refine ⟨787919302049725354188317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8404472555197070444675381 787919302049725354188317)
      ·
        refine ⟨295469738268647007820619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 787919302049725354188317 295469738268647007820619)
        ·
          refine ⟨443204607402970511730929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295469738268647007820619 443204607402970511730929)
          ·
            refine ⟨332403455552227883798197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443204607402970511730929 332403455552227883798197)
            ·
              refine ⟨31162823958021364106081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 332403455552227883798197 31162823958021364106081)
              ·
                rfl

theorem cell19_307240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_307240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307240 prefixEnd_307240 := by exact prefixLift 307240
  have htrace : WordTrace (prefixWord ++ tailWord_307240) baseStart_307240 baseEnd_307240 := by
    simpa [prefixWord, tailWord_307240, baseEnd_307240] using wordTrace_append hprefix tailTrace_307240
  have hstable : (prefixWord ++ tailWord_307240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307240).length < 2 ^ (prefixWord ++ tailWord_307240).sum := by decide
  have hdescent : baseEnd_307240 < baseStart_307240 := by decide
  rcases family_descends (prefixWord ++ tailWord_307240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307242 : List Nat := [3, 1, 4, 1, 2, 3, 5]
def baseStart_307242 : Nat := 118140960795 + 307242 * 2 ^ 59
def prefixEnd_307242 : Nat := 4983230072969 + 3 ^ 40 * 307242 * 2
def baseEnd_307242 : Nat := 31163026814576226757931

theorem tailTrace_307242 : CollatzResearch.WordTrace tailWord_307242 prefixEnd_307242 31163026814576226757931 := by
  unfold tailWord_307242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801509088230545400284995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7470690901948121067426653 2801509088230545400284995)
  ·
    refine ⟨4202263632345818100427493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2801509088230545400284995 4202263632345818100427493)
    ·
      refine ⟨787924431064840893830155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4202263632345818100427493 787924431064840893830155)
      ·
        refine ⟨1181886646597261340745233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787924431064840893830155 1181886646597261340745233)
        ·
          refine ⟨886414984947946005558925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181886646597261340745233 886414984947946005558925)
          ·
            refine ⟨332405619355479752084597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 886414984947946005558925 332405619355479752084597)
            ·
              refine ⟨31163026814576226757931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 332405619355479752084597 31163026814576226757931)
              ·
                rfl

theorem cell19_307242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_307242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307242 prefixEnd_307242 := by exact prefixLift 307242
  have htrace : WordTrace (prefixWord ++ tailWord_307242) baseStart_307242 baseEnd_307242 := by
    simpa [prefixWord, tailWord_307242, baseEnd_307242] using wordTrace_append hprefix tailTrace_307242
  have hstable : (prefixWord ++ tailWord_307242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307242).length < 2 ^ (prefixWord ++ tailWord_307242).sum := by decide
  have hdescent : baseEnd_307242 < baseStart_307242 := by decide
  rcases family_descends (prefixWord ++ tailWord_307242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307318 : List Nat := [5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_307318 : Nat := 118140960795 + 307318 * 2 ^ 59
def prefixEnd_307318 : Nat := 4983230072969 + 3 ^ 40 * 307318 * 2
def baseEnd_307318 : Nat := 93512206090983022584697

theorem tailTrace_307318 : CollatzResearch.WordTrace tailWord_307318 prefixEnd_307318 93512206090983022584697 := by
  unfold tailWord_307318
  simp only [CollatzResearch.WordTrace]
  refine ⟨700550518790427911306663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7472538867097897720604405 700550518790427911306663)
  ·
    refine ⟨1050825778185641866959995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 700550518790427911306663 1050825778185641866959995)
    ·
      refine ⟨1576238667278462800439993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050825778185641866959995 1576238667278462800439993)
      ·
        refine ⟨1182179000458847100329995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576238667278462800439993 1182179000458847100329995)
        ·
          refine ⟨1773268500688270650494993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182179000458847100329995 1773268500688270650494993)
          ·
            refine ⟨1329951375516202987871245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773268500688270650494993 1329951375516202987871245)
            ·
              refine ⟨498731765818576120451717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329951375516202987871245 498731765818576120451717)
              ·
                refine ⟨93512206090983022584697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498731765818576120451717 93512206090983022584697)
                ·
                  rfl

theorem cell19_307318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_307318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307318 prefixEnd_307318 := by exact prefixLift 307318
  have htrace : WordTrace (prefixWord ++ tailWord_307318) baseStart_307318 baseEnd_307318 := by
    simpa [prefixWord, tailWord_307318, baseEnd_307318] using wordTrace_append hprefix tailTrace_307318
  have hstable : (prefixWord ++ tailWord_307318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307318).length < 2 ^ (prefixWord ++ tailWord_307318).sum := by decide
  have hdescent : baseEnd_307318 < baseStart_307318 := by decide
  rcases family_descends (prefixWord ++ tailWord_307318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307350 : List Nat := [5, 3, 2, 1, 1, 1, 6]
def baseStart_307350 : Nat := 118140960795 + 307350 * 2 ^ 59
def prefixEnd_307350 : Nat := 4983230072969 + 3 ^ 40 * 307350 * 2
def baseEnd_307350 : Nat := 31173981068538809957833

theorem tailTrace_307350 : CollatzResearch.WordTrace tailWord_307350 prefixEnd_307350 31173981068538809957833 := by
  unfold tailWord_307350
  simp only [CollatzResearch.WordTrace]
  refine ⟨700623464783182252879469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7473316957687277364047669 700623464783182252879469)
  ·
    refine ⟨262733799293693344829801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 700623464783182252879469 262733799293693344829801)
    ·
      refine ⟨197050349470270008622351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262733799293693344829801 197050349470270008622351)
      ·
        refine ⟨295575524205405012933527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197050349470270008622351 295575524205405012933527)
        ·
          refine ⟨443363286308107519400291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295575524205405012933527 443363286308107519400291)
          ·
            refine ⟨665044929462161279100437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443363286308107519400291 665044929462161279100437)
            ·
              refine ⟨31173981068538809957833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 665044929462161279100437 31173981068538809957833)
              ·
                rfl

theorem cell19_307350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_307350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307350 prefixEnd_307350 := by exact prefixLift 307350
  have htrace : WordTrace (prefixWord ++ tailWord_307350) baseStart_307350 baseEnd_307350 := by
    simpa [prefixWord, tailWord_307350, baseEnd_307350] using wordTrace_append hprefix tailTrace_307350
  have hstable : (prefixWord ++ tailWord_307350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307350).length < 2 ^ (prefixWord ++ tailWord_307350).sum := by decide
  have hdescent : baseEnd_307350 < baseStart_307350 := by decide
  rcases family_descends (prefixWord ++ tailWord_307350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307379 : List Nat := [1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_307379 : Nat := 118140960795 + 307379 * 2 ^ 59
def prefixEnd_307379 : Nat := 4983230072969 + 3 ^ 40 * 307379 * 2
def baseEnd_307379 : Nat := 93530767465752955228975

theorem tailTrace_307379 : CollatzResearch.WordTrace tailWord_307379 prefixEnd_307379 93530767465752955228975 := by
  unfold tailWord_307379
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211033153425853998877191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7474022102283902665918127 11211033153425853998877191)
  ·
    refine ⟨16816549730138780998315787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11211033153425853998877191 16816549730138780998315787)
    ·
      refine ⟨25224824595208171497473681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16816549730138780998315787 25224824595208171497473681)
      ·
        refine ⟨18918618446406128623105261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25224824595208171497473681 18918618446406128623105261)
        ·
          refine ⟨7094481917402298233664473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18918618446406128623105261 7094481917402298233664473)
          ·
            refine ⟨5320861438051723675248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7094481917402298233664473 5320861438051723675248355)
            ·
              refine ⟨7981292157077585512872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320861438051723675248355 7981292157077585512872533)
              ·
                refine ⟨93530767465752955228975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7981292157077585512872533 93530767465752955228975)
                ·
                  rfl

theorem cell19_307379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_307379 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307379 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307379 prefixEnd_307379 := by exact prefixLift 307379
  have htrace : WordTrace (prefixWord ++ tailWord_307379) baseStart_307379 baseEnd_307379 := by
    simpa [prefixWord, tailWord_307379, baseEnd_307379] using wordTrace_append hprefix tailTrace_307379
  have hstable : (prefixWord ++ tailWord_307379).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307379).length < 2 ^ (prefixWord ++ tailWord_307379).sum := by decide
  have hdescent : baseEnd_307379 < baseStart_307379 := by decide
  rcases family_descends (prefixWord ++ tailWord_307379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307390 : List Nat := [4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_307390 : Nat := 118140960795 + 307390 * 2 ^ 59
def prefixEnd_307390 : Nat := 4983230072969 + 3 ^ 40 * 307390 * 2
def baseEnd_307390 : Nat := 93534114598908188984501

theorem tailTrace_307390 : CollatzResearch.WordTrace tailWord_307390 prefixEnd_307390 93534114598908188984501 := by
  unfold tailWord_307390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401429294548250359690953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7474289570924001918351749 1401429294548250359690953)
  ·
    refine ⟨1051071970911187769768215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1401429294548250359690953 1051071970911187769768215)
    ·
      refine ⟨1576607956366781654652323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051071970911187769768215 1576607956366781654652323)
      ·
        refine ⟨2364911934550172481978485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576607956366781654652323 2364911934550172481978485)
        ·
          refine ⟨221710493864078670185483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2364911934550172481978485 221710493864078670185483)
          ·
            refine ⟨332565740796118005278225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221710493864078670185483 332565740796118005278225)
            ·
              refine ⟨249424305597088503958669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332565740796118005278225 249424305597088503958669)
              ·
                refine ⟨93534114598908188984501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249424305597088503958669 93534114598908188984501)
                ·
                  rfl

theorem cell19_307390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_307390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307390 prefixEnd_307390 := by exact prefixLift 307390
  have htrace : WordTrace (prefixWord ++ tailWord_307390) baseStart_307390 baseEnd_307390 := by
    simpa [prefixWord, tailWord_307390, baseEnd_307390] using wordTrace_append hprefix tailTrace_307390
  have hstable : (prefixWord ++ tailWord_307390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307390).length < 2 ^ (prefixWord ++ tailWord_307390).sum := by decide
  have hdescent : baseEnd_307390 < baseStart_307390 := by decide
  rcases family_descends (prefixWord ++ tailWord_307390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307413 : List Nat := [1, 3, 2, 4, 2, 2, 5]
def baseStart_307413 : Nat := 118140960795 + 307413 * 2 ^ 59
def prefixEnd_307413 : Nat := 4983230072969 + 3 ^ 40 * 307413 * 2
def baseEnd_307413 : Nat := 31180371050016983491109

theorem tailTrace_307413 : CollatzResearch.WordTrace tailWord_307413 prefixEnd_307413 31180371050016983491109 := by
  unfold tailWord_307413
  simp only [CollatzResearch.WordTrace]
  refine ⟨11212273235302677805614893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7474848823535118537076595 11212273235302677805614893)
  ·
    refine ⟨4204602463238504177105585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11212273235302677805614893 4204602463238504177105585)
    ·
      refine ⟨3153451847428878132829189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4204602463238504177105585 3153451847428878132829189)
      ·
        refine ⟨591272221392914649905473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3153451847428878132829189 591272221392914649905473)
        ·
          refine ⟨443454166044685987429105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591272221392914649905473 443454166044685987429105)
          ·
            refine ⟨332590624533514490571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443454166044685987429105 332590624533514490571829)
            ·
              refine ⟨31180371050016983491109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 332590624533514490571829 31180371050016983491109)
              ·
                rfl

theorem cell19_307413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_307413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307413 prefixEnd_307413 := by exact prefixLift 307413
  have htrace : WordTrace (prefixWord ++ tailWord_307413) baseStart_307413 baseEnd_307413 := by
    simpa [prefixWord, tailWord_307413, baseEnd_307413] using wordTrace_append hprefix tailTrace_307413
  have hstable : (prefixWord ++ tailWord_307413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307413).length < 2 ^ (prefixWord ++ tailWord_307413).sum := by decide
  have hdescent : baseEnd_307413 < baseStart_307413 := by decide
  rcases family_descends (prefixWord ++ tailWord_307413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307417 : List Nat := [1, 2, 1, 2, 3, 1, 9]
def baseStart_307417 : Nat := 118140960795 + 307417 * 2 ^ 59
def prefixEnd_307417 : Nat := 4983230072969 + 3 ^ 40 * 307417 * 2
def baseEnd_307417 : Nat := 31180776763126708794809

theorem tailTrace_307417 : CollatzResearch.WordTrace tailWord_307417 prefixEnd_307417 31180776763126708794809 := by
  unfold tailWord_307417
  simp only [CollatzResearch.WordTrace]
  refine ⟨11212419127288186488760505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7474946084858790992507003 11212419127288186488760505)
  ·
    refine ⟨8409314345466139866570379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11212419127288186488760505 8409314345466139866570379)
    ·
      refine ⟨12613971518199209799855569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8409314345466139866570379 12613971518199209799855569)
      ·
        refine ⟨9460478638649407349891677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12613971518199209799855569 9460478638649407349891677)
        ·
          refine ⟨3547679489493527756209379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9460478638649407349891677 3547679489493527756209379)
          ·
            refine ⟨5321519234240291634314069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547679489493527756209379 5321519234240291634314069)
            ·
              refine ⟨31180776763126708794809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5321519234240291634314069 31180776763126708794809)
              ·
                rfl

theorem cell19_307417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_307417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307417 prefixEnd_307417 := by exact prefixLift 307417
  have htrace : WordTrace (prefixWord ++ tailWord_307417) baseStart_307417 baseEnd_307417 := by
    simpa [prefixWord, tailWord_307417, baseEnd_307417] using wordTrace_append hprefix tailTrace_307417
  have hstable : (prefixWord ++ tailWord_307417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307417).length < 2 ^ (prefixWord ++ tailWord_307417).sum := by decide
  have hdescent : baseEnd_307417 < baseStart_307417 := by decide
  rcases family_descends (prefixWord ++ tailWord_307417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307434 : List Nat := [3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_307434 : Nat := 118140960795 + 307434 * 2 ^ 59
def prefixEnd_307434 : Nat := 4983230072969 + 3 ^ 40 * 307434 * 2
def baseEnd_307434 : Nat := 93547503131529124006603

theorem tailTrace_307434 : CollatzResearch.WordTrace tailWord_307434 prefixEnd_307434 93547503131529124006603 := by
  unfold tailWord_307434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803259792056649598032339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7475359445484398928086237 2803259792056649598032339)
  ·
    refine ⟨4204889688084974397048509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2803259792056649598032339 4204889688084974397048509)
    ·
      refine ⟨1576833633031865398893191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4204889688084974397048509 1576833633031865398893191)
      ·
        refine ⟨2365250449547798098339787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576833633031865398893191 2365250449547798098339787)
        ·
          refine ⟨3547875674321697147509681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365250449547798098339787 3547875674321697147509681)
          ·
            refine ⟨2660906755741272860632261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3547875674321697147509681 2660906755741272860632261)
            ·
              refine ⟨498920016701488661368549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2660906755741272860632261 498920016701488661368549)
              ·
                refine ⟨93547503131529124006603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498920016701488661368549 93547503131529124006603)
                ·
                  rfl

theorem cell19_307434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_307434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307434 prefixEnd_307434 := by exact prefixLift 307434
  have htrace : WordTrace (prefixWord ++ tailWord_307434) baseStart_307434 baseEnd_307434 := by
    simpa [prefixWord, tailWord_307434, baseEnd_307434] using wordTrace_append hprefix tailTrace_307434
  have hstable : (prefixWord ++ tailWord_307434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307434).length < 2 ^ (prefixWord ++ tailWord_307434).sum := by decide
  have hdescent : baseEnd_307434 < baseStart_307434 := by decide
  rcases family_descends (prefixWord ++ tailWord_307434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307455 : List Nat := [1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_307455 : Nat := 118140960795 + 307455 * 2 ^ 59
def prefixEnd_307455 : Nat := 4983230072969 + 3 ^ 40 * 307455 * 2
def baseEnd_307455 : Nat := 93553893113007297539879

theorem tailTrace_307455 : CollatzResearch.WordTrace tailWord_307455 prefixEnd_307455 93553893113007297539879 := by
  unfold tailWord_307455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213805101150518978643819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7475870067433679319095879 11213805101150518978643819)
  ·
    refine ⟨16820707651725778467965729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11213805101150518978643819 16820707651725778467965729)
    ·
      refine ⟨12615530738794333850974297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16820707651725778467965729 12615530738794333850974297)
      ·
        refine ⟨9461648054095750388230723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12615530738794333850974297 9461648054095750388230723)
        ·
          refine ⟨14192472081143625582346085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9461648054095750388230723 14192472081143625582346085)
          ·
            refine ⟨2661088515214429796689891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14192472081143625582346085 2661088515214429796689891)
            ·
              refine ⟨3991632772821644695034837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661088515214429796689891 3991632772821644695034837)
              ·
                refine ⟨93553893113007297539879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3991632772821644695034837 93553893113007297539879)
                ·
                  rfl

theorem cell19_307455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_307455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307455 prefixEnd_307455 := by exact prefixLift 307455
  have htrace : WordTrace (prefixWord ++ tailWord_307455) baseStart_307455 baseEnd_307455 := by
    simpa [prefixWord, tailWord_307455, baseEnd_307455] using wordTrace_append hprefix tailTrace_307455
  have hstable : (prefixWord ++ tailWord_307455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307455).length < 2 ^ (prefixWord ++ tailWord_307455).sum := by decide
  have hdescent : baseEnd_307455 < baseStart_307455 := by decide
  rcases family_descends (prefixWord ++ tailWord_307455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307512 : List Nat := [2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_307512 : Nat := 118140960795 + 307512 * 2 ^ 59
def prefixEnd_307512 : Nat := 4983230072969 + 3 ^ 40 * 307512 * 2
def baseEnd_307512 : Nat := 93571237348448054273057

theorem tailTrace_307512 : CollatzResearch.WordTrace tailWord_307512 prefixEnd_307512 93571237348448054273057 := by
  unfold tailWord_307512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607942030972008856734395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7477256041296011808979193 5607942030972008856734395)
  ·
    refine ⟨8411913046458013285101593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5607942030972008856734395 8411913046458013285101593)
    ·
      refine ⟨6308934784843509963826195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8411913046458013285101593 6308934784843509963826195)
      ·
        refine ⟨9463402177265264945739293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308934784843509963826195 9463402177265264945739293)
        ·
          refine ⟨3548775816474474354652235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9463402177265264945739293 3548775816474474354652235)
          ·
            refine ⟨5323163724711711531978353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548775816474474354652235 5323163724711711531978353)
            ·
              refine ⟨3992372793533783648983765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5323163724711711531978353 3992372793533783648983765)
              ·
                refine ⟨93571237348448054273057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3992372793533783648983765 93571237348448054273057)
                ·
                  rfl

theorem cell19_307512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_307512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307512 prefixEnd_307512 := by exact prefixLift 307512
  have htrace : WordTrace (prefixWord ++ tailWord_307512) baseStart_307512 baseEnd_307512 := by
    simpa [prefixWord, tailWord_307512, baseEnd_307512] using wordTrace_append hprefix tailTrace_307512
  have hstable : (prefixWord ++ tailWord_307512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307512).length < 2 ^ (prefixWord ++ tailWord_307512).sum := by decide
  have hdescent : baseEnd_307512 < baseStart_307512 := by decide
  rcases family_descends (prefixWord ++ tailWord_307512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307607 : List Nat := [1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_307607 : Nat := 118140960795 + 307607 * 2 ^ 59
def prefixEnd_307607 : Nat := 4983230072969 + 3 ^ 40 * 307607 * 2
def baseEnd_307607 : Nat := 93600144407515982161687

theorem tailTrace_307607 : CollatzResearch.WordTrace tailWord_307607 prefixEnd_307607 93600144407515982161687 := by
  unfold tailWord_307607
  simp only [CollatzResearch.WordTrace]
  refine ⟨11219348996599848938177075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7479565997733232625451383 11219348996599848938177075)
  ·
    refine ⟨16829023494899773407265613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11219348996599848938177075 16829023494899773407265613)
    ·
      refine ⟨6310883810587415027724605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16829023494899773407265613 6310883810587415027724605)
      ·
        refine ⟨2366581428970280635396727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6310883810587415027724605 2366581428970280635396727)
        ·
          refine ⟨3549872143455420953095091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366581428970280635396727 3549872143455420953095091)
          ·
            refine ⟨5324808215183131429642637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549872143455420953095091 5324808215183131429642637)
            ·
              refine ⟨1996803080693674286115989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5324808215183131429642637 1996803080693674286115989)
              ·
                refine ⟨93600144407515982161687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1996803080693674286115989 93600144407515982161687)
                ·
                  rfl

theorem cell19_307607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_307607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307607 prefixEnd_307607 := by exact prefixLift 307607
  have htrace : WordTrace (prefixWord ++ tailWord_307607) baseStart_307607 baseEnd_307607 := by
    simpa [prefixWord, tailWord_307607, baseEnd_307607] using wordTrace_append hprefix tailTrace_307607
  have hstable : (prefixWord ++ tailWord_307607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307607).length < 2 ^ (prefixWord ++ tailWord_307607).sum := by decide
  have hdescent : baseEnd_307607 < baseStart_307607 := by decide
  rcases family_descends (prefixWord ++ tailWord_307607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307645 : List Nat := [1, 4, 1, 2, 2, 9]
def baseStart_307645 : Nat := 118140960795 + 307645 * 2 ^ 59
def prefixEnd_307645 : Nat := 4983230072969 + 3 ^ 40 * 307645 * 2
def baseEnd_307645 : Nat := 10401300803460350368571

theorem tailTrace_307645 : CollatzResearch.WordTrace tailWord_307645 prefixEnd_307645 10401300803460350368571 := by
  unfold tailWord_307645
  simp only [CollatzResearch.WordTrace]
  refine ⟨11220734970462181428060389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7480489980308120952040259 11220734970462181428060389)
  ·
    refine ⟨2103887806961659017761323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11220734970462181428060389 2103887806961659017761323)
    ·
      refine ⟨3155831710442488526641985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103887806961659017761323 3155831710442488526641985)
      ·
        refine ⟨2366873782831866394981489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3155831710442488526641985 2366873782831866394981489)
        ·
          refine ⟨1775155337123899796236117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2366873782831866394981489 1775155337123899796236117)
          ·
            refine ⟨10401300803460350368571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1775155337123899796236117 10401300803460350368571)
            ·
              rfl

theorem cell19_307645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_307645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307645 prefixEnd_307645 := by exact prefixLift 307645
  have htrace : WordTrace (prefixWord ++ tailWord_307645) baseStart_307645 baseEnd_307645 := by
    simpa [prefixWord, tailWord_307645, baseEnd_307645] using wordTrace_append hprefix tailTrace_307645
  have hstable : (prefixWord ++ tailWord_307645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307645).length < 2 ^ (prefixWord ++ tailWord_307645).sum := by decide
  have hdescent : baseEnd_307645 < baseStart_307645 := by decide
  rcases family_descends (prefixWord ++ tailWord_307645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307660 : List Nat := [2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_307660 : Nat := 118140960795 + 307660 * 2 ^ 59
def prefixEnd_307660 : Nat := 4983230072969 + 3 ^ 40 * 307660 * 2
def baseEnd_307660 : Nat := 93616271503627562983765

theorem tailTrace_307660 : CollatzResearch.WordTrace tailWord_307660 prefixEnd_307660 93616271503627562983765 := by
  unfold tailWord_307660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610641032703919494928217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7480854710271892659904289 5610641032703919494928217)
  ·
    refine ⟨4207980774527939621196163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5610641032703919494928217 4207980774527939621196163)
    ·
      refine ⟨6311971161791909431794245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207980774527939621196163 6311971161791909431794245)
      ·
        refine ⟨1183494592835983018461421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6311971161791909431794245 1183494592835983018461421)
        ·
          refine ⟨443810472313493631923033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1183494592835983018461421 443810472313493631923033)
          ·
            refine ⟨332857854235120223942275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443810472313493631923033 332857854235120223942275)
            ·
              refine ⟨499286781352680335913413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332857854235120223942275 499286781352680335913413)
              ·
                refine ⟨93616271503627562983765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499286781352680335913413 93616271503627562983765)
                ·
                  rfl

theorem cell19_307660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_307660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307660 prefixEnd_307660 := by exact prefixLift 307660
  have htrace : WordTrace (prefixWord ++ tailWord_307660) baseStart_307660 baseEnd_307660 := by
    simpa [prefixWord, tailWord_307660, baseEnd_307660] using wordTrace_append hprefix tailTrace_307660
  have hstable : (prefixWord ++ tailWord_307660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307660).length < 2 ^ (prefixWord ++ tailWord_307660).sum := by decide
  have hdescent : baseEnd_307660 < baseStart_307660 := by decide
  rcases family_descends (prefixWord ++ tailWord_307660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307681 : List Nat := [1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_307681 : Nat := 118140960795 + 307681 * 2 ^ 59
def prefixEnd_307681 : Nat := 4983230072969 + 3 ^ 40 * 307681 * 2
def baseEnd_307681 : Nat := 93622661485105736517041

theorem tailTrace_307681 : CollatzResearch.WordTrace tailWord_307681 prefixEnd_307681 93622661485105736517041 := by
  unfold tailWord_307681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222047998331759576370897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7481365332221173050913931 11222047998331759576370897)
  ·
    refine ⟨8416535998748819682278173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11222047998331759576370897 8416535998748819682278173)
    ·
      refine ⟨3156200999530807380854315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8416535998748819682278173 3156200999530807380854315)
      ·
        refine ⟨4734301499296211071281473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156200999530807380854315 4734301499296211071281473)
        ·
          refine ⟨3550726124472158303461105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4734301499296211071281473 3550726124472158303461105)
          ·
            refine ⟨2663044593354118727595829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3550726124472158303461105 2663044593354118727595829)
            ·
              refine ⟨249660430626948630712109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2663044593354118727595829 249660430626948630712109)
              ·
                refine ⟨93622661485105736517041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249660430626948630712109 93622661485105736517041)
                ·
                  rfl

theorem cell19_307681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_307681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307681 prefixEnd_307681 := by exact prefixLift 307681
  have htrace : WordTrace (prefixWord ++ tailWord_307681) baseStart_307681 baseEnd_307681 := by
    simpa [prefixWord, tailWord_307681, baseEnd_307681] using wordTrace_append hprefix tailTrace_307681
  have hstable : (prefixWord ++ tailWord_307681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307681).length < 2 ^ (prefixWord ++ tailWord_307681).sum := by decide
  have hdescent : baseEnd_307681 < baseStart_307681 := by decide
  rcases family_descends (prefixWord ++ tailWord_307681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307736 : List Nat := [2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_307736 : Nat := 118140960795 + 307736 * 2 ^ 59
def prefixEnd_307736 : Nat := 4983230072969 + 3 ^ 40 * 307736 * 2
def baseEnd_307736 : Nat := 93639397150881905294669

theorem tailTrace_307736 : CollatzResearch.WordTrace tailWord_307736 prefixEnd_307736 93639397150881905294669 := by
  unfold tailWord_307736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612027006566251984811531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7482702675421669313082041 5612027006566251984811531)
  ·
    refine ⟨8418040509849377977217297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5612027006566251984811531 8418040509849377977217297)
    ·
      refine ⟨6313530382387033482912973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8418040509849377977217297 6313530382387033482912973)
      ·
        refine ⟨2367573893395137556092365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6313530382387033482912973 2367573893395137556092365)
        ·
          refine ⟨887840210023176583534637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2367573893395137556092365 887840210023176583534637)
          ·
            refine ⟨332940078758691218825489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 887840210023176583534637 332940078758691218825489)
            ·
              refine ⟨249705059069018414119117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332940078758691218825489 249705059069018414119117)
              ·
                refine ⟨93639397150881905294669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249705059069018414119117 93639397150881905294669)
                ·
                  rfl

theorem cell19_307736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_307736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307736 prefixEnd_307736 := by exact prefixLift 307736
  have htrace : WordTrace (prefixWord ++ tailWord_307736) baseStart_307736 baseEnd_307736 := by
    simpa [prefixWord, tailWord_307736, baseEnd_307736] using wordTrace_append hprefix tailTrace_307736
  have hstable : (prefixWord ++ tailWord_307736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307736).length < 2 ^ (prefixWord ++ tailWord_307736).sum := by decide
  have hdescent : baseEnd_307736 < baseStart_307736 := by decide
  rcases family_descends (prefixWord ++ tailWord_307736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307738 : List Nat := [3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_307738 : Nat := 118140960795 + 307738 * 2 ^ 59
def prefixEnd_307738 : Nat := 4983230072969 + 3 ^ 40 * 307738 * 2
def baseEnd_307738 : Nat := 93640005720546493250219

theorem tailTrace_307738 : CollatzResearch.WordTrace tailWord_307738 prefixEnd_307738 93640005720546493250219 := by
  unfold tailWord_307738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806031739781314577798967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7482751306083505540797245 2806031739781314577798967)
  ·
    refine ⟨4209047609671971866698451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2806031739781314577798967 4209047609671971866698451)
    ·
      refine ⟨6313571414507957800047677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209047609671971866698451 6313571414507957800047677)
      ·
        refine ⟨2367589280440484175017879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6313571414507957800047677 2367589280440484175017879)
        ·
          refine ⟨3551383920660726262526819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367589280440484175017879 3551383920660726262526819)
          ·
            refine ⟨5327075880991089393790229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551383920660726262526819 5327075880991089393790229)
            ·
              refine ⟨249706681921457315333917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5327075880991089393790229 249706681921457315333917)
              ·
                refine ⟨93640005720546493250219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249706681921457315333917 93640005720546493250219)
                ·
                  rfl

theorem cell19_307738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_307738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307738 prefixEnd_307738 := by exact prefixLift 307738
  have htrace : WordTrace (prefixWord ++ tailWord_307738) baseStart_307738 baseEnd_307738 := by
    simpa [prefixWord, tailWord_307738, baseEnd_307738] using wordTrace_append hprefix tailTrace_307738
  have hstable : (prefixWord ++ tailWord_307738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307738).length < 2 ^ (prefixWord ++ tailWord_307738).sum := by decide
  have hdescent : baseEnd_307738 < baseStart_307738 := by decide
  rcases family_descends (prefixWord ++ tailWord_307738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307797 : List Nat := [1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_307797 : Nat := 118140960795 + 307797 * 2 ^ 59
def prefixEnd_307797 : Nat := 4983230072969 + 3 ^ 40 * 307797 * 2
def baseEnd_307797 : Nat := 93657958525651837938947

theorem tailTrace_307797 : CollatzResearch.WordTrace tailWord_307797 prefixEnd_307797 93657958525651837938947 := by
  unfold tailWord_307797
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226278865911511387593645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7484185910607674258395763 11226278865911511387593645)
  ·
    refine ⟨4209854574716816770347617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11226278865911511387593645 4209854574716816770347617)
    ·
      refine ⟨3157390931037612577760713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4209854574716816770347617 3157390931037612577760713)
      ·
        refine ⟨2368043198278209433320535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3157390931037612577760713 2368043198278209433320535)
        ·
          refine ⟨3552064797417314149980803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368043198278209433320535 3552064797417314149980803)
          ·
            refine ⟨5328097196125971224971205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552064797417314149980803 5328097196125971224971205)
            ·
              refine ⟨999018224273619604682101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5328097196125971224971205 999018224273619604682101)
              ·
                refine ⟨93657958525651837938947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999018224273619604682101 93657958525651837938947)
                ·
                  rfl

theorem cell19_307797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_307797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307797 prefixEnd_307797 := by exact prefixLift 307797
  have htrace : WordTrace (prefixWord ++ tailWord_307797) baseStart_307797 baseEnd_307797 := by
    simpa [prefixWord, tailWord_307797, baseEnd_307797] using wordTrace_append hprefix tailTrace_307797
  have hstable : (prefixWord ++ tailWord_307797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307797).length < 2 ^ (prefixWord ++ tailWord_307797).sum := by decide
  have hdescent : baseEnd_307797 < baseStart_307797 := by decide
  rcases family_descends (prefixWord ++ tailWord_307797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307816 : List Nat := [2, 1, 4, 3, 9]
def baseStart_307816 : Nat := 118140960795 + 307816 * 2 ^ 59
def prefixEnd_307816 : Nat := 4983230072969 + 3 ^ 40 * 307816 * 2
def baseEnd_307816 : Nat := 3469027405091311982099

theorem tailTrace_307816 : CollatzResearch.WordTrace tailWord_307816 prefixEnd_307816 3469027405091311982099 := by
  unfold tailWord_307816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613485926421338816267651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7484647901895118421690201 5613485926421338816267651)
  ·
    refine ⟨8420228889632008224401477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613485926421338816267651 8420228889632008224401477)
    ·
      refine ⟨1578792916806001542075277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8420228889632008224401477 1578792916806001542075277)
      ·
        refine ⟨592047343802250578278229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1578792916806001542075277 592047343802250578278229)
        ·
          refine ⟨3469027405091311982099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 592047343802250578278229 3469027405091311982099)
          ·
            rfl

theorem cell19_307816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 9].length) (baseStart_307816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307816 prefixEnd_307816 := by exact prefixLift 307816
  have htrace : WordTrace (prefixWord ++ tailWord_307816) baseStart_307816 baseEnd_307816 := by
    simpa [prefixWord, tailWord_307816, baseEnd_307816] using wordTrace_append hprefix tailTrace_307816
  have hstable : (prefixWord ++ tailWord_307816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307816).length < 2 ^ (prefixWord ++ tailWord_307816).sum := by decide
  have hdescent : baseEnd_307816 < baseStart_307816 := by decide
  rcases family_descends (prefixWord ++ tailWord_307816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307829 : List Nat := [1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_307829 : Nat := 118140960795 + 307829 * 2 ^ 59
def prefixEnd_307829 : Nat := 4983230072969 + 3 ^ 40 * 307829 * 2
def baseEnd_307829 : Nat := 93667695640285245227749

theorem tailTrace_307829 : CollatzResearch.WordTrace tailWord_307829 prefixEnd_307829 93667695640285245227749 := by
  unfold tailWord_307829
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227446001795580852758541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7484964001197053901839027 11227446001795580852758541)
  ·
    refine ⟨4210292250673342819784453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11227446001795580852758541 4210292250673342819784453)
    ·
      refine ⟨789429797001251778709585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4210292250673342819784453 789429797001251778709585)
      ·
        refine ⟨592072347750938834032189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 789429797001251778709585 592072347750938834032189)
        ·
          refine ⟨222027130406602062762071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 592072347750938834032189 222027130406602062762071)
          ·
            refine ⟨333040695609903094143107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222027130406602062762071 333040695609903094143107)
            ·
              refine ⟨499561043414854641214661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333040695609903094143107 499561043414854641214661)
              ·
                refine ⟨93667695640285245227749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499561043414854641214661 93667695640285245227749)
                ·
                  rfl

theorem cell19_307829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_307829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307829 prefixEnd_307829 := by exact prefixLift 307829
  have htrace : WordTrace (prefixWord ++ tailWord_307829) baseStart_307829 baseEnd_307829 := by
    simpa [prefixWord, tailWord_307829, baseEnd_307829] using wordTrace_append hprefix tailTrace_307829
  have hstable : (prefixWord ++ tailWord_307829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307829).length < 2 ^ (prefixWord ++ tailWord_307829).sum := by decide
  have hdescent : baseEnd_307829 < baseStart_307829 := by decide
  rcases family_descends (prefixWord ++ tailWord_307829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307833 : List Nat := [1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_307833 : Nat := 118140960795 + 307833 * 2 ^ 59
def prefixEnd_307833 : Nat := 4983230072969 + 3 ^ 40 * 307833 * 2
def baseEnd_307833 : Nat := 93668912779614421138849

theorem tailTrace_307833 : CollatzResearch.WordTrace tailWord_307833 prefixEnd_307833 93668912779614421138849 := by
  unfold tailWord_307833
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227591893781089535904153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7485061262520726357269435 11227591893781089535904153)
  ·
    refine ⟨8420693920335817151928115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11227591893781089535904153 8420693920335817151928115)
    ·
      refine ⟨12631040880503725727892173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420693920335817151928115 12631040880503725727892173)
      ·
        refine ⟨4736640330188897147959565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12631040880503725727892173 4736640330188897147959565)
        ·
          refine ⟨1776240123820836430484837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4736640330188897147959565 1776240123820836430484837)
          ·
            refine ⟨333045023216406830715907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1776240123820836430484837 333045023216406830715907)
            ·
              refine ⟨499567534824610246073861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333045023216406830715907 499567534824610246073861)
              ·
                refine ⟨93668912779614421138849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499567534824610246073861 93668912779614421138849)
                ·
                  rfl

theorem cell19_307833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_307833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307833 prefixEnd_307833 := by exact prefixLift 307833
  have htrace : WordTrace (prefixWord ++ tailWord_307833) baseStart_307833 baseEnd_307833 := by
    simpa [prefixWord, tailWord_307833, baseEnd_307833] using wordTrace_append hprefix tailTrace_307833
  have hstable : (prefixWord ++ tailWord_307833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307833).length < 2 ^ (prefixWord ++ tailWord_307833).sum := by decide
  have hdescent : baseEnd_307833 < baseStart_307833 := by decide
  rcases family_descends (prefixWord ++ tailWord_307833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307850 : List Nat := [3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_307850 : Nat := 118140960795 + 307850 * 2 ^ 59
def prefixEnd_307850 : Nat := 4983230072969 + 3 ^ 40 * 307850 * 2
def baseEnd_307850 : Nat := 93674085621763418761025

theorem tailTrace_307850 : CollatzResearch.WordTrace tailWord_307850 prefixEnd_307850 93674085621763418761025 := by
  unfold tailWord_307850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807052983679875359818251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7485474623146334292848669 2807052983679875359818251)
  ·
    refine ⟨4210579475519813039727377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807052983679875359818251 4210579475519813039727377)
    ·
      refine ⟨3157934606639859779795533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4210579475519813039727377 3157934606639859779795533)
      ·
        refine ⟨1184225477489947417423325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3157934606639859779795533 1184225477489947417423325)
        ·
          refine ⟨444084554058730281533747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1184225477489947417423325 444084554058730281533747)
          ·
            refine ⟨666126831088095422300621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444084554058730281533747 666126831088095422300621)
            ·
              refine ⟨249797561658035783362733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666126831088095422300621 249797561658035783362733)
              ·
                refine ⟨93674085621763418761025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249797561658035783362733 93674085621763418761025)
                ·
                  rfl

theorem cell19_307850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_307850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307850 prefixEnd_307850 := by exact prefixLift 307850
  have htrace : WordTrace (prefixWord ++ tailWord_307850) baseStart_307850 baseEnd_307850 := by
    simpa [prefixWord, tailWord_307850, baseEnd_307850] using wordTrace_append hprefix tailTrace_307850
  have hstable : (prefixWord ++ tailWord_307850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307850).length < 2 ^ (prefixWord ++ tailWord_307850).sum := by decide
  have hdescent : baseEnd_307850 < baseStart_307850 := by decide
  rcases family_descends (prefixWord ++ tailWord_307850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307966 : List Nat := [4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_307966 : Nat := 118140960795 + 307966 * 2 ^ 59
def prefixEnd_307966 : Nat := 4983230072969 + 3 ^ 40 * 307966 * 2
def baseEnd_307966 : Nat := 93709382662309520182931

theorem tailTrace_307966 : CollatzResearch.WordTrace tailWord_307966 prefixEnd_307966 93709382662309520182931 := by
  unfold tailWord_307966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404055350287406656311969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7488295201532835500330501 1404055350287406656311969)
  ·
    refine ⟨1053041512715554992233977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1404055350287406656311969 1053041512715554992233977)
    ·
      refine ⟨789781134536666244175483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053041512715554992233977 789781134536666244175483)
      ·
        refine ⟨1184671701804999366263225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789781134536666244175483 1184671701804999366263225)
        ·
          refine ⟨888503776353749524697419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184671701804999366263225 888503776353749524697419)
          ·
            refine ⟨1332755664530624287046129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888503776353749524697419 1332755664530624287046129)
            ·
              refine ⟨999566748397968215284597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332755664530624287046129 999566748397968215284597)
              ·
                refine ⟨93709382662309520182931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999566748397968215284597 93709382662309520182931)
                ·
                  rfl

theorem cell19_307966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_307966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_307966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_307966 prefixEnd_307966 := by exact prefixLift 307966
  have htrace : WordTrace (prefixWord ++ tailWord_307966) baseStart_307966 baseEnd_307966 := by
    simpa [prefixWord, tailWord_307966, baseEnd_307966] using wordTrace_append hprefix tailTrace_307966
  have hstable : (prefixWord ++ tailWord_307966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307966).length < 2 ^ (prefixWord ++ tailWord_307966).sum := by decide
  have hdescent : baseEnd_307966 < baseStart_307966 := by decide
  rcases family_descends (prefixWord ++ tailWord_307966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308044 : List Nat := [2, 2, 1, 3, 3, 2, 6]
def baseStart_308044 : Nat := 118140960795 + 308044 * 2 ^ 59
def prefixEnd_308044 : Nat := 4983230072969 + 3 ^ 40 * 308044 * 2
def baseEnd_308044 : Nat := 31244372293076150149795

theorem tailTrace_308044 : CollatzResearch.WordTrace tailWord_308044 prefixEnd_308044 31244372293076150149795 := by
  unfold tailWord_308044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617643848008336285917593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7490191797344448381223457 5617643848008336285917593)
  ·
    refine ⟨4213232886006252214438195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5617643848008336285917593 4213232886006252214438195)
    ·
      refine ⟨6319849329009378321657293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213232886006252214438195 6319849329009378321657293)
      ·
        refine ⟨2369943498378516870621485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6319849329009378321657293 2369943498378516870621485)
        ·
          refine ⟨888728811891943826483057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2369943498378516870621485 888728811891943826483057)
          ·
            refine ⟨666546608918957869862293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888728811891943826483057 666546608918957869862293)
            ·
              refine ⟨31244372293076150149795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 666546608918957869862293 31244372293076150149795)
              ·
                rfl

theorem cell19_308044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_308044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308044 prefixEnd_308044 := by exact prefixLift 308044
  have htrace : WordTrace (prefixWord ++ tailWord_308044) baseStart_308044 baseEnd_308044 := by
    simpa [prefixWord, tailWord_308044, baseEnd_308044] using wordTrace_append hprefix tailTrace_308044
  have hstable : (prefixWord ++ tailWord_308044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308044).length < 2 ^ (prefixWord ++ tailWord_308044).sum := by decide
  have hdescent : baseEnd_308044 < baseStart_308044 := by decide
  rcases family_descends (prefixWord ++ tailWord_308044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308101 : List Nat := [1, 3, 1, 1, 3, 5, 5]
def baseStart_308101 : Nat := 118140960795 + 308101 * 2 ^ 59
def prefixEnd_308101 : Nat := 4983230072969 + 3 ^ 40 * 308101 * 2
def baseEnd_308101 : Nat := 31250153704889735727521

theorem tailTrace_308101 : CollatzResearch.WordTrace tailWord_308101 prefixEnd_308101 31250153704889735727521 := by
  unfold tailWord_308101
  simp only [CollatzResearch.WordTrace]
  refine ⟨11237366656810171306660157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7491577771206780871106771 11237366656810171306660157)
  ·
    refine ⟨4214012496303814239997559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11237366656810171306660157 4214012496303814239997559)
    ·
      refine ⟨6321018744455721359996339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214012496303814239997559 6321018744455721359996339)
      ·
        refine ⟨9481528116683582039994509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6321018744455721359996339 9481528116683582039994509)
        ·
          refine ⟨3555573043756343264997941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9481528116683582039994509 3555573043756343264997941)
          ·
            refine ⟨333334972852157181093557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3555573043756343264997941 333334972852157181093557)
            ·
              refine ⟨31250153704889735727521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 333334972852157181093557 31250153704889735727521)
              ·
                rfl

theorem cell19_308101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_308101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308101 prefixEnd_308101 := by exact prefixLift 308101
  have htrace : WordTrace (prefixWord ++ tailWord_308101) baseStart_308101 baseEnd_308101 := by
    simpa [prefixWord, tailWord_308101, baseEnd_308101] using wordTrace_append hprefix tailTrace_308101
  have hstable : (prefixWord ++ tailWord_308101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308101).length < 2 ^ (prefixWord ++ tailWord_308101).sum := by decide
  have hdescent : baseEnd_308101 < baseStart_308101 := by decide
  rcases family_descends (prefixWord ++ tailWord_308101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308160 : List Nat := [2, 1, 1, 2, 3, 10]
def baseStart_308160 : Nat := 118140960795 + 308160 * 2 ^ 59
def prefixEnd_308160 : Nat := 4983230072969 + 3 ^ 40 * 308160 * 2
def baseEnd_308160 : Nat := 10418712657752727985699

theorem tailTrace_308160 : CollatzResearch.WordTrace tailWord_308160 prefixEnd_308160 10418712657752727985699 := by
  unfold tailWord_308160
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619759281798212191528967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7493012375730949588705289 5619759281798212191528967)
  ·
    refine ⟨8429638922697318287293451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5619759281798212191528967 8429638922697318287293451)
    ·
      refine ⟨12644458384045977430940177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8429638922697318287293451 12644458384045977430940177)
      ·
        refine ⟨9483343788034483073205133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12644458384045977430940177 9483343788034483073205133)
        ·
          refine ⟨3556253920512931152451925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9483343788034483073205133 3556253920512931152451925)
          ·
            refine ⟨10418712657752727985699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3556253920512931152451925 10418712657752727985699)
            ·
              rfl

theorem cell19_308160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_308160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308160 prefixEnd_308160 := by exact prefixLift 308160
  have htrace : WordTrace (prefixWord ++ tailWord_308160) baseStart_308160 baseEnd_308160 := by
    simpa [prefixWord, tailWord_308160, baseEnd_308160] using wordTrace_append hprefix tailTrace_308160
  have hstable : (prefixWord ++ tailWord_308160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308160).length < 2 ^ (prefixWord ++ tailWord_308160).sum := by decide
  have hdescent : baseEnd_308160 < baseStart_308160 := by decide
  rcases family_descends (prefixWord ++ tailWord_308160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308217 : List Nat := [1, 2, 1, 3, 1, 3, 8]
def baseStart_308217 : Nat := 118140960795 + 308217 * 2 ^ 59
def prefixEnd_308217 : Nat := 4983230072969 + 3 ^ 40 * 308217 * 2
def baseEnd_308217 : Nat := 31261919385071769534823

theorem tailTrace_308217 : CollatzResearch.WordTrace tailWord_308217 prefixEnd_308217 31261919385071769534823 := by
  unfold tailWord_308217
  simp only [CollatzResearch.WordTrace]
  refine ⟨11241597524389923117882905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7494398349593282078588603 11241597524389923117882905)
  ·
    refine ⟨8431198143292442338412179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11241597524389923117882905 8431198143292442338412179)
    ·
      refine ⟨12646797214938663507618269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8431198143292442338412179 12646797214938663507618269)
      ·
        refine ⟨4742548955601998815356851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12646797214938663507618269 4742548955601998815356851)
        ·
          refine ⟨7113823433402998223035277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742548955601998815356851 7113823433402998223035277)
          ·
            refine ⟨2667683787526124333638229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7113823433402998223035277 2667683787526124333638229)
            ·
              refine ⟨31261919385071769534823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2667683787526124333638229 31261919385071769534823)
              ·
                rfl

theorem cell19_308217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_308217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308217 prefixEnd_308217 := by exact prefixLift 308217
  have htrace : WordTrace (prefixWord ++ tailWord_308217) baseStart_308217 baseEnd_308217 := by
    simpa [prefixWord, tailWord_308217, baseEnd_308217] using wordTrace_append hprefix tailTrace_308217
  have hstable : (prefixWord ++ tailWord_308217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308217).length < 2 ^ (prefixWord ++ tailWord_308217).sum := by decide
  have hdescent : baseEnd_308217 < baseStart_308217 := by decide
  rcases family_descends (prefixWord ++ tailWord_308217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308289 : List Nat := [1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_308289 : Nat := 118140960795 + 308289 * 2 ^ 59
def prefixEnd_308289 : Nat := 4983230072969 + 3 ^ 40 * 308289 * 2
def baseEnd_308289 : Nat := 93807666663140475004273

theorem tailTrace_308289 : CollatzResearch.WordTrace tailWord_308289 prefixEnd_308289 93807666663140475004273 := by
  unfold tailWord_308289
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244223580129079414503921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7496149053419386276335947 11244223580129079414503921)
  ·
    refine ⟨8433167685096809560877941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11244223580129079414503921 8433167685096809560877941)
    ·
      refine ⟨790609470477825896332307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8433167685096809560877941 790609470477825896332307)
      ·
        refine ⟨1185914205716738844498461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790609470477825896332307 1185914205716738844498461)
        ·
          refine ⟨444717827143777066686923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1185914205716738844498461 444717827143777066686923)
          ·
            refine ⟨667076740715665600030385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444717827143777066686923 667076740715665600030385)
            ·
              refine ⟨500307555536749200022789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667076740715665600030385 500307555536749200022789)
              ·
                refine ⟨93807666663140475004273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 500307555536749200022789 93807666663140475004273)
                ·
                  rfl

theorem cell19_308289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_308289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308289 prefixEnd_308289 := by exact prefixLift 308289
  have htrace : WordTrace (prefixWord ++ tailWord_308289) baseStart_308289 baseEnd_308289 := by
    simpa [prefixWord, tailWord_308289, baseEnd_308289] using wordTrace_append hprefix tailTrace_308289
  have hstable : (prefixWord ++ tailWord_308289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308289).length < 2 ^ (prefixWord ++ tailWord_308289).sum := by decide
  have hdescent : baseEnd_308289 < baseStart_308289 := by decide
  rcases family_descends (prefixWord ++ tailWord_308289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308293 : List Nat := [1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_308293 : Nat := 118140960795 + 308293 * 2 ^ 59
def prefixEnd_308293 : Nat := 4983230072969 + 3 ^ 40 * 308293 * 2
def baseEnd_308293 : Nat := 93808883802469650915373

theorem tailTrace_308293 : CollatzResearch.WordTrace tailWord_308293 prefixEnd_308293 93808883802469650915373 := by
  unfold tailWord_308293
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244369472114588097649533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7496246314743058731766355 11244369472114588097649533)
  ·
    refine ⟨4216638552042970536618575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11244369472114588097649533 4216638552042970536618575)
    ·
      refine ⟨6324957828064455804927863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216638552042970536618575 6324957828064455804927863)
      ·
        refine ⟨9487436742096683707391795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324957828064455804927863 9487436742096683707391795)
        ·
          refine ⟨14231155113145025561087693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487436742096683707391795 14231155113145025561087693)
          ·
            refine ⟨5336683167429384585407885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14231155113145025561087693 5336683167429384585407885)
            ·
              refine ⟨2001256187786019219527957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5336683167429384585407885 2001256187786019219527957)
              ·
                refine ⟨93808883802469650915373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2001256187786019219527957 93808883802469650915373)
                ·
                  rfl

theorem cell19_308293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_308293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308293 prefixEnd_308293 := by exact prefixLift 308293
  have htrace : WordTrace (prefixWord ++ tailWord_308293) baseStart_308293 baseEnd_308293 := by
    simpa [prefixWord, tailWord_308293, baseEnd_308293] using wordTrace_append hprefix tailTrace_308293
  have hstable : (prefixWord ++ tailWord_308293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308293).length < 2 ^ (prefixWord ++ tailWord_308293).sum := by decide
  have hdescent : baseEnd_308293 < baseStart_308293 := by decide
  rcases family_descends (prefixWord ++ tailWord_308293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308312 : List Nat := [2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_308312 : Nat := 118140960795 + 308312 * 2 ^ 59
def prefixEnd_308312 : Nat := 4983230072969 + 3 ^ 40 * 308312 * 2
def baseEnd_308312 : Nat := 93814665214283236493099

theorem tailTrace_308312 : CollatzResearch.WordTrace tailWord_308312 prefixEnd_308312 93814665214283236493099 := by
  unfold tailWord_308312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622531229522877171295595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7496708306030502895060793 5622531229522877171295595)
  ·
    refine ⟨8433796844284315756943393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5622531229522877171295595 8433796844284315756943393)
    ·
      refine ⟨6325347633213236817707545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8433796844284315756943393 6325347633213236817707545)
      ·
        refine ⟨4744010724909927613280659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6325347633213236817707545 4744010724909927613280659)
        ·
          refine ⟨7116016087364891419920989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744010724909927613280659 7116016087364891419920989)
          ·
            refine ⟨2668506032761834282470371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7116016087364891419920989 2668506032761834282470371)
            ·
              refine ⟨4002759049142751423705557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668506032761834282470371 4002759049142751423705557)
              ·
                refine ⟨93814665214283236493099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4002759049142751423705557 93814665214283236493099)
                ·
                  rfl

theorem cell19_308312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_308312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308312 prefixEnd_308312 := by exact prefixLift 308312
  have htrace : WordTrace (prefixWord ++ tailWord_308312) baseStart_308312 baseEnd_308312 := by
    simpa [prefixWord, tailWord_308312, baseEnd_308312] using wordTrace_append hprefix tailTrace_308312
  have hstable : (prefixWord ++ tailWord_308312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308312).length < 2 ^ (prefixWord ++ tailWord_308312).sum := by decide
  have hdescent : baseEnd_308312 < baseStart_308312 := by decide
  rcases family_descends (prefixWord ++ tailWord_308312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308407 : List Nat := [1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_308407 : Nat := 118140960795 + 308407 * 2 ^ 59
def prefixEnd_308407 : Nat := 4983230072969 + 3 ^ 40 * 308407 * 2
def baseEnd_308407 : Nat := 93843572273351164381729

theorem tailTrace_308407 : CollatzResearch.WordTrace tailWord_308407 prefixEnd_308407 93843572273351164381729 := by
  unfold tailWord_308407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11248527393701585567299475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7499018262467723711532983 11248527393701585567299475)
  ·
    refine ⟨16872791090552378350949213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11248527393701585567299475 16872791090552378350949213)
    ·
      refine ⟨6327296658957141881605955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16872791090552378350949213 6327296658957141881605955)
      ·
        refine ⟨9490944988435712822408933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6327296658957141881605955 9490944988435712822408933)
        ·
          refine ⟨1779552185331696154201675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9490944988435712822408933 1779552185331696154201675)
          ·
            refine ⟨2669328277997544231302513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779552185331696154201675 2669328277997544231302513)
            ·
              refine ⟨2001996208498158173476885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669328277997544231302513 2001996208498158173476885)
              ·
                refine ⟨93843572273351164381729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2001996208498158173476885 93843572273351164381729)
                ·
                  rfl

theorem cell19_308407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_308407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308407 prefixEnd_308407 := by exact prefixLift 308407
  have htrace : WordTrace (prefixWord ++ tailWord_308407) baseStart_308407 baseEnd_308407 := by
    simpa [prefixWord, tailWord_308407, baseEnd_308407] using wordTrace_append hprefix tailTrace_308407
  have hstable : (prefixWord ++ tailWord_308407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308407).length < 2 ^ (prefixWord ++ tailWord_308407).sum := by decide
  have hdescent : baseEnd_308407 < baseStart_308407 := by decide
  rcases family_descends (prefixWord ++ tailWord_308407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308420 : List Nat := [2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_308420 : Nat := 118140960795 + 308420 * 2 ^ 59
def prefixEnd_308420 : Nat := 4983230072969 + 3 ^ 40 * 308420 * 2
def baseEnd_308420 : Nat := 93847527976170986092805

theorem tailTrace_308420 : CollatzResearch.WordTrace tailWord_308420 prefixEnd_308420 93847527976170986092805 := by
  unfold tailWord_308420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624500771327244393761357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7499334361769659191681809 5624500771327244393761357)
  ·
    refine ⟨2109187789247716647660509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5624500771327244393761357 2109187789247716647660509)
    ·
      refine ⟨790945420967893742872691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2109187789247716647660509 790945420967893742872691)
      ·
        refine ⟨1186418131451840614309037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790945420967893742872691 1186418131451840614309037)
        ·
          refine ⟨444906799294440230365889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1186418131451840614309037 444906799294440230365889)
          ·
            refine ⟨333680099470830172774417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444906799294440230365889 333680099470830172774417)
            ·
              refine ⟨250260074603122629580813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333680099470830172774417 250260074603122629580813)
              ·
                refine ⟨93847527976170986092805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250260074603122629580813 93847527976170986092805)
                ·
                  rfl

theorem cell19_308420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_308420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308420 prefixEnd_308420 := by exact prefixLift 308420
  have htrace : WordTrace (prefixWord ++ tailWord_308420) baseStart_308420 baseEnd_308420 := by
    simpa [prefixWord, tailWord_308420, baseEnd_308420] using wordTrace_append hprefix tailTrace_308420
  have hstable : (prefixWord ++ tailWord_308420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308420).length < 2 ^ (prefixWord ++ tailWord_308420).sum := by decide
  have hdescent : baseEnd_308420 < baseStart_308420 := by decide
  rcases family_descends (prefixWord ++ tailWord_308420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308424 : List Nat := [2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_308424 : Nat := 118140960795 + 308424 * 2 ^ 59
def prefixEnd_308424 : Nat := 4983230072969 + 3 ^ 40 * 308424 * 2
def baseEnd_308424 : Nat := 93848745115500162003905

theorem tailTrace_308424 : CollatzResearch.WordTrace tailWord_308424 prefixEnd_308424 93848745115500162003905 := by
  unfold tailWord_308424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624573717319998735334163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7499431623093331647112217 5624573717319998735334163)
  ·
    refine ⟨8436860575979998103001245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624573717319998735334163 8436860575979998103001245)
    ·
      refine ⟨3163822715992499288625467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8436860575979998103001245 3163822715992499288625467)
      ·
        refine ⟨4745734073988748932938201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163822715992499288625467 4745734073988748932938201)
        ·
          refine ⟨3559300555491561699703651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4745734073988748932938201 3559300555491561699703651)
          ·
            refine ⟨5338950833237342549555477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559300555491561699703651 5338950833237342549555477)
            ·
              refine ⟨250263320308000432010413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5338950833237342549555477 250263320308000432010413)
              ·
                refine ⟨93848745115500162003905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250263320308000432010413 93848745115500162003905)
                ·
                  rfl

theorem cell19_308424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_308424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308424 prefixEnd_308424 := by exact prefixLift 308424
  have htrace : WordTrace (prefixWord ++ tailWord_308424) baseStart_308424 baseEnd_308424 := by
    simpa [prefixWord, tailWord_308424, baseEnd_308424] using wordTrace_append hprefix tailTrace_308424
  have hstable : (prefixWord ++ tailWord_308424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308424).length < 2 ^ (prefixWord ++ tailWord_308424).sum := by decide
  have hdescent : baseEnd_308424 < baseStart_308424 := by decide
  rcases family_descends (prefixWord ++ tailWord_308424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308483 : List Nat := [1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_308483 : Nat := 118140960795 + 308483 * 2 ^ 59
def prefixEnd_308483 : Nat := 4983230072969 + 3 ^ 40 * 308483 * 2
def baseEnd_308483 : Nat := 93866697920605506692633

theorem tailTrace_308483 : CollatzResearch.WordTrace tailWord_308483 prefixEnd_308483 93866697920605506692633 := by
  unfold tailWord_308483
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251299341426250547066103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7500866227617500364710735 11251299341426250547066103)
  ·
    refine ⟨16876949012139375820599155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11251299341426250547066103 16876949012139375820599155)
    ·
      refine ⟨25315423518209063730898733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16876949012139375820599155 25315423518209063730898733)
      ·
        refine ⟨9493283819328398899087025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25315423518209063730898733 9493283819328398899087025)
        ·
          refine ⟨7119962864496299174315269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9493283819328398899087025 7119962864496299174315269)
          ·
            refine ⟨1334993037093056095184113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7119962864496299174315269 1334993037093056095184113)
            ·
              refine ⟨1001244777819792071388085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334993037093056095184113 1001244777819792071388085)
              ·
                refine ⟨93866697920605506692633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1001244777819792071388085 93866697920605506692633)
                ·
                  rfl

theorem cell19_308483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_308483 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308483 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308483 prefixEnd_308483 := by exact prefixLift 308483
  have htrace : WordTrace (prefixWord ++ tailWord_308483) baseStart_308483 baseEnd_308483 := by
    simpa [prefixWord, tailWord_308483, baseEnd_308483] using wordTrace_append hprefix tailTrace_308483
  have hstable : (prefixWord ++ tailWord_308483).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308483).length < 2 ^ (prefixWord ++ tailWord_308483).sum := by decide
  have hdescent : baseEnd_308483 < baseStart_308483 := by decide
  rcases family_descends (prefixWord ++ tailWord_308483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308498 : List Nat := [3, 2, 4, 2, 1, 7]
def baseStart_308498 : Nat := 118140960795 + 308498 * 2 ^ 59
def prefixEnd_308498 : Nat := 4983230072969 + 3 ^ 40 * 308498 * 2
def baseEnd_308498 : Nat := 10430140243676657373251

theorem tailTrace_308498 : CollatzResearch.WordTrace tailWord_308498 prefixEnd_308498 10430140243676657373251 := by
  unfold tailWord_308498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812961609092977027215537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7501230957581272072574765 2812961609092977027215537)
  ·
    refine ⟨2109721206819732770411653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2812961609092977027215537 2109721206819732770411653)
    ·
      refine ⟨395572726278699894452185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2109721206819732770411653 395572726278699894452185)
      ·
        refine ⟨296679544709024920839139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395572726278699894452185 296679544709024920839139)
        ·
          refine ⟨445019317063537381258709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296679544709024920839139 445019317063537381258709)
          ·
            refine ⟨10430140243676657373251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 445019317063537381258709 10430140243676657373251)
            ·
              rfl

theorem cell19_308498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_308498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308498 prefixEnd_308498 := by exact prefixLift 308498
  have htrace : WordTrace (prefixWord ++ tailWord_308498) baseStart_308498 baseEnd_308498 := by
    simpa [prefixWord, tailWord_308498, baseEnd_308498] using wordTrace_append hprefix tailTrace_308498
  have hstable : (prefixWord ++ tailWord_308498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308498).length < 2 ^ (prefixWord ++ tailWord_308498).sum := by decide
  have hdescent : baseEnd_308498 < baseStart_308498 := by decide
  rcases family_descends (prefixWord ++ tailWord_308498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308538 : List Nat := [3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_308538 : Nat := 118140960795 + 308538 * 2 ^ 59
def prefixEnd_308538 : Nat := 4983230072969 + 3 ^ 40 * 308538 * 2
def baseEnd_308538 : Nat := 93883433586381675470261

theorem tailTrace_308538 : CollatzResearch.WordTrace tailWord_308538 prefixEnd_308538 93883433586381675470261 := by
  unfold tailWord_308538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813326339056748735079567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7502203570817996626878845 2813326339056748735079567)
  ·
    refine ⟨4219989508585123102619351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2813326339056748735079567 4219989508585123102619351)
    ·
      refine ⟨6329984262877684653929027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219989508585123102619351 6329984262877684653929027)
      ·
        refine ⟨9494976394316526980893541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329984262877684653929027 9494976394316526980893541)
        ·
          refine ⟨1780308073934348808917539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9494976394316526980893541 1780308073934348808917539)
          ·
            refine ⟨2670462110901523213376309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780308073934348808917539 2670462110901523213376309)
            ·
              refine ⟨250355822897017801254029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2670462110901523213376309 250355822897017801254029)
              ·
                refine ⟨93883433586381675470261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250355822897017801254029 93883433586381675470261)
                ·
                  rfl

theorem cell19_308538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_308538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308538 prefixEnd_308538 := by exact prefixLift 308538
  have htrace : WordTrace (prefixWord ++ tailWord_308538) baseStart_308538 baseEnd_308538 := by
    simpa [prefixWord, tailWord_308538, baseEnd_308538] using wordTrace_append hprefix tailTrace_308538
  have hstable : (prefixWord ++ tailWord_308538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308538).length < 2 ^ (prefixWord ++ tailWord_308538).sum := by decide
  have hdescent : baseEnd_308538 < baseStart_308538 := by decide
  rcases family_descends (prefixWord ++ tailWord_308538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308616 : List Nat := [2, 1, 3, 3, 1, 2, 7]
def baseStart_308616 : Nat := 118140960795 + 308616 * 2 ^ 59
def prefixEnd_308616 : Nat := 4983230072969 + 3 ^ 40 * 308616 * 2
def baseEnd_308616 : Nat := 31302389267766868578905

theorem tailTrace_308616 : CollatzResearch.WordTrace tailWord_308616 prefixEnd_308616 31302389267766868578905 := by
  unfold tailWord_308616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628075124972207130828851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7504100166629609507771801 5628075124972207130828851)
  ·
    refine ⟨8442112687458310696243277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628075124972207130828851 8442112687458310696243277)
    ·
      refine ⟨3165792257796866511091229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8442112687458310696243277 3165792257796866511091229)
      ·
        refine ⟨1187172096673824941659211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3165792257796866511091229 1187172096673824941659211)
        ·
          refine ⟨1780758145010737412488817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187172096673824941659211 1780758145010737412488817)
          ·
            refine ⟨1335568608758053059366613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780758145010737412488817 1335568608758053059366613)
            ·
              refine ⟨31302389267766868578905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1335568608758053059366613 31302389267766868578905)
              ·
                rfl

theorem cell19_308616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_308616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308616 prefixEnd_308616 := by exact prefixLift 308616
  have htrace : WordTrace (prefixWord ++ tailWord_308616) baseStart_308616 baseEnd_308616 := by
    simpa [prefixWord, tailWord_308616, baseEnd_308616] using wordTrace_append hprefix tailTrace_308616
  have hstable : (prefixWord ++ tailWord_308616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308616).length < 2 ^ (prefixWord ++ tailWord_308616).sum := by decide
  have hdescent : baseEnd_308616 < baseStart_308616 := by decide
  rcases family_descends (prefixWord ++ tailWord_308616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308787 : List Nat := [1, 1, 1, 2, 4, 5, 5]
def baseStart_308787 : Nat := 118140960795 + 308787 * 2 ^ 59
def prefixEnd_308787 : Nat := 4983230072969 + 3 ^ 40 * 308787 * 2
def baseEnd_308787 : Nat := 31319733503207625312083

theorem tailTrace_308787 : CollatzResearch.WordTrace tailWord_308787 prefixEnd_308787 31319733503207625312083 := by
  unfold tailWord_308787
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262387132324910466132615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7508258088216606977421743 11262387132324910466132615)
  ·
    refine ⟨16893580698487365699198923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262387132324910466132615 16893580698487365699198923)
    ·
      refine ⟨25340371047731048548798385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893580698487365699198923 25340371047731048548798385)
      ·
        refine ⟨19005278285798286411598789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25340371047731048548798385 19005278285798286411598789)
        ·
          refine ⟨3563489678587178702174773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19005278285798286411598789 3563489678587178702174773)
          ·
            refine ⟨334077157367548003328885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3563489678587178702174773 334077157367548003328885)
            ·
              refine ⟨31319733503207625312083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 334077157367548003328885 31319733503207625312083)
              ·
                rfl

theorem cell19_308787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_308787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308787 prefixEnd_308787 := by exact prefixLift 308787
  have htrace : WordTrace (prefixWord ++ tailWord_308787) baseStart_308787 baseEnd_308787 := by
    simpa [prefixWord, tailWord_308787, baseEnd_308787] using wordTrace_append hprefix tailTrace_308787
  have hstable : (prefixWord ++ tailWord_308787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308787).length < 2 ^ (prefixWord ++ tailWord_308787).sum := by decide
  have hdescent : baseEnd_308787 < baseStart_308787 := by decide
  rcases family_descends (prefixWord ++ tailWord_308787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308861 : List Nat := [1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_308861 : Nat := 118140960795 + 308861 * 2 ^ 59
def prefixEnd_308861 : Nat := 4983230072969 + 3 ^ 40 * 308861 * 2
def baseEnd_308861 : Nat := 93981717587212630291603

theorem tailTrace_308861 : CollatzResearch.WordTrace tailWord_308861 prefixEnd_308861 93981717587212630291603 := by
  unfold tailWord_308861
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265086134056821104326437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7510057422704547402884291 11265086134056821104326437)
  ·
    refine ⟨2112203650135653957061207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11265086134056821104326437 2112203650135653957061207)
    ·
      refine ⟨3168305475203480935591811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112203650135653957061207 3168305475203480935591811)
      ·
        refine ⟨4752458212805221403387717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168305475203480935591811 4752458212805221403387717)
        ·
          refine ⟨891085914900979013135197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4752458212805221403387717 891085914900979013135197)
          ·
            refine ⟨334157218087867129925699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 891085914900979013135197 334157218087867129925699)
            ·
              refine ⟨501235827131800694888549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334157218087867129925699 501235827131800694888549)
              ·
                refine ⟨93981717587212630291603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501235827131800694888549 93981717587212630291603)
                ·
                  rfl

theorem cell19_308861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_308861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308861 prefixEnd_308861 := by exact prefixLift 308861
  have htrace : WordTrace (prefixWord ++ tailWord_308861) baseStart_308861 baseEnd_308861 := by
    simpa [prefixWord, tailWord_308861, baseEnd_308861] using wordTrace_append hprefix tailTrace_308861
  have hstable : (prefixWord ++ tailWord_308861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308861).length < 2 ^ (prefixWord ++ tailWord_308861).sum := by decide
  have hdescent : baseEnd_308861 < baseStart_308861 := by decide
  rcases family_descends (prefixWord ++ tailWord_308861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308960 : List Nat := [2, 1, 1, 3, 1, 2, 9]
def baseStart_308960 : Nat := 118140960795 + 308960 * 2 ^ 59
def prefixEnd_308960 : Nat := 4983230072969 + 3 ^ 40 * 308960 * 2
def baseEnd_308960 : Nat := 31337280595203244697111

theorem tailTrace_308960 : CollatzResearch.WordTrace tailWord_308960 prefixEnd_308960 31337280595203244697111 := by
  unfold tailWord_308960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634348480349080506090167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7512464640465440674786889 5634348480349080506090167)
  ·
    refine ⟨8451522720523620759135251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634348480349080506090167 8451522720523620759135251)
    ·
      refine ⟨12677284080785431138702877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451522720523620759135251 12677284080785431138702877)
      ·
        refine ⟨4753981530294536677013579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12677284080785431138702877 4753981530294536677013579)
        ·
          refine ⟨7130972295441805015520369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753981530294536677013579 7130972295441805015520369)
          ·
            refine ⟨5348229221581353761640277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130972295441805015520369 5348229221581353761640277)
            ·
              refine ⟨31337280595203244697111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5348229221581353761640277 31337280595203244697111)
              ·
                rfl

theorem cell19_308960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_308960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308960 prefixEnd_308960 := by exact prefixLift 308960
  have htrace : WordTrace (prefixWord ++ tailWord_308960) baseStart_308960 baseEnd_308960 := by
    simpa [prefixWord, tailWord_308960, baseEnd_308960] using wordTrace_append hprefix tailTrace_308960
  have hstable : (prefixWord ++ tailWord_308960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308960).length < 2 ^ (prefixWord ++ tailWord_308960).sum := by decide
  have hdescent : baseEnd_308960 < baseStart_308960 := by decide
  rcases family_descends (prefixWord ++ tailWord_308960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308977 : List Nat := [1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_308977 : Nat := 118140960795 + 308977 * 2 ^ 59
def prefixEnd_308977 : Nat := 4983230072969 + 3 ^ 40 * 308977 * 2
def baseEnd_308977 : Nat := 94017014627758731713509

theorem tailTrace_308977 : CollatzResearch.WordTrace tailWord_308977 prefixEnd_308977 94017014627758731713509 := by
  unfold tailWord_308977
  simp only [CollatzResearch.WordTrace]
  refine ⟨11269317001636572915549185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7512878001091048610366123 11269317001636572915549185)
  ·
    refine ⟨8451987751227429686661889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11269317001636572915549185 8451987751227429686661889)
    ·
      refine ⟨6338990813420572264996417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8451987751227429686661889 6338990813420572264996417)
      ·
        refine ⟨4754243110065429198747313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6338990813420572264996417 4754243110065429198747313)
        ·
          refine ⟨3565682332549071899060485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4754243110065429198747313 3565682332549071899060485)
          ·
            refine ⟨668565437352950981073841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3565682332549071899060485 668565437352950981073841)
            ·
              refine ⟨501424078014713235805381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668565437352950981073841 501424078014713235805381)
              ·
                refine ⟨94017014627758731713509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501424078014713235805381 94017014627758731713509)
                ·
                  rfl

theorem cell19_308977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_308977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308977 prefixEnd_308977 := by exact prefixLift 308977
  have htrace : WordTrace (prefixWord ++ tailWord_308977) baseStart_308977 baseEnd_308977 := by
    simpa [prefixWord, tailWord_308977, baseEnd_308977] using wordTrace_append hprefix tailTrace_308977
  have hstable : (prefixWord ++ tailWord_308977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308977).length < 2 ^ (prefixWord ++ tailWord_308977).sum := by decide
  have hdescent : baseEnd_308977 < baseStart_308977 := by decide
  rcases family_descends (prefixWord ++ tailWord_308977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308979 : List Nat := [1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_308979 : Nat := 118140960795 + 308979 * 2 ^ 59
def prefixEnd_308979 : Nat := 4983230072969 + 3 ^ 40 * 308979 * 2
def baseEnd_308979 : Nat := 94017623197423319669059

theorem tailTrace_308979 : CollatzResearch.WordTrace tailWord_308979 prefixEnd_308979 94017623197423319669059 := by
  unfold tailWord_308979
  simp only [CollatzResearch.WordTrace]
  refine ⟨11269389947629327257121991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7512926631752884838081327 11269389947629327257121991)
  ·
    refine ⟨16904084921443990885682987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11269389947629327257121991 16904084921443990885682987)
    ·
      refine ⟨25356127382165986328524481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16904084921443990885682987 25356127382165986328524481)
      ·
        refine ⟨19017095536624489746393361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25356127382165986328524481 19017095536624489746393361)
        ·
          refine ⟨14262821652468367309795021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19017095536624489746393361 14262821652468367309795021)
          ·
            refine ⟨5348558119675637741173133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14262821652468367309795021 5348558119675637741173133)
            ·
              refine ⟨2005709294878364152939925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5348558119675637741173133 2005709294878364152939925)
              ·
                refine ⟨94017623197423319669059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2005709294878364152939925 94017623197423319669059)
                ·
                  rfl

theorem cell19_308979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_308979 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308979 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308979 prefixEnd_308979 := by exact prefixLift 308979
  have htrace : WordTrace (prefixWord ++ tailWord_308979) baseStart_308979 baseEnd_308979 := by
    simpa [prefixWord, tailWord_308979, baseEnd_308979] using wordTrace_append hprefix tailTrace_308979
  have hstable : (prefixWord ++ tailWord_308979).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308979).length < 2 ^ (prefixWord ++ tailWord_308979).sum := by decide
  have hdescent : baseEnd_308979 < baseStart_308979 := by decide
  rcases family_descends (prefixWord ++ tailWord_308979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308996 : List Nat := [2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_308996 : Nat := 118140960795 + 308996 * 2 ^ 59
def prefixEnd_308996 : Nat := 4983230072969 + 3 ^ 40 * 308996 * 2
def baseEnd_308996 : Nat := 94022796039572317291235

theorem tailTrace_308996 : CollatzResearch.WordTrace tailWord_308996 prefixEnd_308996 94022796039572317291235 := by
  unfold tailWord_308996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635004994283869580245421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7513339992378492773660561 5635004994283869580245421)
  ·
    refine ⟨2113126872856451092592033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5635004994283869580245421 2113126872856451092592033)
    ·
      refine ⟨1584845154642338319444025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2113126872856451092592033 1584845154642338319444025)
      ·
        refine ⟨1188633865981753739583019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584845154642338319444025 1188633865981753739583019)
        ·
          refine ⟨1782950798972630609374529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188633865981753739583019 1782950798972630609374529)
          ·
            refine ⟨1337213099229472957030897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782950798972630609374529 1337213099229472957030897)
            ·
              refine ⟨1002909824422104717773173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337213099229472957030897 1002909824422104717773173)
              ·
                refine ⟨94022796039572317291235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1002909824422104717773173 94022796039572317291235)
                ·
                  rfl

theorem cell19_308996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_308996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_308996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_308996 prefixEnd_308996 := by exact prefixLift 308996
  have htrace : WordTrace (prefixWord ++ tailWord_308996) baseStart_308996 baseEnd_308996 := by
    simpa [prefixWord, tailWord_308996, baseEnd_308996] using wordTrace_append hprefix tailTrace_308996
  have hstable : (prefixWord ++ tailWord_308996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308996).length < 2 ^ (prefixWord ++ tailWord_308996).sum := by decide
  have hdescent : baseEnd_308996 < baseStart_308996 := by decide
  rcases family_descends (prefixWord ++ tailWord_308996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309032 : List Nat := [2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_309032 : Nat := 118140960795 + 309032 * 2 ^ 59
def prefixEnd_309032 : Nat := 4983230072969 + 3 ^ 40 * 309032 * 2
def baseEnd_309032 : Nat := 94033750293534900491137

theorem tailTrace_309032 : CollatzResearch.WordTrace tailWord_309032 prefixEnd_309032 94033750293534900491137 := by
  unfold tailWord_309032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635661508218658654400675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7514215344291544872534233 5635661508218658654400675)
  ·
    refine ⟨8453492262327987981601013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635661508218658654400675 8453492262327987981601013)
    ·
      refine ⟨792514899593248873275095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8453492262327987981601013 792514899593248873275095)
      ·
        refine ⟨1188772349389873309912643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792514899593248873275095 1188772349389873309912643)
        ·
          refine ⟨1783158524084809964868965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188772349389873309912643 1783158524084809964868965)
          ·
            refine ⟨334342223265901868412931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1783158524084809964868965 334342223265901868412931)
            ·
              refine ⟨501513334898852802619397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334342223265901868412931 501513334898852802619397)
              ·
                refine ⟨94033750293534900491137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501513334898852802619397 94033750293534900491137)
                ·
                  rfl

theorem cell19_309032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_309032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309032 prefixEnd_309032 := by exact prefixLift 309032
  have htrace : WordTrace (prefixWord ++ tailWord_309032) baseStart_309032 baseEnd_309032 := by
    simpa [prefixWord, tailWord_309032, baseEnd_309032] using wordTrace_append hprefix tailTrace_309032
  have hstable : (prefixWord ++ tailWord_309032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309032).length < 2 ^ (prefixWord ++ tailWord_309032).sum := by decide
  have hdescent : baseEnd_309032 < baseStart_309032 := by decide
  rcases family_descends (prefixWord ++ tailWord_309032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309049 : List Nat := [1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_309049 : Nat := 118140960795 + 309049 * 2 ^ 59
def prefixEnd_309049 : Nat := 4983230072969 + 3 ^ 40 * 309049 * 2
def baseEnd_309049 : Nat := 94038923135683898113313

theorem tailTrace_309049 : CollatzResearch.WordTrace tailWord_309049 prefixEnd_309049 94038923135683898113313 := by
  unfold tailWord_309049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11271943057375729212170201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7514628704917152808113467 11271943057375729212170201)
  ·
    refine ⟨8453957293031796909127651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11271943057375729212170201 8453957293031796909127651)
    ·
      refine ⟨12680935939547695363691477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8453957293031796909127651 12680935939547695363691477)
      ·
        refine ⟨297209436083149110086519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12680935939547695363691477 297209436083149110086519)
        ·
          refine ⟨445814154124723665129779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297209436083149110086519 445814154124723665129779)
          ·
            refine ⟨668721231187085497694669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445814154124723665129779 668721231187085497694669)
            ·
              refine ⟨250770461695157061635501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668721231187085497694669 250770461695157061635501)
              ·
                refine ⟨94038923135683898113313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250770461695157061635501 94038923135683898113313)
                ·
                  rfl

theorem cell19_309049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_309049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309049 prefixEnd_309049 := by exact prefixLift 309049
  have htrace : WordTrace (prefixWord ++ tailWord_309049) baseStart_309049 baseEnd_309049 := by
    simpa [prefixWord, tailWord_309049, baseEnd_309049] using wordTrace_append hprefix tailTrace_309049
  have hstable : (prefixWord ++ tailWord_309049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309049).length < 2 ^ (prefixWord ++ tailWord_309049).sum := by decide
  have hdescent : baseEnd_309049 < baseStart_309049 := by decide
  rcases family_descends (prefixWord ++ tailWord_309049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309093 : List Nat := [1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_309093 : Nat := 118140960795 + 309093 * 2 ^ 59
def prefixEnd_309093 : Nat := 4983230072969 + 3 ^ 40 * 309093 * 2
def baseEnd_309093 : Nat := 94052311668304833135415

theorem tailTrace_309093 : CollatzResearch.WordTrace tailWord_309093 prefixEnd_309093 94052311668304833135415 := by
  unfold tailWord_309093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11273547869216324726771933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7515698579477549817847955 11273547869216324726771933)
  ·
    refine ⟨4227580450956121772539475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11273547869216324726771933 4227580450956121772539475)
    ·
      refine ⟨6341370676434182658809213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4227580450956121772539475 6341370676434182658809213)
      ·
        refine ⟨2378014003662818497053455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6341370676434182658809213 2378014003662818497053455)
        ·
          refine ⟨3567021005494227745580183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378014003662818497053455 3567021005494227745580183)
          ·
            refine ⟨5350531508241341618370275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567021005494227745580183 5350531508241341618370275)
            ·
              refine ⟨8025797262362012427555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350531508241341618370275 8025797262362012427555413)
              ·
                refine ⟨94052311668304833135415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8025797262362012427555413 94052311668304833135415)
                ·
                  rfl

theorem cell19_309093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_309093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309093 prefixEnd_309093 := by exact prefixLift 309093
  have htrace : WordTrace (prefixWord ++ tailWord_309093) baseStart_309093 baseEnd_309093 := by
    simpa [prefixWord, tailWord_309093, baseEnd_309093] using wordTrace_append hprefix tailTrace_309093
  have hstable : (prefixWord ++ tailWord_309093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309093).length < 2 ^ (prefixWord ++ tailWord_309093).sum := by decide
  have hdescent : baseEnd_309093 < baseStart_309093 := by decide
  rcases family_descends (prefixWord ++ tailWord_309093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309127 : List Nat := [1, 1, 4, 2, 5, 1, 5]
def baseStart_309127 : Nat := 118140960795 + 309127 * 2 ^ 59
def prefixEnd_309127 : Nat := 4983230072969 + 3 ^ 40 * 309127 * 2
def baseEnd_309127 : Nat := 31354219117534276126589

theorem tailTrace_309127 : CollatzResearch.WordTrace tailWord_309127 prefixEnd_309127 31354219117534276126589 := by
  unfold tailWord_309127
  simp only [CollatzResearch.WordTrace]
  refine ⟨11274787951093148533509635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7516525300728765689006423 11274787951093148533509635)
  ·
    refine ⟨16912181926639722800264453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11274787951093148533509635 16912181926639722800264453)
    ·
      refine ⟨3171034111244948025049585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16912181926639722800264453 3171034111244948025049585)
      ·
        refine ⟨2378275583433711018787189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3171034111244948025049585 2378275583433711018787189)
        ·
          refine ⟨222963335946910408011299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2378275583433711018787189 222963335946910408011299)
          ·
            refine ⟨334445003920365612016949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222963335946910408011299 334445003920365612016949)
            ·
              refine ⟨31354219117534276126589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 334445003920365612016949 31354219117534276126589)
              ·
                rfl

theorem cell19_309127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_309127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309127 prefixEnd_309127 := by exact prefixLift 309127
  have htrace : WordTrace (prefixWord ++ tailWord_309127) baseStart_309127 baseEnd_309127 := by
    simpa [prefixWord, tailWord_309127, baseEnd_309127] using wordTrace_append hprefix tailTrace_309127
  have hstable : (prefixWord ++ tailWord_309127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309127).length < 2 ^ (prefixWord ++ tailWord_309127).sum := by decide
  have hdescent : baseEnd_309127 < baseStart_309127 := by decide
  rcases family_descends (prefixWord ++ tailWord_309127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309142 : List Nat := [5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_309142 : Nat := 118140960795 + 309142 * 2 ^ 59
def prefixEnd_309142 : Nat := 4983230072969 + 3 ^ 40 * 309142 * 2
def baseEnd_309142 : Nat := 94067221625087238046393

theorem tailTrace_309142 : CollatzResearch.WordTrace tailWord_309142 prefixEnd_309142 94067221625087238046393 := by
  unfold tailWord_309142
  simp only [CollatzResearch.WordTrace]
  refine ⟨704708440377425380956605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7516890030692537396870453 704708440377425380956605)
  ·
    refine ⟨264265665141534517858727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 704708440377425380956605 264265665141534517858727)
    ·
      refine ⟨396398497712301776788091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264265665141534517858727 396398497712301776788091)
      ·
        refine ⟨594597746568452665182137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396398497712301776788091 594597746568452665182137)
        ·
          refine ⟨445948309926339498886603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594597746568452665182137 445948309926339498886603)
          ·
            refine ⟨668922464889509248329905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445948309926339498886603 668922464889509248329905)
            ·
              refine ⟨501691848667131936247429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668922464889509248329905 501691848667131936247429)
              ·
                refine ⟨94067221625087238046393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501691848667131936247429 94067221625087238046393)
                ·
                  rfl

theorem cell19_309142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_309142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309142 prefixEnd_309142 := by exact prefixLift 309142
  have htrace : WordTrace (prefixWord ++ tailWord_309142) baseStart_309142 baseEnd_309142 := by
    simpa [prefixWord, tailWord_309142, baseEnd_309142] using wordTrace_append hprefix tailTrace_309142
  have hstable : (prefixWord ++ tailWord_309142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309142).length < 2 ^ (prefixWord ++ tailWord_309142).sum := by decide
  have hdescent : baseEnd_309142 < baseStart_309142 := by decide
  rcases family_descends (prefixWord ++ tailWord_309142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309148 : List Nat := [2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_309148 : Nat := 118140960795 + 309148 * 2 ^ 59
def prefixEnd_309148 : Nat := 4983230072969 + 3 ^ 40 * 309148 * 2
def baseEnd_309148 : Nat := 94069047334081001913043

theorem tailTrace_309148 : CollatzResearch.WordTrace tailWord_309148 prefixEnd_309148 94069047334081001913043 := by
  unfold tailWord_309148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637776942008534560012049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7517035922678046080016065 5637776942008534560012049)
  ·
    refine ⟨4228332706506400920009037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5637776942008534560012049 4228332706506400920009037)
    ·
      refine ⟨1585624764939900345003389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4228332706506400920009037 1585624764939900345003389)
      ·
        refine ⟨594609286852462629376271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1585624764939900345003389 594609286852462629376271)
        ·
          refine ⟨891913930278693944064407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594609286852462629376271 891913930278693944064407)
          ·
            refine ⟨1337870895418040916096611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891913930278693944064407 1337870895418040916096611)
            ·
              refine ⟨2006806343127061374144917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337870895418040916096611 2006806343127061374144917)
              ·
                refine ⟨94069047334081001913043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2006806343127061374144917 94069047334081001913043)
                ·
                  rfl

theorem cell19_309148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_309148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309148 prefixEnd_309148 := by exact prefixLift 309148
  have htrace : WordTrace (prefixWord ++ tailWord_309148) baseStart_309148 baseEnd_309148 := by
    simpa [prefixWord, tailWord_309148, baseEnd_309148] using wordTrace_append hprefix tailTrace_309148
  have hstable : (prefixWord ++ tailWord_309148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309148).length < 2 ^ (prefixWord ++ tailWord_309148).sum := by decide
  have hdescent : baseEnd_309148 < baseStart_309148 := by decide
  rcases family_descends (prefixWord ++ tailWord_309148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309188 : List Nat := [2, 3, 3, 11]
def baseStart_309188 : Nat := 118140960795 + 309188 * 2 ^ 59
def prefixEnd_309188 : Nat := 4983230072969 + 3 ^ 40 * 309188 * 2
def baseEnd_309188 : Nat := 1161496527498429148445

theorem tailTrace_309188 : CollatzResearch.WordTrace tailWord_309188 prefixEnd_309188 1161496527498429148445 := by
  unfold tailWord_309188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638506401936077975740109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7518008535914770634320145 5638506401936077975740109)
  ·
    refine ⟨2114439900726029240902541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5638506401936077975740109 2114439900726029240902541)
    ·
      refine ⟨792914962772260965338453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2114439900726029240902541 792914962772260965338453)
      ·
        refine ⟨1161496527498429148445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 792914962772260965338453 1161496527498429148445)
        ·
          rfl

theorem cell19_309188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 11].length) (baseStart_309188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309188 prefixEnd_309188 := by exact prefixLift 309188
  have htrace : WordTrace (prefixWord ++ tailWord_309188) baseStart_309188 baseEnd_309188 := by
    simpa [prefixWord, tailWord_309188, baseEnd_309188] using wordTrace_append hprefix tailTrace_309188
  have hstable : (prefixWord ++ tailWord_309188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309188).length < 2 ^ (prefixWord ++ tailWord_309188).sum := by decide
  have hdescent : baseEnd_309188 < baseStart_309188 := by decide
  rcases family_descends (prefixWord ++ tailWord_309188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309205 : List Nat := [1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_309205 : Nat := 118140960795 + 309205 * 2 ^ 59
def prefixEnd_309205 : Nat := 4983230072969 + 3 ^ 40 * 309205 * 2
def baseEnd_309205 : Nat := 94086391569521758646221

theorem tailTrace_309205 : CollatzResearch.WordTrace tailWord_309205 prefixEnd_309205 94086391569521758646221 := by
  unfold tailWord_309205
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277632844810567854849069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7518421896540378569899379 11277632844810567854849069)
  ·
    refine ⟨4229112316803962945568401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11277632844810567854849069 4229112316803962945568401)
    ·
      refine ⟨3171834237602972209176301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4229112316803962945568401 3171834237602972209176301)
      ·
        refine ⟨1189437839101114578441113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3171834237602972209176301 1189437839101114578441113)
        ·
          refine ⟨892078379325835933830835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189437839101114578441113 892078379325835933830835)
          ·
            refine ⟨1338117568988753900746253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892078379325835933830835 1338117568988753900746253)
            ·
              refine ⟨501794088370782712779845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1338117568988753900746253 501794088370782712779845)
              ·
                refine ⟨94086391569521758646221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501794088370782712779845 94086391569521758646221)
                ·
                  rfl

theorem cell19_309205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_309205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309205 prefixEnd_309205 := by exact prefixLift 309205
  have htrace : WordTrace (prefixWord ++ tailWord_309205) baseStart_309205 baseEnd_309205 := by
    simpa [prefixWord, tailWord_309205, baseEnd_309205] using wordTrace_append hprefix tailTrace_309205
  have hstable : (prefixWord ++ tailWord_309205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309205).length < 2 ^ (prefixWord ++ tailWord_309205).sum := by decide
  have hdescent : baseEnd_309205 < baseStart_309205 := by decide
  rcases family_descends (prefixWord ++ tailWord_309205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309281 : List Nat := [1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_309281 : Nat := 118140960795 + 309281 * 2 ^ 59
def prefixEnd_309281 : Nat := 4983230072969 + 3 ^ 40 * 309281 * 2
def baseEnd_309281 : Nat := 94109517216776100957125

theorem tailTrace_309281 : CollatzResearch.WordTrace tailWord_309281 prefixEnd_309281 94109517216776100957125 := by
  unfold tailWord_309281
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280404792535232834615697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7520269861690155223077131 11280404792535232834615697)
  ·
    refine ⟨8460303594401424625961773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11280404792535232834615697 8460303594401424625961773)
    ·
      refine ⟨3172613847900534234735665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8460303594401424625961773 3172613847900534234735665)
      ·
        refine ⟨2379460385925400676051749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3172613847900534234735665 2379460385925400676051749)
        ·
          refine ⟨446148822361012626759703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2379460385925400676051749 446148822361012626759703)
          ·
            refine ⟨669223233541518940139555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446148822361012626759703 669223233541518940139555)
            ·
              refine ⟨1003834850312278410209333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669223233541518940139555 1003834850312278410209333)
              ·
                refine ⟨94109517216776100957125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1003834850312278410209333 94109517216776100957125)
                ·
                  rfl

theorem cell19_309281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_309281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309281 prefixEnd_309281 := by exact prefixLift 309281
  have htrace : WordTrace (prefixWord ++ tailWord_309281) baseStart_309281 baseEnd_309281 := by
    simpa [prefixWord, tailWord_309281, baseEnd_309281] using wordTrace_append hprefix tailTrace_309281
  have hstable : (prefixWord ++ tailWord_309281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309281).length < 2 ^ (prefixWord ++ tailWord_309281).sum := by decide
  have hdescent : baseEnd_309281 < baseStart_309281 := by decide
  rcases family_descends (prefixWord ++ tailWord_309281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309283 : List Nat := [1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_309283 : Nat := 118140960795 + 309283 * 2 ^ 59
def prefixEnd_309283 : Nat := 4983230072969 + 3 ^ 40 * 309283 * 2
def baseEnd_309283 : Nat := 94110125786440688912675

theorem tailTrace_309283 : CollatzResearch.WordTrace tailWord_309283 prefixEnd_309283 94110125786440688912675 := by
  unfold tailWord_309283
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280477738527987176188503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7520318492351991450792335 11280477738527987176188503)
  ·
    refine ⟨16920716607791980764282755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11280477738527987176188503 16920716607791980764282755)
    ·
      refine ⟨25381074911687971146424133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16920716607791980764282755 25381074911687971146424133)
      ·
        refine ⟨4758951545941494589954525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25381074911687971146424133 4758951545941494589954525)
        ·
          refine ⟨1784606829728060471232947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4758951545941494589954525 1784606829728060471232947)
          ·
            refine ⟨2676910244592090706849421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784606829728060471232947 2676910244592090706849421)
            ·
              refine ⟨1003841341722034015068533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2676910244592090706849421 1003841341722034015068533)
              ·
                refine ⟨94110125786440688912675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1003841341722034015068533 94110125786440688912675)
                ·
                  rfl

theorem cell19_309283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_309283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309283 prefixEnd_309283 := by exact prefixLift 309283
  have htrace : WordTrace (prefixWord ++ tailWord_309283) baseStart_309283 baseEnd_309283 := by
    simpa [prefixWord, tailWord_309283, baseEnd_309283] using wordTrace_append hprefix tailTrace_309283
  have hstable : (prefixWord ++ tailWord_309283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309283).length < 2 ^ (prefixWord ++ tailWord_309283).sum := by decide
  have hdescent : baseEnd_309283 < baseStart_309283 := by decide
  rcases family_descends (prefixWord ++ tailWord_309283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309321 : List Nat := [1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_309321 : Nat := 118140960795 + 309321 * 2 ^ 59
def prefixEnd_309321 : Nat := 4983230072969 + 3 ^ 40 * 309321 * 2
def baseEnd_309321 : Nat := 94121688610067860068127

theorem tailTrace_309321 : CollatzResearch.WordTrace tailWord_309321 prefixEnd_309321 94121688610067860068127 := by
  unfold tailWord_309321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281863712390319666071817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7521242474926879777381211 11281863712390319666071817)
  ·
    refine ⟨8461397784292739749553863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11281863712390319666071817 8461397784292739749553863)
    ·
      refine ⟨12692096676439109624330795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461397784292739749553863 12692096676439109624330795)
      ·
        refine ⟨19038145014658664436496193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12692096676439109624330795 19038145014658664436496193)
        ·
          refine ⟨14278608760993998327372145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19038145014658664436496193 14278608760993998327372145)
          ·
            refine ⟨10708956570745498745529109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14278608760993998327372145 10708956570745498745529109)
            ·
              refine ⟨501982339253695253696677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10708956570745498745529109 501982339253695253696677)
              ·
                refine ⟨94121688610067860068127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501982339253695253696677 94121688610067860068127)
                ·
                  rfl

theorem cell19_309321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_309321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309321 prefixEnd_309321 := by exact prefixLift 309321
  have htrace : WordTrace (prefixWord ++ tailWord_309321) baseStart_309321 baseEnd_309321 := by
    simpa [prefixWord, tailWord_309321, baseEnd_309321] using wordTrace_append hprefix tailTrace_309321
  have hstable : (prefixWord ++ tailWord_309321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309321).length < 2 ^ (prefixWord ++ tailWord_309321).sum := by decide
  have hdescent : baseEnd_309321 < baseStart_309321 := by decide
  rcases family_descends (prefixWord ++ tailWord_309321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309490 : List Nat := [3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_309490 : Nat := 118140960795 + 309490 * 2 ^ 59
def prefixEnd_309490 : Nat := 4983230072969 + 3 ^ 40 * 309490 * 2
def baseEnd_309490 : Nat := 94173112746725542312111

theorem tailTrace_309490 : CollatzResearch.WordTrace tailWord_309490 prefixEnd_309490 94173112746725542312111 := by
  unfold tailWord_309490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822006912194515382243481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7525351765852041019315949 2822006912194515382243481)
  ·
    refine ⟨2116505184145886536682611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2822006912194515382243481 2116505184145886536682611)
    ·
      refine ⟨3174757776218829805023917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2116505184145886536682611 3174757776218829805023917)
      ·
        refine ⟨1190534166082061176883969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3174757776218829805023917 1190534166082061176883969)
        ·
          refine ⟨892900624561545882662977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190534166082061176883969 892900624561545882662977)
          ·
            refine ⟨669675468421159411997233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892900624561545882662977 669675468421159411997233)
            ·
              refine ⟨502256601315869558997925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669675468421159411997233 502256601315869558997925)
              ·
                refine ⟨94173112746725542312111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502256601315869558997925 94173112746725542312111)
                ·
                  rfl

theorem cell19_309490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_309490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309490 prefixEnd_309490 := by exact prefixLift 309490
  have htrace : WordTrace (prefixWord ++ tailWord_309490) baseStart_309490 baseEnd_309490 := by
    simpa [prefixWord, tailWord_309490, baseEnd_309490] using wordTrace_append hprefix tailTrace_309490
  have hstable : (prefixWord ++ tailWord_309490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309490).length < 2 ^ (prefixWord ++ tailWord_309490).sum := by decide
  have hdescent : baseEnd_309490 < baseStart_309490 := by decide
  rcases family_descends (prefixWord ++ tailWord_309490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309530 : List Nat := [3, 1, 1, 3, 4, 7]
def baseStart_309530 : Nat := 118140960795 + 309530 * 2 ^ 59
def prefixEnd_309530 : Nat := 4983230072969 + 3 ^ 40 * 309530 * 2
def baseEnd_309530 : Nat := 10465031571113033491457

theorem tailTrace_309530 : CollatzResearch.WordTrace tailWord_309530 prefixEnd_309530 10465031571113033491457 := by
  unfold tailWord_309530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822371642158287090107511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7526324379088765573620029 2822371642158287090107511)
  ·
    refine ⟨4233557463237430635161267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2822371642158287090107511 4233557463237430635161267)
    ·
      refine ⟨6350336194856145952741901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4233557463237430635161267 6350336194856145952741901)
      ·
        refine ⟨2381376073071054732278213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6350336194856145952741901 2381376073071054732278213)
        ·
          refine ⟨446508013700822762302165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2381376073071054732278213 446508013700822762302165)
          ·
            refine ⟨10465031571113033491457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 446508013700822762302165 10465031571113033491457)
            ·
              rfl

theorem cell19_309530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_309530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309530 prefixEnd_309530 := by exact prefixLift 309530
  have htrace : WordTrace (prefixWord ++ tailWord_309530) baseStart_309530 baseEnd_309530 := by
    simpa [prefixWord, tailWord_309530, baseEnd_309530] using wordTrace_append hprefix tailTrace_309530
  have hstable : (prefixWord ++ tailWord_309530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309530).length < 2 ^ (prefixWord ++ tailWord_309530).sum := by decide
  have hdescent : baseEnd_309530 < baseStart_309530 := by decide
  rcases family_descends (prefixWord ++ tailWord_309530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309621 : List Nat := [1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_309621 : Nat := 118140960795 + 309621 * 2 ^ 59
def prefixEnd_309621 : Nat := 4983230072969 + 3 ^ 40 * 309621 * 2
def baseEnd_309621 : Nat := 94212974059756053400643

theorem tailTrace_309621 : CollatzResearch.WordTrace tailWord_309621 prefixEnd_309621 94212974059756053400643 := by
  unfold tailWord_309621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11292805611303470901992717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7528537074202313934661811 11292805611303470901992717)
  ·
    refine ⟨4234802104238801588247269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11292805611303470901992717 4234802104238801588247269)
    ·
      refine ⟨794025394544775297796363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4234802104238801588247269 794025394544775297796363)
      ·
        refine ⟨1191038091817162946694545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794025394544775297796363 1191038091817162946694545)
        ·
          refine ⟨893278568862872210020909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191038091817162946694545 893278568862872210020909)
          ·
            refine ⟨334979463323577078757841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 893278568862872210020909 334979463323577078757841)
            ·
              refine ⟨251234597492682809068381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334979463323577078757841 251234597492682809068381)
              ·
                refine ⟨94212974059756053400643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251234597492682809068381 94212974059756053400643)
                ·
                  rfl

theorem cell19_309621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_309621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309621 prefixEnd_309621 := by exact prefixLift 309621
  have htrace : WordTrace (prefixWord ++ tailWord_309621) baseStart_309621 baseEnd_309621 := by
    simpa [prefixWord, tailWord_309621, baseEnd_309621] using wordTrace_append hprefix tailTrace_309621
  have hstable : (prefixWord ++ tailWord_309621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309621).length < 2 ^ (prefixWord ++ tailWord_309621).sum := by decide
  have hdescent : baseEnd_309621 < baseStart_309621 := by decide
  rcases family_descends (prefixWord ++ tailWord_309621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309644 : List Nat := [2, 2, 1, 2, 1, 6, 5]
def baseStart_309644 : Nat := 118140960795 + 309644 * 2 ^ 59
def prefixEnd_309644 : Nat := 4983230072969 + 3 ^ 40 * 309644 * 2
def baseEnd_309644 : Nat := 31406657536966271629823

theorem tailTrace_309644 : CollatzResearch.WordTrace tailWord_309644 prefixEnd_309644 31406657536966271629823 := by
  unfold tailWord_309644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646822245110072915039993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7529096326813430553386657 5646822245110072915039993)
  ·
    refine ⟨4235116683832554686279995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5646822245110072915039993 4235116683832554686279995)
    ·
      refine ⟨6352675025748832029419993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235116683832554686279995 6352675025748832029419993)
      ·
        refine ⟨4764506269311624022064995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6352675025748832029419993 4764506269311624022064995)
        ·
          refine ⟨7146759403967436033097493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764506269311624022064995 7146759403967436033097493)
          ·
            refine ⟨335004347060973564051445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7146759403967436033097493 335004347060973564051445)
            ·
              refine ⟨31406657536966271629823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 335004347060973564051445 31406657536966271629823)
              ·
                rfl

theorem cell19_309644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_309644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309644 prefixEnd_309644 := by exact prefixLift 309644
  have htrace : WordTrace (prefixWord ++ tailWord_309644) baseStart_309644 baseEnd_309644 := by
    simpa [prefixWord, tailWord_309644, baseEnd_309644] using wordTrace_append hprefix tailTrace_309644
  have hstable : (prefixWord ++ tailWord_309644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309644).length < 2 ^ (prefixWord ++ tailWord_309644).sum := by decide
  have hdescent : baseEnd_309644 < baseStart_309644 := by decide
  rcases family_descends (prefixWord ++ tailWord_309644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309661 : List Nat := [1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_309661 : Nat := 118140960795 + 309661 * 2 ^ 59
def prefixEnd_309661 : Nat := 4983230072969 + 3 ^ 40 * 309661 * 2
def baseEnd_309661 : Nat := 94225145453047812511645

theorem tailTrace_309661 : CollatzResearch.WordTrace tailWord_309661 prefixEnd_309661 94225145453047812511645 := by
  unfold tailWord_309661
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294264531158557733448837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7529509687439038488965891 11294264531158557733448837)
  ·
    refine ⟨2117674599592229575021657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11294264531158557733448837 2117674599592229575021657)
    ·
      refine ⟨1588255949694172181266243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2117674599592229575021657 1588255949694172181266243)
      ·
        refine ⟨2382383924541258271899365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588255949694172181266243 2382383924541258271899365)
        ·
          refine ⟨446696985851485925981131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2382383924541258271899365 446696985851485925981131)
          ·
            refine ⟨670045478777228888971697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446696985851485925981131 670045478777228888971697)
            ·
              refine ⟨502534109082921666728773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670045478777228888971697 502534109082921666728773)
              ·
                refine ⟨94225145453047812511645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502534109082921666728773 94225145453047812511645)
                ·
                  rfl

theorem cell19_309661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_309661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309661 prefixEnd_309661 := by exact prefixLift 309661
  have htrace : WordTrace (prefixWord ++ tailWord_309661) baseStart_309661 baseEnd_309661 := by
    simpa [prefixWord, tailWord_309661, baseEnd_309661] using wordTrace_append hprefix tailTrace_309661
  have hstable : (prefixWord ++ tailWord_309661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309661).length < 2 ^ (prefixWord ++ tailWord_309661).sum := by decide
  have hdescent : baseEnd_309661 < baseStart_309661 := by decide
  rcases family_descends (prefixWord ++ tailWord_309661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309663 : List Nat := [1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_309663 : Nat := 118140960795 + 309663 * 2 ^ 59
def prefixEnd_309663 : Nat := 4983230072969 + 3 ^ 40 * 309663 * 2
def baseEnd_309663 : Nat := 94225754022712400467195

theorem tailTrace_309663 : CollatzResearch.WordTrace tailWord_309663 prefixEnd_309663 94225754022712400467195 := by
  unfold tailWord_309663
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294337477151312075021643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7529558318100874716681095 11294337477151312075021643)
  ·
    refine ⟨16941506215726968112532465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294337477151312075021643 16941506215726968112532465)
    ·
      refine ⟨12706129661795226084399349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16941506215726968112532465 12706129661795226084399349)
      ·
        refine ⟨1191199655793302445412439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12706129661795226084399349 1191199655793302445412439)
        ·
          refine ⟨1786799483689953668118659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191199655793302445412439 1786799483689953668118659)
          ·
            refine ⟨2680199225534930502177989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786799483689953668118659 2680199225534930502177989)
            ·
              refine ⟨502537354787799469158373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2680199225534930502177989 502537354787799469158373)
              ·
                refine ⟨94225754022712400467195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502537354787799469158373 94225754022712400467195)
                ·
                  rfl

theorem cell19_309663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_309663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309663 prefixEnd_309663 := by exact prefixLift 309663
  have htrace : WordTrace (prefixWord ++ tailWord_309663) baseStart_309663 baseEnd_309663 := by
    simpa [prefixWord, tailWord_309663, baseEnd_309663] using wordTrace_append hprefix tailTrace_309663
  have hstable : (prefixWord ++ tailWord_309663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309663).length < 2 ^ (prefixWord ++ tailWord_309663).sum := by decide
  have hdescent : baseEnd_309663 < baseStart_309663 := by decide
  rcases family_descends (prefixWord ++ tailWord_309663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309697 : List Nat := [1, 2, 7, 1, 1, 7]
def baseStart_309697 : Nat := 118140960795 + 309697 * 2 ^ 59
def prefixEnd_309697 : Nat := 4983230072969 + 3 ^ 40 * 309697 * 2
def baseEnd_309697 : Nat := 10470677745223377301283

theorem tailTrace_309697 : CollatzResearch.WordTrace tailWord_309697 prefixEnd_309697 10470677745223377301283 := by
  unfold tailWord_309697
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295577559028135881759345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7530385039352090587839563 11295577559028135881759345)
  ·
    refine ⟨8471683169271101911319509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11295577559028135881759345 8471683169271101911319509)
    ·
      refine ⟨198555074279791451046551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8471683169271101911319509 198555074279791451046551)
      ·
        refine ⟨297832611419687176569827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198555074279791451046551 297832611419687176569827)
        ·
          refine ⟨446748917129530764854741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297832611419687176569827 446748917129530764854741)
          ·
            refine ⟨10470677745223377301283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 446748917129530764854741 10470677745223377301283)
            ·
              rfl

theorem cell19_309697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_309697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309697 prefixEnd_309697 := by exact prefixLift 309697
  have htrace : WordTrace (prefixWord ++ tailWord_309697) baseStart_309697 baseEnd_309697 := by
    simpa [prefixWord, tailWord_309697, baseEnd_309697] using wordTrace_append hprefix tailTrace_309697
  have hstable : (prefixWord ++ tailWord_309697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309697).length < 2 ^ (prefixWord ++ tailWord_309697).sum := by decide
  have hdescent : baseEnd_309697 < baseStart_309697 := by decide
  rcases family_descends (prefixWord ++ tailWord_309697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309703 : List Nat := [1, 1, 4, 1, 1, 11]
def baseStart_309703 : Nat := 118140960795 + 309703 * 2 ^ 59
def prefixEnd_309703 : Nat := 4983230072969 + 3 ^ 40 * 309703 * 2
def baseEnd_309703 : Nat := 10470880601778239953133

theorem tailTrace_309703 : CollatzResearch.WordTrace tailWord_309703 prefixEnd_309703 10470880601778239953133 := by
  unfold tailWord_309703
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295796397006398906477763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7530530931337599270985175 11295796397006398906477763)
  ·
    refine ⟨16943694595509598359716645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11295796397006398906477763 16943694595509598359716645)
    ·
      refine ⟨3176942736658049692446871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16943694595509598359716645 3176942736658049692446871)
      ·
        refine ⟨4765414104987074538670307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176942736658049692446871 4765414104987074538670307)
        ·
          refine ⟨7148121157480611808005461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4765414104987074538670307 7148121157480611808005461)
          ·
            refine ⟨10470880601778239953133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7148121157480611808005461 10470880601778239953133)
            ·
              rfl

theorem cell19_309703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_309703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309703 prefixEnd_309703 := by exact prefixLift 309703
  have htrace : WordTrace (prefixWord ++ tailWord_309703) baseStart_309703 baseEnd_309703 := by
    simpa [prefixWord, tailWord_309703, baseEnd_309703] using wordTrace_append hprefix tailTrace_309703
  have hstable : (prefixWord ++ tailWord_309703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309703).length < 2 ^ (prefixWord ++ tailWord_309703).sum := by decide
  have hdescent : baseEnd_309703 < baseStart_309703 := by decide
  rcases family_descends (prefixWord ++ tailWord_309703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309714 : List Nat := [3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_309714 : Nat := 118140960795 + 309714 * 2 ^ 59
def prefixEnd_309714 : Nat := 4983230072969 + 3 ^ 40 * 309714 * 2
def baseEnd_309714 : Nat := 94241272549159393333723

theorem tailTrace_309714 : CollatzResearch.WordTrace tailWord_309714 prefixEnd_309714 94241272549159393333723 := by
  unfold tailWord_309714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824049399991636946282049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7530798399977698523418797 2824049399991636946282049)
  ·
    refine ⟨2118037049993727709711537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2824049399991636946282049 2118037049993727709711537)
    ·
      refine ⟨1588527787495295782283653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2118037049993727709711537 1588527787495295782283653)
      ·
        refine ⟨297848960155367959178185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1588527787495295782283653 297848960155367959178185)
        ·
          refine ⟨223386720116525969383639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297848960155367959178185 223386720116525969383639)
          ·
            refine ⟨335080080174788954075459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223386720116525969383639 335080080174788954075459)
            ·
              refine ⟨502620120262183431113189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335080080174788954075459 502620120262183431113189)
              ·
                refine ⟨94241272549159393333723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502620120262183431113189 94241272549159393333723)
                ·
                  rfl

theorem cell19_309714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_309714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309714 prefixEnd_309714 := by exact prefixLift 309714
  have htrace : WordTrace (prefixWord ++ tailWord_309714) baseStart_309714 baseEnd_309714 := by
    simpa [prefixWord, tailWord_309714, baseEnd_309714] using wordTrace_append hprefix tailTrace_309714
  have hstable : (prefixWord ++ tailWord_309714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309714).length < 2 ^ (prefixWord ++ tailWord_309714).sum := by decide
  have hdescent : baseEnd_309714 < baseStart_309714 := by decide
  rcases family_descends (prefixWord ++ tailWord_309714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309739 : List Nat := [1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_309739 : Nat := 118140960795 + 309739 * 2 ^ 59
def prefixEnd_309739 : Nat := 4983230072969 + 3 ^ 40 * 309739 * 2
def baseEnd_309739 : Nat := 94248879669966742778099

theorem tailTrace_309739 : CollatzResearch.WordTrace tailWord_309739 prefixEnd_309739 94248879669966742778099 := by
  unfold tailWord_309739
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297109424875977054788271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7531406283250651369858847 11297109424875977054788271)
  ·
    refine ⟨16945664137313965582182407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297109424875977054788271 16945664137313965582182407)
    ·
      refine ⟨25418496205970948373273611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16945664137313965582182407 25418496205970948373273611)
      ·
        refine ⟨38127744308956422559910417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25418496205970948373273611 38127744308956422559910417)
        ·
          refine ⟨28595808231717316919932813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38127744308956422559910417 28595808231717316919932813)
          ·
            refine ⟨10723428086893993844974805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28595808231717316919932813 10723428086893993844974805)
            ·
              refine ⟨251330345786577980741597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10723428086893993844974805 251330345786577980741597)
              ·
                refine ⟨94248879669966742778099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251330345786577980741597 94248879669966742778099)
                ·
                  rfl

theorem cell19_309739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_309739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309739 prefixEnd_309739 := by exact prefixLift 309739
  have htrace : WordTrace (prefixWord ++ tailWord_309739) baseStart_309739 baseEnd_309739 := by
    simpa [prefixWord, tailWord_309739, baseEnd_309739] using wordTrace_append hprefix tailTrace_309739
  have hstable : (prefixWord ++ tailWord_309739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309739).length < 2 ^ (prefixWord ++ tailWord_309739).sum := by decide
  have hdescent : baseEnd_309739 < baseStart_309739 := by decide
  rcases family_descends (prefixWord ++ tailWord_309739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309779 : List Nat := [1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_309779 : Nat := 118140960795 + 309779 * 2 ^ 59
def prefixEnd_309779 : Nat := 4983230072969 + 3 ^ 40 * 309779 * 2
def baseEnd_309779 : Nat := 94261051063258501889101

theorem tailTrace_309779 : CollatzResearch.WordTrace tailWord_309779 prefixEnd_309779 94261051063258501889101 := by
  unfold tailWord_309779
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298568344731063886244391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7532378896487375924162927 11298568344731063886244391)
  ·
    refine ⟨16947852517096595829366587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11298568344731063886244391 16947852517096595829366587)
    ·
      refine ⟨25421778775644893744049881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16947852517096595829366587 25421778775644893744049881)
      ·
        refine ⟨19066334081733670308037411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25421778775644893744049881 19066334081733670308037411)
        ·
          refine ⟨28599501122600505462056117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19066334081733670308037411 28599501122600505462056117)
          ·
            refine ⟨2681203230243797387067761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28599501122600505462056117 2681203230243797387067761)
            ·
              refine ⟨2010902422682848040300821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681203230243797387067761 2010902422682848040300821)
              ·
                refine ⟨94261051063258501889101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2010902422682848040300821 94261051063258501889101)
                ·
                  rfl

theorem cell19_309779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_309779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309779 prefixEnd_309779 := by exact prefixLift 309779
  have htrace : WordTrace (prefixWord ++ tailWord_309779) baseStart_309779 baseEnd_309779 := by
    simpa [prefixWord, tailWord_309779, baseEnd_309779] using wordTrace_append hprefix tailTrace_309779
  have hstable : (prefixWord ++ tailWord_309779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309779).length < 2 ^ (prefixWord ++ tailWord_309779).sum := by decide
  have hdescent : baseEnd_309779 < baseStart_309779 := by decide
  rcases family_descends (prefixWord ++ tailWord_309779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309792 : List Nat := [2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_309792 : Nat := 118140960795 + 309792 * 2 ^ 59
def prefixEnd_309792 : Nat := 4983230072969 + 3 ^ 40 * 309792 * 2
def baseEnd_309792 : Nat := 94265006766078323600177

theorem tailTrace_309792 : CollatzResearch.WordTrace tailWord_309792 prefixEnd_309792 94265006766078323600177 := by
  unfold tailWord_309792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649521246841983553233815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7532694995789311404311753 5649521246841983553233815)
  ·
    refine ⟨8474281870262975329850723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5649521246841983553233815 8474281870262975329850723)
    ·
      refine ⟨12711422805394462994776085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8474281870262975329850723 12711422805394462994776085)
      ·
        refine ⟨595847944002865452880129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12711422805394462994776085 595847944002865452880129)
        ·
          refine ⟨446885958002149089660097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595847944002865452880129 446885958002149089660097)
          ·
            refine ⟨335164468501611817245073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446885958002149089660097 335164468501611817245073)
            ·
              refine ⟨251373351376208862933805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335164468501611817245073 251373351376208862933805)
              ·
                refine ⟨94265006766078323600177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251373351376208862933805 94265006766078323600177)
                ·
                  rfl

theorem cell19_309792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_309792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309792 prefixEnd_309792 := by exact prefixLift 309792
  have htrace : WordTrace (prefixWord ++ tailWord_309792) baseStart_309792 baseEnd_309792 := by
    simpa [prefixWord, tailWord_309792, baseEnd_309792] using wordTrace_append hprefix tailTrace_309792
  have hstable : (prefixWord ++ tailWord_309792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309792).length < 2 ^ (prefixWord ++ tailWord_309792).sum := by decide
  have hdescent : baseEnd_309792 < baseStart_309792 := by decide
  rcases family_descends (prefixWord ++ tailWord_309792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309828 : List Nat := [2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_309828 : Nat := 118140960795 + 309828 * 2 ^ 59
def prefixEnd_309828 : Nat := 4983230072969 + 3 ^ 40 * 309828 * 2
def baseEnd_309828 : Nat := 94275961020040906800079

theorem tailTrace_309828 : CollatzResearch.WordTrace tailWord_309828 prefixEnd_309828 94275961020040906800079 := by
  unfold tailWord_309828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650177760776772627389069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7533570347702363503185425 5650177760776772627389069)
  ·
    refine ⟨2118816660291289735270901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5650177760776772627389069 2118816660291289735270901)
    ·
      refine ⟨198639061902308412681647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2118816660291289735270901 198639061902308412681647)
      ·
        refine ⟨297958592853462619022471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198639061902308412681647 297958592853462619022471)
        ·
          refine ⟨446937889280193928533707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297958592853462619022471 446937889280193928533707)
          ·
            refine ⟨670406833920290892800561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446937889280193928533707 670406833920290892800561)
            ·
              refine ⟨502805125440218169600421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670406833920290892800561 502805125440218169600421)
              ·
                refine ⟨94275961020040906800079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502805125440218169600421 94275961020040906800079)
                ·
                  rfl

theorem cell19_309828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_309828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309828 prefixEnd_309828 := by exact prefixLift 309828
  have htrace : WordTrace (prefixWord ++ tailWord_309828) baseStart_309828 baseEnd_309828 := by
    simpa [prefixWord, tailWord_309828, baseEnd_309828] using wordTrace_append hprefix tailTrace_309828
  have hstable : (prefixWord ++ tailWord_309828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309828).length < 2 ^ (prefixWord ++ tailWord_309828).sum := by decide
  have hdescent : baseEnd_309828 < baseStart_309828 := by decide
  rcases family_descends (prefixWord ++ tailWord_309828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309830 : List Nat := [6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_309830 : Nat := 118140960795 + 309830 * 2 ^ 59
def prefixEnd_309830 : Nat := 4983230072969 + 3 ^ 40 * 309830 * 2
def baseEnd_309830 : Nat := 94276569589705494755629

theorem tailTrace_309830 : CollatzResearch.WordTrace tailWord_309830 prefixEnd_309830 94276569589705494755629 := by
  unfold tailWord_309830
  simp only [CollatzResearch.WordTrace]
  refine ⟨353138389610821862385967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7533618978364199730900629 353138389610821862385967)
  ·
    refine ⟨529707584416232793578951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353138389610821862385967 529707584416232793578951)
    ·
      refine ⟨794561376624349190368427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529707584416232793578951 794561376624349190368427)
      ·
        refine ⟨1191842064936523785552641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794561376624349190368427 1191842064936523785552641)
        ·
          refine ⟨893881548702392839164481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191842064936523785552641 893881548702392839164481)
          ·
            refine ⟨670411161526794629373361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893881548702392839164481 670411161526794629373361)
            ·
              refine ⟨502808371145095972030021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670411161526794629373361 502808371145095972030021)
              ·
                refine ⟨94276569589705494755629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502808371145095972030021 94276569589705494755629)
                ·
                  rfl

theorem cell19_309830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_309830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309830 prefixEnd_309830 := by exact prefixLift 309830
  have htrace : WordTrace (prefixWord ++ tailWord_309830) baseStart_309830 baseEnd_309830 := by
    simpa [prefixWord, tailWord_309830, baseEnd_309830] using wordTrace_append hprefix tailTrace_309830
  have hstable : (prefixWord ++ tailWord_309830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309830).length < 2 ^ (prefixWord ++ tailWord_309830).sum := by decide
  have hdescent : baseEnd_309830 < baseStart_309830 := by decide
  rcases family_descends (prefixWord ++ tailWord_309830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309834 : List Nat := [3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_309834 : Nat := 118140960795 + 309834 * 2 ^ 59
def prefixEnd_309834 : Nat := 4983230072969 + 3 ^ 40 * 309834 * 2
def baseEnd_309834 : Nat := 94277786729034670666729

theorem tailTrace_309834 : CollatzResearch.WordTrace tailWord_309834 prefixEnd_309834 94277786729034670666729 := by
  unfold tailWord_309834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825143589882952069874139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7533716239687872186331037 2825143589882952069874139)
  ·
    refine ⟨4237715384824428104811209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2825143589882952069874139 4237715384824428104811209)
    ·
      refine ⟨3178286538618321078608407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4237715384824428104811209 3178286538618321078608407)
      ·
        refine ⟨4767429807927481617912611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178286538618321078608407 4767429807927481617912611)
        ·
          refine ⟨7151144711891222426868917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767429807927481617912611 7151144711891222426868917)
          ·
            refine ⟨670419816739802102518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7151144711891222426868917 670419816739802102518961)
            ·
              refine ⟨502814862554851576889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670419816739802102518961 502814862554851576889221)
              ·
                refine ⟨94277786729034670666729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502814862554851576889221 94277786729034670666729)
                ·
                  rfl

theorem cell19_309834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_309834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309834 prefixEnd_309834 := by exact prefixLift 309834
  have htrace : WordTrace (prefixWord ++ tailWord_309834) baseStart_309834 baseEnd_309834 := by
    simpa [prefixWord, tailWord_309834, baseEnd_309834] using wordTrace_append hprefix tailTrace_309834
  have hstable : (prefixWord ++ tailWord_309834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309834).length < 2 ^ (prefixWord ++ tailWord_309834).sum := by decide
  have hdescent : baseEnd_309834 < baseStart_309834 := by decide
  rcases family_descends (prefixWord ++ tailWord_309834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309872 : List Nat := [2, 1, 1, 1, 8, 6]
def baseStart_309872 : Nat := 118140960795 + 309872 * 2 ^ 59
def prefixEnd_309872 : Nat := 4983230072969 + 3 ^ 40 * 309872 * 2
def baseEnd_309872 : Nat := 10476594394740204646909

theorem tailTrace_309872 : CollatzResearch.WordTrace tailWord_309872 prefixEnd_309872 10476594394740204646909 := by
  unfold tailWord_309872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650980166697070384689935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7534640222262760512919913 5650980166697070384689935)
  ·
    refine ⟨8476470250045605577034903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650980166697070384689935 8476470250045605577034903)
    ·
      refine ⟨12714705375068408365552355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8476470250045605577034903 12714705375068408365552355)
      ·
        refine ⟨19072058062602612548328533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12714705375068408365552355 19072058062602612548328533)
        ·
          refine ⟨223500680421124365800725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 19072058062602612548328533 223500680421124365800725)
          ·
            refine ⟨10476594394740204646909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 223500680421124365800725 10476594394740204646909)
            ·
              rfl

theorem cell19_309872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_309872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309872 prefixEnd_309872 := by exact prefixLift 309872
  have htrace : WordTrace (prefixWord ++ tailWord_309872) baseStart_309872 baseEnd_309872 := by
    simpa [prefixWord, tailWord_309872, baseEnd_309872] using wordTrace_append hprefix tailTrace_309872
  have hstable : (prefixWord ++ tailWord_309872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309872).length < 2 ^ (prefixWord ++ tailWord_309872).sum := by decide
  have hdescent : baseEnd_309872 < baseStart_309872 := by decide
  rcases family_descends (prefixWord ++ tailWord_309872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309874 : List Nat := [3, 2, 1, 2, 11]
def baseStart_309874 : Nat := 118140960795 + 309874 * 2 ^ 59
def prefixEnd_309874 : Nat := 4983230072969 + 3 ^ 40 * 309874 * 2
def baseEnd_309874 : Nat := 3492220671197275176953

theorem tailTrace_309874 : CollatzResearch.WordTrace tailWord_309874 prefixEnd_309874 3492220671197275176953 := by
  unfold tailWord_309874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825508319846723777738169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7534688852924596740635117 2825508319846723777738169)
  ·
    refine ⟨2119131239885042833303627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2825508319846723777738169 2119131239885042833303627)
    ·
      refine ⟨3178696859827564249955441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119131239885042833303627 3178696859827564249955441)
      ·
        refine ⟨2384022644870673187466581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3178696859827564249955441 2384022644870673187466581)
        ·
          refine ⟨3492220671197275176953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2384022644870673187466581 3492220671197275176953)
          ·
            rfl

theorem cell19_309874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 11].length) (baseStart_309874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309874 prefixEnd_309874 := by exact prefixLift 309874
  have htrace : WordTrace (prefixWord ++ tailWord_309874) baseStart_309874 baseEnd_309874 := by
    simpa [prefixWord, tailWord_309874, baseEnd_309874] using wordTrace_append hprefix tailTrace_309874
  have hstable : (prefixWord ++ tailWord_309874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309874).length < 2 ^ (prefixWord ++ tailWord_309874).sum := by decide
  have hdescent : baseEnd_309874 < baseStart_309874 := by decide
  rcases family_descends (prefixWord ++ tailWord_309874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309927 : List Nat := [1, 1, 6, 3, 1, 1, 6]
def baseStart_309927 : Nat := 118140960795 + 309927 * 2 ^ 59
def prefixEnd_309927 : Nat := 4983230072969 + 3 ^ 40 * 309927 * 2
def baseEnd_309927 : Nat := 31435361739479336866603

theorem tailTrace_309927 : CollatzResearch.WordTrace tailWord_309927 prefixEnd_309927 31435361739479336866603 := by
  unfold tailWord_309927
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303966348194885162632035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7535977565463256775088023 11303966348194885162632035)
  ·
    refine ⟨16955949522292327743948053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11303966348194885162632035 16955949522292327743948053)
    ·
      refine ⟨794810133857452862997565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16955949522292327743948053 794810133857452862997565)
      ·
        refine ⟨298053800196544823624087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 794810133857452862997565 298053800196544823624087)
        ·
          refine ⟨447080700294817235436131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298053800196544823624087 447080700294817235436131)
          ·
            refine ⟨670621050442225853154197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447080700294817235436131 670621050442225853154197)
            ·
              refine ⟨31435361739479336866603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 670621050442225853154197 31435361739479336866603)
              ·
                rfl

theorem cell19_309927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_309927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309927 prefixEnd_309927 := by exact prefixLift 309927
  have htrace : WordTrace (prefixWord ++ tailWord_309927) baseStart_309927 baseEnd_309927 := by
    simpa [prefixWord, tailWord_309927, baseEnd_309927] using wordTrace_append hprefix tailTrace_309927
  have hstable : (prefixWord ++ tailWord_309927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309927).length < 2 ^ (prefixWord ++ tailWord_309927).sum := by decide
  have hdescent : baseEnd_309927 < baseStart_309927 := by decide
  rcases family_descends (prefixWord ++ tailWord_309927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309969 : List Nat := [1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_309969 : Nat := 118140960795 + 309969 * 2 ^ 59
def prefixEnd_309969 : Nat := 4983230072969 + 3 ^ 40 * 309969 * 2
def baseEnd_309969 : Nat := 94318865181394357666361

theorem tailTrace_309969 : CollatzResearch.WordTrace tailWord_309969 prefixEnd_309969 94318865181394357666361 := by
  unfold tailWord_309969
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305498214042726335660961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7536998809361817557107307 11305498214042726335660961)
  ·
    refine ⟨8479123660532044751745721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11305498214042726335660961 8479123660532044751745721)
    ·
      refine ⟨6359342745399033563809291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8479123660532044751745721 6359342745399033563809291)
      ·
        refine ⟨9539014118098550345713937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6359342745399033563809291 9539014118098550345713937)
        ·
          refine ⟨7154260588573912759285453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9539014118098550345713937 7154260588573912759285453)
          ·
            refine ⟨2682847720715217284732045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7154260588573912759285453 2682847720715217284732045)
            ·
              refine ⟨1006067895268206481774517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682847720715217284732045 1006067895268206481774517)
              ·
                refine ⟨94318865181394357666361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1006067895268206481774517 94318865181394357666361)
                ·
                  rfl

theorem cell19_309969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_309969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309969 prefixEnd_309969 := by exact prefixLift 309969
  have htrace : WordTrace (prefixWord ++ tailWord_309969) baseStart_309969 baseEnd_309969 := by
    simpa [prefixWord, tailWord_309969, baseEnd_309969] using wordTrace_append hprefix tailTrace_309969
  have hstable : (prefixWord ++ tailWord_309969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309969).length < 2 ^ (prefixWord ++ tailWord_309969).sum := by decide
  have hdescent : baseEnd_309969 < baseStart_309969 := by decide
  rcases family_descends (prefixWord ++ tailWord_309969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309988 : List Nat := [2, 3, 1, 1, 1, 4, 7]
def baseStart_309988 : Nat := 118140960795 + 309988 * 2 ^ 59
def prefixEnd_309988 : Nat := 4983230072969 + 3 ^ 40 * 309988 * 2
def baseEnd_309988 : Nat := 31441548864402647748029

theorem tailTrace_309988 : CollatzResearch.WordTrace tailWord_309988 prefixEnd_309988 31441548864402647748029 := by
  unfold tailWord_309988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5653095600486946290301309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7537460800649261720401745 5653095600486946290301309)
  ·
    refine ⟨2119910850182604858862991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5653095600486946290301309 2119910850182604858862991)
    ·
      refine ⟨3179866275273907288294487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119910850182604858862991 3179866275273907288294487)
      ·
        refine ⟨4769799412910860932441731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3179866275273907288294487 4769799412910860932441731)
        ·
          refine ⟨7154699119366291398662597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4769799412910860932441731 7154699119366291398662597)
          ·
            refine ⟨1341506084881179637249237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7154699119366291398662597 1341506084881179637249237)
            ·
              refine ⟨31441548864402647748029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1341506084881179637249237 31441548864402647748029)
              ·
                rfl

theorem cell19_309988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_309988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_309988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_309988 prefixEnd_309988 := by exact prefixLift 309988
  have htrace : WordTrace (prefixWord ++ tailWord_309988) baseStart_309988 baseEnd_309988 := by
    simpa [prefixWord, tailWord_309988, baseEnd_309988] using wordTrace_append hprefix tailTrace_309988
  have hstable : (prefixWord ++ tailWord_309988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309988).length < 2 ^ (prefixWord ++ tailWord_309988).sum := by decide
  have hdescent : baseEnd_309988 < baseStart_309988 := by decide
  rcases family_descends (prefixWord ++ tailWord_309988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310026 : List Nat := [3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_310026 : Nat := 118140960795 + 310026 * 2 ^ 59
def prefixEnd_310026 : Nat := 4983230072969 + 3 ^ 40 * 310026 * 2
def baseEnd_310026 : Nat := 94336209416835114399539

theorem tailTrace_310026 : CollatzResearch.WordTrace tailWord_310026 prefixEnd_310026 94336209416835114399539 := by
  unfold tailWord_310026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826894293709056267621483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7538384783224150046990621 2826894293709056267621483)
  ·
    refine ⟨4240341440563584401432225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2826894293709056267621483 4240341440563584401432225)
    ·
      refine ⟨3180256080422688301074169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4240341440563584401432225 3180256080422688301074169)
      ·
        refine ⟨2385192060317016225805627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180256080422688301074169 2385192060317016225805627)
        ·
          refine ⟨3577788090475524338708441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385192060317016225805627 3577788090475524338708441)
          ·
            refine ⟨2683341067856643254031331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3577788090475524338708441 2683341067856643254031331)
            ·
              refine ⟨4025011601784964881046997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683341067856643254031331 4025011601784964881046997)
              ·
                refine ⟨94336209416835114399539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4025011601784964881046997 94336209416835114399539)
                ·
                  rfl

theorem cell19_310026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_310026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310026 prefixEnd_310026 := by exact prefixLift 310026
  have htrace : WordTrace (prefixWord ++ tailWord_310026) baseStart_310026 baseEnd_310026 := by
    simpa [prefixWord, tailWord_310026, baseEnd_310026] using wordTrace_append hprefix tailTrace_310026
  have hstable : (prefixWord ++ tailWord_310026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310026).length < 2 ^ (prefixWord ++ tailWord_310026).sum := by decide
  have hdescent : baseEnd_310026 < baseStart_310026 := by decide
  rcases family_descends (prefixWord ++ tailWord_310026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310058 : List Nat := [3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_310058 : Nat := 118140960795 + 310058 * 2 ^ 59
def prefixEnd_310058 : Nat := 4983230072969 + 3 ^ 40 * 310058 * 2
def baseEnd_310058 : Nat := 94345946531468521688341

theorem tailTrace_310058 : CollatzResearch.WordTrace tailWord_310058 prefixEnd_310058 94345946531468521688341 := by
  unfold tailWord_310058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827186077680073633912707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7539162873813529690433885 2827186077680073633912707)
  ·
    refine ⟨4240779116520110450869061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827186077680073633912707 4240779116520110450869061)
    ·
      refine ⟨795146084347520709537949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4240779116520110450869061 795146084347520709537949)
      ·
        refine ⟨298179781630320266076731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 795146084347520709537949 298179781630320266076731)
        ·
          refine ⟨447269672445480399115097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298179781630320266076731 447269672445480399115097)
          ·
            refine ⟨335452254334110299336323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447269672445480399115097 335452254334110299336323)
            ·
              refine ⟨503178381501165449004485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335452254334110299336323 503178381501165449004485)
              ·
                refine ⟨94345946531468521688341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503178381501165449004485 94345946531468521688341)
                ·
                  rfl

theorem cell19_310058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_310058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310058 prefixEnd_310058 := by exact prefixLift 310058
  have htrace : WordTrace (prefixWord ++ tailWord_310058) baseStart_310058 baseEnd_310058 := by
    simpa [prefixWord, tailWord_310058, baseEnd_310058] using wordTrace_append hprefix tailTrace_310058
  have hstable : (prefixWord ++ tailWord_310058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310058).length < 2 ^ (prefixWord ++ tailWord_310058).sum := by decide
  have hdescent : baseEnd_310058 < baseStart_310058 := by decide
  rcases family_descends (prefixWord ++ tailWord_310058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310100 : List Nat := [2, 4, 1, 1, 4, 1, 6]
def baseStart_310100 : Nat := 118140960795 + 310100 * 2 ^ 59
def prefixEnd_310100 : Nat := 4983230072969 + 3 ^ 40 * 310100 * 2
def baseEnd_310100 : Nat := 31452908831474956251631

theorem tailTrace_310100 : CollatzResearch.WordTrace tailWord_310100 prefixEnd_310100 31452908831474956251631 := by
  unfold tailWord_310100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5655138088284067854339877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7540184117712090472453169 5655138088284067854339877)
  ·
    refine ⟨1060338391553262722688727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5655138088284067854339877 1060338391553262722688727)
    ·
      refine ⟨1590507587329894084033091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060338391553262722688727 1590507587329894084033091)
      ·
        refine ⟨2385761380994841126049637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590507587329894084033091 2385761380994841126049637)
        ·
          refine ⟨447330258936532711134307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2385761380994841126049637 447330258936532711134307)
          ·
            refine ⟨670995388404799066701461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447330258936532711134307 670995388404799066701461)
            ·
              refine ⟨31452908831474956251631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 670995388404799066701461 31452908831474956251631)
              ·
                rfl

theorem cell19_310100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_310100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310100 prefixEnd_310100 := by exact prefixLift 310100
  have htrace : WordTrace (prefixWord ++ tailWord_310100) baseStart_310100 baseEnd_310100 := by
    simpa [prefixWord, tailWord_310100, baseEnd_310100] using wordTrace_append hprefix tailTrace_310100
  have hstable : (prefixWord ++ tailWord_310100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310100).length < 2 ^ (prefixWord ++ tailWord_310100).sum := by decide
  have hdescent : baseEnd_310100 < baseStart_310100 := by decide
  rcases family_descends (prefixWord ++ tailWord_310100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310134 : List Nat := [5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_310134 : Nat := 118140960795 + 310134 * 2 ^ 59
def prefixEnd_310134 : Nat := 4983230072969 + 3 ^ 40 * 310134 * 2
def baseEnd_310134 : Nat := 94369072178722863999245

theorem tailTrace_310134 : CollatzResearch.WordTrace tailWord_310134 prefixEnd_310134 94369072178722863999245 := by
  unfold tailWord_310134
  simp only [CollatzResearch.WordTrace]
  refine ⟨706969766152809969713591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7541010838963306343611637 706969766152809969713591)
  ·
    refine ⟨1060454649229214954570387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706969766152809969713591 1060454649229214954570387)
    ·
      refine ⟨1590681973843822431855581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060454649229214954570387 1590681973843822431855581)
      ·
        refine ⟨596505740191433411945843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1590681973843822431855581 596505740191433411945843)
        ·
          refine ⟨894758610287150117918765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596505740191433411945843 894758610287150117918765)
          ·
            refine ⟨335534478857681294219537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894758610287150117918765 335534478857681294219537)
            ·
              refine ⟨251650859143260970664653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335534478857681294219537 251650859143260970664653)
              ·
                refine ⟨94369072178722863999245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251650859143260970664653 94369072178722863999245)
                ·
                  rfl

theorem cell19_310134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_310134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310134 prefixEnd_310134 := by exact prefixLift 310134
  have htrace : WordTrace (prefixWord ++ tailWord_310134) baseStart_310134 baseEnd_310134 := by
    simpa [prefixWord, tailWord_310134, baseEnd_310134] using wordTrace_append hprefix tailTrace_310134
  have hstable : (prefixWord ++ tailWord_310134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310134).length < 2 ^ (prefixWord ++ tailWord_310134).sum := by decide
  have hdescent : baseEnd_310134 < baseStart_310134 := by decide
  rcases family_descends (prefixWord ++ tailWord_310134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310197 : List Nat := [1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_310197 : Nat := 118140960795 + 310197 * 2 ^ 59
def prefixEnd_310197 : Nat := 4983230072969 + 3 ^ 40 * 310197 * 2
def baseEnd_310197 : Nat := 94388242123157384599073

theorem tailTrace_310197 : CollatzResearch.WordTrace tailWord_310197 prefixEnd_310197 94388242123157384599073 := by
  unfold tailWord_310197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313814057216721274960845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7542542704811147516640563 11313814057216721274960845)
  ·
    refine ⟨4242680271456270478110317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11313814057216721274960845 4242680271456270478110317)
    ·
      refine ⟨1591005101796101429291369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4242680271456270478110317 1591005101796101429291369)
      ·
        refine ⟨1193253826347076071968527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1591005101796101429291369 1193253826347076071968527)
        ·
          refine ⟨1789880739520614107952791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193253826347076071968527 1789880739520614107952791)
          ·
            refine ⟨2684821109280921161929187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789880739520614107952791 2684821109280921161929187)
            ·
              refine ⟨4027231663921381742893781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684821109280921161929187 4027231663921381742893781)
              ·
                refine ⟨94388242123157384599073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4027231663921381742893781 94388242123157384599073)
                ·
                  rfl

theorem cell19_310197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_310197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310197 prefixEnd_310197 := by exact prefixLift 310197
  have htrace : WordTrace (prefixWord ++ tailWord_310197) baseStart_310197 baseEnd_310197 := by
    simpa [prefixWord, tailWord_310197, baseEnd_310197] using wordTrace_append hprefix tailTrace_310197
  have hstable : (prefixWord ++ tailWord_310197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310197).length < 2 ^ (prefixWord ++ tailWord_310197).sum := by decide
  have hdescent : baseEnd_310197 < baseStart_310197 := by decide
  rcases family_descends (prefixWord ++ tailWord_310197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310212 : List Nat := [2, 3, 3, 3, 2, 6]
def baseStart_310212 : Nat := 118140960795 + 310212 * 2 ^ 59
def prefixEnd_310212 : Nat := 4983230072969 + 3 ^ 40 * 310212 * 2
def baseEnd_310212 : Nat := 10488089599515754918411

theorem tailTrace_310212 : CollatzResearch.WordTrace tailWord_310212 prefixEnd_310212 10488089599515754918411 := by
  unfold tailWord_310212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657180576081189418378445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7542907434774919224504593 5657180576081189418378445)
  ·
    refine ⟨2121442716030446031891917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5657180576081189418378445 2121442716030446031891917)
    ·
      refine ⟨795541018511417261959469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2121442716030446031891917 795541018511417261959469)
      ·
        refine ⟨298327881941781473234801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 795541018511417261959469 298327881941781473234801)
        ·
          refine ⟨223745911456336104926101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298327881941781473234801 223745911456336104926101)
          ·
            refine ⟨10488089599515754918411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 223745911456336104926101 10488089599515754918411)
            ·
              rfl

theorem cell19_310212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_310212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310212 prefixEnd_310212 := by exact prefixLift 310212
  have htrace : WordTrace (prefixWord ++ tailWord_310212) baseStart_310212 baseEnd_310212 := by
    simpa [prefixWord, tailWord_310212, baseEnd_310212] using wordTrace_append hprefix tailTrace_310212
  have hstable : (prefixWord ++ tailWord_310212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310212).length < 2 ^ (prefixWord ++ tailWord_310212).sum := by decide
  have hdescent : baseEnd_310212 < baseStart_310212 := by decide
  rcases family_descends (prefixWord ++ tailWord_310212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310216 : List Nat := [2, 1, 3, 1, 5, 7]
def baseStart_310216 : Nat := 118140960795 + 310216 * 2 ^ 59
def prefixEnd_310216 : Nat := 4983230072969 + 3 ^ 40 * 310216 * 2
def baseEnd_310216 : Nat := 10488224837218996686311

theorem tailTrace_310216 : CollatzResearch.WordTrace tailWord_310216 prefixEnd_310216 10488224837218996686311 := by
  unfold tailWord_310216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657253522073943759951251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7543004696098591679935001 5657253522073943759951251)
  ·
    refine ⟨8485880283110915639926877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657253522073943759951251 8485880283110915639926877)
    ·
      refine ⟨3182205106166593364972579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8485880283110915639926877 3182205106166593364972579)
      ·
        refine ⟨4773307659249890047458869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182205106166593364972579 4773307659249890047458869)
        ·
          refine ⟨447497593054677191949269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4773307659249890047458869 447497593054677191949269)
          ·
            refine ⟨10488224837218996686311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 447497593054677191949269 10488224837218996686311)
            ·
              rfl

theorem cell19_310216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_310216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310216 prefixEnd_310216 := by exact prefixLift 310216
  have htrace : WordTrace (prefixWord ++ tailWord_310216) baseStart_310216 baseEnd_310216 := by
    simpa [prefixWord, tailWord_310216, baseEnd_310216] using wordTrace_append hprefix tailTrace_310216
  have hstable : (prefixWord ++ tailWord_310216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310216).length < 2 ^ (prefixWord ++ tailWord_310216).sum := by decide
  have hdescent : baseEnd_310216 < baseStart_310216 := by decide
  rcases family_descends (prefixWord ++ tailWord_310216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310233 : List Nat := [1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_310233 : Nat := 118140960795 + 310233 * 2 ^ 59
def prefixEnd_310233 : Nat := 4983230072969 + 3 ^ 40 * 310233 * 2
def baseEnd_310233 : Nat := 94399196377119967798975

theorem tailTrace_310233 : CollatzResearch.WordTrace tailWord_310233 prefixEnd_310233 94399196377119967798975 := by
  unfold tailWord_310233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11315127085086299423271353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7543418056724199615514235 11315127085086299423271353)
  ·
    refine ⟨8486345313814724567453515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11315127085086299423271353 8486345313814724567453515)
    ·
      refine ⟨12729517970722086851180273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8486345313814724567453515 12729517970722086851180273)
      ·
        refine ⟨9547138478041565138385205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12729517970722086851180273 9547138478041565138385205)
        ·
          refine ⟨895044232316396731723613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9547138478041565138385205 895044232316396731723613)
          ·
            refine ⟨335641587118648774396355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 895044232316396731723613 335641587118648774396355)
            ·
              refine ⟨503462380677973161594533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335641587118648774396355 503462380677973161594533)
              ·
                refine ⟨94399196377119967798975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503462380677973161594533 94399196377119967798975)
                ·
                  rfl

theorem cell19_310233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_310233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310233 prefixEnd_310233 := by exact prefixLift 310233
  have htrace : WordTrace (prefixWord ++ tailWord_310233) baseStart_310233 baseEnd_310233 := by
    simpa [prefixWord, tailWord_310233, baseEnd_310233] using wordTrace_append hprefix tailTrace_310233
  have hstable : (prefixWord ++ tailWord_310233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310233).length < 2 ^ (prefixWord ++ tailWord_310233).sum := by decide
  have hdescent : baseEnd_310233 < baseStart_310233 := by decide
  rcases family_descends (prefixWord ++ tailWord_310233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310273 : List Nat := [1, 2, 4, 1, 2, 3, 6]
def baseStart_310273 : Nat := 118140960795 + 310273 * 2 ^ 59
def prefixEnd_310273 : Nat := 4983230072969 + 3 ^ 40 * 310273 * 2
def baseEnd_310273 : Nat := 31470455923470575636659

theorem tailTrace_310273 : CollatzResearch.WordTrace tailWord_310273 prefixEnd_310273 31470455923470575636659 := by
  unfold tailWord_310273
  simp only [CollatzResearch.WordTrace]
  refine ⟨11316586004941386254727473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7544390669960924169818315 11316586004941386254727473)
  ·
    refine ⟨8487439503706039691045605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11316586004941386254727473 8487439503706039691045605)
    ·
      refine ⟨1591394906944882442071051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8487439503706039691045605 1591394906944882442071051)
      ·
        refine ⟨2387092360417323663106577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591394906944882442071051 2387092360417323663106577)
        ·
          refine ⟨1790319270312992747329933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2387092360417323663106577 1790319270312992747329933)
          ·
            refine ⟨671369726367372280248725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1790319270312992747329933 671369726367372280248725)
            ·
              refine ⟨31470455923470575636659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 671369726367372280248725 31470455923470575636659)
              ·
                rfl

theorem cell19_310273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_310273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310273 prefixEnd_310273 := by exact prefixLift 310273
  have htrace : WordTrace (prefixWord ++ tailWord_310273) baseStart_310273 baseEnd_310273 := by
    simpa [prefixWord, tailWord_310273, baseEnd_310273] using wordTrace_append hprefix tailTrace_310273
  have hstable : (prefixWord ++ tailWord_310273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310273).length < 2 ^ (prefixWord ++ tailWord_310273).sum := by decide
  have hdescent : baseEnd_310273 < baseStart_310273 := by decide
  rcases family_descends (prefixWord ++ tailWord_310273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310398 : List Nat := [4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_310398 : Nat := 118140960795 + 310398 * 2 ^ 59
def prefixEnd_310398 : Nat := 4983230072969 + 3 ^ 40 * 310398 * 2
def baseEnd_310398 : Nat := 94449403374448474131859

theorem tailTrace_310398 : CollatzResearch.WordTrace tailWord_310398 prefixEnd_310398 94449403374448474131859 := by
  unfold tailWord_310398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415143141186066575378481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7547430086325688402018565 1415143141186066575378481)
  ·
    refine ⟨1061357355889549931533861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1415143141186066575378481 1061357355889549931533861)
    ·
      refine ⟨199004504229290612162599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1061357355889549931533861 199004504229290612162599)
      ·
        refine ⟨298506756343935918243899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199004504229290612162599 298506756343935918243899)
        ·
          refine ⟨447760134515903877365849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298506756343935918243899 447760134515903877365849)
          ·
            refine ⟨335820100886927908024387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447760134515903877365849 335820100886927908024387)
            ·
              refine ⟨503730151330391862036581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335820100886927908024387 503730151330391862036581)
              ·
                refine ⟨94449403374448474131859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503730151330391862036581 94449403374448474131859)
                ·
                  rfl

theorem cell19_310398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_310398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310398 prefixEnd_310398 := by exact prefixLift 310398
  have htrace : WordTrace (prefixWord ++ tailWord_310398) baseStart_310398 baseEnd_310398 := by
    simpa [prefixWord, tailWord_310398, baseEnd_310398] using wordTrace_append hprefix tailTrace_310398
  have hstable : (prefixWord ++ tailWord_310398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310398).length < 2 ^ (prefixWord ++ tailWord_310398).sum := by decide
  have hdescent : baseEnd_310398 < baseStart_310398 := by decide
  rcases family_descends (prefixWord ++ tailWord_310398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310404 : List Nat := [2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_310404 : Nat := 118140960795 + 310404 * 2 ^ 59
def prefixEnd_310404 : Nat := 4983230072969 + 3 ^ 40 * 310404 * 2
def baseEnd_310404 : Nat := 94451229083442237998509

theorem tailTrace_310404 : CollatzResearch.WordTrace tailWord_310404 prefixEnd_310404 94451229083442237998509 := by
  unfold tailWord_310404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660681983733397813873133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7547575978311197085164177 5660681983733397813873133)
  ·
    refine ⟨2122755743900024180202425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5660681983733397813873133 2122755743900024180202425)
    ·
      refine ⟨1592066807925018135151819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2122755743900024180202425 1592066807925018135151819)
      ·
        refine ⟨2388100211887527202727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592066807925018135151819 2388100211887527202727729)
        ·
          refine ⟨1791075158915645402045797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388100211887527202727729 1791075158915645402045797)
          ·
            refine ⟨335826592296683512883587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1791075158915645402045797 335826592296683512883587)
            ·
              refine ⟨503739888445025269325381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335826592296683512883587 503739888445025269325381)
              ·
                refine ⟨94451229083442237998509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503739888445025269325381 94451229083442237998509)
                ·
                  rfl

theorem cell19_310404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_310404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310404 prefixEnd_310404 := by exact prefixLift 310404
  have htrace : WordTrace (prefixWord ++ tailWord_310404) baseStart_310404 baseEnd_310404 := by
    simpa [prefixWord, tailWord_310404, baseEnd_310404] using wordTrace_append hprefix tailTrace_310404
  have hstable : (prefixWord ++ tailWord_310404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310404).length < 2 ^ (prefixWord ++ tailWord_310404).sum := by decide
  have hdescent : baseEnd_310404 < baseStart_310404 := by decide
  rcases family_descends (prefixWord ++ tailWord_310404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310423 : List Nat := [1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_310423 : Nat := 118140960795 + 310423 * 2 ^ 59
def prefixEnd_310423 : Nat := 4983230072969 + 3 ^ 40 * 310423 * 2
def baseEnd_310423 : Nat := 94457010495255823576235

theorem tailTrace_310423 : CollatzResearch.WordTrace tailWord_310423 prefixEnd_310423 94457010495255823576235 := by
  unfold tailWord_310423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11322056954397961872687923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7548037969598641248458615 11322056954397961872687923)
  ·
    refine ⟨16983085431596942809031885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11322056954397961872687923 16983085431596942809031885)
    ·
      refine ⟨6368657036848853553386957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16983085431596942809031885 6368657036848853553386957)
      ·
        refine ⟨2388246388818320082520109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6368657036848853553386957 2388246388818320082520109)
        ·
          refine ⟨895592395806870030945041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2388246388818320082520109 895592395806870030945041)
          ·
            refine ⟨671694296855152523208781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895592395806870030945041 671694296855152523208781)
            ·
              refine ⟨251885361320682196203293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 671694296855152523208781 251885361320682196203293)
              ·
                refine ⟨94457010495255823576235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251885361320682196203293 94457010495255823576235)
                ·
                  rfl

theorem cell19_310423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_310423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310423 prefixEnd_310423 := by exact prefixLift 310423
  have htrace : WordTrace (prefixWord ++ tailWord_310423) baseStart_310423 baseEnd_310423 := by
    simpa [prefixWord, tailWord_310423, baseEnd_310423] using wordTrace_append hprefix tailTrace_310423
  have hstable : (prefixWord ++ tailWord_310423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310423).length < 2 ^ (prefixWord ++ tailWord_310423).sum := by decide
  have hdescent : baseEnd_310423 < baseStart_310423 := by decide
  rcases family_descends (prefixWord ++ tailWord_310423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310442 : List Nat := [3, 1, 5, 1, 1, 2, 6]
def baseStart_310442 : Nat := 118140960795 + 310442 * 2 ^ 59
def prefixEnd_310442 : Nat := 4983230072969 + 3 ^ 40 * 310442 * 2
def baseEnd_310442 : Nat := 31487597302356469717987

theorem tailTrace_310442 : CollatzResearch.WordTrace tailWord_310442 prefixEnd_310442 31487597302356469717987 := by
  unfold tailWord_310442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830687485332282029407395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7548499960886085411753053 2830687485332282029407395)
  ·
    refine ⟨4246031227998423044111093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2830687485332282029407395 4246031227998423044111093)
    ·
      refine ⟨398065427624852160385415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4246031227998423044111093 398065427624852160385415)
      ·
        refine ⟨597098141437278240578123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398065427624852160385415 597098141437278240578123)
        ·
          refine ⟨895647212155917360867185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597098141437278240578123 895647212155917360867185)
          ·
            refine ⟨671735409116938020650389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895647212155917360867185 671735409116938020650389)
            ·
              refine ⟨31487597302356469717987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 671735409116938020650389 31487597302356469717987)
              ·
                rfl

theorem cell19_310442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_310442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310442 prefixEnd_310442 := by exact prefixLift 310442
  have htrace : WordTrace (prefixWord ++ tailWord_310442) baseStart_310442 baseEnd_310442 := by
    simpa [prefixWord, tailWord_310442, baseEnd_310442] using wordTrace_append hprefix tailTrace_310442
  have hstable : (prefixWord ++ tailWord_310442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310442).length < 2 ^ (prefixWord ++ tailWord_310442).sum := by decide
  have hdescent : baseEnd_310442 < baseStart_310442 := by decide
  rcases family_descends (prefixWord ++ tailWord_310442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310478 : List Nat := [4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_310478 : Nat := 118140960795 + 310478 * 2 ^ 59
def prefixEnd_310478 : Nat := 4983230072969 + 3 ^ 40 * 310478 * 2
def baseEnd_310478 : Nat := 94473746161031992353863

theorem tailTrace_310478 : CollatzResearch.WordTrace tailWord_310478 prefixEnd_310478 94473746161031992353863 := by
  unfold tailWord_310478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415507871149838283242511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7549375312799137510626725 1415507871149838283242511)
  ·
    refine ⟨2123261806724757424863767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415507871149838283242511 2123261806724757424863767)
    ·
      refine ⟨3184892710087136137295651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123261806724757424863767 3184892710087136137295651)
      ·
        refine ⟨4777339065130704205943477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184892710087136137295651 4777339065130704205943477)
        ·
          refine ⟨447875537356003519307201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4777339065130704205943477 447875537356003519307201)
          ·
            refine ⟨335906653017002639480401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447875537356003519307201 335906653017002639480401)
            ·
              refine ⟨251929989762751979610301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335906653017002639480401 251929989762751979610301)
              ·
                refine ⟨94473746161031992353863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251929989762751979610301 94473746161031992353863)
                ·
                  rfl

theorem cell19_310478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_310478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310478 prefixEnd_310478 := by exact prefixLift 310478
  have htrace : WordTrace (prefixWord ++ tailWord_310478) baseStart_310478 baseEnd_310478 := by
    simpa [prefixWord, tailWord_310478, baseEnd_310478] using wordTrace_append hprefix tailTrace_310478
  have hstable : (prefixWord ++ tailWord_310478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310478).length < 2 ^ (prefixWord ++ tailWord_310478).sum := by decide
  have hdescent : baseEnd_310478 < baseStart_310478 := by decide
  rcases family_descends (prefixWord ++ tailWord_310478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310482 : List Nat := [3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_310482 : Nat := 118140960795 + 310482 * 2 ^ 59
def prefixEnd_310482 : Nat := 4983230072969 + 3 ^ 40 * 310482 * 2
def baseEnd_310482 : Nat := 94474963300361168264963

theorem tailTrace_310482 : CollatzResearch.WordTrace tailWord_310482 prefixEnd_310482 94474963300361168264963 := by
  unfold tailWord_310482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831052215296053737271425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7549472574122809966057133 2831052215296053737271425)
  ·
    refine ⟨2123289161472040302953569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2831052215296053737271425 2123289161472040302953569)
    ·
      refine ⟨1592466871104030227215177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2123289161472040302953569 1592466871104030227215177)
      ·
        refine ⟨1194350153328022670411383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1592466871104030227215177 1194350153328022670411383)
        ·
          refine ⟨1791525229992034005617075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194350153328022670411383 1791525229992034005617075)
          ·
            refine ⟨2687287844988051008425613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791525229992034005617075 2687287844988051008425613)
            ·
              refine ⟨1007732941870519128159605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2687287844988051008425613 1007732941870519128159605)
              ·
                refine ⟨94474963300361168264963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1007732941870519128159605 94474963300361168264963)
                ·
                  rfl

theorem cell19_310482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_310482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310482 prefixEnd_310482 := by exact prefixLift 310482
  have htrace : WordTrace (prefixWord ++ tailWord_310482) baseStart_310482 baseEnd_310482 := by
    simpa [prefixWord, tailWord_310482, baseEnd_310482] using wordTrace_append hprefix tailTrace_310482
  have hstable : (prefixWord ++ tailWord_310482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310482).length < 2 ^ (prefixWord ++ tailWord_310482).sum := by decide
  have hdescent : baseEnd_310482 < baseStart_310482 := by decide
  rcases family_descends (prefixWord ++ tailWord_310482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310560 : List Nat := [2, 1, 1, 5, 10]
def baseStart_310560 : Nat := 118140960795 + 310560 * 2 ^ 59
def prefixEnd_310560 : Nat := 4983230072969 + 3 ^ 40 * 310560 * 2
def baseEnd_310560 : Nat := 3499951759899262908571

theorem tailTrace_310560 : CollatzResearch.WordTrace tailWord_310560 prefixEnd_310560 3499951759899262908571 := by
  unfold tailWord_310560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663526877450817135212567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7551369169934422846950089 5663526877450817135212567)
  ·
    refine ⟨8495290316176225702818851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663526877450817135212567 8495290316176225702818851)
    ·
      refine ⟨12742935474264338554228277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8495290316176225702818851 12742935474264338554228277)
      ·
        refine ⟨1194650200712281739458901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12742935474264338554228277 1194650200712281739458901)
        ·
          refine ⟨3499951759899262908571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1194650200712281739458901 3499951759899262908571)
          ·
            rfl

theorem cell19_310560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 10].length) (baseStart_310560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310560 prefixEnd_310560 := by exact prefixLift 310560
  have htrace : WordTrace (prefixWord ++ tailWord_310560) baseStart_310560 baseEnd_310560 := by
    simpa [prefixWord, tailWord_310560, baseEnd_310560] using wordTrace_append hprefix tailTrace_310560
  have hstable : (prefixWord ++ tailWord_310560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310560).length < 2 ^ (prefixWord ++ tailWord_310560).sum := by decide
  have hdescent : baseEnd_310560 < baseStart_310560 := by decide
  rcases family_descends (prefixWord ++ tailWord_310560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310573 : List Nat := [1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_310573 : Nat := 118140960795 + 310573 * 2 ^ 59
def prefixEnd_310573 : Nat := 4983230072969 + 3 ^ 40 * 310573 * 2
def baseEnd_310573 : Nat := 94502653220099920242493

theorem tailTrace_310573 : CollatzResearch.WordTrace tailWord_310573 prefixEnd_310573 94502653220099920242493 := by
  unfold tailWord_310573
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327527903854537490648373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7551685269236358327098915 11327527903854537490648373)
  ·
    refine ⟨1061955740986362889748285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11327527903854537490648373 1061955740986362889748285)
    ·
      refine ⟨398233402869886083655607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1061955740986362889748285 398233402869886083655607)
      ·
        refine ⟨597350104304829125483411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398233402869886083655607 597350104304829125483411)
        ·
          refine ⟨896025156457243688225117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597350104304829125483411 896025156457243688225117)
          ·
            refine ⟨336009433671466383084419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 896025156457243688225117 336009433671466383084419)
            ·
              refine ⟨504014150507199574626629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336009433671466383084419 504014150507199574626629)
              ·
                refine ⟨94502653220099920242493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504014150507199574626629 94502653220099920242493)
                ·
                  rfl

theorem cell19_310573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_310573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310573 prefixEnd_310573 := by exact prefixLift 310573
  have htrace : WordTrace (prefixWord ++ tailWord_310573) baseStart_310573 baseEnd_310573 := by
    simpa [prefixWord, tailWord_310573, baseEnd_310573] using wordTrace_append hprefix tailTrace_310573
  have hstable : (prefixWord ++ tailWord_310573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310573).length < 2 ^ (prefixWord ++ tailWord_310573).sum := by decide
  have hdescent : baseEnd_310573 < baseStart_310573 := by decide
  rcases family_descends (prefixWord ++ tailWord_310573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310577 : List Nat := [1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_310577 : Nat := 118140960795 + 310577 * 2 ^ 59
def prefixEnd_310577 : Nat := 4983230072969 + 3 ^ 40 * 310577 * 2
def baseEnd_310577 : Nat := 94503870359429096153593

theorem tailTrace_310577 : CollatzResearch.WordTrace tailWord_310577 prefixEnd_310577 94503870359429096153593 := by
  unfold tailWord_310577
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327673795840046173793985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7551782530560030782529323 11327673795840046173793985)
  ·
    refine ⟨8495755346880034630345489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11327673795840046173793985 8495755346880034630345489)
    ·
      refine ⟨6371816510160025972759117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8495755346880034630345489 6371816510160025972759117)
      ·
        refine ⟨2389431191310009739784669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6371816510160025972759117 2389431191310009739784669)
        ·
          refine ⟨896036696741253652419251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2389431191310009739784669 896036696741253652419251)
          ·
            refine ⟨1344055045111880478628877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896036696741253652419251 1344055045111880478628877)
            ·
              refine ⟨504020641916955179485829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1344055045111880478628877 504020641916955179485829)
              ·
                refine ⟨94503870359429096153593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504020641916955179485829 94503870359429096153593)
                ·
                  rfl

theorem cell19_310577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_310577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310577 prefixEnd_310577 := by exact prefixLift 310577
  have htrace : WordTrace (prefixWord ++ tailWord_310577) baseStart_310577 baseEnd_310577 := by
    simpa [prefixWord, tailWord_310577, baseEnd_310577] using wordTrace_append hprefix tailTrace_310577
  have hstable : (prefixWord ++ tailWord_310577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310577).length < 2 ^ (prefixWord ++ tailWord_310577).sum := by decide
  have hdescent : baseEnd_310577 < baseStart_310577 := by decide
  rcases family_descends (prefixWord ++ tailWord_310577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310670 : List Nat := [4, 1, 1, 4, 2, 2, 5]
def baseStart_310670 : Nat := 118140960795 + 310670 * 2 ^ 59
def prefixEnd_310670 : Nat := 4983230072969 + 3 ^ 40 * 310670 * 2
def baseEnd_310670 : Nat := 31510722949610812028891

theorem tailTrace_310670 : CollatzResearch.WordTrace tailWord_310670 prefixEnd_310670 31510722949610812028891 := by
  unfold tailWord_310670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416383223062890382116183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7554043856335415371286309 1416383223062890382116183)
  ·
    refine ⟨2124574834594335573174275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1416383223062890382116183 2124574834594335573174275)
    ·
      refine ⟨3186862251891503359761413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124574834594335573174275 3186862251891503359761413)
      ·
        refine ⟨597536672229656879955265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3186862251891503359761413 597536672229656879955265)
        ·
          refine ⟨448152504172242659966449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597536672229656879955265 448152504172242659966449)
          ·
            refine ⟨336114378129181994974837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448152504172242659966449 336114378129181994974837)
            ·
              refine ⟨31510722949610812028891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336114378129181994974837 31510722949610812028891)
              ·
                rfl

theorem cell19_310670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_310670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310670 prefixEnd_310670 := by exact prefixLift 310670
  have htrace : WordTrace (prefixWord ++ tailWord_310670) baseStart_310670 baseEnd_310670 := by
    simpa [prefixWord, tailWord_310670, baseEnd_310670] using wordTrace_append hprefix tailTrace_310670
  have hstable : (prefixWord ++ tailWord_310670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310670).length < 2 ^ (prefixWord ++ tailWord_310670).sum := by decide
  have hdescent : baseEnd_310670 < baseStart_310670 := by decide
  rcases family_descends (prefixWord ++ tailWord_310670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310712 : List Nat := [2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_310712 : Nat := 118140960795 + 310712 * 2 ^ 59
def prefixEnd_310712 : Nat := 4983230072969 + 3 ^ 40 * 310712 * 2
def baseEnd_310712 : Nat := 94544948811788783153225

theorem tailTrace_310712 : CollatzResearch.WordTrace tailWord_310712 prefixEnd_310712 94544948811788783153225 := by
  unfold tailWord_310712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666298825175482114979195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7555065100233976153305593 5666298825175482114979195)
  ·
    refine ⟨8499448237763223172468793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5666298825175482114979195 8499448237763223172468793)
    ·
      refine ⟨6374586178322417379351595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8499448237763223172468793 6374586178322417379351595)
      ·
        refine ⟨9561879267483626069027393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6374586178322417379351595 9561879267483626069027393)
        ·
          refine ⟨7171409450612719551770545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9561879267483626069027393 7171409450612719551770545)
          ·
            refine ⟨5378557087959539663827909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7171409450612719551770545 5378557087959539663827909)
            ·
              refine ⟨1008479453992413686967733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5378557087959539663827909 1008479453992413686967733)
              ·
                refine ⟨94544948811788783153225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008479453992413686967733 94544948811788783153225)
                ·
                  rfl

theorem cell19_310712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_310712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310712 prefixEnd_310712 := by exact prefixLift 310712
  have htrace : WordTrace (prefixWord ++ tailWord_310712) baseStart_310712 baseEnd_310712 := by
    simpa [prefixWord, tailWord_310712, baseEnd_310712] using wordTrace_append hprefix tailTrace_310712
  have hstable : (prefixWord ++ tailWord_310712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310712).length < 2 ^ (prefixWord ++ tailWord_310712).sum := by decide
  have hdescent : baseEnd_310712 < baseStart_310712 := by decide
  rcases family_descends (prefixWord ++ tailWord_310712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
