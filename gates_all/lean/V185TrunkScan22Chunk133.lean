import V185TrunkScan22Chunk132

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1187765 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1187765 : Nat := 118140960795 + 1187765 * 2 ^ 59
def prefixEnd_1187765 : Nat := 4983230072969 + 3 ^ 40 * 1187765 * 2
def baseEnd_1187765 : Nat := 406596233058433731783383

theorem tailTrace_1187765 : CollatzResearch.WordTrace tailWord_1187765 prefixEnd_1187765 406596233058433731783383 := by
  unfold tailWord_1187765
  simp only [CollatzResearch.WordTrace]
  refine ⟨43321348541937733957068749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28880899027958489304712499 43321348541937733957068749)
  ·
    refine ⟨16245505703226650233900781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43321348541937733957068749 16245505703226650233900781)
    ·
      refine ⟨6092064638709993837712793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16245505703226650233900781 6092064638709993837712793)
      ·
        refine ⟨4569048479032495378284595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6092064638709993837712793 4569048479032495378284595)
        ·
          refine ⟨6853572718548743067426893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569048479032495378284595 6853572718548743067426893)
          ·
            refine ⟨2570089769455778650285085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6853572718548743067426893 2570089769455778650285085)
            ·
              refine ⟨963783663545916993856907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2570089769455778650285085 963783663545916993856907)
              ·
                refine ⟨1445675495318875490785361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963783663545916993856907 1445675495318875490785361)
                ·
                  refine ⟨1084256621489156618089021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445675495318875490785361 1084256621489156618089021)
                  ·
                    refine ⟨406596233058433731783383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084256621489156618089021 406596233058433731783383)
                    ·
                      rfl

theorem cell22_1187765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1187765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187765 prefixEnd_1187765 := by exact prefixLift 1187765
  have htrace : WordTrace (prefixWord ++ tailWord_1187765) baseStart_1187765 baseEnd_1187765 := by
    simpa [prefixWord, tailWord_1187765, baseEnd_1187765] using wordTrace_append hprefix tailTrace_1187765
  have hstable : (prefixWord ++ tailWord_1187765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187765).length < 2 ^ (prefixWord ++ tailWord_1187765).sum := by decide
  have hdescent : baseEnd_1187765 < baseStart_1187765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187776 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_1187776 : Nat := 118140960795 + 1187776 * 2 ^ 59
def prefixEnd_1187776 : Nat := 4983230072969 + 3 ^ 40 * 1187776 * 2
def baseEnd_1187776 : Nat := 406599998583233369758349

theorem tailTrace_1187776 : CollatzResearch.WordTrace tailWord_1187776 prefixEnd_1187776 406599998583233369758349 := by
  unfold tailWord_1187776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21660874872448941417859591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28881166496598588557146121 21660874872448941417859591)
  ·
    refine ⟨32491312308673412126789387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21660874872448941417859591 32491312308673412126789387)
    ·
      refine ⟨48736968463010118190184081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32491312308673412126789387 48736968463010118190184081)
      ·
        refine ⟨36552726347257588642638061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48736968463010118190184081 36552726347257588642638061)
        ·
          refine ⟨13707272380221595740989273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36552726347257588642638061 13707272380221595740989273)
          ·
            refine ⟨10280454285166196805741955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13707272380221595740989273 10280454285166196805741955)
            ·
              refine ⟨15420681427749295208612933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10280454285166196805741955 15420681427749295208612933)
              ·
                refine ⟨2891377767702992851614925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15420681427749295208612933 2891377767702992851614925)
                ·
                  refine ⟨1084266662888622319355597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2891377767702992851614925 1084266662888622319355597)
                  ·
                    refine ⟨406599998583233369758349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084266662888622319355597 406599998583233369758349)
                    ·
                      rfl

theorem cell22_1187776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_1187776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187776 prefixEnd_1187776 := by exact prefixLift 1187776
  have htrace : WordTrace (prefixWord ++ tailWord_1187776) baseStart_1187776 baseEnd_1187776 := by
    simpa [prefixWord, tailWord_1187776, baseEnd_1187776] using wordTrace_append hprefix tailTrace_1187776
  have hstable : (prefixWord ++ tailWord_1187776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187776).length < 2 ^ (prefixWord ++ tailWord_1187776).sum := by decide
  have hdescent : baseEnd_1187776 < baseStart_1187776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187793 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 1, 3]
def baseStart_1187793 : Nat := 118140960795 + 1187793 * 2 ^ 59
def prefixEnd_1187793 : Nat := 4983230072969 + 3 ^ 40 * 1187793 * 2
def baseEnd_1187793 : Nat := 406605818030650992083297

theorem tailTrace_1187793 : CollatzResearch.WordTrace tailWord_1187793 prefixEnd_1187793 406605818030650992083297 := by
  unfold tailWord_1187793
  simp only [CollatzResearch.WordTrace]
  refine ⟨43322369785836294739088033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28881579857224196492725355 43322369785836294739088033)
  ·
    refine ⟨32491777339377221054316025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43322369785836294739088033 32491777339377221054316025)
    ·
      refine ⟨24368833004532915790737019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32491777339377221054316025 24368833004532915790737019)
      ·
        refine ⟨36553249506799373686105529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24368833004532915790737019 36553249506799373686105529)
        ·
          refine ⟨27414937130099530264579147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36553249506799373686105529 27414937130099530264579147)
          ·
            refine ⟨41122405695149295396868721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27414937130099530264579147 41122405695149295396868721)
            ·
              refine ⟨30841804271361971547651541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41122405695149295396868721 30841804271361971547651541)
              ·
                refine ⟨722854787610046208148083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30841804271361971547651541 722854787610046208148083)
                ·
                  refine ⟨1084282181415069312222125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722854787610046208148083 1084282181415069312222125)
                  ·
                    refine ⟨406605818030650992083297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084282181415069312222125 406605818030650992083297)
                    ·
                      rfl

theorem cell22_1187793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_1187793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187793 prefixEnd_1187793 := by exact prefixLift 1187793
  have htrace : WordTrace (prefixWord ++ tailWord_1187793) baseStart_1187793 baseEnd_1187793 := by
    simpa [prefixWord, tailWord_1187793, baseEnd_1187793] using wordTrace_append hprefix tailTrace_1187793
  have hstable : (prefixWord ++ tailWord_1187793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187793).length < 2 ^ (prefixWord ++ tailWord_1187793).sum := by decide
  have hdescent : baseEnd_1187793 < baseStart_1187793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187836 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1187836 : Nat := 118140960795 + 1187836 * 2 ^ 59
def prefixEnd_1187836 : Nat := 4983230072969 + 3 ^ 40 * 1187836 * 2
def baseEnd_1187836 : Nat := 406620537809413213258165

theorem tailTrace_1187836 : CollatzResearch.WordTrace tailWord_1187836 prefixEnd_1187836 406620537809413213258165 := by
  unfold tailWord_1187836
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661969062340256541451681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28882625416453675388602241 21661969062340256541451681)
  ·
    refine ⟨16246476796755192406088761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21661969062340256541451681 16246476796755192406088761)
    ·
      refine ⟨12184857597566394304566571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16246476796755192406088761 12184857597566394304566571)
      ·
        refine ⟨18277286396349591456849857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12184857597566394304566571 18277286396349591456849857)
        ·
          refine ⟨13707964797262193592637393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18277286396349591456849857 13707964797262193592637393)
          ·
            refine ⟨10280973597946645194478045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13707964797262193592637393 10280973597946645194478045)
            ·
              refine ⟨3855365099229991947929267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10280973597946645194478045 3855365099229991947929267)
              ·
                refine ⟨5783047648844987921893901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855365099229991947929267 5783047648844987921893901)
                ·
                  refine ⟨2168642868316870470710213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5783047648844987921893901 2168642868316870470710213)
                  ·
                    refine ⟨406620537809413213258165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168642868316870470710213 406620537809413213258165)
                    ·
                      rfl

theorem cell22_1187836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1187836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187836 prefixEnd_1187836 := by exact prefixLift 1187836
  have htrace : WordTrace (prefixWord ++ tailWord_1187836) baseStart_1187836 baseEnd_1187836 := by
    simpa [prefixWord, tailWord_1187836, baseEnd_1187836] using wordTrace_append hprefix tailTrace_1187836
  have hstable : (prefixWord ++ tailWord_1187836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187836).length < 2 ^ (prefixWord ++ tailWord_1187836).sum := by decide
  have hdescent : baseEnd_1187836 < baseStart_1187836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187902 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1187902 : Nat := 118140960795 + 1187902 * 2 ^ 59
def prefixEnd_1187902 : Nat := 4983230072969 + 3 ^ 40 * 1187902 * 2
def baseEnd_1187902 : Nat := 135547710319403680369321

theorem tailTrace_1187902 : CollatzResearch.WordTrace tailWord_1187902 prefixEnd_1187902 135547710319403680369321 := by
  unfold tailWord_1187902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415793167805175794350745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28884230228294270903203973 5415793167805175794350745)
  ·
    refine ⟨4061844875853881845763059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5415793167805175794350745 4061844875853881845763059)
    ·
      refine ⟨6092767313780822768644589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061844875853881845763059 6092767313780822768644589)
      ·
        refine ⟨2284787742667808538241721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6092767313780822768644589 2284787742667808538241721)
        ·
          refine ⟨1713590807000856403681291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284787742667808538241721 1713590807000856403681291)
          ·
            refine ⟨2570386210501284605521937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713590807000856403681291 2570386210501284605521937)
            ·
              refine ⟨1927789657875963454141453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570386210501284605521937 1927789657875963454141453)
              ·
                refine ⟨722921121703486295303045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1927789657875963454141453 722921121703486295303045)
                ·
                  refine ⟨135547710319403680369321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722921121703486295303045 135547710319403680369321)
                  ·
                    rfl

theorem cell22_1187902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1187902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187902 prefixEnd_1187902 := by exact prefixLift 1187902
  have htrace : WordTrace (prefixWord ++ tailWord_1187902) baseStart_1187902 baseEnd_1187902 := by
    simpa [prefixWord, tailWord_1187902, baseEnd_1187902] using wordTrace_append hprefix tailTrace_1187902
  have hstable : (prefixWord ++ tailWord_1187902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187902).length < 2 ^ (prefixWord ++ tailWord_1187902).sum := by decide
  have hdescent : baseEnd_1187902 < baseStart_1187902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187928 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1187928 : Nat := 118140960795 + 1187928 * 2 ^ 59
def prefixEnd_1187928 : Nat := 4983230072969 + 3 ^ 40 * 1187928 * 2
def baseEnd_1187928 : Nat := 406652031289555639957883

theorem tailTrace_1187928 : CollatzResearch.WordTrace tailWord_1187928 prefixEnd_1187928 406652031289555639957883 := by
  unfold tailWord_1187928
  simp only [CollatzResearch.WordTrace]
  refine ⟨21663646820173606397626219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28884862426898141863501625 21663646820173606397626219)
  ·
    refine ⟨32495470230260409596439329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21663646820173606397626219 32495470230260409596439329)
    ·
      refine ⟨24371602672695307197329497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32495470230260409596439329 24371602672695307197329497)
      ·
        refine ⟨18278702004521480397997123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24371602672695307197329497 18278702004521480397997123)
        ·
          refine ⟨27418053006782220596995685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18278702004521480397997123 27418053006782220596995685)
          ·
            refine ⟨5140884938771666361936691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27418053006782220596995685 5140884938771666361936691)
            ·
              refine ⟨7711327408157499542905037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140884938771666361936691 7711327408157499542905037)
              ·
                refine ⟨2891747778059062328589389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7711327408157499542905037 2891747778059062328589389)
                ·
                  refine ⟨1084405416772148373221021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2891747778059062328589389 1084405416772148373221021)
                  ·
                    refine ⟨406652031289555639957883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084405416772148373221021 406652031289555639957883)
                    ·
                      rfl

theorem cell22_1187928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1187928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187928 prefixEnd_1187928 := by exact prefixLift 1187928
  have htrace : WordTrace (prefixWord ++ tailWord_1187928) baseStart_1187928 baseEnd_1187928 := by
    simpa [prefixWord, tailWord_1187928, baseEnd_1187928] using wordTrace_append hprefix tailTrace_1187928
  have hstable : (prefixWord ++ tailWord_1187928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187928).length < 2 ^ (prefixWord ++ tailWord_1187928).sum := by decide
  have hdescent : baseEnd_1187928 < baseStart_1187928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187934 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1187934 : Nat := 118140960795 + 1187934 * 2 ^ 59
def prefixEnd_1187934 : Nat := 4983230072969 + 3 ^ 40 * 1187934 * 2
def baseEnd_1187934 : Nat := 406654085212173624307865

theorem tailTrace_1187934 : CollatzResearch.WordTrace tailWord_1187934 prefixEnd_1187934 406654085212173624307865 := by
  unfold tailWord_1187934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415939059790684477496357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28885008318883650546647237 5415939059790684477496357)
  ·
    refine ⟨1015488573710753339530567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5415939059790684477496357 1015488573710753339530567)
    ·
      refine ⟨1523232860566130009295851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015488573710753339530567 1523232860566130009295851)
      ·
        refine ⟨2284849290849195013943777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523232860566130009295851 2284849290849195013943777)
        ·
          refine ⟨1713636968136896260457833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284849290849195013943777 1713636968136896260457833)
          ·
            refine ⟨1285227726102672195343375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713636968136896260457833 1285227726102672195343375)
            ·
              refine ⟨1927841589154008293015063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285227726102672195343375 1927841589154008293015063)
              ·
                refine ⟨2891762383731012439522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927841589154008293015063 2891762383731012439522595)
                ·
                  refine ⟨4337643575596518659283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891762383731012439522595 4337643575596518659283893)
                  ·
                    refine ⟨406654085212173624307865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4337643575596518659283893 406654085212173624307865)
                    ·
                      rfl

theorem cell22_1187934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1187934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187934 prefixEnd_1187934 := by exact prefixLift 1187934
  have htrace : WordTrace (prefixWord ++ tailWord_1187934) baseStart_1187934 baseEnd_1187934 := by
    simpa [prefixWord, tailWord_1187934, baseEnd_1187934] using wordTrace_append hprefix tailTrace_1187934
  have hstable : (prefixWord ++ tailWord_1187934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187934).length < 2 ^ (prefixWord ++ tailWord_1187934).sum := by decide
  have hdescent : baseEnd_1187934 < baseStart_1187934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187958 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1187958 : Nat := 118140960795 + 1187958 * 2 ^ 59
def prefixEnd_1187958 : Nat := 4983230072969 + 3 ^ 40 * 1187958 * 2
def baseEnd_1187958 : Nat := 135554100300881853902597

theorem tailTrace_1187958 : CollatzResearch.WordTrace tailWord_1187958 prefixEnd_1187958 135554100300881853902597 := by
  unfold tailWord_1187958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708024239389907994927783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28885591886825685279229685 2708024239389907994927783)
  ·
    refine ⟨4062036359084861992391675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2708024239389907994927783 4062036359084861992391675)
    ·
      refine ⟨6093054538627292988587513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062036359084861992391675 6093054538627292988587513)
      ·
        refine ⟨4569790903970469741440635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6093054538627292988587513 4569790903970469741440635)
        ·
          refine ⟨6854686355955704612160953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569790903970469741440635 6854686355955704612160953)
          ·
            refine ⟨5141014766966778459120715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6854686355955704612160953 5141014766966778459120715)
            ·
              refine ⟨7711522150450167688681073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141014766966778459120715 7711522150450167688681073)
              ·
                refine ⟨5783641612837625766510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7711522150450167688681073 5783641612837625766510805)
                ·
                  refine ⟨135554100300881853902597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5783641612837625766510805 135554100300881853902597)
                  ·
                    rfl

theorem cell22_1187958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1187958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187958 prefixEnd_1187958 := by exact prefixLift 1187958
  have htrace : WordTrace (prefixWord ++ tailWord_1187958) baseStart_1187958 baseEnd_1187958 := by
    simpa [prefixWord, tailWord_1187958, baseEnd_1187958] using wordTrace_append hprefix tailTrace_1187958
  have hstable : (prefixWord ++ tailWord_1187958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187958).length < 2 ^ (prefixWord ++ tailWord_1187958).sum := by decide
  have hdescent : baseEnd_1187958 < baseStart_1187958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187992 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_1187992 : Nat := 118140960795 + 1187992 * 2 ^ 59
def prefixEnd_1187992 : Nat := 4983230072969 + 3 ^ 40 * 1187992 * 2
def baseEnd_1187992 : Nat := 135557979932493602119229

theorem tailTrace_1187992 : CollatzResearch.WordTrace tailWord_1187992 prefixEnd_1187992 135557979932493602119229 := by
  unfold tailWord_1187992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664813956057675862791115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28886418608076901150388153 21664813956057675862791115)
  ·
    refine ⟨32497220934086513794186673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21664813956057675862791115 32497220934086513794186673)
    ·
      refine ⟨24372915700564885345640005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32497220934086513794186673 24372915700564885345640005)
      ·
        refine ⟨4569921693855916002307501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24372915700564885345640005 4569921693855916002307501)
        ·
          refine ⟨1713720635195968500865313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4569921693855916002307501 1713720635195968500865313)
          ·
            refine ⟨1285290476396976375648985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713720635195968500865313 1285290476396976375648985)
            ·
              refine ⟨963967857297732281736739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285290476396976375648985 963967857297732281736739)
              ·
                refine ⟨1445951785946598422605109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963967857297732281736739 1445951785946598422605109)
                ·
                  refine ⟨135557979932493602119229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1445951785946598422605109 135557979932493602119229)
                  ·
                    rfl

theorem cell22_1187992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_1187992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187992 prefixEnd_1187992 := by exact prefixLift 1187992
  have htrace : WordTrace (prefixWord ++ tailWord_1187992) baseStart_1187992 baseEnd_1187992 := by
    simpa [prefixWord, tailWord_1187992, baseEnd_1187992] using wordTrace_append hprefix tailTrace_1187992
  have hstable : (prefixWord ++ tailWord_1187992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187992).length < 2 ^ (prefixWord ++ tailWord_1187992).sum := by decide
  have hdescent : baseEnd_1187992 < baseStart_1187992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188018 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1188018 : Nat := 118140960795 + 1188018 * 2 ^ 59
def prefixEnd_1188018 : Nat := 4983230072969 + 3 ^ 40 * 1188018 * 2
def baseEnd_1188018 : Nat := 406682840128825405207607

theorem tailTrace_1188018 : CollatzResearch.WordTrace tailWord_1188018 prefixEnd_1188018 406682840128825405207607 := by
  unfold tailWord_1188018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832644052505289541507177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28887050806680772110685805 10832644052505289541507177)
  ·
    refine ⟨8124483039378967156130383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10832644052505289541507177 8124483039378967156130383)
    ·
      refine ⟨12186724559068450734195575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124483039378967156130383 12186724559068450734195575)
      ·
        refine ⟨18280086838602676101293363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12186724559068450734195575 18280086838602676101293363)
        ·
          refine ⟨27420130257904014151940045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18280086838602676101293363 27420130257904014151940045)
          ·
            refine ⟨10282548846714005306977517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27420130257904014151940045 10282548846714005306977517)
            ·
              refine ⟨3855955817517751990116569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10282548846714005306977517 3855955817517751990116569)
              ·
                refine ⟨2891966863138313992587427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855955817517751990116569 2891966863138313992587427)
                ·
                  refine ⟨4337950294707470988881141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891966863138313992587427 4337950294707470988881141)
                  ·
                    refine ⟨406682840128825405207607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4337950294707470988881141 406682840128825405207607)
                    ·
                      rfl

theorem cell22_1188018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1188018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188018 prefixEnd_1188018 := by exact prefixLift 1188018
  have htrace : WordTrace (prefixWord ++ tailWord_1188018) baseStart_1188018 baseEnd_1188018 := by
    simpa [prefixWord, tailWord_1188018, baseEnd_1188018] using wordTrace_append hprefix tailTrace_1188018
  have hstable : (prefixWord ++ tailWord_1188018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188018).length < 2 ^ (prefixWord ++ tailWord_1188018).sum := by decide
  have hdescent : baseEnd_1188018 < baseStart_1188018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188097 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1188097 : Nat := 118140960795 + 1188097 * 2 ^ 59
def prefixEnd_1188097 : Nat := 4983230072969 + 3 ^ 40 * 1188097 * 2
def baseEnd_1188097 : Nat := 406709883443295532482365

theorem tailTrace_1188097 : CollatzResearch.WordTrace tailWord_1188097 prefixEnd_1188097 406709883443295532482365 := by
  unfold tailWord_1188097
  simp only [CollatzResearch.WordTrace]
  refine ⟨43333457576734954658154545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28888971717823303105436363 43333457576734954658154545)
  ·
    refine ⟨32500093182551215993615909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43333457576734954658154545 32500093182551215993615909)
    ·
      refine ⟨6093767471728352998802983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32500093182551215993615909 6093767471728352998802983)
      ·
        refine ⟨9140651207592529498204475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6093767471728352998802983 9140651207592529498204475)
        ·
          refine ⟨13710976811388794247306713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9140651207592529498204475 13710976811388794247306713)
          ·
            refine ⟨10283232608541595685480035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13710976811388794247306713 10283232608541595685480035)
            ·
              refine ⟨15424848912812393528220053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283232608541595685480035 15424848912812393528220053)
              ·
                refine ⟨723039792788080946635315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15424848912812393528220053 723039792788080946635315)
                ·
                  refine ⟨1084559689182121419952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723039792788080946635315 1084559689182121419952973)
                  ·
                    refine ⟨406709883443295532482365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084559689182121419952973 406709883443295532482365)
                    ·
                      rfl

theorem cell22_1188097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1188097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188097 prefixEnd_1188097 := by exact prefixLift 1188097
  have htrace : WordTrace (prefixWord ++ tailWord_1188097) baseStart_1188097 baseEnd_1188097 := by
    simpa [prefixWord, tailWord_1188097, baseEnd_1188097] using wordTrace_append hprefix tailTrace_1188097
  have hstable : (prefixWord ++ tailWord_1188097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188097).length < 2 ^ (prefixWord ++ tailWord_1188097).sum := by decide
  have hdescent : baseEnd_1188097 < baseStart_1188097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188108 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1188108 : Nat := 118140960795 + 1188108 * 2 ^ 59
def prefixEnd_1188108 : Nat := 4983230072969 + 3 ^ 40 * 1188108 * 2
def baseEnd_1188108 : Nat := 406713648968095170457331

theorem tailTrace_1188108 : CollatzResearch.WordTrace tailWord_1188108 prefixEnd_1188108 406713648968095170457331 := by
  unfold tailWord_1188108
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666929389847551768402489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28889239186463402357869985 21666929389847551768402489)
  ·
    refine ⟨16250197042385663826301867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21666929389847551768402489 16250197042385663826301867)
    ·
      refine ⟨24375295563578495739452801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16250197042385663826301867 24375295563578495739452801)
      ·
        refine ⟨18281471672683871804589601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24375295563578495739452801 18281471672683871804589601)
        ·
          refine ⟨13711103754512903853442201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18281471672683871804589601 13711103754512903853442201)
          ·
            refine ⟨10283327815884677890081651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13711103754512903853442201 10283327815884677890081651)
            ·
              refine ⟨15424991723827016835122477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283327815884677890081651 15424991723827016835122477)
              ·
                refine ⟨5784371896435131313170929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15424991723827016835122477 5784371896435131313170929)
                ·
                  refine ⟨4338278922326348484878197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5784371896435131313170929 4338278922326348484878197)
                  ·
                    refine ⟨406713648968095170457331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4338278922326348484878197 406713648968095170457331)
                    ·
                      rfl

theorem cell22_1188108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1188108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188108 prefixEnd_1188108 := by exact prefixLift 1188108
  have htrace : WordTrace (prefixWord ++ tailWord_1188108) baseStart_1188108 baseEnd_1188108 := by
    simpa [prefixWord, tailWord_1188108, baseEnd_1188108] using wordTrace_append hprefix tailTrace_1188108
  have hstable : (prefixWord ++ tailWord_1188108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188108).length < 2 ^ (prefixWord ++ tailWord_1188108).sum := by decide
  have hdescent : baseEnd_1188108 < baseStart_1188108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188123 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_1188123 : Nat := 118140960795 + 1188123 * 2 ^ 59
def prefixEnd_1188123 : Nat := 4983230072969 + 3 ^ 40 * 1188123 * 2
def baseEnd_1188123 : Nat := 406718783774640131332285

theorem tailTrace_1188123 : CollatzResearch.WordTrace tailWord_1188123 prefixEnd_1188123 406718783774640131332285 := by
  unfold tailWord_1188123
  simp only [CollatzResearch.WordTrace]
  refine ⟨43334405874640761098601023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28889603916427174065734015 43334405874640761098601023)
  ·
    refine ⟨65001608811961141647901535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43334405874640761098601023 65001608811961141647901535)
    ·
      refine ⟨97502413217941712471852303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65001608811961141647901535 97502413217941712471852303)
      ·
        refine ⟨146253619826912568707778455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97502413217941712471852303 146253619826912568707778455)
        ·
          refine ⟨219380429740368853061667683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146253619826912568707778455 219380429740368853061667683)
          ·
            refine ⟨329070644610553279592501525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219380429740368853061667683 329070644610553279592501525)
            ·
              refine ⟨15425186466119684980898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 329070644610553279592501525 15425186466119684980898509)
              ·
                refine ⟨5784444924794881867836941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15425186466119684980898509 5784444924794881867836941)
                ·
                  refine ⟨2169166846798080700438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5784444924794881867836941 2169166846798080700438853)
                  ·
                    refine ⟨406718783774640131332285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169166846798080700438853 406718783774640131332285)
                    ·
                      rfl

theorem cell22_1188123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_1188123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188123 prefixEnd_1188123 := by exact prefixLift 1188123
  have htrace : WordTrace (prefixWord ++ tailWord_1188123) baseStart_1188123 baseEnd_1188123 := by
    simpa [prefixWord, tailWord_1188123, baseEnd_1188123] using wordTrace_append hprefix tailTrace_1188123
  have hstable : (prefixWord ++ tailWord_1188123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188123).length < 2 ^ (prefixWord ++ tailWord_1188123).sum := by decide
  have hdescent : baseEnd_1188123 < baseStart_1188123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188140 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_1188140 : Nat := 118140960795 + 1188140 * 2 ^ 59
def prefixEnd_1188140 : Nat := 4983230072969 + 3 ^ 40 * 1188140 * 2
def baseEnd_1188140 : Nat := 406724603222057753657233

theorem tailTrace_1188140 : CollatzResearch.WordTrace tailWord_1188140 prefixEnd_1188140 406724603222057753657233 := by
  unfold tailWord_1188140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21667512957789586500984937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28890017277052782001313249 21667512957789586500984937)
  ·
    refine ⟨16250634718342189875738703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21667512957789586500984937 16250634718342189875738703)
    ·
      refine ⟨24375952077513284813608055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16250634718342189875738703 24375952077513284813608055)
      ·
        refine ⟨36563928116269927220412083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24375952077513284813608055 36563928116269927220412083)
        ·
          refine ⟨54845892174404890830618125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36563928116269927220412083 54845892174404890830618125)
          ·
            refine ⟨20567209565401834061481797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54845892174404890830618125 20567209565401834061481797)
            ·
              refine ⟨3856351793512843886527837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20567209565401834061481797 3856351793512843886527837)
              ·
                refine ⟨1446131922567316457447939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3856351793512843886527837 1446131922567316457447939)
                ·
                  refine ⟨2169197883850974686171909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446131922567316457447939 2169197883850974686171909)
                  ·
                    refine ⟨406724603222057753657233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169197883850974686171909 406724603222057753657233)
                    ·
                      rfl

theorem cell22_1188140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_1188140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188140 prefixEnd_1188140 := by exact prefixLift 1188140
  have htrace : WordTrace (prefixWord ++ tailWord_1188140) baseStart_1188140 baseEnd_1188140 := by
    simpa [prefixWord, tailWord_1188140, baseEnd_1188140] using wordTrace_append hprefix tailTrace_1188140
  have hstable : (prefixWord ++ tailWord_1188140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188140).length < 2 ^ (prefixWord ++ tailWord_1188140).sum := by decide
  have hdescent : baseEnd_1188140 < baseStart_1188140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188161 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 5]
def baseStart_1188161 : Nat := 118140960795 + 1188161 * 2 ^ 59
def prefixEnd_1188161 : Nat := 4983230072969 + 3 ^ 40 * 1188161 * 2
def baseEnd_1188161 : Nat := 135577263983740232960723

theorem tailTrace_1188161 : CollatzResearch.WordTrace tailWord_1188161 prefixEnd_1188161 135577263983740232960723 := by
  unfold tailWord_1188161
  simp only [CollatzResearch.WordTrace]
  refine ⟨43335791848503093588484337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28890527899002062392322891 43335791848503093588484337)
  ·
    refine ⟨32501843886377320191363253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43335791848503093588484337 32501843886377320191363253)
    ·
      refine ⟨3047047864347873767940305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32501843886377320191363253 3047047864347873767940305)
      ·
        refine ⟨2285285898260905325955229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3047047864347873767940305 2285285898260905325955229)
        ·
          refine ⟨856982211847839497233211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2285285898260905325955229 856982211847839497233211)
          ·
            refine ⟨1285473317771759245849817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856982211847839497233211 1285473317771759245849817)
            ·
              refine ⟨964104988328819434387363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285473317771759245849817 964104988328819434387363)
              ·
                refine ⟨1446157482493229151581045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964104988328819434387363 1446157482493229151581045)
                ·
                  refine ⟨135577263983740232960723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1446157482493229151581045 135577263983740232960723)
                  ·
                    rfl

theorem cell22_1188161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_1188161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188161 prefixEnd_1188161 := by exact prefixLift 1188161
  have htrace : WordTrace (prefixWord ++ tailWord_1188161) baseStart_1188161 baseEnd_1188161 := by
    simpa [prefixWord, tailWord_1188161, baseEnd_1188161] using wordTrace_append hprefix tailTrace_1188161
  have hstable : (prefixWord ++ tailWord_1188161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188161).length < 2 ^ (prefixWord ++ tailWord_1188161).sum := by decide
  have hdescent : baseEnd_1188161 < baseStart_1188161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188168 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1188168 : Nat := 118140960795 + 1188168 * 2 ^ 59
def prefixEnd_1188168 : Nat := 4983230072969 + 3 ^ 40 * 1188168 * 2
def baseEnd_1188168 : Nat := 406734188194275013957147

theorem tailTrace_1188168 : CollatzResearch.WordTrace tailWord_1188168 prefixEnd_1188168 406734188194275013957147 := by
  unfold tailWord_1188168
  simp only [CollatzResearch.WordTrace]
  refine ⟨21668023579738866891994579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28890698106318489189326105 21668023579738866891994579)
  ·
    refine ⟨32502035369608300337991869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21668023579738866891994579 32502035369608300337991869)
    ·
      refine ⟨12188263263603112626746951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32502035369608300337991869 12188263263603112626746951)
      ·
        refine ⟨18282394895404668940120427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12188263263603112626746951 18282394895404668940120427)
        ·
          refine ⟨27423592343107003410180641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18282394895404668940120427 27423592343107003410180641)
          ·
            refine ⟨20567694257330252557635481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27423592343107003410180641 20567694257330252557635481)
            ·
              refine ⟨15425770692997689418226611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20567694257330252557635481 15425770692997689418226611)
              ·
                refine ⟨23138656039496534127339917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15425770692997689418226611 23138656039496534127339917)
                ·
                  refine ⟨8676996014811200297752469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23138656039496534127339917 8676996014811200297752469)
                  ·
                    refine ⟨406734188194275013957147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8676996014811200297752469 406734188194275013957147)
                    ·
                      rfl

theorem cell22_1188168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1188168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188168 prefixEnd_1188168 := by exact prefixLift 1188168
  have htrace : WordTrace (prefixWord ++ tailWord_1188168) baseStart_1188168 baseEnd_1188168 := by
    simpa [prefixWord, tailWord_1188168, baseEnd_1188168] using wordTrace_append hprefix tailTrace_1188168
  have hstable : (prefixWord ++ tailWord_1188168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188168).length < 2 ^ (prefixWord ++ tailWord_1188168).sum := by decide
  have hdescent : baseEnd_1188168 < baseStart_1188168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188183 : List Nat := [1, 1, 3, 2, 3, 1, 1, 10]
def baseStart_1188183 : Nat := 118140960795 + 1188183 * 2 ^ 59
def prefixEnd_1188183 : Nat := 4983230072969 + 3 ^ 40 * 1188183 * 2
def baseEnd_1188183 : Nat := 45193258111202219425789

theorem tailTrace_1188183 : CollatzResearch.WordTrace tailWord_1188183 prefixEnd_1188183 45193258111202219425789 := by
  unfold tailWord_1188183
  simp only [CollatzResearch.WordTrace]
  refine ⟨43336594254423391345785203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28891062836282260897190135 43336594254423391345785203)
  ·
    refine ⟨65004891381635087018677805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43336594254423391345785203 65004891381635087018677805)
    ·
      refine ⟨24376834268113157632004177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65004891381635087018677805 24376834268113157632004177)
      ·
        refine ⟨18282625701084868224003133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24376834268113157632004177 18282625701084868224003133)
        ·
          refine ⟨6855984637906825584001175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18282625701084868224003133 6855984637906825584001175)
          ·
            refine ⟨10283976956860238376001763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6855984637906825584001175 10283976956860238376001763)
            ·
              refine ⟨15425965435290357564002645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283976956860238376001763 15425965435290357564002645)
              ·
                refine ⟨45193258111202219425789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15425965435290357564002645 45193258111202219425789)
                ·
                  rfl

theorem cell22_1188183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 10].length) (baseStart_1188183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188183 prefixEnd_1188183 := by exact prefixLift 1188183
  have htrace : WordTrace (prefixWord ++ tailWord_1188183) baseStart_1188183 baseEnd_1188183 := by
    simpa [prefixWord, tailWord_1188183, baseEnd_1188183] using wordTrace_append hprefix tailTrace_1188183
  have hstable : (prefixWord ++ tailWord_1188183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188183).length < 2 ^ (prefixWord ++ tailWord_1188183).sum := by decide
  have hdescent : baseEnd_1188183 < baseStart_1188183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188202 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1188202 : Nat := 118140960795 + 1188202 * 2 ^ 59
def prefixEnd_1188202 : Nat := 4983230072969 + 3 ^ 40 * 1188202 * 2
def baseEnd_1188202 : Nat := 406745827089110258607043

theorem tailTrace_1188202 : CollatzResearch.WordTrace tailWord_1188202 prefixEnd_1188202 406745827089110258607043 := by
  unfold tailWord_1188202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834321810338639397681715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28891524827569705060484573 10834321810338639397681715)
  ·
    refine ⟨16251482715507959096522573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10834321810338639397681715 16251482715507959096522573)
    ·
      refine ⟨6094306018315484661195965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16251482715507959096522573 6094306018315484661195965)
      ·
        refine ⟨2285364756868306747948487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6094306018315484661195965 2285364756868306747948487)
        ·
          refine ⟨3428047135302460121922731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285364756868306747948487 3428047135302460121922731)
          ·
            refine ⟨5142070702953690182884097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428047135302460121922731 5142070702953690182884097)
            ·
              refine ⟨3856553027215267637163073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5142070702953690182884097 3856553027215267637163073)
              ·
                refine ⟨2892414770411450727872305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856553027215267637163073 2892414770411450727872305)
                ·
                  refine ⟨2169311077808588045904229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892414770411450727872305 2169311077808588045904229)
                  ·
                    refine ⟨406745827089110258607043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169311077808588045904229 406745827089110258607043)
                    ·
                      rfl

theorem cell22_1188202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1188202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188202 prefixEnd_1188202 := by exact prefixLift 1188202
  have htrace : WordTrace (prefixWord ++ tailWord_1188202) baseStart_1188202 baseEnd_1188202 := by
    simpa [prefixWord, tailWord_1188202, baseEnd_1188202] using wordTrace_append hprefix tailTrace_1188202
  have hstable : (prefixWord ++ tailWord_1188202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188202).length < 2 ^ (prefixWord ++ tailWord_1188202).sum := by decide
  have hdescent : baseEnd_1188202 < baseStart_1188202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188204 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_1188204 : Nat := 118140960795 + 1188204 * 2 ^ 59
def prefixEnd_1188204 : Nat := 4983230072969 + 3 ^ 40 * 1188204 * 2
def baseEnd_1188204 : Nat := 406746511729982920057037

theorem tailTrace_1188204 : CollatzResearch.WordTrace tailWord_1188204 prefixEnd_1188204 406746511729982920057037 := by
  unfold tailWord_1188204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21668680093673655966149833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28891573458231541288199777 21668680093673655966149833)
  ·
    refine ⟨16251510070255241974612375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21668680093673655966149833 16251510070255241974612375)
    ·
      refine ⟨24377265105382862961918563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16251510070255241974612375 24377265105382862961918563)
      ·
        refine ⟨36565897658074294442877845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24377265105382862961918563 36565897658074294442877845)
        ·
          refine ⟨1714026452722232552009899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36565897658074294442877845 1714026452722232552009899)
          ·
            refine ⟨2571039679083348828014849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714026452722232552009899 2571039679083348828014849)
            ·
              refine ⟨1928279759312511621011137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571039679083348828014849 1928279759312511621011137)
              ·
                refine ⟨1446209819484383715758353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928279759312511621011137 1446209819484383715758353)
                ·
                  refine ⟨1084657364613287786818765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446209819484383715758353 1084657364613287786818765)
                  ·
                    refine ⟨406746511729982920057037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084657364613287786818765 406746511729982920057037)
                    ·
                      rfl

theorem cell22_1188204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_1188204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188204 prefixEnd_1188204 := by exact prefixLift 1188204
  have htrace : WordTrace (prefixWord ++ tailWord_1188204) baseStart_1188204 baseEnd_1188204 := by
    simpa [prefixWord, tailWord_1188204, baseEnd_1188204] using wordTrace_append hprefix tailTrace_1188204
  have hstable : (prefixWord ++ tailWord_1188204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188204).length < 2 ^ (prefixWord ++ tailWord_1188204).sum := by decide
  have hdescent : baseEnd_1188204 < baseStart_1188204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188232 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_1188232 : Nat := 118140960795 + 1188232 * 2 ^ 59
def prefixEnd_1188232 : Nat := 4983230072969 + 3 ^ 40 * 1188232 * 2
def baseEnd_1188232 : Nat := 406756096702200180356951

theorem tailTrace_1188232 : CollatzResearch.WordTrace tailWord_1188232 prefixEnd_1188232 406756096702200180356951 := by
  unfold tailWord_1188232
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669190715622936357159475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28892254287497248476212633 21669190715622936357159475)
  ·
    refine ⟨32503786073434404535739213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21669190715622936357159475 32503786073434404535739213)
    ·
      refine ⟨12188919777537901700902205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32503786073434404535739213 12188919777537901700902205)
      ·
        refine ⟨4570844916576713137838327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12188919777537901700902205 4570844916576713137838327)
        ·
          refine ⟨6856267374865069706757491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4570844916576713137838327 6856267374865069706757491)
          ·
            refine ⟨10284401062297604560136237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856267374865069706757491 10284401062297604560136237)
            ·
              refine ⟨3856650398361601710051089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10284401062297604560136237 3856650398361601710051089)
              ·
                refine ⟨2892487798771201282538317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856650398361601710051089 2892487798771201282538317)
                ·
                  refine ⟨1084682924539200480951869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2892487798771201282538317 1084682924539200480951869)
                  ·
                    refine ⟨406756096702200180356951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084682924539200480951869 406756096702200180356951)
                    ·
                      rfl

theorem cell22_1188232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_1188232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188232 prefixEnd_1188232 := by exact prefixLift 1188232
  have htrace : WordTrace (prefixWord ++ tailWord_1188232) baseStart_1188232 baseEnd_1188232 := by
    simpa [prefixWord, tailWord_1188232, baseEnd_1188232] using wordTrace_append hprefix tailTrace_1188232
  have hstable : (prefixWord ++ tailWord_1188232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188232).length < 2 ^ (prefixWord ++ tailWord_1188232).sum := by decide
  have hdescent : baseEnd_1188232 < baseStart_1188232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188234 : List Nat := [3, 1, 2, 5, 1, 1, 3, 6]
def baseStart_1188234 : Nat := 118140960795 + 1188234 * 2 ^ 59
def prefixEnd_1188234 : Nat := 4983230072969 + 3 ^ 40 * 1188234 * 2
def baseEnd_1188234 : Nat := 45195197927008093534105

theorem tailTrace_1188234 : CollatzResearch.WordTrace tailWord_1188234 prefixEnd_1188234 45195197927008093534105 := by
  unfold tailWord_1188234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834613594309656763972939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28892302918159084703927837 10834613594309656763972939)
  ·
    refine ⟨16251920391464485145959409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10834613594309656763972939 16251920391464485145959409)
    ·
      refine ⟨12188940293598363859469557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16251920391464485145959409 12188940293598363859469557)
      ·
        refine ⟨1142713152524846611825271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12188940293598363859469557 1142713152524846611825271)
        ·
          refine ⟨1714069728787269917737907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142713152524846611825271 1714069728787269917737907)
          ·
            refine ⟨2571104593180904876606861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714069728787269917737907 2571104593180904876606861)
            ·
              refine ⟨964164222442839328727573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2571104593180904876606861 964164222442839328727573)
              ·
                refine ⟨45195197927008093534105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 964164222442839328727573 45195197927008093534105)
                ·
                  rfl

theorem cell22_1188234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_1188234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188234 prefixEnd_1188234 := by exact prefixLift 1188234
  have htrace : WordTrace (prefixWord ++ tailWord_1188234) baseStart_1188234 baseEnd_1188234 := by
    simpa [prefixWord, tailWord_1188234, baseEnd_1188234] using wordTrace_append hprefix tailTrace_1188234
  have hstable : (prefixWord ++ tailWord_1188234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188234).length < 2 ^ (prefixWord ++ tailWord_1188234).sum := by decide
  have hdescent : baseEnd_1188234 < baseStart_1188234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188249 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 1, 3]
def baseStart_1188249 : Nat := 118140960795 + 1188249 * 2 ^ 59
def prefixEnd_1188249 : Nat := 4983230072969 + 3 ^ 40 * 1188249 * 2
def baseEnd_1188249 : Nat := 406761916149617802681899

theorem tailTrace_1188249 : CollatzResearch.WordTrace tailWord_1188249 prefixEnd_1188249 406761916149617802681899 := by
  unfold tailWord_1188249
  simp only [CollatzResearch.WordTrace]
  refine ⟨43339001472184284617687801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28892667648122856411791867 43339001472184284617687801)
  ·
    refine ⟨32504251104138213463265851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43339001472184284617687801 32504251104138213463265851)
    ·
      refine ⟨48756376656207320194898777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32504251104138213463265851 48756376656207320194898777)
      ·
        refine ⟨36567282492155490146174083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48756376656207320194898777 36567282492155490146174083)
        ·
          refine ⟨54850923738233235219261125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36567282492155490146174083 54850923738233235219261125)
          ·
            refine ⟨10284548200918731603611461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54850923738233235219261125 10284548200918731603611461)
            ·
              refine ⟨1928352787672262175677149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10284548200918731603611461 1928352787672262175677149)
              ·
                refine ⟨723132295377098315878931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1928352787672262175677149 723132295377098315878931)
                ·
                  refine ⟨1084698443065647473818397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723132295377098315878931 1084698443065647473818397)
                  ·
                    refine ⟨406761916149617802681899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084698443065647473818397 406761916149617802681899)
                    ·
                      rfl

theorem cell22_1188249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_1188249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188249 prefixEnd_1188249 := by exact prefixLift 1188249
  have htrace : WordTrace (prefixWord ++ tailWord_1188249) baseStart_1188249 baseEnd_1188249 := by
    simpa [prefixWord, tailWord_1188249, baseEnd_1188249] using wordTrace_append hprefix tailTrace_1188249
  have hstable : (prefixWord ++ tailWord_1188249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188249).length < 2 ^ (prefixWord ++ tailWord_1188249).sum := by decide
  have hdescent : baseEnd_1188249 < baseStart_1188249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188260 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1188260 : Nat := 118140960795 + 1188260 * 2 ^ 59
def prefixEnd_1188260 : Nat := 4983230072969 + 3 ^ 40 * 1188260 * 2
def baseEnd_1188260 : Nat := 406765681674417440656865

theorem tailTrace_1188260 : CollatzResearch.WordTrace tailWord_1188260 prefixEnd_1188260 406765681674417440656865 := by
  unfold tailWord_1188260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669701337572216748169117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28892935116762955664225489 21669701337572216748169117)
  ·
    refine ⟨8126138001589581280563419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21669701337572216748169117 8126138001589581280563419)
    ·
      refine ⟨12189207002384371920845129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8126138001589581280563419 12189207002384371920845129)
      ·
        refine ⟨9141905251788278940633847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12189207002384371920845129 9141905251788278940633847)
        ·
          refine ⟨13712857877682418410950771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9141905251788278940633847 13712857877682418410950771)
          ·
            refine ⟨20569286816523627616426157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13712857877682418410950771 20569286816523627616426157)
            ·
              refine ⟨7713482556196360356159809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20569286816523627616426157 7713482556196360356159809)
              ·
                refine ⟨5785111917147270267119857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7713482556196360356159809 5785111917147270267119857)
                ·
                  refine ⟨4338833937860452700339893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785111917147270267119857 4338833937860452700339893)
                  ·
                    refine ⟨406765681674417440656865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4338833937860452700339893 406765681674417440656865)
                    ·
                      rfl

theorem cell22_1188260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1188260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188260 prefixEnd_1188260 := by exact prefixLift 1188260
  have htrace : WordTrace (prefixWord ++ tailWord_1188260) baseStart_1188260 baseEnd_1188260 := by
    simpa [prefixWord, tailWord_1188260, baseEnd_1188260] using wordTrace_append hprefix tailTrace_1188260
  have hstable : (prefixWord ++ tailWord_1188260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188260).length < 2 ^ (prefixWord ++ tailWord_1188260).sum := by decide
  have hdescent : baseEnd_1188260 < baseStart_1188260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188305 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_1188305 : Nat := 118140960795 + 1188305 * 2 ^ 59
def prefixEnd_1188305 : Nat := 4983230072969 + 3 ^ 40 * 1188305 * 2
def baseEnd_1188305 : Nat := 406781086094052323281727

theorem tailTrace_1188305 : CollatzResearch.WordTrace tailWord_1188305 prefixEnd_1188305 406781086094052323281727 := by
  unfold tailWord_1188305
  simp only [CollatzResearch.WordTrace]
  refine ⟨43341043959981406181726369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28894029306654270787817579 43341043959981406181726369)
  ·
    refine ⟨32505782969986054636294777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43341043959981406181726369 32505782969986054636294777)
    ·
      refine ⟨24379337227489540977221083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32505782969986054636294777 24379337227489540977221083)
      ·
        refine ⟨36569005841234311465831625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24379337227489540977221083 36569005841234311465831625)
        ·
          refine ⟨27426754380925733599373719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36569005841234311465831625 27426754380925733599373719)
          ·
            refine ⟨41140131571388600399060579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27426754380925733599373719 41140131571388600399060579)
            ·
              refine ⟨61710197357082900598590869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41140131571388600399060579 61710197357082900598590869)
              ·
                refine ⟨2892665501113260965558947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61710197357082900598590869 2892665501113260965558947)
                ·
                  refine ⟨4338998251669891448338421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892665501113260965558947 4338998251669891448338421)
                  ·
                    refine ⟨406781086094052323281727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4338998251669891448338421 406781086094052323281727)
                    ·
                      rfl

theorem cell22_1188305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_1188305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188305 prefixEnd_1188305 := by exact prefixLift 1188305
  have htrace : WordTrace (prefixWord ++ tailWord_1188305) baseStart_1188305 baseEnd_1188305 := by
    simpa [prefixWord, tailWord_1188305, baseEnd_1188305] using wordTrace_append hprefix tailTrace_1188305
  have hstable : (prefixWord ++ tailWord_1188305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188305).length < 2 ^ (prefixWord ++ tailWord_1188305).sum := by decide
  have hdescent : baseEnd_1188305 < baseStart_1188305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188375 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 4]
def baseStart_1188375 : Nat := 118140960795 + 1188375 * 2 ^ 59
def prefixEnd_1188375 : Nat := 4983230072969 + 3 ^ 40 * 1188375 * 2
def baseEnd_1188375 : Nat := 135601682841531824677171

theorem tailTrace_1188375 : CollatzResearch.WordTrace tailWord_1188375 prefixEnd_1188375 135601682841531824677171 := by
  unfold tailWord_1188375
  simp only [CollatzResearch.WordTrace]
  refine ⟨43343597069727808136774579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28895731379818538757849719 43343597069727808136774579)
  ·
    refine ⟨65015395604591712205161869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43343597069727808136774579 65015395604591712205161869)
    ·
      refine ⟨24380773351721892076935701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65015395604591712205161869 24380773351721892076935701)
      ·
        refine ⟨1142848750861963691106361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24380773351721892076935701 1142848750861963691106361)
        ·
          refine ⟨857136563146472768329771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142848750861963691106361 857136563146472768329771)
          ·
            refine ⟨1285704844719709152494657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857136563146472768329771 1285704844719709152494657)
            ·
              refine ⟨964278633539781864370993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285704844719709152494657 964278633539781864370993)
              ·
                refine ⟨723208975154836398278245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964278633539781864370993 723208975154836398278245)
                ·
                  refine ⟨135601682841531824677171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723208975154836398278245 135601682841531824677171)
                  ·
                    rfl

theorem cell22_1188375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 4].length) (baseStart_1188375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188375 prefixEnd_1188375 := by exact prefixLift 1188375
  have htrace : WordTrace (prefixWord ++ tailWord_1188375) baseStart_1188375 baseEnd_1188375 := by
    simpa [prefixWord, tailWord_1188375, baseEnd_1188375] using wordTrace_append hprefix tailTrace_1188375
  have hstable : (prefixWord ++ tailWord_1188375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188375).length < 2 ^ (prefixWord ++ tailWord_1188375).sum := by decide
  have hdescent : baseEnd_1188375 < baseStart_1188375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188429 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1188429 : Nat := 118140960795 + 1188429 * 2 ^ 59
def prefixEnd_1188429 : Nat := 4983230072969 + 3 ^ 40 * 1188429 * 2
def baseEnd_1188429 : Nat := 406823533828157333181347

theorem tailTrace_1188429 : CollatzResearch.WordTrace tailWord_1188429 prefixEnd_1188429 406823533828157333181347 := by
  unfold tailWord_1188429
  simp only [CollatzResearch.WordTrace]
  refine ⟨43345566611532175359240341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28897044407688116906160227 43345566611532175359240341)
  ·
    refine ⟨2031823434915570719964391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43345566611532175359240341 2031823434915570719964391)
    ·
      refine ⟨3047735152373356079946587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031823434915570719964391 3047735152373356079946587)
      ·
        refine ⟨4571602728560034119919881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047735152373356079946587 4571602728560034119919881)
        ·
          refine ⟨3428702046420025589939911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4571602728560034119919881 3428702046420025589939911)
          ·
            refine ⟨5143053069630038384909867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428702046420025589939911 5143053069630038384909867)
            ·
              refine ⟨7714579604445057577364801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143053069630038384909867 7714579604445057577364801)
              ·
                refine ⟨5785934703333793183023601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7714579604445057577364801 5785934703333793183023601)
                ·
                  refine ⟨4339451027500344887267701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785934703333793183023601 4339451027500344887267701)
                  ·
                    refine ⟨406823533828157333181347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4339451027500344887267701 406823533828157333181347)
                    ·
                      rfl

theorem cell22_1188429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1188429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188429 prefixEnd_1188429 := by exact prefixLift 1188429
  have htrace : WordTrace (prefixWord ++ tailWord_1188429) baseStart_1188429 baseEnd_1188429 := by
    simpa [prefixWord, tailWord_1188429, baseEnd_1188429] using wordTrace_append hprefix tailTrace_1188429
  have hstable : (prefixWord ++ tailWord_1188429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188429).length < 2 ^ (prefixWord ++ tailWord_1188429).sum := by decide
  have hdescent : baseEnd_1188429 < baseStart_1188429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188461 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_1188461 : Nat := 118140960795 + 1188461 * 2 ^ 59
def prefixEnd_1188461 : Nat := 4983230072969 + 3 ^ 40 * 1188461 * 2
def baseEnd_1188461 : Nat := 406834488082119916381249

theorem tailTrace_1188461 : CollatzResearch.WordTrace tailWord_1188461 prefixEnd_1188461 406834488082119916381249 := by
  unfold tailWord_1188461
  simp only [CollatzResearch.WordTrace]
  refine ⟨43346733747416244824405237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28897822498277496549603491 43346733747416244824405237)
  ·
    refine ⟨4063756288820272952287991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43346733747416244824405237 4063756288820272952287991)
    ·
      refine ⟨6095634433230409428431987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4063756288820272952287991 6095634433230409428431987)
      ·
        refine ⟨9143451649845614142647981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6095634433230409428431987 9143451649845614142647981)
        ·
          refine ⟨3428794368692105303492993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9143451649845614142647981 3428794368692105303492993)
          ·
            refine ⟨2571595776519078977619745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3428794368692105303492993 2571595776519078977619745)
            ·
              refine ⟨1928696832389309233214809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571595776519078977619745 1928696832389309233214809)
              ·
                refine ⟨1446522624291981924911107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928696832389309233214809 1446522624291981924911107)
                ·
                  refine ⟨2169783936437972887366661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446522624291981924911107 2169783936437972887366661)
                  ·
                    refine ⟨406834488082119916381249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169783936437972887366661 406834488082119916381249)
                    ·
                      rfl

theorem cell22_1188461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_1188461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188461 prefixEnd_1188461 := by exact prefixLift 1188461
  have htrace : WordTrace (prefixWord ++ tailWord_1188461) baseStart_1188461 baseEnd_1188461 := by
    simpa [prefixWord, tailWord_1188461, baseEnd_1188461] using wordTrace_append hprefix tailTrace_1188461
  have hstable : (prefixWord ++ tailWord_1188461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188461).length < 2 ^ (prefixWord ++ tailWord_1188461).sum := by decide
  have hdescent : baseEnd_1188461 < baseStart_1188461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188508 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1188508 : Nat := 118140960795 + 1188508 * 2 ^ 59
def prefixEnd_1188508 : Nat := 4983230072969 + 3 ^ 40 * 1188508 * 2
def baseEnd_1188508 : Nat := 406850577142627460456105

theorem tailTrace_1188508 : CollatzResearch.WordTrace tailWord_1188508 prefixEnd_1188508 406850577142627460456105 := by
  unfold tailWord_1188508
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674223989122985925683089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28898965318830647900910785 21674223989122985925683089)
  ·
    refine ⟨16255667991842239444262317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21674223989122985925683089 16255667991842239444262317)
    ·
      refine ⟨6095875496940839791598369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16255667991842239444262317 6095875496940839791598369)
      ·
        refine ⟨4571906622705629843698777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6095875496940839791598369 4571906622705629843698777)
        ·
          refine ⟨3428929967029222382774083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4571906622705629843698777 3428929967029222382774083)
          ·
            refine ⟨5143394950543833574161125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428929967029222382774083 5143394950543833574161125)
            ·
              refine ⟨964386553226968795155211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5143394950543833574161125 964386553226968795155211)
              ·
                refine ⟨1446579829840453192732817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964386553226968795155211 1446579829840453192732817)
                ·
                  refine ⟨1084934872380339894549613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446579829840453192732817 1084934872380339894549613)
                  ·
                    refine ⟨406850577142627460456105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084934872380339894549613 406850577142627460456105)
                    ·
                      rfl

theorem cell22_1188508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1188508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188508 prefixEnd_1188508 := by exact prefixLift 1188508
  have htrace : WordTrace (prefixWord ++ tailWord_1188508) baseStart_1188508 baseEnd_1188508 := by
    simpa [prefixWord, tailWord_1188508, baseEnd_1188508] using wordTrace_append hprefix tailTrace_1188508
  have hstable : (prefixWord ++ tailWord_1188508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188508).length < 2 ^ (prefixWord ++ tailWord_1188508).sum := by decide
  have hdescent : baseEnd_1188508 < baseStart_1188508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188639 : List Nat := [1, 1, 2, 4, 2, 3, 1, 8]
def baseStart_1188639 : Nat := 118140960795 + 1188639 * 2 ^ 59
def prefixEnd_1188639 : Nat := 4983230072969 + 3 ^ 40 * 1188639 * 2
def baseEnd_1188639 : Nat := 45210602346642976158967

theorem tailTrace_1188639 : CollatzResearch.WordTrace tailWord_1188639 prefixEnd_1188639 45210602346642976158967 := by
  unfold tailWord_1188639
  simp only [CollatzResearch.WordTrace]
  refine ⟨43353225940771381224384971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28902150627180920816256647 43353225940771381224384971)
  ·
    refine ⟨65029838911157071836577457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43353225940771381224384971 65029838911157071836577457)
    ·
      refine ⟨48772379183367803877433093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65029838911157071836577457 48772379183367803877433093)
      ·
        refine ⟨9144821096881463227018705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48772379183367803877433093 9144821096881463227018705)
        ·
          refine ⟨6858615822661097420264029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9144821096881463227018705 6858615822661097420264029)
          ·
            refine ⟨2571980933497911532599011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6858615822661097420264029 2571980933497911532599011)
            ·
              refine ⟨3857971400246867298898517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571980933497911532599011 3857971400246867298898517)
              ·
                refine ⟨45210602346642976158967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3857971400246867298898517 45210602346642976158967)
                ·
                  rfl

theorem cell22_1188639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 8].length) (baseStart_1188639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188639 prefixEnd_1188639 := by exact prefixLift 1188639
  have htrace : WordTrace (prefixWord ++ tailWord_1188639) baseStart_1188639 baseEnd_1188639 := by
    simpa [prefixWord, tailWord_1188639, baseEnd_1188639] using wordTrace_append hprefix tailTrace_1188639
  have hstable : (prefixWord ++ tailWord_1188639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188639).length < 2 ^ (prefixWord ++ tailWord_1188639).sum := by decide
  have hdescent : baseEnd_1188639 < baseStart_1188639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188662 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1188662 : Nat := 118140960795 + 1188662 * 2 ^ 59
def prefixEnd_1188662 : Nat := 4983230072969 + 3 ^ 40 * 1188662 * 2
def baseEnd_1188662 : Nat := 135634431496607464035211

theorem tailTrace_1188662 : CollatzResearch.WordTrace tailWord_1188662 prefixEnd_1188662 135634431496607464035211 := by
  unfold tailWord_1188662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709629051230503509529515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28902709879792037434981493 2709629051230503509529515)
  ·
    refine ⟨4064443576845755264294273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709629051230503509529515 4064443576845755264294273)
    ·
      refine ⟨3048332682634316448220705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4064443576845755264294273 3048332682634316448220705)
      ·
        refine ⟨2286249511975737336165529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3048332682634316448220705 2286249511975737336165529)
        ·
          refine ⟨1714687133981803002124147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2286249511975737336165529 1714687133981803002124147)
          ·
            refine ⟨2572030700972704503186221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714687133981803002124147 2572030700972704503186221)
            ·
              refine ⟨964511512864764188694833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2572030700972704503186221 964511512864764188694833)
              ·
                refine ⟨723383634648573141521125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964511512864764188694833 723383634648573141521125)
                ·
                  refine ⟨135634431496607464035211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723383634648573141521125 135634431496607464035211)
                  ·
                    rfl

theorem cell22_1188662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1188662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188662 prefixEnd_1188662 := by exact prefixLift 1188662
  have htrace : WordTrace (prefixWord ++ tailWord_1188662) baseStart_1188662 baseEnd_1188662 := by
    simpa [prefixWord, tailWord_1188662, baseEnd_1188662] using wordTrace_append hprefix tailTrace_1188662
  have hstable : (prefixWord ++ tailWord_1188662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188662).length < 2 ^ (prefixWord ++ tailWord_1188662).sum := by decide
  have hdescent : baseEnd_1188662 < baseStart_1188662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188673 : List Nat := [1, 2, 5, 3, 1, 1, 2, 7]
def baseStart_1188673 : Nat := 118140960795 + 1188673 * 2 ^ 59
def prefixEnd_1188673 : Nat := 4983230072969 + 3 ^ 40 * 1188673 * 2
def baseEnd_1188673 : Nat := 45211895557180225564511

theorem tailTrace_1188673 : CollatzResearch.WordTrace tailWord_1188673 prefixEnd_1188673 45211895557180225564511 := by
  unfold tailWord_1188673
  simp only [CollatzResearch.WordTrace]
  refine ⟨43354466022648205031122673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28902977348432136687415115 43354466022648205031122673)
  ·
    refine ⟨32515849516986153773342005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43354466022648205031122673 32515849516986153773342005)
    ·
      refine ⟨3048360892217451916250813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32515849516986153773342005 3048360892217451916250813)
      ·
        refine ⟨1143135334581544468594055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3048360892217451916250813 1143135334581544468594055)
        ·
          refine ⟨1714703001872316702891083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143135334581544468594055 1714703001872316702891083)
          ·
            refine ⟨2572054502808475054336625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714703001872316702891083 2572054502808475054336625)
            ·
              refine ⟨1929040877106356290752469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572054502808475054336625 1929040877106356290752469)
              ·
                refine ⟨45211895557180225564511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1929040877106356290752469 45211895557180225564511)
                ·
                  rfl

theorem cell22_1188673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 7].length) (baseStart_1188673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188673 prefixEnd_1188673 := by exact prefixLift 1188673
  have htrace : WordTrace (prefixWord ++ tailWord_1188673) baseStart_1188673 baseEnd_1188673 := by
    simpa [prefixWord, tailWord_1188673, baseEnd_1188673] using wordTrace_append hprefix tailTrace_1188673
  have hstable : (prefixWord ++ tailWord_1188673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188673).length < 2 ^ (prefixWord ++ tailWord_1188673).sum := by decide
  have hdescent : baseEnd_1188673 < baseStart_1188673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188746 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_1188746 : Nat := 118140960795 + 1188746 * 2 ^ 59
def prefixEnd_1188746 : Nat := 4983230072969 + 3 ^ 40 * 1188746 * 2
def baseEnd_1188746 : Nat := 135644016468824724335125

theorem tailTrace_1188746 : CollatzResearch.WordTrace tailWord_1188746 prefixEnd_1188746 135644016468824724335125 := by
  unfold tailWord_1188746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839282137845934624632523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28904752367589158999020061 10839282137845934624632523)
  ·
    refine ⟨16258923206768901936948785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10839282137845934624632523 16258923206768901936948785)
    ·
      refine ⟨12194192405076676452711589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16258923206768901936948785 12194192405076676452711589)
      ·
        refine ⟨2286411075951876834883423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12194192405076676452711589 2286411075951876834883423)
        ·
          refine ⟨3429616613927815252325135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286411075951876834883423 3429616613927815252325135)
          ·
            refine ⟨5144424920891722878487703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429616613927815252325135 5144424920891722878487703)
            ·
              refine ⟨7716637381337584317731555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144424920891722878487703 7716637381337584317731555)
              ·
                refine ⟨11574956072006376476597333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716637381337584317731555 11574956072006376476597333)
                ·
                  refine ⟨135644016468824724335125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11574956072006376476597333 135644016468824724335125)
                  ·
                    rfl

theorem cell22_1188746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_1188746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188746 prefixEnd_1188746 := by exact prefixLift 1188746
  have htrace : WordTrace (prefixWord ++ tailWord_1188746) baseStart_1188746 baseEnd_1188746 := by
    simpa [prefixWord, tailWord_1188746, baseEnd_1188746] using wordTrace_append hprefix tailTrace_1188746
  have hstable : (prefixWord ++ tailWord_1188746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188746).length < 2 ^ (prefixWord ++ tailWord_1188746).sum := by decide
  have hdescent : baseEnd_1188746 < baseStart_1188746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188761 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_1188761 : Nat := 118140960795 + 1188761 * 2 ^ 59
def prefixEnd_1188761 : Nat := 4983230072969 + 3 ^ 40 * 1188761 * 2
def baseEnd_1188761 : Nat := 406937184213019133880329

theorem tailTrace_1188761 : CollatzResearch.WordTrace tailWord_1188761 prefixEnd_1188761 406937184213019133880329 := by
  unfold tailWord_1188761
  simp only [CollatzResearch.WordTrace]
  refine ⟨43357675646329396060326137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28905117097552930706884091 43357675646329396060326137)
  ·
    refine ⟨32518256734747047045244603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43357675646329396060326137 32518256734747047045244603)
    ·
      refine ⟨48777385102120570567866905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32518256734747047045244603 48777385102120570567866905)
      ·
        refine ⟨36583038826590427925900179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48777385102120570567866905 36583038826590427925900179)
        ·
          refine ⟨54874558239885641888850269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36583038826590427925900179 54874558239885641888850269)
          ·
            refine ⟨20577959339957115708318851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54874558239885641888850269 20577959339957115708318851)
            ·
              refine ⟨30866939009935673562478277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20577959339957115708318851 30866939009935673562478277)
              ·
                refine ⟨5787551064362938792964677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30866939009935673562478277 5787551064362938792964677)
                ·
                  refine ⟨1085165824568051023680877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5787551064362938792964677 1085165824568051023680877)
                  ·
                    refine ⟨406937184213019133880329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085165824568051023680877 406937184213019133880329)
                    ·
                      rfl

theorem cell22_1188761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_1188761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188761 prefixEnd_1188761 := by exact prefixLift 1188761
  have htrace : WordTrace (prefixWord ++ tailWord_1188761) baseStart_1188761 baseEnd_1188761 := by
    simpa [prefixWord, tailWord_1188761, baseEnd_1188761] using wordTrace_append hprefix tailTrace_1188761
  have hstable : (prefixWord ++ tailWord_1188761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188761).length < 2 ^ (prefixWord ++ tailWord_1188761).sum := by decide
  have hdescent : baseEnd_1188761 < baseStart_1188761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188840 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 1, 3]
def baseStart_1188840 : Nat := 118140960795 + 1188840 * 2 ^ 59
def prefixEnd_1188840 : Nat := 4983230072969 + 3 ^ 40 * 1188840 * 2
def baseEnd_1188840 : Nat := 406964227527489261155087

theorem tailTrace_1188840 : CollatzResearch.WordTrace tailWord_1188840 prefixEnd_1188840 406964227527489261155087 := by
  unfold tailWord_1188840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21680278506521596276225987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28907038008695461701634649 21680278506521596276225987)
  ·
    refine ⟨32520417759782394414338981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21680278506521596276225987 32520417759782394414338981)
    ·
      refine ⟨6097578329959198952688559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32520417759782394414338981 6097578329959198952688559)
      ·
        refine ⟨9146367494938798429032839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097578329959198952688559 9146367494938798429032839)
        ·
          refine ⟨13719551242408197643549259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9146367494938798429032839 13719551242408197643549259)
          ·
            refine ⟨20579326863612296465323889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13719551242408197643549259 20579326863612296465323889)
            ·
              refine ⟨15434495147709222348992917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20579326863612296465323889 15434495147709222348992917)
              ·
                refine ⟨723491960048869797609043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15434495147709222348992917 723491960048869797609043)
                ·
                  refine ⟨1085237940073304696413565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723491960048869797609043 1085237940073304696413565)
                  ·
                    refine ⟨406964227527489261155087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085237940073304696413565 406964227527489261155087)
                    ·
                      rfl

theorem cell22_1188840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_1188840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188840 prefixEnd_1188840 := by exact prefixLift 1188840
  have htrace : WordTrace (prefixWord ++ tailWord_1188840) baseStart_1188840 baseEnd_1188840 := by
    simpa [prefixWord, tailWord_1188840, baseEnd_1188840] using wordTrace_append hprefix tailTrace_1188840
  have hstable : (prefixWord ++ tailWord_1188840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188840).length < 2 ^ (prefixWord ++ tailWord_1188840).sum := by decide
  have hdescent : baseEnd_1188840 < baseStart_1188840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188913 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_1188913 : Nat := 118140960795 + 1188913 * 2 ^ 59
def prefixEnd_1188913 : Nat := 4983230072969 + 3 ^ 40 * 1188913 * 2
def baseEnd_1188913 : Nat := 406989216919341404079863

theorem tailTrace_1188913 : CollatzResearch.WordTrace tailWord_1188913 prefixEnd_1188913 406989216919341404079863 := by
  unfold tailWord_1188913
  simp only [CollatzResearch.WordTrace]
  refine ⟨43363219541778726019859393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28908813027852484013239595 43363219541778726019859393)
  ·
    refine ⟨32522414656334044514894545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43363219541778726019859393 32522414656334044514894545)
    ·
      refine ⟨24391810992250533386170909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32522414656334044514894545 24391810992250533386170909)
      ·
        refine ⟨9146929122093950019814091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24391810992250533386170909 9146929122093950019814091)
        ·
          refine ⟨13720393683140925029721137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9146929122093950019814091 13720393683140925029721137)
          ·
            refine ⟨10290295262355693772290853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13720393683140925029721137 10290295262355693772290853)
            ·
              refine ⟨1929430361691692582304535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10290295262355693772290853 1929430361691692582304535)
              ·
                refine ⟨2894145542537538873456803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929430361691692582304535 2894145542537538873456803)
                ·
                  refine ⟨4341218313806308310185205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894145542537538873456803 4341218313806308310185205)
                  ·
                    refine ⟨406989216919341404079863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4341218313806308310185205 406989216919341404079863)
                    ·
                      rfl

theorem cell22_1188913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_1188913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188913 prefixEnd_1188913 := by exact prefixLift 1188913
  have htrace : WordTrace (prefixWord ++ tailWord_1188913) baseStart_1188913 baseEnd_1188913 := by
    simpa [prefixWord, tailWord_1188913, baseEnd_1188913] using wordTrace_append hprefix tailTrace_1188913
  have hstable : (prefixWord ++ tailWord_1188913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188913).length < 2 ^ (prefixWord ++ tailWord_1188913).sum := by decide
  have hdescent : baseEnd_1188913 < baseStart_1188913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188934 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1188934 : Nat := 118140960795 + 1188934 * 2 ^ 59
def prefixEnd_1188934 : Nat := 4983230072969 + 3 ^ 40 * 1188934 * 2
def baseEnd_1188934 : Nat := 406996405648504349304799

theorem tailTrace_1188934 : CollatzResearch.WordTrace tailWord_1188934 prefixEnd_1188934 406996405648504349304799 := by
  unfold tailWord_1188934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355124546084457706449183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28909323649801764404249237 1355124546084457706449183)
  ·
    refine ⟨2032686819126686559673775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355124546084457706449183 2032686819126686559673775)
    ·
      refine ⟨3049030228690029839510663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032686819126686559673775 3049030228690029839510663)
      ·
        refine ⟨4573545343035044759265995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049030228690029839510663 4573545343035044759265995)
        ·
          refine ⟨6860318014552567138898993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4573545343035044759265995 6860318014552567138898993)
          ·
            refine ⟨5145238510914425354174245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860318014552567138898993 5145238510914425354174245)
            ·
              refine ⟨964732220796454753907671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5145238510914425354174245 964732220796454753907671)
              ·
                refine ⟨1447098331194682130861507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964732220796454753907671 1447098331194682130861507)
                ·
                  refine ⟨2170647496792023196292261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447098331194682130861507 2170647496792023196292261)
                  ·
                    refine ⟨406996405648504349304799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2170647496792023196292261 406996405648504349304799)
                    ·
                      rfl

theorem cell22_1188934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1188934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188934 prefixEnd_1188934 := by exact prefixLift 1188934
  have htrace : WordTrace (prefixWord ++ tailWord_1188934) baseStart_1188934 baseEnd_1188934 := by
    simpa [prefixWord, tailWord_1188934, baseEnd_1188934] using wordTrace_append hprefix tailTrace_1188934
  have hstable : (prefixWord ++ tailWord_1188934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188934).length < 2 ^ (prefixWord ++ tailWord_1188934).sum := by decide
  have hdescent : baseEnd_1188934 < baseStart_1188934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188992 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 1, 3]
def baseStart_1188992 : Nat := 118140960795 + 1188992 * 2 ^ 59
def prefixEnd_1188992 : Nat := 4983230072969 + 3 ^ 40 * 1188992 * 2
def baseEnd_1188992 : Nat := 407016260233811531354621

theorem tailTrace_1188992 : CollatzResearch.WordTrace tailWord_1188992 prefixEnd_1188992 407016260233811531354621 := by
  unfold tailWord_1188992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683050454246261255992615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28910733938995015007990153 21683050454246261255992615)
  ·
    refine ⟨32524575681369391883988923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21683050454246261255992615 32524575681369391883988923)
    ·
      refine ⟨48786863522054087825983385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32524575681369391883988923 48786863522054087825983385)
      ·
        refine ⟨36590147641540565869487539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48786863522054087825983385 36590147641540565869487539)
        ·
          refine ⟨54885221462310848804231309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36590147641540565869487539 54885221462310848804231309)
          ·
            refine ⟨20581958048366568301586741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54885221462310848804231309 20581958048366568301586741)
            ·
              refine ⟨1929558567034365778273757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20581958048366568301586741 1929558567034365778273757)
              ·
                refine ⟨723584462637887166852659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929558567034365778273757 723584462637887166852659)
                ·
                  refine ⟨1085376693956830750278989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723584462637887166852659 1085376693956830750278989)
                  ·
                    refine ⟨407016260233811531354621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085376693956830750278989 407016260233811531354621)
                    ·
                      rfl

theorem cell22_1188992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_1188992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1188992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1188992 prefixEnd_1188992 := by exact prefixLift 1188992
  have htrace : WordTrace (prefixWord ++ tailWord_1188992) baseStart_1188992 baseEnd_1188992 := by
    simpa [prefixWord, tailWord_1188992, baseEnd_1188992] using wordTrace_append hprefix tailTrace_1188992
  have hstable : (prefixWord ++ tailWord_1188992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188992).length < 2 ^ (prefixWord ++ tailWord_1188992).sum := by decide
  have hdescent : baseEnd_1188992 < baseStart_1188992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189022 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1189022 : Nat := 118140960795 + 1189022 * 2 ^ 59
def prefixEnd_1189022 : Nat := 4983230072969 + 3 ^ 40 * 1189022 * 2
def baseEnd_1189022 : Nat := 135675509948967151034843

theorem tailTrace_1189022 : CollatzResearch.WordTrace tailWord_1189022 prefixEnd_1189022 135675509948967151034843 := by
  unfold tailWord_1189022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420899387297979704447165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28911463398922558423718213 5420899387297979704447165)
  ·
    refine ⟨2032837270236742389167687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5420899387297979704447165 2032837270236742389167687)
    ·
      refine ⟨3049255905355113583751531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032837270236742389167687 3049255905355113583751531)
      ·
        refine ⟨4573883858032670375627297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049255905355113583751531 4573883858032670375627297)
        ·
          refine ⟨3430412893524502781720473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4573883858032670375627297 3430412893524502781720473)
          ·
            refine ⟨2572809670143377086290355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3430412893524502781720473 2572809670143377086290355)
            ·
              refine ⟨3859214505215065629435533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572809670143377086290355 3859214505215065629435533)
              ·
                refine ⟨1447205439455649611038325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859214505215065629435533 1447205439455649611038325)
                ·
                  refine ⟨135675509948967151034843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447205439455649611038325 135675509948967151034843)
                  ·
                    rfl

theorem cell22_1189022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1189022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189022 prefixEnd_1189022 := by exact prefixLift 1189022
  have htrace : WordTrace (prefixWord ++ tailWord_1189022) baseStart_1189022 baseEnd_1189022 := by
    simpa [prefixWord, tailWord_1189022, baseEnd_1189022] using wordTrace_append hprefix tailTrace_1189022
  have hstable : (prefixWord ++ tailWord_1189022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189022).length < 2 ^ (prefixWord ++ tailWord_1189022).sum := by decide
  have hdescent : baseEnd_1189022 < baseStart_1189022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189050 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_1189050 : Nat := 118140960795 + 1189050 * 2 ^ 59
def prefixEnd_1189050 : Nat := 4983230072969 + 3 ^ 40 * 1189050 * 2
def baseEnd_1189050 : Nat := 135678704939706237801481

theorem tailTrace_1189050 : CollatzResearch.WordTrace tailWord_1189050 prefixEnd_1189050 135678704939706237801481 := by
  unfold tailWord_1189050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10842054085570599604399151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28912144228188265611731069 10842054085570599604399151)
  ·
    refine ⟨16263081128355899406598727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10842054085570599604399151 16263081128355899406598727)
    ·
      refine ⟨24394621692533849109898091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16263081128355899406598727 24394621692533849109898091)
      ·
        refine ⟨36591932538800773664847137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24394621692533849109898091 36591932538800773664847137)
        ·
          refine ⟨27443949404100580248635353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36591932538800773664847137 27443949404100580248635353)
          ·
            refine ⟨20582962053075435186476515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27443949404100580248635353 20582962053075435186476515)
            ·
              refine ⟨30874443079613152779714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20582962053075435186476515 30874443079613152779714773)
              ·
                refine ⟨723619759678433268274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30874443079613152779714773 723619759678433268274565)
                ·
                  refine ⟨135678704939706237801481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723619759678433268274565 135678704939706237801481)
                  ·
                    rfl

theorem cell22_1189050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_1189050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189050 prefixEnd_1189050 := by exact prefixLift 1189050
  have htrace : WordTrace (prefixWord ++ tailWord_1189050) baseStart_1189050 baseEnd_1189050 := by
    simpa [prefixWord, tailWord_1189050, baseEnd_1189050] using wordTrace_append hprefix tailTrace_1189050
  have hstable : (prefixWord ++ tailWord_1189050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189050).length < 2 ^ (prefixWord ++ tailWord_1189050).sum := by decide
  have hdescent : baseEnd_1189050 < baseStart_1189050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189116 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1189116 : Nat := 118140960795 + 1189116 * 2 ^ 59
def prefixEnd_1189116 : Nat := 4983230072969 + 3 ^ 40 * 1189116 * 2
def baseEnd_1189116 : Nat := 407058707967916541254241

theorem tailTrace_1189116 : CollatzResearch.WordTrace tailWord_1189116 prefixEnd_1189116 407058707967916541254241 := by
  unfold tailWord_1189116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21685311780021645844749601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28913749040028861126332801 21685311780021645844749601)
  ·
    refine ⟨16263983835016234383562201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21685311780021645844749601 16263983835016234383562201)
    ·
      refine ⟨12197987876262175787671651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16263983835016234383562201 12197987876262175787671651)
      ·
        refine ⟨18296981814393263681507477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12197987876262175787671651 18296981814393263681507477)
        ·
          refine ⟨857671022549684235070663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18296981814393263681507477 857671022549684235070663)
          ·
            refine ⟨1286506533824526352605995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857671022549684235070663 1286506533824526352605995)
            ·
              refine ⟨1929759800736789528908993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286506533824526352605995 1929759800736789528908993)
              ·
                refine ⟨1447319850552592146681745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929759800736789528908993 1447319850552592146681745)
                ·
                  refine ⟨1085489887914444110011309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1447319850552592146681745 1085489887914444110011309)
                  ·
                    refine ⟨407058707967916541254241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085489887914444110011309 407058707967916541254241)
                    ·
                      rfl

theorem cell22_1189116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1189116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189116 prefixEnd_1189116 := by exact prefixLift 1189116
  have htrace : WordTrace (prefixWord ++ tailWord_1189116) baseStart_1189116 baseEnd_1189116 := by
    simpa [prefixWord, tailWord_1189116, baseEnd_1189116] using wordTrace_append hprefix tailTrace_1189116
  have hstable : (prefixWord ++ tailWord_1189116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189116).length < 2 ^ (prefixWord ++ tailWord_1189116).sum := by decide
  have hdescent : baseEnd_1189116 < baseStart_1189116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189200 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_1189200 : Nat := 118140960795 + 1189200 * 2 ^ 59
def prefixEnd_1189200 : Nat := 4983230072969 + 3 ^ 40 * 1189200 * 2
def baseEnd_1189200 : Nat := 407087462884568322153983

theorem tailTrace_1189200 : CollatzResearch.WordTrace tailWord_1189200 prefixEnd_1189200 407087462884568322153983 := by
  unfold tailWord_1189200
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686843645869487017778527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28915791527825982690371369 21686843645869487017778527)
  ·
    refine ⟨32530265468804230526667791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21686843645869487017778527 32530265468804230526667791)
    ·
      refine ⟨48795398203206345790001687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32530265468804230526667791 48795398203206345790001687)
      ·
        refine ⟨73193097304809518685002531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48795398203206345790001687 73193097304809518685002531)
        ·
          refine ⟨109789645957214278027503797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73193097304809518685002531 109789645957214278027503797)
          ·
            refine ⟨10292779308488838565078481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109789645957214278027503797 10292779308488838565078481)
            ·
              refine ⟨7719584481366628923808861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10292779308488838565078481 7719584481366628923808861)
              ·
                refine ⟨2894844180512485846428323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7719584481366628923808861 2894844180512485846428323)
                ·
                  refine ⟨4342266270768728769642485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894844180512485846428323 4342266270768728769642485)
                  ·
                    refine ⟨407087462884568322153983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4342266270768728769642485 407087462884568322153983)
                    ·
                      rfl

theorem cell22_1189200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_1189200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189200 prefixEnd_1189200 := by exact prefixLift 1189200
  have htrace : WordTrace (prefixWord ++ tailWord_1189200) baseStart_1189200 baseEnd_1189200 := by
    simpa [prefixWord, tailWord_1189200, baseEnd_1189200] using wordTrace_append hprefix tailTrace_1189200
  have hstable : (prefixWord ++ tailWord_1189200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189200).length < 2 ^ (prefixWord ++ tailWord_1189200).sum := by decide
  have hdescent : baseEnd_1189200 < baseStart_1189200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189234 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_1189234 : Nat := 118140960795 + 1189234 * 2 ^ 59
def prefixEnd_1189234 : Nat := 4983230072969 + 3 ^ 40 * 1189234 * 2
def baseEnd_1189234 : Nat := 407099101779403566803879

theorem tailTrace_1189234 : CollatzResearch.WordTrace tailWord_1189234 prefixEnd_1189234 407099101779403566803879 := by
  unfold tailWord_1189234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10843731843403949460573689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28916618249077198561529837 10843731843403949460573689)
  ·
    refine ⟨8132798882552962095430267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10843731843403949460573689 8132798882552962095430267)
    ·
      refine ⟨12199198323829443143145401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8132798882552962095430267 12199198323829443143145401)
      ·
        refine ⟨9149398742872082357359051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12199198323829443143145401 9149398742872082357359051)
        ·
          refine ⟨13724098114308123536038577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9149398742872082357359051 13724098114308123536038577)
          ·
            refine ⟨10293073585731092652028933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13724098114308123536038577 10293073585731092652028933)
            ·
              refine ⟨1929951297324579872255425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10293073585731092652028933 1929951297324579872255425)
              ·
                refine ⟨1447463472993434904191569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929951297324579872255425 1447463472993434904191569)
                ·
                  refine ⟨1085597604745076178143677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1447463472993434904191569 1085597604745076178143677)
                  ·
                    refine ⟨407099101779403566803879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085597604745076178143677 407099101779403566803879)
                    ·
                      rfl

theorem cell22_1189234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_1189234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189234 prefixEnd_1189234 := by exact prefixLift 1189234
  have htrace : WordTrace (prefixWord ++ tailWord_1189234) baseStart_1189234 baseEnd_1189234 := by
    simpa [prefixWord, tailWord_1189234, baseEnd_1189234] using wordTrace_append hprefix tailTrace_1189234
  have hstable : (prefixWord ++ tailWord_1189234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189234).length < 2 ^ (prefixWord ++ tailWord_1189234).sum := by decide
  have hdescent : baseEnd_1189234 < baseStart_1189234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189260 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1189260 : Nat := 118140960795 + 1189260 * 2 ^ 59
def prefixEnd_1189260 : Nat := 4983230072969 + 3 ^ 40 * 1189260 * 2
def baseEnd_1189260 : Nat := 407108002110748165653799

theorem tailTrace_1189260 : CollatzResearch.WordTrace tailWord_1189260 prefixEnd_1189260 407108002110748165653799 := by
  unfold tailWord_1189260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21687937835760802141370617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28917250447681069521827489 21687937835760802141370617)
  ·
    refine ⟨16265953376820601606027963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21687937835760802141370617 16265953376820601606027963)
    ·
      refine ⟨24398930065230902409041945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16265953376820601606027963 24398930065230902409041945)
      ·
        refine ⟨18299197548923176806781459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24398930065230902409041945 18299197548923176806781459)
        ·
          refine ⟨27448796323384765210172189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18299197548923176806781459 27448796323384765210172189)
          ·
            refine ⟨10293298621269286953814571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27448796323384765210172189 10293298621269286953814571)
            ·
              refine ⟨15439947931903930430721857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293298621269286953814571 15439947931903930430721857)
              ·
                refine ⟨11579960948927947823041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15439947931903930430721857 11579960948927947823041393)
                ·
                  refine ⟨8684970711695960867281045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11579960948927947823041393 8684970711695960867281045)
                  ·
                    refine ⟨407108002110748165653799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8684970711695960867281045 407108002110748165653799)
                    ·
                      rfl

theorem cell22_1189260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1189260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189260 prefixEnd_1189260 := by exact prefixLift 1189260
  have htrace : WordTrace (prefixWord ++ tailWord_1189260) baseStart_1189260 baseEnd_1189260 := by
    simpa [prefixWord, tailWord_1189260, baseEnd_1189260] using wordTrace_append hprefix tailTrace_1189260
  have hstable : (prefixWord ++ tailWord_1189260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189260).length < 2 ^ (prefixWord ++ tailWord_1189260).sum := by decide
  have hdescent : baseEnd_1189260 < baseStart_1189260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189292 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_1189292 : Nat := 118140960795 + 1189292 * 2 ^ 59
def prefixEnd_1189292 : Nat := 4983230072969 + 3 ^ 40 * 1189292 * 2
def baseEnd_1189292 : Nat := 135706318788236916284567

theorem tailTrace_1189292 : CollatzResearch.WordTrace tailWord_1189292 prefixEnd_1189292 135706318788236916284567 := by
  unfold tailWord_1189292
  simp only [CollatzResearch.WordTrace]
  refine ⟨21688521403702836873953065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28918028538270449165270753 21688521403702836873953065)
  ·
    refine ⟨16266391052777127655464799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21688521403702836873953065 16266391052777127655464799)
    ·
      refine ⟨24399586579165691483197199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16266391052777127655464799 24399586579165691483197199)
      ·
        refine ⟨36599379868748537224795799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24399586579165691483197199 36599379868748537224795799)
        ·
          refine ⟨54899069803122805837193699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36599379868748537224795799 54899069803122805837193699)
          ·
            refine ⟨82348604704684208755790549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54899069803122805837193699 82348604704684208755790549)
            ·
              refine ⟨1930045422766036142713841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82348604704684208755790549 1930045422766036142713841)
              ·
                refine ⟨1447534067074527107035381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930045422766036142713841 1447534067074527107035381)
                ·
                  refine ⟨135706318788236916284567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447534067074527107035381 135706318788236916284567)
                  ·
                    rfl

theorem cell22_1189292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_1189292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189292 prefixEnd_1189292 := by exact prefixLift 1189292
  have htrace : WordTrace (prefixWord ++ tailWord_1189292) baseStart_1189292 baseEnd_1189292 := by
    simpa [prefixWord, tailWord_1189292, baseEnd_1189292] using wordTrace_append hprefix tailTrace_1189292
  have hstable : (prefixWord ++ tailWord_1189292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189292).length < 2 ^ (prefixWord ++ tailWord_1189292).sum := by decide
  have hdescent : baseEnd_1189292 < baseStart_1189292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189309 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 5]
def baseStart_1189309 : Nat := 118140960795 + 1189309 * 2 ^ 59
def prefixEnd_1189309 : Nat := 4983230072969 + 3 ^ 40 * 1189309 * 2
def baseEnd_1189309 : Nat := 135708258604042790392883

theorem tailTrace_1189309 : CollatzResearch.WordTrace tailWord_1189309 prefixEnd_1189309 135708258604042790392883 := by
  unfold tailWord_1189309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43377662848344085651274981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28918441898896057100849987 43377662848344085651274981)
  ·
    refine ⟨8133311784064516059614059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43377662848344085651274981 8133311784064516059614059)
    ·
      refine ⟨12199967676096774089421089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8133311784064516059614059 12199967676096774089421089)
      ·
        refine ⟨9149975757072580567065817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12199967676096774089421089 9149975757072580567065817)
        ·
          refine ⟨6862481817804435425299363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9149975757072580567065817 6862481817804435425299363)
          ·
            refine ⟨10293722726706653137949045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862481817804435425299363 10293722726706653137949045)
            ·
              refine ⟨965036505628748731682723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10293722726706653137949045 965036505628748731682723)
              ·
                refine ⟨1447554758443123097524085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965036505628748731682723 1447554758443123097524085)
                ·
                  refine ⟨135708258604042790392883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447554758443123097524085 135708258604042790392883)
                  ·
                    rfl

theorem cell22_1189309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_1189309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189309 prefixEnd_1189309 := by exact prefixLift 1189309
  have htrace : WordTrace (prefixWord ++ tailWord_1189309) baseStart_1189309 baseEnd_1189309 := by
    simpa [prefixWord, tailWord_1189309, baseEnd_1189309] using wordTrace_append hprefix tailTrace_1189309
  have hstable : (prefixWord ++ tailWord_1189309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189309).length < 2 ^ (prefixWord ++ tailWord_1189309).sum := by decide
  have hdescent : baseEnd_1189309 < baseStart_1189309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189416 : List Nat := [2, 1, 5, 2, 2, 2, 1, 7]
def baseStart_1189416 : Nat := 118140960795 + 1189416 * 2 ^ 59
def prefixEnd_1189416 : Nat := 4983230072969 + 3 ^ 40 * 1189416 * 2
def baseEnd_1189416 : Nat := 45240156010979528750369

theorem tailTrace_1189416 : CollatzResearch.WordTrace tailWord_1189416 prefixEnd_1189416 45240156010979528750369 := by
  unfold tailWord_1189416
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690782729478221462710051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28921043639304295283613401 21690782729478221462710051)
  ·
    refine ⟨32536174094217332194065077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21690782729478221462710051 32536174094217332194065077)
    ·
      refine ⟨3050266321332874893193601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32536174094217332194065077 3050266321332874893193601)
      ·
        refine ⟨2287699740999656169895201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3050266321332874893193601 2287699740999656169895201)
        ·
          refine ⟨1715774805749742127421401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2287699740999656169895201 1715774805749742127421401)
          ·
            refine ⟨1286831104312306595566051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715774805749742127421401 1286831104312306595566051)
            ·
              refine ⟨1930246656468459893349077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286831104312306595566051 1930246656468459893349077)
              ·
                refine ⟨45240156010979528750369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1930246656468459893349077 45240156010979528750369)
                ·
                  rfl

theorem cell22_1189416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_1189416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189416 prefixEnd_1189416 := by exact prefixLift 1189416
  have htrace : WordTrace (prefixWord ++ tailWord_1189416) baseStart_1189416 baseEnd_1189416 := by
    simpa [prefixWord, tailWord_1189416, baseEnd_1189416] using wordTrace_append hprefix tailTrace_1189416
  have hstable : (prefixWord ++ tailWord_1189416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189416).length < 2 ^ (prefixWord ++ tailWord_1189416).sum := by decide
  have hdescent : baseEnd_1189416 < baseStart_1189416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189504 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_1189504 : Nat := 118140960795 + 1189504 * 2 ^ 59
def prefixEnd_1189504 : Nat := 4983230072969 + 3 ^ 40 * 1189504 * 2
def baseEnd_1189504 : Nat := 407191528297212862553051

theorem tailTrace_1189504 : CollatzResearch.WordTrace tailWord_1189504 prefixEnd_1189504 407191528297212862553051 := by
  unfold tailWord_1189504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21692387541318816977311783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28923183388425089303082377 21692387541318816977311783)
  ·
    refine ⟨32538581311978225465967675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21692387541318816977311783 32538581311978225465967675)
    ·
      refine ⟨48807871967967338198951513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32538581311978225465967675 48807871967967338198951513)
      ·
        refine ⟨36605903975975503649213635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48807871967967338198951513 36605903975975503649213635)
        ·
          refine ⟨54908855963963255473820453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36605903975975503649213635 54908855963963255473820453)
          ·
            refine ⟨10295410493243110401341335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54908855963963255473820453 10295410493243110401341335)
            ·
              refine ⟨15443115739864665602012003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10295410493243110401341335 15443115739864665602012003)
              ·
                refine ⟨23164673609796998403018005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15443115739864665602012003 23164673609796998403018005)
                ·
                  refine ⟨1085844075459234300141469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23164673609796998403018005 1085844075459234300141469)
                  ·
                    refine ⟨407191528297212862553051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085844075459234300141469 407191528297212862553051)
                    ·
                      rfl

theorem cell22_1189504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_1189504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189504 prefixEnd_1189504 := by exact prefixLift 1189504
  have htrace : WordTrace (prefixWord ++ tailWord_1189504) baseStart_1189504 baseEnd_1189504 := by
    simpa [prefixWord, tailWord_1189504, baseEnd_1189504] using wordTrace_append hprefix tailTrace_1189504
  have hstable : (prefixWord ++ tailWord_1189504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189504).length < 2 ^ (prefixWord ++ tailWord_1189504).sum := by decide
  have hdescent : baseEnd_1189504 < baseStart_1189504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189574 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1189574 : Nat := 118140960795 + 1189574 * 2 ^ 59
def prefixEnd_1189574 : Nat := 4983230072969 + 3 ^ 40 * 1189574 * 2
def baseEnd_1189574 : Nat := 135738496909252004434279

theorem tailTrace_1189574 : CollatzResearch.WordTrace tailWord_1189574 prefixEnd_1189574 135738496909252004434279 := by
  unfold tailWord_1189574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355854006012001122177243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28924885461589357273114517 1355854006012001122177243)
  ·
    refine ⟨2033781009018001683265865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355854006012001122177243 2033781009018001683265865)
    ·
      refine ⟨1525335756763501262449399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2033781009018001683265865 1525335756763501262449399)
      ·
        refine ⟨2288003635145251893674099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525335756763501262449399 2288003635145251893674099)
        ·
          refine ⟨3432005452717877840511149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288003635145251893674099 3432005452717877840511149)
          ·
            refine ⟨1287002044769204190191681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3432005452717877840511149 1287002044769204190191681)
            ·
              refine ⟨965251533576903142643761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287002044769204190191681 965251533576903142643761)
              ·
                refine ⟨723938650182677356982821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965251533576903142643761 723938650182677356982821)
                ·
                  refine ⟨135738496909252004434279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723938650182677356982821 135738496909252004434279)
                  ·
                    rfl

theorem cell22_1189574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1189574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189574 prefixEnd_1189574 := by exact prefixLift 1189574
  have htrace : WordTrace (prefixWord ++ tailWord_1189574) baseStart_1189574 baseEnd_1189574 := by
    simpa [prefixWord, tailWord_1189574, baseEnd_1189574] using wordTrace_append hprefix tailTrace_1189574
  have hstable : (prefixWord ++ tailWord_1189574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189574).length < 2 ^ (prefixWord ++ tailWord_1189574).sum := by decide
  have hdescent : baseEnd_1189574 < baseStart_1189574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189594 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1189594 : Nat := 118140960795 + 1189594 * 2 ^ 59
def prefixEnd_1189594 : Nat := 4983230072969 + 3 ^ 40 * 1189594 * 2
def baseEnd_1189594 : Nat := 407222337136482627802775

theorem tailTrace_1189594 : CollatzResearch.WordTrace tailWord_1189594 prefixEnd_1189594 407222337136482627802775 := by
  unfold tailWord_1189594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847014413077894831349959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28925371768207719550266557 10847014413077894831349959)
  ·
    refine ⟨16270521619616842247024939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10847014413077894831349959 16270521619616842247024939)
    ·
      refine ⟨24405782429425263370537409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16270521619616842247024939 24405782429425263370537409)
      ·
        refine ⟨18304336822068947527903057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24405782429425263370537409 18304336822068947527903057)
        ·
          refine ⟨13728252616551710645927293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18304336822068947527903057 13728252616551710645927293)
          ·
            refine ⟨5148094731206891492222735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13728252616551710645927293 5148094731206891492222735)
            ·
              refine ⟨7722142096810337238334103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5148094731206891492222735 7722142096810337238334103)
              ·
                refine ⟨11583213145215505857501155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7722142096810337238334103 11583213145215505857501155)
                ·
                  refine ⟨17374819717823258786251733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11583213145215505857501155 17374819717823258786251733)
                  ·
                    refine ⟨407222337136482627802775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17374819717823258786251733 407222337136482627802775)
                    ·
                      rfl

theorem cell22_1189594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1189594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189594 prefixEnd_1189594 := by exact prefixLift 1189594
  have htrace : WordTrace (prefixWord ++ tailWord_1189594) baseStart_1189594 baseEnd_1189594 := by
    simpa [prefixWord, tailWord_1189594, baseEnd_1189594] using wordTrace_append hprefix tailTrace_1189594
  have hstable : (prefixWord ++ tailWord_1189594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189594).length < 2 ^ (prefixWord ++ tailWord_1189594).sum := by decide
  have hdescent : baseEnd_1189594 < baseStart_1189594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189630 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1189630 : Nat := 118140960795 + 1189630 * 2 ^ 59
def prefixEnd_1189630 : Nat := 4983230072969 + 3 ^ 40 * 1189630 * 2
def baseEnd_1189630 : Nat := 135744886890730177967555

theorem tailTrace_1189630 : CollatzResearch.WordTrace tailWord_1189630 prefixEnd_1189630 135744886890730177967555 := by
  unfold tailWord_1189630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423671335022644684213793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28926247120120771649140229 5423671335022644684213793)
  ·
    refine ⟨4067753501266983513160345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5423671335022644684213793 4067753501266983513160345)
    ·
      refine ⟨3050815125950237634870259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4067753501266983513160345 3050815125950237634870259)
      ·
        refine ⟨4576222688925356452305389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050815125950237634870259 4576222688925356452305389)
        ·
          refine ⟨1716083508347008669614521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4576222688925356452305389 1716083508347008669614521)
          ·
            refine ⟨1287062631260256502210891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716083508347008669614521 1287062631260256502210891)
            ·
              refine ⟨1930593946890384753316337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287062631260256502210891 1930593946890384753316337)
              ·
                refine ⟨1447945460167788564987253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930593946890384753316337 1447945460167788564987253)
                ·
                  refine ⟨135744886890730177967555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447945460167788564987253 135744886890730177967555)
                  ·
                    rfl

theorem cell22_1189630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1189630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189630 prefixEnd_1189630 := by exact prefixLift 1189630
  have htrace : WordTrace (prefixWord ++ tailWord_1189630) baseStart_1189630 baseEnd_1189630 := by
    simpa [prefixWord, tailWord_1189630, baseEnd_1189630] using wordTrace_append hprefix tailTrace_1189630
  have hstable : (prefixWord ++ tailWord_1189630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189630).length < 2 ^ (prefixWord ++ tailWord_1189630).sum := by decide
  have hdescent : baseEnd_1189630 < baseStart_1189630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189656 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1189656 : Nat := 118140960795 + 1189656 * 2 ^ 59
def prefixEnd_1189656 : Nat := 4983230072969 + 3 ^ 40 * 1189656 * 2
def baseEnd_1189656 : Nat := 407243561003535132752585

theorem tailTrace_1189656 : CollatzResearch.WordTrace tailWord_1189656 prefixEnd_1189656 407243561003535132752585 := by
  unfold tailWord_1189656
  simp only [CollatzResearch.WordTrace]
  refine ⟨21695159489043481957078411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28926879318724642609437881 21695159489043481957078411)
  ·
    refine ⟨32542739233565222935617617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21695159489043481957078411 32542739233565222935617617)
    ·
      refine ⟨24407054425173917201713213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32542739233565222935617617 24407054425173917201713213)
      ·
        refine ⟨9152645409440218950642455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24407054425173917201713213 9152645409440218950642455)
        ·
          refine ⟨13728968114160328425963683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9152645409440218950642455 13728968114160328425963683)
          ·
            refine ⟨20593452171240492638945525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13728968114160328425963683 20593452171240492638945525)
            ·
              refine ⟨1930636141053796184901143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20593452171240492638945525 1930636141053796184901143)
              ·
                refine ⟨2895954211580694277351715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930636141053796184901143 2895954211580694277351715)
                ·
                  refine ⟨4343931317371041416027573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895954211580694277351715 4343931317371041416027573)
                  ·
                    refine ⟨407243561003535132752585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4343931317371041416027573 407243561003535132752585)
                    ·
                      rfl

theorem cell22_1189656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1189656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189656 prefixEnd_1189656 := by exact prefixLift 1189656
  have htrace : WordTrace (prefixWord ++ tailWord_1189656) baseStart_1189656 baseEnd_1189656 := by
    simpa [prefixWord, tailWord_1189656, baseEnd_1189656] using wordTrace_append hprefix tailTrace_1189656
  have hstable : (prefixWord ++ tailWord_1189656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189656).length < 2 ^ (prefixWord ++ tailWord_1189656).sum := by decide
  have hdescent : baseEnd_1189656 < baseStart_1189656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189735 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1189735 : Nat := 118140960795 + 1189735 * 2 ^ 59
def prefixEnd_1189735 : Nat := 4983230072969 + 3 ^ 40 * 1189735 * 2
def baseEnd_1189735 : Nat := 407270604318005260027343

theorem tailTrace_1189735 : CollatzResearch.WordTrace tailWord_1189735 prefixEnd_1189735 407270604318005260027343 := by
  unfold tailWord_1189735
  simp only [CollatzResearch.WordTrace]
  refine ⟨43393200344800760406282659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28928800229867173604188439 43393200344800760406282659)
  ·
    refine ⟨65089800517201140609423989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43393200344800760406282659 65089800517201140609423989)
    ·
      refine ⟨6102168798487606932133499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65089800517201140609423989 6102168798487606932133499)
      ·
        refine ⟨9153253197731410398200249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6102168798487606932133499 9153253197731410398200249)
        ·
          refine ⟨6864939898298557798650187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9153253197731410398200249 6864939898298557798650187)
          ·
            refine ⟨10297409847447836697975281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864939898298557798650187 10297409847447836697975281)
            ·
              refine ⟨7723057385585877523481461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10297409847447836697975281 7723057385585877523481461)
              ·
                refine ⟨724036629898676017826387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7723057385585877523481461 724036629898676017826387)
                ·
                  refine ⟨1086054944848014026739581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724036629898676017826387 1086054944848014026739581)
                  ·
                    refine ⟨407270604318005260027343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086054944848014026739581 407270604318005260027343)
                    ·
                      rfl

theorem cell22_1189735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1189735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189735 prefixEnd_1189735 := by exact prefixLift 1189735
  have htrace : WordTrace (prefixWord ++ tailWord_1189735) baseStart_1189735 baseEnd_1189735 := by
    simpa [prefixWord, tailWord_1189735, baseEnd_1189735] using wordTrace_append hprefix tailTrace_1189735
  have hstable : (prefixWord ++ tailWord_1189735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189735).length < 2 ^ (prefixWord ++ tailWord_1189735).sum := by decide
  have hdescent : baseEnd_1189735 < baseStart_1189735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189746 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1189746 : Nat := 118140960795 + 1189746 * 2 ^ 59
def prefixEnd_1189746 : Nat := 4983230072969 + 3 ^ 40 * 1189746 * 2
def baseEnd_1189746 : Nat := 407274369842804898002309

theorem tailTrace_1189746 : CollatzResearch.WordTrace tailWord_1189746 prefixEnd_1189746 407274369842804898002309 := by
  unfold tailWord_1189746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848400386940227321233273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28929067698507272856622061 10848400386940227321233273)
  ·
    refine ⟨8136300290205170490924955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10848400386940227321233273 8136300290205170490924955)
    ·
      refine ⟨12204450435307755736387433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8136300290205170490924955 12204450435307755736387433)
      ·
        refine ⟨9153337826480816802290575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12204450435307755736387433 9153337826480816802290575)
        ·
          refine ⟨13730006739721225203435863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9153337826480816802290575 13730006739721225203435863)
          ·
            refine ⟨20595010109581837805153795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13730006739721225203435863 20595010109581837805153795)
            ·
              refine ⟨30892515164372756707730693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20595010109581837805153795 30892515164372756707730693)
              ·
                refine ⟨5792346593319891882699505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30892515164372756707730693 5792346593319891882699505)
                ·
                  refine ⟨4344259944989918912024629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792346593319891882699505 4344259944989918912024629)
                  ·
                    refine ⟨407274369842804898002309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4344259944989918912024629 407274369842804898002309)
                    ·
                      rfl

theorem cell22_1189746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1189746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189746 prefixEnd_1189746 := by exact prefixLift 1189746
  have htrace : WordTrace (prefixWord ++ tailWord_1189746) baseStart_1189746 baseEnd_1189746 := by
    simpa [prefixWord, tailWord_1189746, baseEnd_1189746] using wordTrace_append hprefix tailTrace_1189746
  have hstable : (prefixWord ++ tailWord_1189746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189746).length < 2 ^ (prefixWord ++ tailWord_1189746).sum := by decide
  have hdescent : baseEnd_1189746 < baseStart_1189746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189921 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 1, 3]
def baseStart_1189921 : Nat := 118140960795 + 1189921 * 2 ^ 59
def prefixEnd_1189921 : Nat := 4983230072969 + 3 ^ 40 * 1189921 * 2
def baseEnd_1189921 : Nat := 407334275919162774876773

theorem tailTrace_1189921 : CollatzResearch.WordTrace tailWord_1189921 prefixEnd_1189921 407334275919162774876773 := by
  unfold tailWord_1189921
  simp only [CollatzResearch.WordTrace]
  refine ⟨43399984322126914172553617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28933322881417942781702411 43399984322126914172553617)
  ·
    refine ⟨32549988241595185629415213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43399984322126914172553617 32549988241595185629415213)
    ·
      refine ⟨12206245590598194611030705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32549988241595185629415213 12206245590598194611030705)
      ·
        refine ⟨9154684192948645958273029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12206245590598194611030705 9154684192948645958273029)
        ·
          refine ⟨1716503286177871117176193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9154684192948645958273029 1716503286177871117176193)
          ·
            refine ⟨1287377464633403337882145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716503286177871117176193 1287377464633403337882145)
            ·
              refine ⟨965533098475052503411609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287377464633403337882145 965533098475052503411609)
              ·
                refine ⟨724149823856289377558707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965533098475052503411609 724149823856289377558707)
                ·
                  refine ⟨1086224735784434066338061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724149823856289377558707 1086224735784434066338061)
                  ·
                    refine ⟨407334275919162774876773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086224735784434066338061 407334275919162774876773)
                    ·
                      rfl

theorem cell22_1189921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_1189921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189921 prefixEnd_1189921 := by exact prefixLift 1189921
  have htrace : WordTrace (prefixWord ++ tailWord_1189921) baseStart_1189921 baseEnd_1189921 := by
    simpa [prefixWord, tailWord_1189921, baseEnd_1189921] using wordTrace_append hprefix tailTrace_1189921
  have hstable : (prefixWord ++ tailWord_1189921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189921).length < 2 ^ (prefixWord ++ tailWord_1189921).sum := by decide
  have hdescent : baseEnd_1189921 < baseStart_1189921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189930 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1189930 : Nat := 118140960795 + 1189930 * 2 ^ 59
def prefixEnd_1189930 : Nat := 4983230072969 + 3 ^ 40 * 1189930 * 2
def baseEnd_1189930 : Nat := 407337356803089751401745

theorem tailTrace_1189930 : CollatzResearch.WordTrace tailWord_1189930 prefixEnd_1189930 407337356803089751401745 := by
  unfold tailWord_1189930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850078144773577177407811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28933541719396205806420829 10850078144773577177407811)
  ·
    refine ⟨16275117217160365766111717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10850078144773577177407811 16275117217160365766111717)
    ·
      refine ⟨3051584478217568581145947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16275117217160365766111717 3051584478217568581145947)
      ·
        refine ⟨4577376717326352871718921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051584478217568581145947 4577376717326352871718921)
        ·
          refine ⟨3433032537994764653789191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4577376717326352871718921 3433032537994764653789191)
          ·
            refine ⟨5149548806992146980683787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433032537994764653789191 5149548806992146980683787)
            ·
              refine ⟨7724323210488220471025681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149548806992146980683787 7724323210488220471025681)
              ·
                refine ⟨5793242407866165353269261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7724323210488220471025681 5793242407866165353269261)
                ·
                  refine ⟨2172465902949812007475973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5793242407866165353269261 2172465902949812007475973)
                  ·
                    refine ⟨407337356803089751401745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2172465902949812007475973 407337356803089751401745)
                    ·
                      rfl

theorem cell22_1189930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1189930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189930 prefixEnd_1189930 := by exact prefixLift 1189930
  have htrace : WordTrace (prefixWord ++ tailWord_1189930) baseStart_1189930 baseEnd_1189930 := by
    simpa [prefixWord, tailWord_1189930, baseEnd_1189930] using wordTrace_append hprefix tailTrace_1189930
  have hstable : (prefixWord ++ tailWord_1189930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189930).length < 2 ^ (prefixWord ++ tailWord_1189930).sum := by decide
  have hdescent : baseEnd_1189930 < baseStart_1189930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189943 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_1189943 : Nat := 118140960795 + 1189943 * 2 ^ 59
def prefixEnd_1189943 : Nat := 4983230072969 + 3 ^ 40 * 1189943 * 2
def baseEnd_1189943 : Nat := 407341806968762050826705

theorem tailTrace_1189943 : CollatzResearch.WordTrace tailWord_1189943 prefixEnd_1189943 407341806968762050826705 := by
  unfold tailWord_1189943
  simp only [CollatzResearch.WordTrace]
  refine ⟨43400786728047211929854483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28933857818698141286569655 43400786728047211929854483)
  ·
    refine ⟨65101180092070817894781725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43400786728047211929854483 65101180092070817894781725)
    ·
      refine ⟨24412942534526556710543147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65101180092070817894781725 24412942534526556710543147)
      ·
        refine ⟨36619413801789835065814721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24412942534526556710543147 36619413801789835065814721)
        ·
          refine ⟨27464560351342376299361041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36619413801789835065814721 27464560351342376299361041)
          ·
            refine ⟨20598420263506782224520781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27464560351342376299361041 20598420263506782224520781)
            ·
              refine ⟨7724407598815043334195293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20598420263506782224520781 7724407598815043334195293)
              ·
                refine ⟨2896652849555641250323235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7724407598815043334195293 2896652849555641250323235)
                ·
                  refine ⟨4344979274333461875484853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896652849555641250323235 4344979274333461875484853)
                  ·
                    refine ⟨407341806968762050826705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4344979274333461875484853 407341806968762050826705)
                    ·
                      rfl

theorem cell22_1189943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_1189943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189943 prefixEnd_1189943 := by exact prefixLift 1189943
  have htrace : WordTrace (prefixWord ++ tailWord_1189943) baseStart_1189943 baseEnd_1189943 := by
    simpa [prefixWord, tailWord_1189943, baseEnd_1189943] using wordTrace_append hprefix tailTrace_1189943
  have hstable : (prefixWord ++ tailWord_1189943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189943).length < 2 ^ (prefixWord ++ tailWord_1189943).sum := by decide
  have hdescent : baseEnd_1189943 < baseStart_1189943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189945 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 6]
def baseStart_1189945 : Nat := 118140960795 + 1189945 * 2 ^ 59
def prefixEnd_1189945 : Nat := 4983230072969 + 3 ^ 40 * 1189945 * 2
def baseEnd_1189945 : Nat := 135780830536544904092233

theorem tailTrace_1189945 : CollatzResearch.WordTrace tailWord_1189945 prefixEnd_1189945 135780830536544904092233 := by
  unfold tailWord_1189945
  simp only [CollatzResearch.WordTrace]
  refine ⟨43400859674039966271427289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28933906449359977514284859 43400859674039966271427289)
  ·
    refine ⟨32550644755529974703570467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43400859674039966271427289 32550644755529974703570467)
    ·
      refine ⟨48825967133294962055355701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32550644755529974703570467 48825967133294962055355701)
      ·
        refine ⟨4577434418746402692689597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48825967133294962055355701 4577434418746402692689597)
        ·
          refine ⟨1716537907029901009758599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4577434418746402692689597 1716537907029901009758599)
          ·
            refine ⟨2574806860544851514637899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716537907029901009758599 2574806860544851514637899)
            ·
              refine ⟨3862210290817277271956849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574806860544851514637899 3862210290817277271956849)
              ·
                refine ⟨2896657718112957953967637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862210290817277271956849 2896657718112957953967637)
                ·
                  refine ⟨135780830536544904092233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2896657718112957953967637 135780830536544904092233)
                  ·
                    rfl

theorem cell22_1189945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_1189945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189945 prefixEnd_1189945 := by exact prefixLift 1189945
  have htrace : WordTrace (prefixWord ++ tailWord_1189945) baseStart_1189945 baseEnd_1189945 := by
    simpa [prefixWord, tailWord_1189945, baseEnd_1189945] using wordTrace_append hprefix tailTrace_1189945
  have hstable : (prefixWord ++ tailWord_1189945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189945).length < 2 ^ (prefixWord ++ tailWord_1189945).sum := by decide
  have hdescent : baseEnd_1189945 < baseStart_1189945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189973 : List Nat := [1, 3, 2, 2, 1, 4, 9]
def baseStart_1189973 : Nat := 118140960795 + 1189973 * 2 ^ 59
def prefixEnd_1189973 : Nat := 4983230072969 + 3 ^ 40 * 1189973 * 2
def baseEnd_1189973 : Nat := 15087113947475998984319

theorem tailTrace_1189973 : CollatzResearch.WordTrace tailWord_1189973 prefixEnd_1189973 15087113947475998984319 := by
  unfold tailWord_1189973
  simp only [CollatzResearch.WordTrace]
  refine ⟨43401880917938527053446573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28934587278625684702297715 43401880917938527053446573)
  ·
    refine ⟨16275705344226947645042465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43401880917938527053446573 16275705344226947645042465)
    ·
      refine ⟨12206779008170210733781849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16275705344226947645042465 12206779008170210733781849)
      ·
        refine ⟨9155084256127658050336387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12206779008170210733781849 9155084256127658050336387)
        ·
          refine ⟨13732626384191487075504581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9155084256127658050336387 13732626384191487075504581)
          ·
            refine ⟨2574867447035903826657109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13732626384191487075504581 2574867447035903826657109)
            ·
              refine ⟨15087113947475998984319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2574867447035903826657109 15087113947475998984319)
              ·
                rfl

theorem cell22_1189973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 9].length) (baseStart_1189973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189973 prefixEnd_1189973 := by exact prefixLift 1189973
  have htrace : WordTrace (prefixWord ++ tailWord_1189973) baseStart_1189973 baseEnd_1189973 := by
    simpa [prefixWord, tailWord_1189973, baseEnd_1189973] using wordTrace_append hprefix tailTrace_1189973
  have hstable : (prefixWord ++ tailWord_1189973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189973).length < 2 ^ (prefixWord ++ tailWord_1189973).sum := by decide
  have hdescent : baseEnd_1189973 < baseStart_1189973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189994 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1189994 : Nat := 118140960795 + 1189994 * 2 ^ 59
def prefixEnd_1189994 : Nat := 4983230072969 + 3 ^ 40 * 1189994 * 2
def baseEnd_1189994 : Nat := 407359265311014917801549

theorem tailTrace_1189994 : CollatzResearch.WordTrace tailWord_1189994 prefixEnd_1189994 407359265311014917801549 := by
  unfold tailWord_1189994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850661712715611909990259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28935097900574965093307357 10850661712715611909990259)
  ·
    refine ⟨16275992569073417864985389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10850661712715611909990259 16275992569073417864985389)
    ·
      refine ⟨6103497213402531699369521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16275992569073417864985389 6103497213402531699369521)
      ·
        refine ⟨4577622910051898774527141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6103497213402531699369521 4577622910051898774527141)
        ·
          refine ⟨858304295634731020223839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4577622910051898774527141 858304295634731020223839)
          ·
            refine ⟨1287456443452096530335759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858304295634731020223839 1287456443452096530335759)
            ·
              refine ⟨1931184665178144795503639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287456443452096530335759 1931184665178144795503639)
              ·
                refine ⟨2896776997767217193255459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931184665178144795503639 2896776997767217193255459)
                ·
                  refine ⟨4345165496650825789883189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896776997767217193255459 4345165496650825789883189)
                  ·
                    refine ⟨407359265311014917801549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4345165496650825789883189 407359265311014917801549)
                    ·
                      rfl

theorem cell22_1189994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1189994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1189994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1189994 prefixEnd_1189994 := by exact prefixLift 1189994
  have htrace : WordTrace (prefixWord ++ tailWord_1189994) baseStart_1189994 baseEnd_1189994 := by
    simpa [prefixWord, tailWord_1189994, baseEnd_1189994] using wordTrace_append hprefix tailTrace_1189994
  have hstable : (prefixWord ++ tailWord_1189994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189994).length < 2 ^ (prefixWord ++ tailWord_1189994).sum := by decide
  have hdescent : baseEnd_1189994 < baseStart_1189994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190039 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 3, 3]
def baseStart_1190039 : Nat := 118140960795 + 1190039 * 2 ^ 59
def prefixEnd_1190039 : Nat := 4983230072969 + 3 ^ 40 * 1190039 * 2
def baseEnd_1190039 : Nat := 407374669730649800426411

theorem tailTrace_1190039 : CollatzResearch.WordTrace tailWord_1190039 prefixEnd_1190039 407374669730649800426411 := by
  unfold tailWord_1190039
  simp only [CollatzResearch.WordTrace]
  refine ⟨43404288135699420325349171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28936192090466280216899447 43404288135699420325349171)
  ·
    refine ⟨65106432203549130488023757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43404288135699420325349171 65106432203549130488023757)
    ·
      refine ⟨24414912076330923933008909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65106432203549130488023757 24414912076330923933008909)
      ·
        refine ⟨9155592028624096474878341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24414912076330923933008909 9155592028624096474878341)
        ·
          refine ⟨1716673505367018089039689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9155592028624096474878341 1716673505367018089039689)
          ·
            refine ⟨1287505129025263566779767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716673505367018089039689 1287505129025263566779767)
            ·
              refine ⟨1931257693537895350169651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287505129025263566779767 1931257693537895350169651)
              ·
                refine ⟨2896886540306843025254477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931257693537895350169651 2896886540306843025254477)
                ·
                  refine ⟨1086332452615066134470429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2896886540306843025254477 1086332452615066134470429)
                  ·
                    refine ⟨407374669730649800426411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086332452615066134470429 407374669730649800426411)
                    ·
                      rfl

theorem cell22_1190039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_1190039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190039 prefixEnd_1190039 := by exact prefixLift 1190039
  have htrace : WordTrace (prefixWord ++ tailWord_1190039) baseStart_1190039 baseEnd_1190039 := by
    simpa [prefixWord, tailWord_1190039, baseEnd_1190039] using wordTrace_append hprefix tailTrace_1190039
  have hstable : (prefixWord ++ tailWord_1190039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190039).length < 2 ^ (prefixWord ++ tailWord_1190039).sum := by decide
  have hdescent : baseEnd_1190039 < baseStart_1190039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190052 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1190052 : Nat := 118140960795 + 1190052 * 2 ^ 59
def prefixEnd_1190052 : Nat := 4983230072969 + 3 ^ 40 * 1190052 * 2
def baseEnd_1190052 : Nat := 135793039965440699950457

theorem tailTrace_1190052 : CollatzResearch.WordTrace tailWord_1190052 prefixEnd_1190052 135793039965440699950457 := by
  unfold tailWord_1190052
  simp only [CollatzResearch.WordTrace]
  refine ⟨21702381142326161772786205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28936508189768215697048273 21702381142326161772786205)
  ·
    refine ⟨8138392928372310664794827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21702381142326161772786205 8138392928372310664794827)
    ·
      refine ⟨12207589392558465997192241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8138392928372310664794827 12207589392558465997192241)
      ·
        refine ⟨9155692044418849497894181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12207589392558465997192241 9155692044418849497894181)
        ·
          refine ⟨1716692258328534280855159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9155692044418849497894181 1716692258328534280855159)
          ·
            refine ⟨2575038387492801421282739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716692258328534280855159 2575038387492801421282739)
            ·
              refine ⟨3862557581239202131924109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575038387492801421282739 3862557581239202131924109)
              ·
                refine ⟨1448459092964700799471541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3862557581239202131924109 1448459092964700799471541)
                ·
                  refine ⟨135793039965440699950457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1448459092964700799471541 135793039965440699950457)
                  ·
                    rfl

theorem cell22_1190052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1190052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190052 prefixEnd_1190052 := by exact prefixLift 1190052
  have htrace : WordTrace (prefixWord ++ tailWord_1190052) baseStart_1190052 baseEnd_1190052 := by
    simpa [prefixWord, tailWord_1190052, baseEnd_1190052] using wordTrace_append hprefix tailTrace_1190052
  have hstable : (prefixWord ++ tailWord_1190052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190052).length < 2 ^ (prefixWord ++ tailWord_1190052).sum := by decide
  have hdescent : baseEnd_1190052 < baseStart_1190052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190063 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 8]
def baseStart_1190063 : Nat := 118140960795 + 1190063 * 2 ^ 59
def prefixEnd_1190063 : Nat := 4983230072969 + 3 ^ 40 * 1190063 * 2
def baseEnd_1190063 : Nat := 135794295140373912608779

theorem tailTrace_1190063 : CollatzResearch.WordTrace tailWord_1190063 prefixEnd_1190063 135794295140373912608779 := by
  unfold tailWord_1190063
  simp only [CollatzResearch.WordTrace]
  refine ⟨43405163487612472424222843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28936775658408314949481895 43405163487612472424222843)
  ·
    refine ⟨65107745231418708636334265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43405163487612472424222843 65107745231418708636334265)
    ·
      refine ⟨48830808923564031477250699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65107745231418708636334265 48830808923564031477250699)
      ·
        refine ⟨73246213385346047215876049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48830808923564031477250699 73246213385346047215876049)
        ·
          refine ⟨54934660039009535411907037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73246213385346047215876049 54934660039009535411907037)
          ·
            refine ⟨20600497514628575779465139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54934660039009535411907037 20600497514628575779465139)
            ·
              refine ⟨30900746271942863669197709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20600497514628575779465139 30900746271942863669197709)
              ·
                refine ⟨11587779851978573875949141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30900746271942863669197709 11587779851978573875949141)
                ·
                  refine ⟨135794295140373912608779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11587779851978573875949141 135794295140373912608779)
                  ·
                    rfl

theorem cell22_1190063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_1190063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190063 prefixEnd_1190063 := by exact prefixLift 1190063
  have htrace : WordTrace (prefixWord ++ tailWord_1190063) baseStart_1190063 baseEnd_1190063 := by
    simpa [prefixWord, tailWord_1190063, baseEnd_1190063] using wordTrace_append hprefix tailTrace_1190063
  have hstable : (prefixWord ++ tailWord_1190063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190063).length < 2 ^ (prefixWord ++ tailWord_1190063).sum := by decide
  have hdescent : baseEnd_1190063 < baseStart_1190063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190112 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_1190112 : Nat := 118140960795 + 1190112 * 2 ^ 59
def prefixEnd_1190112 : Nat := 4983230072969 + 3 ^ 40 * 1190112 * 2
def baseEnd_1190112 : Nat := 407399659122501943351187

theorem tailTrace_1190112 : CollatzResearch.WordTrace tailWord_1190112 prefixEnd_1190112 407399659122501943351187 := by
  unfold tailWord_1190112
  simp only [CollatzResearch.WordTrace]
  refine ⟨21703475332217476896378295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28937967109623302528504393 21703475332217476896378295)
  ·
    refine ⟨32555212998326215344567443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21703475332217476896378295 32555212998326215344567443)
    ·
      refine ⟨48832819497489323016851165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32555212998326215344567443 48832819497489323016851165)
      ·
        refine ⟨18312307311558496131319187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48832819497489323016851165 18312307311558496131319187)
        ·
          refine ⟨27468460967337744196978781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18312307311558496131319187 27468460967337744196978781)
          ·
            refine ⟨10300672862751654073867043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27468460967337744196978781 10300672862751654073867043)
            ·
              refine ⟨15451009294127481110800565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10300672862751654073867043 15451009294127481110800565)
              ·
                refine ⟨1448532121324451354137553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15451009294127481110800565 1448532121324451354137553)
                ·
                  refine ⟨1086399090993338515603165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1448532121324451354137553 1086399090993338515603165)
                  ·
                    refine ⟨407399659122501943351187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086399090993338515603165 407399659122501943351187)
                    ·
                      rfl

theorem cell22_1190112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_1190112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190112 prefixEnd_1190112 := by exact prefixLift 1190112
  have htrace : WordTrace (prefixWord ++ tailWord_1190112) baseStart_1190112 baseEnd_1190112 := by
    simpa [prefixWord, tailWord_1190112, baseEnd_1190112] using wordTrace_append hprefix tailTrace_1190112
  have hstable : (prefixWord ++ tailWord_1190112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190112).length < 2 ^ (prefixWord ++ tailWord_1190112).sum := by decide
  have hdescent : baseEnd_1190112 < baseStart_1190112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190127 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 2, 4]
def baseStart_1190127 : Nat := 118140960795 + 1190127 * 2 ^ 59
def prefixEnd_1190127 : Nat := 4983230072969 + 3 ^ 40 * 1190127 * 2
def baseEnd_1190127 : Nat := 407404793929046904226141

theorem tailTrace_1190127 : CollatzResearch.WordTrace tailWord_1190127 prefixEnd_1190127 407404793929046904226141 := by
  unfold tailWord_1190127
  simp only [CollatzResearch.WordTrace]
  refine ⟨43407497759380611354552635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28938331839587074236368423 43407497759380611354552635)
  ·
    refine ⟨65111246639070917031828953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43407497759380611354552635 65111246639070917031828953)
    ·
      refine ⟨48833434979303187773871715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65111246639070917031828953 48833434979303187773871715)
      ·
        refine ⟨73250152468954781660807573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48833434979303187773871715 73250152468954781660807573)
        ·
          refine ⟨3433600896982255390350355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73250152468954781660807573 3433600896982255390350355)
          ·
            refine ⟨5150401345473383085525533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433600896982255390350355 5150401345473383085525533)
            ·
              refine ⟨1931400504552518657072075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5150401345473383085525533 1931400504552518657072075)
              ·
                refine ⟨2897100756828777985608113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931400504552518657072075 2897100756828777985608113)
                ·
                  refine ⟨2172825567621583489206085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897100756828777985608113 2172825567621583489206085)
                  ·
                    refine ⟨407404793929046904226141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2172825567621583489206085 407404793929046904226141)
                    ·
                      rfl

theorem cell22_1190127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_1190127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190127 prefixEnd_1190127 := by exact prefixLift 1190127
  have htrace : WordTrace (prefixWord ++ tailWord_1190127) baseStart_1190127 baseEnd_1190127 := by
    simpa [prefixWord, tailWord_1190127, baseEnd_1190127] using wordTrace_append hprefix tailTrace_1190127
  have hstable : (prefixWord ++ tailWord_1190127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190127).length < 2 ^ (prefixWord ++ tailWord_1190127).sum := by decide
  have hdescent : baseEnd_1190127 < baseStart_1190127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190146 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1190146 : Nat := 118140960795 + 1190146 * 2 ^ 59
def prefixEnd_1190146 : Nat := 4983230072969 + 3 ^ 40 * 1190146 * 2
def baseEnd_1190146 : Nat := 407411298017337188001083

theorem tailTrace_1190146 : CollatzResearch.WordTrace tailWord_1190146 prefixEnd_1190146 407411298017337188001083 := by
  unfold tailWord_1190146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852047686577944399873573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28938793830874518399662861 10852047686577944399873573)
  ·
    refine ⟨2034758941233364574976295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10852047686577944399873573 2034758941233364574976295)
    ·
      refine ⟨3052138411850046862464443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034758941233364574976295 3052138411850046862464443)
      ·
        refine ⟨4578207617775070293696665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3052138411850046862464443 4578207617775070293696665)
        ·
          refine ⟨3433655713331302720272499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4578207617775070293696665 3433655713331302720272499)
          ·
            refine ⟨5150483569996954080408749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433655713331302720272499 5150483569996954080408749)
            ·
              refine ⟨1931431338748857780153281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5150483569996954080408749 1931431338748857780153281)
              ·
                refine ⟨1448573504061643335114961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1931431338748857780153281 1448573504061643335114961)
                ·
                  refine ⟨1086430128046232501336221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1448573504061643335114961 1086430128046232501336221)
                  ·
                    refine ⟨407411298017337188001083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086430128046232501336221 407411298017337188001083)
                    ·
                      rfl

theorem cell22_1190146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1190146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190146 prefixEnd_1190146 := by exact prefixLift 1190146
  have htrace : WordTrace (prefixWord ++ tailWord_1190146) baseStart_1190146 baseEnd_1190146 := by
    simpa [prefixWord, tailWord_1190146, baseEnd_1190146] using wordTrace_append hprefix tailTrace_1190146
  have hstable : (prefixWord ++ tailWord_1190146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190146).length < 2 ^ (prefixWord ++ tailWord_1190146).sum := by decide
  have hdescent : baseEnd_1190146 < baseStart_1190146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190247 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1190247 : Nat := 118140960795 + 1190247 * 2 ^ 59
def prefixEnd_1190247 : Nat := 4983230072969 + 3 ^ 40 * 1190247 * 2
def baseEnd_1190247 : Nat := 407445872381406591225773

theorem tailTrace_1190247 : CollatzResearch.WordTrace tailWord_1190247 prefixEnd_1190247 407445872381406591225773 := by
  unfold tailWord_1190247
  simp only [CollatzResearch.WordTrace]
  refine ⟨43411874518945871848920995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28941249679297247899280663 43411874518945871848920995)
  ·
    refine ⟨65117811778418807773381493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43411874518945871848920995 65117811778418807773381493)
    ·
      refine ⟨6104794854226763228754515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65117811778418807773381493 6104794854226763228754515)
      ·
        refine ⟨9157192281340144843131773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6104794854226763228754515 9157192281340144843131773)
        ·
          refine ⟨3433947105502554316174415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9157192281340144843131773 3433947105502554316174415)
          ·
            refine ⟨5150920658253831474261623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433947105502554316174415 5150920658253831474261623)
            ·
              refine ⟨7726380987380747211392435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150920658253831474261623 7726380987380747211392435)
              ·
                refine ⟨11589571481071120817088653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7726380987380747211392435 11589571481071120817088653)
                ·
                  refine ⟨4346089305401670306408245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11589571481071120817088653 4346089305401670306408245)
                  ·
                    refine ⟨407445872381406591225773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4346089305401670306408245 407445872381406591225773)
                    ·
                      rfl

theorem cell22_1190247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1190247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190247 prefixEnd_1190247 := by exact prefixLift 1190247
  have htrace : WordTrace (prefixWord ++ tailWord_1190247) baseStart_1190247 baseEnd_1190247 := by
    simpa [prefixWord, tailWord_1190247, baseEnd_1190247] using wordTrace_append hprefix tailTrace_1190247
  have hstable : (prefixWord ++ tailWord_1190247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190247).length < 2 ^ (prefixWord ++ tailWord_1190247).sum := by decide
  have hdescent : baseEnd_1190247 < baseStart_1190247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190296 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_1190296 : Nat := 118140960795 + 1190296 * 2 ^ 59
def prefixEnd_1190296 : Nat := 4983230072969 + 3 ^ 40 * 1190296 * 2
def baseEnd_1190296 : Nat := 407462646082786796750623

theorem tailTrace_1190296 : CollatzResearch.WordTrace tailWord_1190296 prefixEnd_1190296 407462646082786796750623 := by
  unfold tailWord_1190296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21706830847884176608727371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28942441130512235478303161 21706830847884176608727371)
  ·
    refine ⟨32560246271826264913091057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21706830847884176608727371 32560246271826264913091057)
    ·
      refine ⟨24420184703869698684818293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32560246271826264913091057 24420184703869698684818293)
      ·
        refine ⟨2289392315987784251701715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24420184703869698684818293 2289392315987784251701715)
        ·
          refine ⟨3434088473981676377552573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289392315987784251701715 3434088473981676377552573)
          ·
            refine ⟨1287783177743128641582215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3434088473981676377552573 1287783177743128641582215)
            ·
              refine ⟨1931674766614692962373323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287783177743128641582215 1931674766614692962373323)
              ·
                refine ⟨2897512149922039443559985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931674766614692962373323 2897512149922039443559985)
                ·
                  refine ⟨2173134112441529582669989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897512149922039443559985 2173134112441529582669989)
                  ·
                    refine ⟨407462646082786796750623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173134112441529582669989 407462646082786796750623)
                    ·
                      rfl

theorem cell22_1190296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_1190296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190296 prefixEnd_1190296 := by exact prefixLift 1190296
  have htrace : WordTrace (prefixWord ++ tailWord_1190296) baseStart_1190296 baseEnd_1190296 := by
    simpa [prefixWord, tailWord_1190296, baseEnd_1190296] using wordTrace_append hprefix tailTrace_1190296
  have hstable : (prefixWord ++ tailWord_1190296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190296).length < 2 ^ (prefixWord ++ tailWord_1190296).sum := by decide
  have hdescent : baseEnd_1190296 < baseStart_1190296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190322 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_1190322 : Nat := 118140960795 + 1190322 * 2 ^ 59
def prefixEnd_1190322 : Nat := 4983230072969 + 3 ^ 40 * 1190322 * 2
def baseEnd_1190322 : Nat := 135823848804710465200181

theorem tailTrace_1190322 : CollatzResearch.WordTrace tailWord_1190322 prefixEnd_1190322 135823848804710465200181 := by
  unfold tailWord_1190322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10853652498418539914475305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28943073329116106438600813 10853652498418539914475305)
  ·
    refine ⟨8140239373813904935856479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10853652498418539914475305 8140239373813904935856479)
    ·
      refine ⟨12210359060720857403784719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8140239373813904935856479 12210359060720857403784719)
      ·
        refine ⟨18315538591081286105677079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12210359060720857403784719 18315538591081286105677079)
        ·
          refine ⟨27473307886621929158515619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18315538591081286105677079 27473307886621929158515619)
          ·
            refine ⟨41209961829932893737773429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27473307886621929158515619 41209961829932893737773429)
            ·
              refine ⟨3863433921556208787916259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41209961829932893737773429 3863433921556208787916259)
              ·
                refine ⟨5795150882334313181874389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863433921556208787916259 5795150882334313181874389)
                ·
                  refine ⟨135823848804710465200181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5795150882334313181874389 135823848804710465200181)
                  ·
                    rfl

theorem cell22_1190322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_1190322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190322 prefixEnd_1190322 := by exact prefixLift 1190322
  have htrace : WordTrace (prefixWord ++ tailWord_1190322) baseStart_1190322 baseEnd_1190322 := by
    simpa [prefixWord, tailWord_1190322, baseEnd_1190322] using wordTrace_append hprefix tailTrace_1190322
  have hstable : (prefixWord ++ tailWord_1190322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190322).length < 2 ^ (prefixWord ++ tailWord_1190322).sum := by decide
  have hdescent : baseEnd_1190322 < baseStart_1190322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190369 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1190369 : Nat := 118140960795 + 1190369 * 2 ^ 59
def prefixEnd_1190369 : Nat := 4983230072969 + 3 ^ 40 * 1190369 * 2
def baseEnd_1190369 : Nat := 407487635474638939675399

theorem tailTrace_1190369 : CollatzResearch.WordTrace tailWord_1190369 prefixEnd_1190369 407487635474638939675399 := by
  unfold tailWord_1190369
  simp only [CollatzResearch.WordTrace]
  refine ⟨43416324224503886684862161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28944216149669257789908107 43416324224503886684862161)
  ·
    refine ⟨32562243168377915013646621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43416324224503886684862161 32562243168377915013646621)
    ·
      refine ⟨12210841188141718130117483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32562243168377915013646621 12210841188141718130117483)
      ·
        refine ⟨18316261782212577195176225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12210841188141718130117483 18316261782212577195176225)
        ·
          refine ⟨13737196336659432896382169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18316261782212577195176225 13737196336659432896382169)
          ·
            refine ⟨10302897252494574672286627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13737196336659432896382169 10302897252494574672286627)
            ·
              refine ⟨15454345878741862008429941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10302897252494574672286627 15454345878741862008429941)
              ·
                refine ⟨1448844926132049563290307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15454345878741862008429941 1448844926132049563290307)
                ·
                  refine ⟨2173267389198074344935461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448844926132049563290307 2173267389198074344935461)
                  ·
                    refine ⟨407487635474638939675399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173267389198074344935461 407487635474638939675399)
                    ·
                      rfl

theorem cell22_1190369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1190369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190369 prefixEnd_1190369 := by exact prefixLift 1190369
  have htrace : WordTrace (prefixWord ++ tailWord_1190369) baseStart_1190369 baseEnd_1190369 := by
    simpa [prefixWord, tailWord_1190369, baseEnd_1190369] using wordTrace_append hprefix tailTrace_1190369
  have hstable : (prefixWord ++ tailWord_1190369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190369).length < 2 ^ (prefixWord ++ tailWord_1190369).sum := by decide
  have hdescent : baseEnd_1190369 < baseStart_1190369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190420 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1190420 : Nat := 118140960795 + 1190420 * 2 ^ 59
def prefixEnd_1190420 : Nat := 4983230072969 + 3 ^ 40 * 1190420 * 2
def baseEnd_1190420 : Nat := 407505093816891806650243

theorem tailTrace_1190420 : CollatzResearch.WordTrace tailWord_1190420 prefixEnd_1190420 407505093816891806650243 := by
  unfold tailWord_1190420
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709092173659561197484357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28945456231546081596645809 21709092173659561197484357)
  ·
    refine ⟨4070454782561167724528317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21709092173659561197484357 4070454782561167724528317)
    ·
      refine ⟨1526420543460437896698119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4070454782561167724528317 1526420543460437896698119)
      ·
        refine ⟨2289630815190656845047179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526420543460437896698119 2289630815190656845047179)
        ·
          refine ⟨3434446222785985267570769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289630815190656845047179 3434446222785985267570769)
          ·
            refine ⟨2575834667089488950678077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434446222785985267570769 2575834667089488950678077)
            ·
              refine ⟨965938000158558356504279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2575834667089488950678077 965938000158558356504279)
              ·
                refine ⟨1448907000237837534756419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965938000158558356504279 1448907000237837534756419)
                ·
                  refine ⟨2173360500356756302134629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448907000237837534756419 2173360500356756302134629)
                  ·
                    refine ⟨407505093816891806650243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173360500356756302134629 407505093816891806650243)
                    ·
                      rfl

theorem cell22_1190420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1190420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190420 prefixEnd_1190420 := by exact prefixLift 1190420
  have htrace : WordTrace (prefixWord ++ tailWord_1190420) baseStart_1190420 baseEnd_1190420 := by
    simpa [prefixWord, tailWord_1190420, baseEnd_1190420] using wordTrace_append hprefix tailTrace_1190420
  have hstable : (prefixWord ++ tailWord_1190420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190420).length < 2 ^ (prefixWord ++ tailWord_1190420).sum := by decide
  have hdescent : baseEnd_1190420 < baseStart_1190420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190444 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_1190444 : Nat := 118140960795 + 1190444 * 2 ^ 59
def prefixEnd_1190444 : Nat := 4983230072969 + 3 ^ 40 * 1190444 * 2
def baseEnd_1190444 : Nat := 407513309507363744050169

theorem tailTrace_1190444 : CollatzResearch.WordTrace tailWord_1190444 prefixEnd_1190444 407513309507363744050169 := by
  unfold tailWord_1190444
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709529849616087246921193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28946039799488116329228257 21709529849616087246921193)
  ·
    refine ⟨16282147387212065435190895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21709529849616087246921193 16282147387212065435190895)
    ·
      refine ⟨24423221080818098152786343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16282147387212065435190895 24423221080818098152786343)
      ·
        refine ⟨36634831621227147229179515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24423221080818098152786343 36634831621227147229179515)
        ·
          refine ⟨54952247431840720843769273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36634831621227147229179515 54952247431840720843769273)
          ·
            refine ⟨41214185573880540632826955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54952247431840720843769273 41214185573880540632826955)
            ·
              refine ⟨61821278360820810949240433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41214185573880540632826955 61821278360820810949240433)
              ·
                refine ⟨46365958770615608211930325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61821278360820810949240433 46365958770615608211930325)
                ·
                  refine ⟨1086702158686303317467117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46365958770615608211930325 1086702158686303317467117)
                  ·
                    refine ⟨407513309507363744050169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086702158686303317467117 407513309507363744050169)
                    ·
                      rfl

theorem cell22_1190444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_1190444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190444 prefixEnd_1190444 := by exact prefixLift 1190444
  have htrace : WordTrace (prefixWord ++ tailWord_1190444) baseStart_1190444 baseEnd_1190444 := by
    simpa [prefixWord, tailWord_1190444, baseEnd_1190444] using wordTrace_append hprefix tailTrace_1190444
  have hstable : (prefixWord ++ tailWord_1190444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190444).length < 2 ^ (prefixWord ++ tailWord_1190444).sum := by decide
  have hdescent : baseEnd_1190444 < baseStart_1190444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190461 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_1190461 : Nat := 118140960795 + 1190461 * 2 ^ 59
def prefixEnd_1190461 : Nat := 4983230072969 + 3 ^ 40 * 1190461 * 2
def baseEnd_1190461 : Nat := 407519128954781366375117

theorem tailTrace_1190461 : CollatzResearch.WordTrace tailWord_1190461 prefixEnd_1190461 407519128954781366375117 := by
  unfold tailWord_1190461
  simp only [CollatzResearch.WordTrace]
  refine ⟨43419679740170586397211237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28946453160113724264807491 43419679740170586397211237)
  ·
    refine ⟨8141189951281984949477107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43419679740170586397211237 8141189951281984949477107)
    ·
      refine ⟨12211784926922977424215661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8141189951281984949477107 12211784926922977424215661)
      ·
        refine ⟨4579419347596116534080873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12211784926922977424215661 4579419347596116534080873)
        ·
          refine ⟨3434564510697087400560655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4579419347596116534080873 3434564510697087400560655)
          ·
            refine ⟨5151846766045631100840983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434564510697087400560655 5151846766045631100840983)
            ·
              refine ⟨7727770149068446651261475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151846766045631100840983 7727770149068446651261475)
              ·
                refine ⟨11591655223602669976892213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7727770149068446651261475 11591655223602669976892213)
                ·
                  refine ⟨1086717677212750310333645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11591655223602669976892213 1086717677212750310333645)
                  ·
                    refine ⟨407519128954781366375117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086717677212750310333645 407519128954781366375117)
                    ·
                      rfl

theorem cell22_1190461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_1190461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190461 prefixEnd_1190461 := by exact prefixLift 1190461
  have htrace : WordTrace (prefixWord ++ tailWord_1190461) baseStart_1190461 baseEnd_1190461 := by
    simpa [prefixWord, tailWord_1190461, baseEnd_1190461] using wordTrace_append hprefix tailTrace_1190461
  have hstable : (prefixWord ++ tailWord_1190461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190461).length < 2 ^ (prefixWord ++ tailWord_1190461).sum := by decide
  have hdescent : baseEnd_1190461 < baseStart_1190461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190478 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_1190478 : Nat := 118140960795 + 1190478 * 2 ^ 59
def prefixEnd_1190478 : Nat := 4983230072969 + 3 ^ 40 * 1190478 * 2
def baseEnd_1190478 : Nat := 407524948402198988700065

theorem tailTrace_1190478 : CollatzResearch.WordTrace tailWord_1190478 prefixEnd_1190478 407524948402198988700065 := by
  unfold tailWord_1190478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427537472638624787572511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28946866520739332200386725 5427537472638624787572511)
  ·
    refine ⟨8141306208957937181358767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5427537472638624787572511 8141306208957937181358767)
    ·
      refine ⟨12211959313436905772038151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8141306208957937181358767 12211959313436905772038151)
      ·
        refine ⟨18317938970155358658057227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12211959313436905772038151 18317938970155358658057227)
        ·
          refine ⟨27476908455233037987085841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18317938970155358658057227 27476908455233037987085841)
          ·
            refine ⟨20607681341424778490314381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27476908455233037987085841 20607681341424778490314381)
            ·
              refine ⟨7727880503034291933867893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20607681341424778490314381 7727880503034291933867893)
              ·
                refine ⟨724488797159464868800115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7727880503034291933867893 724488797159464868800115)
                ·
                  refine ⟨1086733195739197303200173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724488797159464868800115 1086733195739197303200173)
                  ·
                    refine ⟨407524948402198988700065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086733195739197303200173 407524948402198988700065)
                    ·
                      rfl

theorem cell22_1190478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_1190478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190478 prefixEnd_1190478 := by exact prefixLift 1190478
  have htrace : WordTrace (prefixWord ++ tailWord_1190478) baseStart_1190478 baseEnd_1190478 := by
    simpa [prefixWord, tailWord_1190478, baseEnd_1190478] using wordTrace_append hprefix tailTrace_1190478
  have hstable : (prefixWord ++ tailWord_1190478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190478).length < 2 ^ (prefixWord ++ tailWord_1190478).sum := by decide
  have hdescent : baseEnd_1190478 < baseStart_1190478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190519 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 6]
def baseStart_1190519 : Nat := 118140960795 + 1190519 * 2 ^ 59
def prefixEnd_1190519 : Nat := 4983230072969 + 3 ^ 40 * 1190519 * 2
def baseEnd_1190519 : Nat := 135846327846696182808313

theorem tailTrace_1190519 : CollatzResearch.WordTrace tailWord_1190519 prefixEnd_1190519 135846327846696182808313 := by
  unfold tailWord_1190519
  simp only [CollatzResearch.WordTrace]
  refine ⟨43421795173960462302822611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28947863449306974868548407 43421795173960462302822611)
  ·
    refine ⟨65132692760940693454233917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43421795173960462302822611 65132692760940693454233917)
    ·
      refine ⟨24424759785352760045337719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65132692760940693454233917 24424759785352760045337719)
      ·
        refine ⟨36637139678029140068006579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24424759785352760045337719 36637139678029140068006579)
        ·
          refine ⟨54955709517043710102009869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36637139678029140068006579 54955709517043710102009869)
          ·
            refine ⟨20608391068891391288253701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54955709517043710102009869 20608391068891391288253701)
            ·
              refine ⟨3864073325417135866547569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20608391068891391288253701 3864073325417135866547569)
              ·
                refine ⟨2898054994062851899910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3864073325417135866547569 2898054994062851899910677)
                ·
                  refine ⟨135846327846696182808313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2898054994062851899910677 135846327846696182808313)
                  ·
                    rfl

theorem cell22_1190519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_1190519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190519 prefixEnd_1190519 := by exact prefixLift 1190519
  have htrace : WordTrace (prefixWord ++ tailWord_1190519) baseStart_1190519 baseEnd_1190519 := by
    simpa [prefixWord, tailWord_1190519, baseEnd_1190519] using wordTrace_append hprefix tailTrace_1190519
  have hstable : (prefixWord ++ tailWord_1190519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190519).length < 2 ^ (prefixWord ++ tailWord_1190519).sum := by decide
  have hdescent : baseEnd_1190519 < baseStart_1190519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190521 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_1190521 : Nat := 118140960795 + 1190521 * 2 ^ 59
def prefixEnd_1190521 : Nat := 4983230072969 + 3 ^ 40 * 1190521 * 2
def baseEnd_1190521 : Nat := 407539668180961209874933

theorem tailTrace_1190521 : CollatzResearch.WordTrace tailWord_1190521 prefixEnd_1190521 407539668180961209874933 := by
  unfold tailWord_1190521
  simp only [CollatzResearch.WordTrace]
  refine ⟨43421868119953216644395417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28947912079968811096263611 43421868119953216644395417)
  ·
    refine ⟨32566401089964912483296563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43421868119953216644395417 32566401089964912483296563)
    ·
      refine ⟨48849601634947368724944845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32566401089964912483296563 48849601634947368724944845)
      ·
        refine ⟨18318600613105263271854317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48849601634947368724944845 18318600613105263271854317)
        ·
          refine ⟨6869475229914473726945369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18318600613105263271854317 6869475229914473726945369)
          ·
            refine ⟨5152106422435855295209027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6869475229914473726945369 5152106422435855295209027)
            ·
              refine ⟨7728159633653782942813541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152106422435855295209027 7728159633653782942813541)
              ·
                refine ⟨1449029931310084301777539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7728159633653782942813541 1449029931310084301777539)
                ·
                  refine ⟨2173544896965126452666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449029931310084301777539 2173544896965126452666309)
                  ·
                    refine ⟨407539668180961209874933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173544896965126452666309 407539668180961209874933)
                    ·
                      rfl

theorem cell22_1190521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_1190521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190521 prefixEnd_1190521 := by exact prefixLift 1190521
  have htrace : WordTrace (prefixWord ++ tailWord_1190521) baseStart_1190521 baseEnd_1190521 := by
    simpa [prefixWord, tailWord_1190521, baseEnd_1190521] using wordTrace_append hprefix tailTrace_1190521
  have hstable : (prefixWord ++ tailWord_1190521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190521).length < 2 ^ (prefixWord ++ tailWord_1190521).sum := by decide
  have hdescent : baseEnd_1190521 < baseStart_1190521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190551 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 4, 3]
def baseStart_1190551 : Nat := 118140960795 + 1190551 * 2 ^ 59
def prefixEnd_1190551 : Nat := 4983230072969 + 3 ^ 40 * 1190551 * 2
def baseEnd_1190551 : Nat := 407549937794051131624841

theorem tailTrace_1190551 : CollatzResearch.WordTrace tailWord_1190551 prefixEnd_1190551 407549937794051131624841 := by
  unfold tailWord_1190551
  simp only [CollatzResearch.WordTrace]
  refine ⟨43422962309844531767987507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28948641539896354511991671 43422962309844531767987507)
  ·
    refine ⟨65134443464766797651981261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43422962309844531767987507 65134443464766797651981261)
    ·
      refine ⟨24425416299287549119492973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65134443464766797651981261 24425416299287549119492973)
      ·
        refine ⟨9159531112232830919809865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24425416299287549119492973 9159531112232830919809865)
        ·
          refine ⟨6869648334174623189857399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9159531112232830919809865 6869648334174623189857399)
          ·
            refine ⟨10304472501261934784786099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6869648334174623189857399 10304472501261934784786099)
            ·
              refine ⟨15456708751892902177179149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10304472501261934784786099 15456708751892902177179149)
              ·
                refine ⟨5796265781959838316442181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15456708751892902177179149 5796265781959838316442181)
                ·
                  refine ⟨1086799834117469684332909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5796265781959838316442181 1086799834117469684332909)
                  ·
                    refine ⟨407549937794051131624841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1086799834117469684332909 407549937794051131624841)
                    ·
                      rfl

theorem cell22_1190551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_1190551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190551 prefixEnd_1190551 := by exact prefixLift 1190551
  have htrace : WordTrace (prefixWord ++ tailWord_1190551) baseStart_1190551 baseEnd_1190551 := by
    simpa [prefixWord, tailWord_1190551, baseEnd_1190551] using wordTrace_append hprefix tailTrace_1190551
  have hstable : (prefixWord ++ tailWord_1190551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190551).length < 2 ^ (prefixWord ++ tailWord_1190551).sum := by decide
  have hdescent : baseEnd_1190551 < baseStart_1190551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190553 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 4]
def baseStart_1190553 : Nat := 118140960795 + 1190553 * 2 ^ 59
def prefixEnd_1190553 : Nat := 4983230072969 + 3 ^ 40 * 1190553 * 2
def baseEnd_1190553 : Nat := 135850207478307931024945

theorem tailTrace_1190553 : CollatzResearch.WordTrace tailWord_1190553 prefixEnd_1190553 135850207478307931024945 := by
  unfold tailWord_1190553
  simp only [CollatzResearch.WordTrace]
  refine ⟨43423035255837286109560313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28948690170558190739706875 43423035255837286109560313)
  ·
    refine ⟨32567276441877964582170235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43423035255837286109560313 32567276441877964582170235)
    ·
      refine ⟨48850914662816946873255353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32567276441877964582170235 48850914662816946873255353)
      ·
        refine ⟨36638185997112710154941515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48850914662816946873255353 36638185997112710154941515)
        ·
          refine ⟨54957278995669065232412273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36638185997112710154941515 54957278995669065232412273)
          ·
            refine ⟨41217959246751798924309205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54957278995669065232412273 41217959246751798924309205)
            ·
              refine ⟨966045919845745287288497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41217959246751798924309205 966045919845745287288497)
              ·
                refine ⟨724534439884308965466373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966045919845745287288497 724534439884308965466373)
                ·
                  refine ⟨135850207478307931024945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724534439884308965466373 135850207478307931024945)
                  ·
                    rfl

theorem cell22_1190553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_1190553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190553 prefixEnd_1190553 := by exact prefixLift 1190553
  have htrace : WordTrace (prefixWord ++ tailWord_1190553) baseStart_1190553 baseEnd_1190553 := by
    simpa [prefixWord, tailWord_1190553, baseEnd_1190553] using wordTrace_append hprefix tailTrace_1190553
  have hstable : (prefixWord ++ tailWord_1190553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190553).length < 2 ^ (prefixWord ++ tailWord_1190553).sum := by decide
  have hdescent : baseEnd_1190553 < baseStart_1190553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190581 : List Nat := [1, 3, 3, 3, 1, 1, 2, 8]
def baseStart_1190581 : Nat := 118140960795 + 1190581 * 2 ^ 59
def prefixEnd_1190581 : Nat := 4983230072969 + 3 ^ 40 * 1190581 * 2
def baseEnd_1190581 : Nat := 45284467489682339263861

theorem tailTrace_1190581 : CollatzResearch.WordTrace tailWord_1190581 prefixEnd_1190581 45284467489682339263861 := by
  unfold tailWord_1190581
  simp only [CollatzResearch.WordTrace]
  refine ⟨43424056499735846891579597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28949370999823897927719731 43424056499735846891579597)
  ·
    refine ⟨16284021187400942584342349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43424056499735846891579597 16284021187400942584342349)
    ·
      refine ⟨6106507945275353469128381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16284021187400942584342349 6106507945275353469128381)
      ·
        refine ⟨2289940479478257550923143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6106507945275353469128381 2289940479478257550923143)
        ·
          refine ⟨3434910719217386326384715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289940479478257550923143 3434910719217386326384715)
          ·
            refine ⟨5152366078826079489577073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434910719217386326384715 5152366078826079489577073)
            ·
              refine ⟨3864274559119559617182805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5152366078826079489577073 3864274559119559617182805)
              ·
                refine ⟨45284467489682339263861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3864274559119559617182805 45284467489682339263861)
                ·
                  rfl

theorem cell22_1190581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 8].length) (baseStart_1190581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190581 prefixEnd_1190581 := by exact prefixLift 1190581
  have htrace : WordTrace (prefixWord ++ tailWord_1190581) baseStart_1190581 baseEnd_1190581 := by
    simpa [prefixWord, tailWord_1190581, baseEnd_1190581] using wordTrace_append hprefix tailTrace_1190581
  have hstable : (prefixWord ++ tailWord_1190581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190581).length < 2 ^ (prefixWord ++ tailWord_1190581).sum := by decide
  have hdescent : baseEnd_1190581 < baseStart_1190581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190583 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 2, 4]
def baseStart_1190583 : Nat := 118140960795 + 1190583 * 2 ^ 59
def prefixEnd_1190583 : Nat := 4983230072969 + 3 ^ 40 * 1190583 * 2
def baseEnd_1190583 : Nat := 407560892048013714824743

theorem tailTrace_1190583 : CollatzResearch.WordTrace tailWord_1190583 prefixEnd_1190583 407560892048013714824743 := by
  unfold tailWord_1190583
  simp only [CollatzResearch.WordTrace]
  refine ⟨43424129445728601233152403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28949419630485734155434935 43424129445728601233152403)
  ·
    refine ⟨65136194168592901849728605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43424129445728601233152403 65136194168592901849728605)
    ·
      refine ⟨24426072813222338193648227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65136194168592901849728605 24426072813222338193648227)
      ·
        refine ⟨36639109219833507290472341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24426072813222338193648227 36639109219833507290472341)
        ·
          refine ⟨1717458244679695654240891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36639109219833507290472341 1717458244679695654240891)
          ·
            refine ⟨2576187367019543481361337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717458244679695654240891 2576187367019543481361337)
            ·
              refine ⟨1932140525264657611021003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576187367019543481361337 1932140525264657611021003)
              ·
                refine ⟨2898210787896986416531505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932140525264657611021003 2898210787896986416531505)
                ·
                  refine ⟨2173658090922739812398629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2898210787896986416531505 2173658090922739812398629)
                  ·
                    refine ⟨407560892048013714824743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173658090922739812398629 407560892048013714824743)
                    ·
                      rfl

theorem cell22_1190583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_1190583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190583 prefixEnd_1190583 := by exact prefixLift 1190583
  have htrace : WordTrace (prefixWord ++ tailWord_1190583) baseStart_1190583 baseEnd_1190583 := by
    simpa [prefixWord, tailWord_1190583, baseEnd_1190583] using wordTrace_append hprefix tailTrace_1190583
  have hstable : (prefixWord ++ tailWord_1190583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190583).length < 2 ^ (prefixWord ++ tailWord_1190583).sum := by decide
  have hdescent : baseEnd_1190583 < baseStart_1190583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190598 : List Nat := [6, 1, 2, 1, 12]
def baseStart_1190598 : Nat := 118140960795 + 1190598 * 2 ^ 59
def prefixEnd_1190598 : Nat := 4983230072969 + 3 ^ 40 * 1190598 * 2
def baseEnd_1190598 : Nat := 1677226447961146813579

theorem tailTrace_1190598 : CollatzResearch.WordTrace tailWord_1190598 prefixEnd_1190598 1677226447961146813579 := by
  unfold tailWord_1190598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357021141896070587342139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28949784360449505863298965 1357021141896070587342139)
  ·
    refine ⟨2035531712844105881013209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357021141896070587342139 2035531712844105881013209)
    ·
      refine ⟨1526648784633079410759907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2035531712844105881013209 1526648784633079410759907)
      ·
        refine ⟨2289973176949619116139861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526648784633079410759907 2289973176949619116139861)
        ·
          refine ⟨1677226447961146813579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2289973176949619116139861 1677226447961146813579)
          ·
            rfl

theorem cell22_1190598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 12].length) (baseStart_1190598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190598 prefixEnd_1190598 := by exact prefixLift 1190598
  have htrace : WordTrace (prefixWord ++ tailWord_1190598) baseStart_1190598 baseEnd_1190598 := by
    simpa [prefixWord, tailWord_1190598, baseEnd_1190598] using wordTrace_append hprefix tailTrace_1190598
  have hstable : (prefixWord ++ tailWord_1190598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190598).length < 2 ^ (prefixWord ++ tailWord_1190598).sum := by decide
  have hdescent : baseEnd_1190598 < baseStart_1190598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190658 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1190658 : Nat := 118140960795 + 1190658 * 2 ^ 59
def prefixEnd_1190658 : Nat := 4983230072969 + 3 ^ 40 * 1190658 * 2
def baseEnd_1190658 : Nat := 407586566080738519199513

theorem tailTrace_1190658 : CollatzResearch.WordTrace tailWord_1190658 prefixEnd_1190658 407586566080738519199513 := by
  unfold tailWord_1190658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856716230114222260533157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28951243280304592694755085 10856716230114222260533157)
  ·
    refine ⟨2035634293146416673849967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10856716230114222260533157 2035634293146416673849967)
    ·
      refine ⟨3053451439719625010774951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2035634293146416673849967 3053451439719625010774951)
      ·
        refine ⟨4580177159579437516162427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053451439719625010774951 4580177159579437516162427)
        ·
          refine ⟨6870265739369156274243641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4580177159579437516162427 6870265739369156274243641)
          ·
            refine ⟨5152699304526867205682731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6870265739369156274243641 5152699304526867205682731)
            ·
              refine ⟨7729048956790300808524097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152699304526867205682731 7729048956790300808524097)
              ·
                refine ⟨5796786717592725606393073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7729048956790300808524097 5796786717592725606393073)
                ·
                  refine ⟨4347590038194544204794805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796786717592725606393073 4347590038194544204794805)
                  ·
                    refine ⟨407586566080738519199513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4347590038194544204794805 407586566080738519199513)
                    ·
                      rfl

theorem cell22_1190658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1190658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190658 prefixEnd_1190658 := by exact prefixLift 1190658
  have htrace : WordTrace (prefixWord ++ tailWord_1190658) baseStart_1190658 baseEnd_1190658 := by
    simpa [prefixWord, tailWord_1190658, baseEnd_1190658] using wordTrace_append hprefix tailTrace_1190658
  have hstable : (prefixWord ++ tailWord_1190658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190658).length < 2 ^ (prefixWord ++ tailWord_1190658).sum := by decide
  have hdescent : baseEnd_1190658 < baseStart_1190658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190671 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 6]
def baseStart_1190671 : Nat := 118140960795 + 1190671 * 2 ^ 59
def prefixEnd_1190671 : Nat := 4983230072969 + 3 ^ 40 * 1190671 * 2
def baseEnd_1190671 : Nat := 135863672082136939541491

theorem tailTrace_1190671 : CollatzResearch.WordTrace tailWord_1190671 prefixEnd_1190671 135863672082136939541491 := by
  unfold tailWord_1190671
  simp only [CollatzResearch.WordTrace]
  refine ⟨43427339069409792262355867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28951559379606528174903911 43427339069409792262355867)
  ·
    refine ⟨65141008604114688393533801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43427339069409792262355867 65141008604114688393533801)
    ·
      refine ⟨48855756453086016295150351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65141008604114688393533801 48855756453086016295150351)
      ·
        refine ⟨73283634679629024442725527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48855756453086016295150351 73283634679629024442725527)
        ·
          refine ⟨109925452019443536664088291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73283634679629024442725527 109925452019443536664088291)
          ·
            refine ⟨164888178029165304996132437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109925452019443536664088291 164888178029165304996132437)
            ·
              refine ⟨1932283336279280917923427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 164888178029165304996132437 1932283336279280917923427)
              ·
                refine ⟨2898425004418921376885141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932283336279280917923427 2898425004418921376885141)
                ·
                  refine ⟨135863672082136939541491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2898425004418921376885141 135863672082136939541491)
                  ·
                    rfl

theorem cell22_1190671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 6].length) (baseStart_1190671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190671 prefixEnd_1190671 := by exact prefixLift 1190671
  have htrace : WordTrace (prefixWord ++ tailWord_1190671) baseStart_1190671 baseEnd_1190671 := by
    simpa [prefixWord, tailWord_1190671, baseEnd_1190671] using wordTrace_append hprefix tailTrace_1190671
  have hstable : (prefixWord ++ tailWord_1190671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190671).length < 2 ^ (prefixWord ++ tailWord_1190671).sum := by decide
  have hdescent : baseEnd_1190671 < baseStart_1190671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190690 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1190690 : Nat := 118140960795 + 1190690 * 2 ^ 59
def prefixEnd_1190690 : Nat := 4983230072969 + 3 ^ 40 * 1190690 * 2
def baseEnd_1190690 : Nat := 407597520334701102399415

theorem tailTrace_1190690 : CollatzResearch.WordTrace tailWord_1190690 prefixEnd_1190690 407597520334701102399415 := by
  unfold tailWord_1190690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10857008014085239626824381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28952021370893972338198349 10857008014085239626824381)
  ·
    refine ⟨4071378005281964860059143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10857008014085239626824381 4071378005281964860059143)
    ·
      refine ⟨6107067007922947290088715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071378005281964860059143 6107067007922947290088715)
      ·
        refine ⟨9160600511884420935133073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6107067007922947290088715 9160600511884420935133073)
        ·
          refine ⟨6870450383913315701349805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160600511884420935133073 6870450383913315701349805)
          ·
            refine ⟨2576418893967493388006177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6870450383913315701349805 2576418893967493388006177)
            ·
              refine ⟨1932314170475620041004633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576418893967493388006177 1932314170475620041004633)
              ·
                refine ⟨1449235627856715030753475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932314170475620041004633 1449235627856715030753475)
                ·
                  refine ⟨2173853441785072546130213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449235627856715030753475 2173853441785072546130213)
                  ·
                    refine ⟨407597520334701102399415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173853441785072546130213 407597520334701102399415)
                    ·
                      rfl

theorem cell22_1190690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1190690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190690 prefixEnd_1190690 := by exact prefixLift 1190690
  have htrace : WordTrace (prefixWord ++ tailWord_1190690) baseStart_1190690 baseEnd_1190690 := by
    simpa [prefixWord, tailWord_1190690, baseEnd_1190690] using wordTrace_append hprefix tailTrace_1190690
  have hstable : (prefixWord ++ tailWord_1190690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190690).length < 2 ^ (prefixWord ++ tailWord_1190690).sum := by decide
  have hdescent : baseEnd_1190690 < baseStart_1190690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190793 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_1190793 : Nat := 118140960795 + 1190793 * 2 ^ 59
def prefixEnd_1190793 : Nat := 4983230072969 + 3 ^ 40 * 1190793 * 2
def baseEnd_1190793 : Nat := 407632779339643167074099

theorem tailTrace_1190793 : CollatzResearch.WordTrace tailWord_1190793 prefixEnd_1190793 407632779339643167074099 := by
  unfold tailWord_1190793
  simp only [CollatzResearch.WordTrace]
  refine ⟨43431788774967807098297033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28954525849978538065531355 43431788774967807098297033)
  ·
    refine ⟨32573841581225855323722775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43431788774967807098297033 32573841581225855323722775)
    ·
      refine ⟨48860762371838782985584163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32573841581225855323722775 48860762371838782985584163)
      ·
        refine ⟨73291143557758174478376245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48860762371838782985584163 73291143557758174478376245)
        ·
          refine ⟨6871044708539828857347773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73291143557758174478376245 6871044708539828857347773)
          ·
            refine ⟨2576641765702435821505415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6871044708539828857347773 2576641765702435821505415)
            ·
              refine ⟨3864962648553653732258123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576641765702435821505415 3864962648553653732258123)
              ·
                refine ⟨5797443972830480598387185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864962648553653732258123 5797443972830480598387185)
                ·
                  refine ⟨4348082979622860448790389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797443972830480598387185 4348082979622860448790389)
                  ·
                    refine ⟨407632779339643167074099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4348082979622860448790389 407632779339643167074099)
                    ·
                      rfl

theorem cell22_1190793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_1190793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190793 prefixEnd_1190793 := by exact prefixLift 1190793
  have htrace : WordTrace (prefixWord ++ tailWord_1190793) baseStart_1190793 baseEnd_1190793 := by
    simpa [prefixWord, tailWord_1190793, baseEnd_1190793] using wordTrace_append hprefix tailTrace_1190793
  have hstable : (prefixWord ++ tailWord_1190793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190793).length < 2 ^ (prefixWord ++ tailWord_1190793).sum := by decide
  have hdescent : baseEnd_1190793 < baseStart_1190793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190829 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1190829 : Nat := 118140960795 + 1190829 * 2 ^ 59
def prefixEnd_1190829 : Nat := 4983230072969 + 3 ^ 40 * 1190829 * 2
def baseEnd_1190829 : Nat := 135881700958450357724663

theorem tailTrace_1190829 : CollatzResearch.WordTrace tailWord_1190829 prefixEnd_1190829 135881700958450357724663 := by
  unfold tailWord_1190829
  simp only [CollatzResearch.WordTrace]
  refine ⟨43433101802837385246607541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28955401201891590164405027 43433101802837385246607541)
  ·
    refine ⟨4071853294016004866869457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43433101802837385246607541 4071853294016004866869457)
    ·
      refine ⟨3053889970512003650152093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4071853294016004866869457 3053889970512003650152093)
      ·
        refine ⟨1145208738942001368807035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3053889970512003650152093 1145208738942001368807035)
        ·
          refine ⟨1717813108413002053210553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145208738942001368807035 1717813108413002053210553)
          ·
            refine ⟨1288359831309751539907915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717813108413002053210553 1288359831309751539907915)
            ·
              refine ⟨1932539746964627309861873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288359831309751539907915 1932539746964627309861873)
              ·
                refine ⟨1449404810223470482396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932539746964627309861873 1449404810223470482396405)
                ·
                  refine ⟨135881700958450357724663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449404810223470482396405 135881700958450357724663)
                  ·
                    rfl

theorem cell22_1190829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1190829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190829 prefixEnd_1190829 := by exact prefixLift 1190829
  have htrace : WordTrace (prefixWord ++ tailWord_1190829) baseStart_1190829 baseEnd_1190829 := by
    simpa [prefixWord, tailWord_1190829, baseEnd_1190829] using wordTrace_append hprefix tailTrace_1190829
  have hstable : (prefixWord ++ tailWord_1190829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190829).length < 2 ^ (prefixWord ++ tailWord_1190829).sum := by decide
  have hdescent : baseEnd_1190829 < baseStart_1190829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190840 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_1190840 : Nat := 118140960795 + 1190840 * 2 ^ 59
def prefixEnd_1190840 : Nat := 4983230072969 + 3 ^ 40 * 1190840 * 2
def baseEnd_1190840 : Nat := 135882956133383570382985

theorem tailTrace_1190840 : CollatzResearch.WordTrace tailWord_1190840 prefixEnd_1190840 135882956133383570382985 := by
  unfold tailWord_1190840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716751502898767062628987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28955668670531689416838649 21716751502898767062628987)
  ·
    refine ⟨32575127254348150593943481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21716751502898767062628987 32575127254348150593943481)
    ·
      refine ⟨24431345440761112945457611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32575127254348150593943481 24431345440761112945457611)
      ·
        refine ⟨36647018161141669418186417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24431345440761112945457611 36647018161141669418186417)
        ·
          refine ⟨27485263620856252063639813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36647018161141669418186417 27485263620856252063639813)
          ·
            refine ⟨5153486928910547261932465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27485263620856252063639813 5153486928910547261932465)
            ·
              refine ⟨3865115196682910446449349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153486928910547261932465 3865115196682910446449349)
              ·
                refine ⟨724709099378045708709253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3865115196682910446449349 724709099378045708709253)
                ·
                  refine ⟨135882956133383570382985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724709099378045708709253 135882956133383570382985)
                  ·
                    rfl

theorem cell22_1190840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_1190840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190840 prefixEnd_1190840 := by exact prefixLift 1190840
  have htrace : WordTrace (prefixWord ++ tailWord_1190840) baseStart_1190840 baseEnd_1190840 := by
    simpa [prefixWord, tailWord_1190840, baseEnd_1190840] using wordTrace_append hprefix tailTrace_1190840
  have hstable : (prefixWord ++ tailWord_1190840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190840).length < 2 ^ (prefixWord ++ tailWord_1190840).sum := by decide
  have hdescent : baseEnd_1190840 < baseStart_1190840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190855 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1190855 : Nat := 118140960795 + 1190855 * 2 ^ 59
def prefixEnd_1190855 : Nat := 4983230072969 + 3 ^ 40 * 1190855 * 2
def baseEnd_1190855 : Nat := 407654003206695672023909

theorem tailTrace_1190855 : CollatzResearch.WordTrace tailWord_1190855 prefixEnd_1190855 407654003206695672023909 := by
  unfold tailWord_1190855
  simp only [CollatzResearch.WordTrace]
  refine ⟨43434050100743191687054019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28956033400495461124702679 43434050100743191687054019)
  ·
    refine ⟨65151075151114787530581029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43434050100743191687054019 65151075151114787530581029)
    ·
      refine ⟨12215826590834022661983943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65151075151114787530581029 12215826590834022661983943)
      ·
        refine ⟨18323739886251033992975915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12215826590834022661983943 18323739886251033992975915)
        ·
          refine ⟨27485609829376550989463873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18323739886251033992975915 27485609829376550989463873)
          ·
            refine ⟨20614207372032413242097905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27485609829376550989463873 20614207372032413242097905)
            ·
              refine ⟨15460655529024309931573429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20614207372032413242097905 15460655529024309931573429)
              ·
                refine ⟨1449436455846029056085009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15460655529024309931573429 1449436455846029056085009)
                ·
                  refine ⟨1087077341884521792063757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449436455846029056085009 1087077341884521792063757)
                  ·
                    refine ⟨407654003206695672023909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087077341884521792063757 407654003206695672023909)
                    ·
                      rfl

theorem cell22_1190855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1190855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190855 prefixEnd_1190855 := by exact prefixLift 1190855
  have htrace : WordTrace (prefixWord ++ tailWord_1190855) baseStart_1190855 baseEnd_1190855 := by
    simpa [prefixWord, tailWord_1190855, baseEnd_1190855] using wordTrace_append hprefix tailTrace_1190855
  have hstable : (prefixWord ++ tailWord_1190855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190855).length < 2 ^ (prefixWord ++ tailWord_1190855).sum := by decide
  have hdescent : baseEnd_1190855 < baseStart_1190855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190951 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1190951 : Nat := 118140960795 + 1190951 * 2 ^ 59
def prefixEnd_1190951 : Nat := 4983230072969 + 3 ^ 40 * 1190951 * 2
def baseEnd_1190951 : Nat := 407686865968583421623615

theorem tailTrace_1190951 : CollatzResearch.WordTrace tailWord_1190951 prefixEnd_1190951 407686865968583421623615 := by
  unfold tailWord_1190951
  simp only [CollatzResearch.WordTrace]
  refine ⟨43437551508395400082548707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28958367672263600055032471 43437551508395400082548707)
  ·
    refine ⟨65156327262593100123823061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43437551508395400082548707 65156327262593100123823061)
    ·
      refine ⟨1527101420217025784152103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 65156327262593100123823061 1527101420217025784152103)
      ·
        refine ⟨2290652130325538676228155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527101420217025784152103 2290652130325538676228155)
        ·
          refine ⟨3435978195488308014342233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290652130325538676228155 3435978195488308014342233)
          ·
            refine ⟨2576983646616231010756675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435978195488308014342233 2576983646616231010756675)
            ·
              refine ⟨3865475469924346516135013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576983646616231010756675 3865475469924346516135013)
              ·
                refine ⟨724776650610814971775315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3865475469924346516135013 724776650610814971775315)
                ·
                  refine ⟨1087164975916222457662973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724776650610814971775315 1087164975916222457662973)
                  ·
                    refine ⟨407686865968583421623615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087164975916222457662973 407686865968583421623615)
                    ·
                      rfl

theorem cell22_1190951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1190951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190951 prefixEnd_1190951 := by exact prefixLift 1190951
  have htrace : WordTrace (prefixWord ++ tailWord_1190951) baseStart_1190951 baseEnd_1190951 := by
    simpa [prefixWord, tailWord_1190951, baseEnd_1190951] using wordTrace_append hprefix tailTrace_1190951
  have hstable : (prefixWord ++ tailWord_1190951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190951).length < 2 ^ (prefixWord ++ tailWord_1190951).sum := by decide
  have hdescent : baseEnd_1190951 < baseStart_1190951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190990 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1190990 : Nat := 118140960795 + 1190990 * 2 ^ 59
def prefixEnd_1190990 : Nat := 4983230072969 + 3 ^ 40 * 1190990 * 2
def baseEnd_1190990 : Nat := 407700216465600319898495

theorem tailTrace_1190990 : CollatzResearch.WordTrace tailWord_1190990 prefixEnd_1190990 407700216465600319898495 := by
  unfold tailWord_1190990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429871744406763717902303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28959315970169406495478949 5429871744406763717902303)
  ·
    refine ⟨8144807616610145576853455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429871744406763717902303 8144807616610145576853455)
    ·
      refine ⟨12217211424915218365280183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144807616610145576853455 12217211424915218365280183)
      ·
        refine ⟨18325817137372827547920275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12217211424915218365280183 18325817137372827547920275)
        ·
          refine ⟨27488725706059241321880413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18325817137372827547920275 27488725706059241321880413)
          ·
            refine ⟨10308272139772215495705155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27488725706059241321880413 10308272139772215495705155)
            ·
              refine ⟨15462408209658323243557733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10308272139772215495705155 15462408209658323243557733)
              ·
                refine ⟨2899201539310935608167075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15462408209658323243557733 2899201539310935608167075)
                ·
                  refine ⟨4348802308966403412250613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899201539310935608167075 4348802308966403412250613)
                  ·
                    refine ⟨407700216465600319898495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4348802308966403412250613 407700216465600319898495)
                    ·
                      rfl

theorem cell22_1190990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1190990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190990 prefixEnd_1190990 := by exact prefixLift 1190990
  have htrace : WordTrace (prefixWord ++ tailWord_1190990) baseStart_1190990 baseEnd_1190990 := by
    simpa [prefixWord, tailWord_1190990, baseEnd_1190990] using wordTrace_append hprefix tailTrace_1190990
  have hstable : (prefixWord ++ tailWord_1190990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190990).length < 2 ^ (prefixWord ++ tailWord_1190990).sum := by decide
  have hdescent : baseEnd_1190990 < baseStart_1190990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190994 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_1190994 : Nat := 118140960795 + 1190994 * 2 ^ 59
def prefixEnd_1190994 : Nat := 4983230072969 + 3 ^ 40 * 1190994 * 2
def baseEnd_1190994 : Nat := 407701585747345642798483

theorem tailTrace_1190994 : CollatzResearch.WordTrace tailWord_1190994 prefixEnd_1190994 407701585747345642798483 := by
  unfold tailWord_1190994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859779961809904606591009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28959413231493078950909357 10859779961809904606591009)
  ·
    refine ⟨8144834971357428454943257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10859779961809904606591009 8144834971357428454943257)
    ·
      refine ⟨6108626228518071341207443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8144834971357428454943257 6108626228518071341207443)
      ·
        refine ⟨9162939342777107011811165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6108626228518071341207443 9162939342777107011811165)
        ·
          refine ⟨3436102253541415129429187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9162939342777107011811165 3436102253541415129429187)
          ·
            refine ⟨5154153380312122694143781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436102253541415129429187 5154153380312122694143781)
            ·
              refine ⟨966403758808523005151959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5154153380312122694143781 966403758808523005151959)
              ·
                refine ⟨1449605638212784507727939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966403758808523005151959 1449605638212784507727939)
                ·
                  refine ⟨2174408457319176761591909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449605638212784507727939 2174408457319176761591909)
                  ·
                    refine ⟨407701585747345642798483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2174408457319176761591909 407701585747345642798483)
                    ·
                      rfl

theorem cell22_1190994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_1190994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190994 prefixEnd_1190994 := by exact prefixLift 1190994
  have htrace : WordTrace (prefixWord ++ tailWord_1190994) baseStart_1190994 baseEnd_1190994 := by
    simpa [prefixWord, tailWord_1190994, baseEnd_1190994] using wordTrace_append hprefix tailTrace_1190994
  have hstable : (prefixWord ++ tailWord_1190994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190994).length < 2 ^ (prefixWord ++ tailWord_1190994).sum := by decide
  have hdescent : baseEnd_1190994 < baseStart_1190994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190998 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1190998 : Nat := 118140960795 + 1190998 * 2 ^ 59
def prefixEnd_1190998 : Nat := 4983230072969 + 3 ^ 40 * 1190998 * 2
def baseEnd_1190998 : Nat := 135900985009696988566157

theorem tailTrace_1190998 : CollatzResearch.WordTrace tailWord_1190998 prefixEnd_1190998 135900985009696988566157 := by
  unfold tailWord_1190998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714954108701570444344353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28959510492816751406339765 2714954108701570444344353)
  ·
    refine ⟨2036215581526177833258265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2714954108701570444344353 2036215581526177833258265)
    ·
      refine ⟨1527161686144633374943699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036215581526177833258265 1527161686144633374943699)
      ·
        refine ⟨2290742529216950062415549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527161686144633374943699 2290742529216950062415549)
        ·
          refine ⟨859028448456356273405831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2290742529216950062415549 859028448456356273405831)
          ·
            refine ⟨1288542672684534410108747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859028448456356273405831 1288542672684534410108747)
            ·
              refine ⟨1932814009026801615163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288542672684534410108747 1932814009026801615163121)
              ·
                refine ⟨1449610506770101211372341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932814009026801615163121 1449610506770101211372341)
                ·
                  refine ⟨135900985009696988566157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449610506770101211372341 135900985009696988566157)
                  ·
                    rfl

theorem cell22_1190998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1190998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1190998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1190998 prefixEnd_1190998 := by exact prefixLift 1190998
  have htrace : WordTrace (prefixWord ++ tailWord_1190998) baseStart_1190998 baseEnd_1190998 := by
    simpa [prefixWord, tailWord_1190998, baseEnd_1190998] using wordTrace_append hprefix tailTrace_1190998
  have hstable : (prefixWord ++ tailWord_1190998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190998).length < 2 ^ (prefixWord ++ tailWord_1190998).sum := by decide
  have hdescent : baseEnd_1190998 < baseStart_1190998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191024 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_1191024 : Nat := 118140960795 + 1191024 * 2 ^ 59
def prefixEnd_1191024 : Nat := 4983230072969 + 3 ^ 40 * 1191024 * 2
def baseEnd_1191024 : Nat := 407711855360435564548391

theorem tailTrace_1191024 : CollatzResearch.WordTrace tailWord_1191024 prefixEnd_1191024 407711855360435564548391 := by
  unfold tailWord_1191024
  simp only [CollatzResearch.WordTrace]
  refine ⟨21720107018565466774978063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28960142691420622366637417 21720107018565466774978063)
  ·
    refine ⟨32580160527848200162467095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21720107018565466774978063 32580160527848200162467095)
    ·
      refine ⟨48870240791772300243700643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32580160527848200162467095 48870240791772300243700643)
      ·
        refine ⟨73305361187658450365550965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48870240791772300243700643 73305361187658450365550965)
        ·
          refine ⟨6872377611342979721770403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73305361187658450365550965 6872377611342979721770403)
          ·
            refine ⟨10308566417014469582655605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6872377611342979721770403 10308566417014469582655605)
            ·
              refine ⟨966428101595106523373963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10308566417014469582655605 966428101595106523373963)
              ·
                refine ⟨1449642152392659785060945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966428101595106523373963 1449642152392659785060945)
                ·
                  refine ⟨1087231614294494838795709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449642152392659785060945 1087231614294494838795709)
                  ·
                    refine ⟨407711855360435564548391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087231614294494838795709 407711855360435564548391)
                    ·
                      rfl

theorem cell22_1191024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_1191024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191024 prefixEnd_1191024 := by exact prefixLift 1191024
  have htrace : WordTrace (prefixWord ++ tailWord_1191024) baseStart_1191024 baseEnd_1191024 := by
    simpa [prefixWord, tailWord_1191024, baseEnd_1191024] using wordTrace_append hprefix tailTrace_1191024
  have hstable : (prefixWord ++ tailWord_1191024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191024).length < 2 ^ (prefixWord ++ tailWord_1191024).sum := by decide
  have hdescent : baseEnd_1191024 < baseStart_1191024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191112 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_1191112 : Nat := 118140960795 + 1191112 * 2 ^ 59
def prefixEnd_1191112 : Nat := 4983230072969 + 3 ^ 40 * 1191112 * 2
def baseEnd_1191112 : Nat := 407741979558832668348121

theorem tailTrace_1191112 : CollatzResearch.WordTrace tailWord_1191112 prefixEnd_1191112 407741979558832668348121 := by
  unfold tailWord_1191112
  simp only [CollatzResearch.WordTrace]
  refine ⟨21721711830406062289579795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28962282440541416386106393 21721711830406062289579795)
  ·
    refine ⟨32582567745609093434369693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21721711830406062289579795 32582567745609093434369693)
    ·
      refine ⟨12218462904603410037888635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32582567745609093434369693 12218462904603410037888635)
      ·
        refine ⟨18327694356905115056832953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12218462904603410037888635 18327694356905115056832953)
        ·
          refine ⟨13745770767678836292624715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18327694356905115056832953 13745770767678836292624715)
          ·
            refine ⟨20618656151518254438937073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13745770767678836292624715 20618656151518254438937073)
            ·
              refine ⟨15463992113638690829202805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20618656151518254438937073 15463992113638690829202805)
              ·
                refine ⟨1449749260653627265237763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15463992113638690829202805 1449749260653627265237763)
                ·
                  refine ⟨2174623890980440897856645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449749260653627265237763 2174623890980440897856645)
                  ·
                    refine ⟨407741979558832668348121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2174623890980440897856645 407741979558832668348121)
                    ·
                      rfl

theorem cell22_1191112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_1191112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191112 prefixEnd_1191112 := by exact prefixLift 1191112
  have htrace : WordTrace (prefixWord ++ tailWord_1191112) baseStart_1191112 baseEnd_1191112 := by
    simpa [prefixWord, tailWord_1191112, baseEnd_1191112] using wordTrace_append hprefix tailTrace_1191112
  have hstable : (prefixWord ++ tailWord_1191112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191112).length < 2 ^ (prefixWord ++ tailWord_1191112).sum := by decide
  have hdescent : baseEnd_1191112 < baseStart_1191112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191172 : List Nat := [2, 3, 2, 2, 2, 2, 9]
def baseStart_1191172 : Nat := 118140960795 + 1191172 * 2 ^ 59
def prefixEnd_1191172 : Nat := 4983230072969 + 3 ^ 40 * 1191172 * 2
def baseEnd_1191172 : Nat := 15102315510556018957331

theorem tailTrace_1191172 : CollatzResearch.WordTrace tailWord_1191172 prefixEnd_1191172 15102315510556018957331 := by
  unfold tailWord_1191172
  simp only [CollatzResearch.WordTrace]
  refine ⟨21722806020297377413171885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28963741360396503217562513 21722806020297377413171885)
  ·
    refine ⟨8146052257611516529939457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21722806020297377413171885 8146052257611516529939457)
    ·
      refine ⟨6109539193208637397454593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8146052257611516529939457 6109539193208637397454593)
      ·
        refine ⟨4582154394906478048090945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6109539193208637397454593 4582154394906478048090945)
        ·
          refine ⟨3436615796179858536068209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4582154394906478048090945 3436615796179858536068209)
          ·
            refine ⟨2577461847134893902051157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436615796179858536068209 2577461847134893902051157)
            ·
              refine ⟨15102315510556018957331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2577461847134893902051157 15102315510556018957331)
              ·
                rfl

theorem cell22_1191172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 9].length) (baseStart_1191172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191172 prefixEnd_1191172 := by exact prefixLift 1191172
  have htrace : WordTrace (prefixWord ++ tailWord_1191172) baseStart_1191172 baseEnd_1191172 := by
    simpa [prefixWord, tailWord_1191172, baseEnd_1191172] using wordTrace_append hprefix tailTrace_1191172
  have hstable : (prefixWord ++ tailWord_1191172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191172).length < 2 ^ (prefixWord ++ tailWord_1191172).sum := by decide
  have hdescent : baseEnd_1191172 < baseStart_1191172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191204 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1191204 : Nat := 118140960795 + 1191204 * 2 ^ 59
def prefixEnd_1191204 : Nat := 4983230072969 + 3 ^ 40 * 1191204 * 2
def baseEnd_1191204 : Nat := 407773473038975095047839

theorem tailTrace_1191204 : CollatzResearch.WordTrace tailWord_1191204 prefixEnd_1191204 407773473038975095047839 := by
  unfold tailWord_1191204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21723389588239412145754333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28964519450985882861005777 21723389588239412145754333)
  ·
    refine ⟨8146271095589779554657875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21723389588239412145754333 8146271095589779554657875)
    ·
      refine ⟨12219406643384669331986813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8146271095589779554657875 12219406643384669331986813)
      ·
        refine ⟨4582277491269250999495055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12219406643384669331986813 4582277491269250999495055)
        ·
          refine ⟨6873416236903876499242583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4582277491269250999495055 6873416236903876499242583)
          ·
            refine ⟨10310124355355814748863875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873416236903876499242583 10310124355355814748863875)
            ·
              refine ⟨15465186533033722123295813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10310124355355814748863875 15465186533033722123295813)
              ·
                refine ⟨2899722474943822898117965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15465186533033722123295813 2899722474943822898117965)
                ·
                  refine ⟨1087395928103933586794237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2899722474943822898117965 1087395928103933586794237)
                  ·
                    refine ⟨407773473038975095047839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087395928103933586794237 407773473038975095047839)
                    ·
                      rfl

theorem cell22_1191204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1191204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191204 prefixEnd_1191204 := by exact prefixLift 1191204
  have htrace : WordTrace (prefixWord ++ tailWord_1191204) baseStart_1191204 baseEnd_1191204 := by
    simpa [prefixWord, tailWord_1191204, baseEnd_1191204] using wordTrace_append hprefix tailTrace_1191204
  have hstable : (prefixWord ++ tailWord_1191204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191204).length < 2 ^ (prefixWord ++ tailWord_1191204).sum := by decide
  have hdescent : baseEnd_1191204 < baseStart_1191204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191217 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 7]
def baseStart_1191217 : Nat := 118140960795 + 1191217 * 2 ^ 59
def prefixEnd_1191217 : Nat := 4983230072969 + 3 ^ 40 * 1191217 * 2
def baseEnd_1191217 : Nat := 135925974401549131490933

theorem tailTrace_1191217 : CollatzResearch.WordTrace tailWord_1191217 prefixEnd_1191217 135925974401549131490933 := by
  unfold tailWord_1191217
  simp only [CollatzResearch.WordTrace]
  refine ⟨43447253325431727511731905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28964835550287818341154603 43447253325431727511731905)
  ·
    refine ⟨32585439994073795633798929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43447253325431727511731905 32585439994073795633798929)
    ·
      refine ⟨24439079995555346725349197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32585439994073795633798929 24439079995555346725349197)
      ·
        refine ⟨9164654998333255022005949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24439079995555346725349197 9164654998333255022005949)
        ·
          refine ⟨3436745624374970633252231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9164654998333255022005949 3436745624374970633252231)
          ·
            refine ⟨5155118436562455949878347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436745624374970633252231 5155118436562455949878347)
            ·
              refine ⟨7732677654843683924817521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5155118436562455949878347 7732677654843683924817521)
              ·
                refine ⟨5799508241132762943613141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7732677654843683924817521 5799508241132762943613141)
                ·
                  refine ⟨135925974401549131490933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5799508241132762943613141 135925974401549131490933)
                  ·
                    rfl

theorem cell22_1191217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_1191217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191217 prefixEnd_1191217 := by exact prefixLift 1191217
  have htrace : WordTrace (prefixWord ++ tailWord_1191217) baseStart_1191217 baseEnd_1191217 := by
    simpa [prefixWord, tailWord_1191217, baseEnd_1191217] using wordTrace_append hprefix tailTrace_1191217
  have hstable : (prefixWord ++ tailWord_1191217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191217).length < 2 ^ (prefixWord ++ tailWord_1191217).sum := by decide
  have hdescent : baseEnd_1191217 < baseStart_1191217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191264 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_1191264 : Nat := 118140960795 + 1191264 * 2 ^ 59
def prefixEnd_1191264 : Nat := 4983230072969 + 3 ^ 40 * 1191264 * 2
def baseEnd_1191264 : Nat := 407794012265154938547655

theorem tailTrace_1191264 : CollatzResearch.WordTrace tailWord_1191264 prefixEnd_1191264 407794012265154938547655 := by
  unfold tailWord_1191264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21724483778130727269346423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28965978370840969692461897 21724483778130727269346423)
  ·
    refine ⟨32586725667196090904019635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21724483778130727269346423 32586725667196090904019635)
    ·
      refine ⟨48880088500794136356029453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32586725667196090904019635 48880088500794136356029453)
      ·
        refine ⟨18330033187797801133511045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48880088500794136356029453 18330033187797801133511045)
        ·
          refine ⟨3436881222712087712533321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18330033187797801133511045 3436881222712087712533321)
          ·
            refine ⟨2577660917034065784399991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436881222712087712533321 2577660917034065784399991)
            ·
              refine ⟨3866491375551098676599987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577660917034065784399991 3866491375551098676599987)
              ·
                refine ⟨5799737063326648014899981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866491375551098676599987 5799737063326648014899981)
                ·
                  refine ⟨2174901398747493005587493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5799737063326648014899981 2174901398747493005587493)
                  ·
                    refine ⟨407794012265154938547655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2174901398747493005587493 407794012265154938547655)
                    ·
                      rfl

theorem cell22_1191264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_1191264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191264 prefixEnd_1191264 := by exact prefixLift 1191264
  have htrace : WordTrace (prefixWord ++ tailWord_1191264) baseStart_1191264 baseEnd_1191264 := by
    simpa [prefixWord, tailWord_1191264, baseEnd_1191264] using wordTrace_append hprefix tailTrace_1191264
  have hstable : (prefixWord ++ tailWord_1191264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191264).length < 2 ^ (prefixWord ++ tailWord_1191264).sum := by decide
  have hdescent : baseEnd_1191264 < baseStart_1191264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191279 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 4]
def baseStart_1191279 : Nat := 118140960795 + 1191279 * 2 ^ 59
def prefixEnd_1191279 : Nat := 4983230072969 + 3 ^ 40 * 1191279 * 2
def baseEnd_1191279 : Nat := 135933049023899966474203

theorem tailTrace_1191279 : CollatzResearch.WordTrace tailWord_1191279 prefixEnd_1191279 135933049023899966474203 := by
  unfold tailWord_1191279
  simp only [CollatzResearch.WordTrace]
  refine ⟨43449514651207112100488891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28966343100804741400325927 43449514651207112100488891)
  ·
    refine ⟨65174271976810668150733337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43449514651207112100488891 65174271976810668150733337)
    ·
      refine ⟨48880703982608001113050003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65174271976810668150733337 48880703982608001113050003)
      ·
        refine ⟨73321055973912001669575005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48880703982608001113050003 73321055973912001669575005)
        ·
          refine ⟨27495395990217000626090627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73321055973912001669575005 27495395990217000626090627)
          ·
            refine ⟨41243093985325500939135941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27495395990217000626090627 41243093985325500939135941)
            ·
              refine ⟨7733080122248531426087989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41243093985325500939135941 7733080122248531426087989)
              ·
                refine ⟨724976261460799821195749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7733080122248531426087989 724976261460799821195749)
                ·
                  refine ⟨135933049023899966474203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724976261460799821195749 135933049023899966474203)
                  ·
                    rfl

theorem cell22_1191279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 4].length) (baseStart_1191279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191279 prefixEnd_1191279 := by exact prefixLift 1191279
  have htrace : WordTrace (prefixWord ++ tailWord_1191279) baseStart_1191279 baseEnd_1191279 := by
    simpa [prefixWord, tailWord_1191279, baseEnd_1191279] using wordTrace_append hprefix tailTrace_1191279
  have hstable : (prefixWord ++ tailWord_1191279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191279).length < 2 ^ (prefixWord ++ tailWord_1191279).sum := by decide
  have hdescent : baseEnd_1191279 < baseStart_1191279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191429 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_1191429 : Nat := 118140960795 + 1191429 * 2 ^ 59
def prefixEnd_1191429 : Nat := 4983230072969 + 3 ^ 40 * 1191429 * 2
def baseEnd_1191429 : Nat := 407850495137149508172149

theorem tailTrace_1191429 : CollatzResearch.WordTrace tailWord_1191429 prefixEnd_1191429 407850495137149508172149 := by
  unfold tailWord_1191429
  simp only [CollatzResearch.WordTrace]
  refine ⟨43454985600663687718449341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28969990400442458478966227 43454985600663687718449341)
  ·
    refine ⟨16295619600248882894418503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43454985600663687718449341 16295619600248882894418503)
    ·
      refine ⟨24443429400373324341627755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16295619600248882894418503 24443429400373324341627755)
      ·
        refine ⟨36665144100559986512441633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24443429400373324341627755 36665144100559986512441633)
        ·
          refine ⟨27498858075419989884331225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36665144100559986512441633 27498858075419989884331225)
          ·
            refine ⟨20624143556564992413248419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27498858075419989884331225 20624143556564992413248419)
            ·
              refine ⟨30936215334847488619872629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20624143556564992413248419 30936215334847488619872629)
              ·
                refine ⟨2900270187641952058113059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30936215334847488619872629 2900270187641952058113059)
                ·
                  refine ⟨4350405281462928087169589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900270187641952058113059 4350405281462928087169589)
                  ·
                    refine ⟨407850495137149508172149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4350405281462928087169589 407850495137149508172149)
                    ·
                      rfl

theorem cell22_1191429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_1191429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191429 prefixEnd_1191429 := by exact prefixLift 1191429
  have htrace : WordTrace (prefixWord ++ tailWord_1191429) baseStart_1191429 baseEnd_1191429 := by
    simpa [prefixWord, tailWord_1191429, baseEnd_1191429] using wordTrace_append hprefix tailTrace_1191429
  have hstable : (prefixWord ++ tailWord_1191429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191429).length < 2 ^ (prefixWord ++ tailWord_1191429).sum := by decide
  have hdescent : baseEnd_1191429 < baseStart_1191429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191459 : List Nat := [1, 1, 1, 4, 5, 10]
def baseStart_1191459 : Nat := 118140960795 + 1191459 * 2 ^ 59
def prefixEnd_1191459 : Nat := 4983230072969 + 3 ^ 40 * 1191459 * 2
def baseEnd_1191459 : Nat := 5035318083336289258297

theorem tailTrace_1191459 : CollatzResearch.WordTrace tailWord_1191459 prefixEnd_1191459 5035318083336289258297 := by
  unfold tailWord_1191459
  simp only [CollatzResearch.WordTrace]
  refine ⟨43456079790555002842041431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28970719860370001894694287 43456079790555002842041431)
  ·
    refine ⟨65184119685832504263062147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43456079790555002842041431 65184119685832504263062147)
    ·
      refine ⟨97776179528748756394593221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65184119685832504263062147 97776179528748756394593221)
      ·
        refine ⟨18333033661640391823986229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97776179528748756394593221 18333033661640391823986229)
        ·
          refine ⟨1718721905778786733498709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18333033661640391823986229 1718721905778786733498709)
          ·
            refine ⟨5035318083336289258297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1718721905778786733498709 5035318083336289258297)
            ·
              rfl

theorem cell22_1191459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 10].length) (baseStart_1191459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191459 prefixEnd_1191459 := by exact prefixLift 1191459
  have htrace : WordTrace (prefixWord ++ tailWord_1191459) baseStart_1191459 baseEnd_1191459 := by
    simpa [prefixWord, tailWord_1191459, baseEnd_1191459] using wordTrace_append hprefix tailTrace_1191459
  have hstable : (prefixWord ++ tailWord_1191459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191459).length < 2 ^ (prefixWord ++ tailWord_1191459).sum := by decide
  have hdescent : baseEnd_1191459 < baseStart_1191459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191474 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1191474 : Nat := 118140960795 + 1191474 * 2 ^ 59
def prefixEnd_1191474 : Nat := 4983230072969 + 3 ^ 40 * 1191474 * 2
def baseEnd_1191474 : Nat := 407865899556784390797011

theorem tailTrace_1191474 : CollatzResearch.WordTrace tailWord_1191474 prefixEnd_1191474 407865899556784390797011 := by
  unfold tailWord_1191474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864156721375165100959369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28971084590333773602558317 10864156721375165100959369)
  ·
    refine ⟨8148117541031373825719527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10864156721375165100959369 8148117541031373825719527)
    ·
      refine ⟨12222176311547060738579291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8148117541031373825719527 12222176311547060738579291)
      ·
        refine ⟨18333264467320591107868937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12222176311547060738579291 18333264467320591107868937)
        ·
          refine ⟨13749948350490443330901703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18333264467320591107868937 13749948350490443330901703)
          ·
            refine ⟨20624922525735664996352555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13749948350490443330901703 20624922525735664996352555)
            ·
              refine ⟨30937383788603497494528833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20624922525735664996352555 30937383788603497494528833)
              ·
                refine ⟨23203037841452623120896625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30937383788603497494528833 23203037841452623120896625)
                ·
                  refine ⟨17402278381089467340672469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23203037841452623120896625 17402278381089467340672469)
                  ·
                    refine ⟨407865899556784390797011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17402278381089467340672469 407865899556784390797011)
                    ·
                      rfl

theorem cell22_1191474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1191474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191474 prefixEnd_1191474 := by exact prefixLift 1191474
  have htrace : WordTrace (prefixWord ++ tailWord_1191474) baseStart_1191474 baseEnd_1191474 := by
    simpa [prefixWord, tailWord_1191474, baseEnd_1191474] using wordTrace_append hprefix tailTrace_1191474
  have hstable : (prefixWord ++ tailWord_1191474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191474).length < 2 ^ (prefixWord ++ tailWord_1191474).sum := by decide
  have hdescent : baseEnd_1191474 < baseStart_1191474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191495 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 2, 4]
def baseStart_1191495 : Nat := 118140960795 + 1191495 * 2 ^ 59
def prefixEnd_1191495 : Nat := 4983230072969 + 3 ^ 40 * 1191495 * 2
def baseEnd_1191495 : Nat := 407873088285947336021947

theorem tailTrace_1191495 : CollatzResearch.WordTrace tailWord_1191495 prefixEnd_1191495 407873088285947336021947 := by
  unfold tailWord_1191495
  simp only [CollatzResearch.WordTrace]
  refine ⟨43457392818424580990351939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28971595212283053993567959 43457392818424580990351939)
  ·
    refine ⟨65186089227636871485527909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43457392818424580990351939 65186089227636871485527909)
    ·
      refine ⟨12222391730181913403536483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65186089227636871485527909 12222391730181913403536483)
      ·
        refine ⟨18333587595272870105304725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12222391730181913403536483 18333587595272870105304725)
        ·
          refine ⟨859386918528415786186159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18333587595272870105304725 859386918528415786186159)
          ·
            refine ⟨1289080377792623679279239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859386918528415786186159 1289080377792623679279239)
            ·
              refine ⟨1933620566688935518918859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289080377792623679279239 1933620566688935518918859)
              ·
                refine ⟨2900430850033403278378289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933620566688935518918859 2900430850033403278378289)
                ·
                  refine ⟨2175323137525052458783717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900430850033403278378289 2175323137525052458783717)
                  ·
                    refine ⟨407873088285947336021947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175323137525052458783717 407873088285947336021947)
                    ·
                      rfl

theorem cell22_1191495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_1191495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191495 prefixEnd_1191495 := by exact prefixLift 1191495
  have htrace : WordTrace (prefixWord ++ tailWord_1191495) baseStart_1191495 baseEnd_1191495 := by
    simpa [prefixWord, tailWord_1191495, baseEnd_1191495] using wordTrace_append hprefix tailTrace_1191495
  have hstable : (prefixWord ++ tailWord_1191495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191495).length < 2 ^ (prefixWord ++ tailWord_1191495).sum := by decide
  have hdescent : baseEnd_1191495 < baseStart_1191495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191504 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_1191504 : Nat := 118140960795 + 1191504 * 2 ^ 59
def prefixEnd_1191504 : Nat := 4983230072969 + 3 ^ 40 * 1191504 * 2
def baseEnd_1191504 : Nat := 135958723056624770848973

theorem tailTrace_1191504 : CollatzResearch.WordTrace tailWord_1191504 prefixEnd_1191504 135958723056624770848973 := by
  unfold tailWord_1191504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21728860537695987763714783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28971814050261317018286377 21728860537695987763714783)
  ·
    refine ⟨32593290806543981645572175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21728860537695987763714783 32593290806543981645572175)
    ·
      refine ⟨48889936209815972468358263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32593290806543981645572175 48889936209815972468358263)
      ·
        refine ⟨73334904314723958702537395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48889936209815972468358263 73334904314723958702537395)
        ·
          refine ⟨110002356472085938053806093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73334904314723958702537395 110002356472085938053806093)
          ·
            refine ⟨41250883677032226770177285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110002356472085938053806093 41250883677032226770177285)
            ·
              refine ⟨7734540689443542519408241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41250883677032226770177285 7734540689443542519408241)
              ·
                refine ⟨5800905517082656889556181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7734540689443542519408241 5800905517082656889556181)
                ·
                  refine ⟨135958723056624770848973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5800905517082656889556181 135958723056624770848973)
                  ·
                    rfl

theorem cell22_1191504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_1191504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191504 prefixEnd_1191504 := by exact prefixLift 1191504
  have htrace : WordTrace (prefixWord ++ tailWord_1191504) baseStart_1191504 baseEnd_1191504 := by
    simpa [prefixWord, tailWord_1191504, baseEnd_1191504] using wordTrace_append hprefix tailTrace_1191504
  have hstable : (prefixWord ++ tailWord_1191504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191504).length < 2 ^ (prefixWord ++ tailWord_1191504).sum := by decide
  have hdescent : baseEnd_1191504 < baseStart_1191504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191510 : List Nat := [5, 2, 2, 2, 1, 1, 9]
def baseStart_1191510 : Nat := 118140960795 + 1191510 * 2 ^ 59
def prefixEnd_1191510 : Nat := 4983230072969 + 3 ^ 40 * 1191510 * 2
def baseEnd_1191510 : Nat := 15106600855277492477663

theorem tailTrace_1191510 : CollatzResearch.WordTrace tailWord_1191510 prefixEnd_1191510 15106600855277492477663 := by
  unfold tailWord_1191510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716121244585639909509249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28971959942246825701431989 2716121244585639909509249)
  ·
    refine ⟨2037090933439229932131937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2716121244585639909509249 2037090933439229932131937)
    ·
      refine ⟨1527818200079422449098953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2037090933439229932131937 1527818200079422449098953)
      ·
        refine ⟨1145863650059566836824215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1527818200079422449098953 1145863650059566836824215)
        ·
          refine ⟨1718795475089350255236323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145863650059566836824215 1718795475089350255236323)
          ·
            refine ⟨2578193212634025382854485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718795475089350255236323 2578193212634025382854485)
            ·
              refine ⟨15106600855277492477663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2578193212634025382854485 15106600855277492477663)
              ·
                rfl

theorem cell22_1191510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 9].length) (baseStart_1191510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191510 prefixEnd_1191510 := by exact prefixLift 1191510
  have htrace : WordTrace (prefixWord ++ tailWord_1191510) baseStart_1191510 baseEnd_1191510 := by
    simpa [prefixWord, tailWord_1191510, baseEnd_1191510] using wordTrace_append hprefix tailTrace_1191510
  have hstable : (prefixWord ++ tailWord_1191510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191510).length < 2 ^ (prefixWord ++ tailWord_1191510).sum := by decide
  have hdescent : baseEnd_1191510 < baseStart_1191510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191525 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_1191525 : Nat := 118140960795 + 1191525 * 2 ^ 59
def prefixEnd_1191525 : Nat := 4983230072969 + 3 ^ 40 * 1191525 * 2
def baseEnd_1191525 : Nat := 407883357899037257771855

theorem tailTrace_1191525 : CollatzResearch.WordTrace tailWord_1191525 prefixEnd_1191525 407883357899037257771855 := by
  unfold tailWord_1191525
  simp only [CollatzResearch.WordTrace]
  refine ⟨43458487008315896113944029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28972324672210597409296019 43458487008315896113944029)
  ·
    refine ⟨16296932628118461042729011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43458487008315896113944029 16296932628118461042729011)
    ·
      refine ⟨24445398942177691564093517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16296932628118461042729011 24445398942177691564093517)
      ·
        refine ⟨9167024603316634336535069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24445398942177691564093517 9167024603316634336535069)
        ·
          refine ⟨3437634226243737876200651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9167024603316634336535069 3437634226243737876200651)
          ·
            refine ⟨5156451339365606814300977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437634226243737876200651 5156451339365606814300977)
            ·
              refine ⟨3867338504524205110725733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156451339365606814300977 3867338504524205110725733)
              ·
                refine ⟨725125969598288458261075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3867338504524205110725733 725125969598288458261075)
                ·
                  refine ⟨1087688954397432687391613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725125969598288458261075 1087688954397432687391613)
                  ·
                    refine ⟨407883357899037257771855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087688954397432687391613 407883357899037257771855)
                    ·
                      rfl

theorem cell22_1191525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_1191525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191525 prefixEnd_1191525 := by exact prefixLift 1191525
  have htrace : WordTrace (prefixWord ++ tailWord_1191525) baseStart_1191525 baseEnd_1191525 := by
    simpa [prefixWord, tailWord_1191525, baseEnd_1191525] using wordTrace_append hprefix tailTrace_1191525
  have hstable : (prefixWord ++ tailWord_1191525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191525).length < 2 ^ (prefixWord ++ tailWord_1191525).sum := by decide
  have hdescent : baseEnd_1191525 < baseStart_1191525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191536 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_1191536 : Nat := 118140960795 + 1191536 * 2 ^ 59
def prefixEnd_1191536 : Nat := 4983230072969 + 3 ^ 40 * 1191536 * 2
def baseEnd_1191536 : Nat := 407887123423836895746821

theorem tailTrace_1191536 : CollatzResearch.WordTrace tailWord_1191536 prefixEnd_1191536 407887123423836895746821 := by
  unfold tailWord_1191536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21729444105638022496297231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28972592140850696661729641 21729444105638022496297231)
  ·
    refine ⟨32594166158457033744445847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21729444105638022496297231 32594166158457033744445847)
    ·
      refine ⟨48891249237685550616668771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32594166158457033744445847 48891249237685550616668771)
      ·
        refine ⟨73336873856528325925003157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48891249237685550616668771 73336873856528325925003157)
        ·
          refine ⟨3437665962024765277734523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73336873856528325925003157 3437665962024765277734523)
          ·
            refine ⟨5156498943037147916601785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437665962024765277734523 5156498943037147916601785)
            ·
              refine ⟨3867374207277860937451339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156498943037147916601785 3867374207277860937451339)
              ·
                refine ⟨5801061310916791406177009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867374207277860937451339 5801061310916791406177009)
                ·
                  refine ⟨4350795983187593554632757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5801061310916791406177009 4350795983187593554632757)
                  ·
                    refine ⟨407887123423836895746821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4350795983187593554632757 407887123423836895746821)
                    ·
                      rfl

theorem cell22_1191536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_1191536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191536 prefixEnd_1191536 := by exact prefixLift 1191536
  have htrace : WordTrace (prefixWord ++ tailWord_1191536) baseStart_1191536 baseEnd_1191536 := by
    simpa [prefixWord, tailWord_1191536, baseEnd_1191536] using wordTrace_append hprefix tailTrace_1191536
  have hstable : (prefixWord ++ tailWord_1191536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191536).length < 2 ^ (prefixWord ++ tailWord_1191536).sum := by decide
  have hdescent : baseEnd_1191536 < baseStart_1191536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191613 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1191613 : Nat := 118140960795 + 1191613 * 2 ^ 59
def prefixEnd_1191613 : Nat := 4983230072969 + 3 ^ 40 * 1191613 * 2
def baseEnd_1191613 : Nat := 407913482097434361571585

theorem tailTrace_1191613 : CollatzResearch.WordTrace tailWord_1191613 prefixEnd_1191613 407913482097434361571585 := by
  unfold tailWord_1191613
  simp only [CollatzResearch.WordTrace]
  refine ⟨43461696631997087143147493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28974464421331391428764995 43461696631997087143147493)
  ·
    refine ⟨8149068118499453839340155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43461696631997087143147493 8149068118499453839340155)
    ·
      refine ⟨12223602177749180759010233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8149068118499453839340155 12223602177749180759010233)
      ·
        refine ⟨9167701633311885569257675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12223602177749180759010233 9167701633311885569257675)
        ·
          refine ⟨13751552449967828353886513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9167701633311885569257675 13751552449967828353886513)
          ·
            refine ⟨10313664337475871265414885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13751552449967828353886513 10313664337475871265414885)
            ·
              refine ⟨1933812063276725862265291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10313664337475871265414885 1933812063276725862265291)
              ·
                refine ⟨2900718094915088793397937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933812063276725862265291 2900718094915088793397937)
                ·
                  refine ⟨2175538571186316595048453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900718094915088793397937 2175538571186316595048453)
                  ·
                    refine ⟨407913482097434361571585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175538571186316595048453 407913482097434361571585)
                    ·
                      rfl

theorem cell22_1191613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1191613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191613 prefixEnd_1191613 := by exact prefixLift 1191613
  have htrace : WordTrace (prefixWord ++ tailWord_1191613) baseStart_1191613 baseEnd_1191613 := by
    simpa [prefixWord, tailWord_1191613, baseEnd_1191613] using wordTrace_append hprefix tailTrace_1191613
  have hstable : (prefixWord ++ tailWord_1191613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191613).length < 2 ^ (prefixWord ++ tailWord_1191613).sum := by decide
  have hdescent : baseEnd_1191613 < baseStart_1191613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191628 : List Nat := [2, 2, 1, 5, 3, 9]
def baseStart_1191628 : Nat := 118140960795 + 1191628 * 2 ^ 59
def prefixEnd_1191628 : Nat := 4983230072969 + 3 ^ 40 * 1191628 * 2
def baseEnd_1191628 : Nat := 5036032307456534845019

theorem tailTrace_1191628 : CollatzResearch.WordTrace tailWord_1191628 prefixEnd_1191628 5036032307456534845019 := by
  unfold tailWord_1191628
  simp only [CollatzResearch.WordTrace]
  refine ⟨21731121863471372352471769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28974829151295163136629025 21731121863471372352471769)
  ·
    refine ⟨16298341397603529264353827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21731121863471372352471769 16298341397603529264353827)
    ·
      refine ⟨24447512096405293896530741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16298341397603529264353827 24447512096405293896530741)
      ·
        refine ⟨2291954259037996302799757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24447512096405293896530741 2291954259037996302799757)
        ·
          refine ⟨859482847139248613549909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2291954259037996302799757 859482847139248613549909)
          ·
            refine ⟨5036032307456534845019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 859482847139248613549909 5036032307456534845019)
            ·
              rfl

theorem cell22_1191628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 9].length) (baseStart_1191628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191628 prefixEnd_1191628 := by exact prefixLift 1191628
  have htrace : WordTrace (prefixWord ++ tailWord_1191628) baseStart_1191628 baseEnd_1191628 := by
    simpa [prefixWord, tailWord_1191628, baseEnd_1191628] using wordTrace_append hprefix tailTrace_1191628
  have hstable : (prefixWord ++ tailWord_1191628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191628).length < 2 ^ (prefixWord ++ tailWord_1191628).sum := by decide
  have hdescent : baseEnd_1191628 < baseStart_1191628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191641 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_1191641 : Nat := 118140960795 + 1191641 * 2 ^ 59
def prefixEnd_1191641 : Nat := 4983230072969 + 3 ^ 40 * 1191641 * 2
def baseEnd_1191641 : Nat := 407923067069651621871499

theorem tailTrace_1191641 : CollatzResearch.WordTrace tailWord_1191641 prefixEnd_1191641 407923067069651621871499 := by
  unfold tailWord_1191641
  simp only [CollatzResearch.WordTrace]
  refine ⟨43462717875895647925166777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28975145250597098616777851 43462717875895647925166777)
  ·
    refine ⟨32597038406921735943875083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43462717875895647925166777 32597038406921735943875083)
    ·
      refine ⟨48895557610382603915812625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32597038406921735943875083 48895557610382603915812625)
      ·
        refine ⟨36671668207786952936859469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48895557610382603915812625 36671668207786952936859469)
        ·
          refine ⟨13751875577920107351322301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36671668207786952936859469 13751875577920107351322301)
          ·
            refine ⟨5156953341720040256745863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13751875577920107351322301 5156953341720040256745863)
            ·
              refine ⟨7735430012580060385118795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156953341720040256745863 7735430012580060385118795)
              ·
                refine ⟨11603145018870090577678193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7735430012580060385118795 11603145018870090577678193)
                ·
                  refine ⟨8702358764152567933258645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11603145018870090577678193 8702358764152567933258645)
                  ·
                    refine ⟨407923067069651621871499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8702358764152567933258645 407923067069651621871499)
                    ·
                      rfl

theorem cell22_1191641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_1191641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191641 prefixEnd_1191641 := by exact prefixLift 1191641
  have htrace : WordTrace (prefixWord ++ tailWord_1191641) baseStart_1191641 baseEnd_1191641 := by
    simpa [prefixWord, tailWord_1191641, baseEnd_1191641] using wordTrace_append hprefix tailTrace_1191641
  have hstable : (prefixWord ++ tailWord_1191641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191641).length < 2 ^ (prefixWord ++ tailWord_1191641).sum := by decide
  have hdescent : baseEnd_1191641 < baseStart_1191641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191690 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_1191690 : Nat := 118140960795 + 1191690 * 2 ^ 59
def prefixEnd_1191690 : Nat := 4983230072969 + 3 ^ 40 * 1191690 * 2
def baseEnd_1191690 : Nat := 135979946923677275798783

theorem tailTrace_1191690 : CollatzResearch.WordTrace tailWord_1191690 prefixEnd_1191690 135979946923677275798783 := by
  unfold tailWord_1191690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10866126263179532323425131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28976336701812086195800349 10866126263179532323425131)
  ·
    refine ⟨16299189394769298485137697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10866126263179532323425131 16299189394769298485137697)
    ·
      refine ⟨12224392046076973863853273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16299189394769298485137697 12224392046076973863853273)
      ·
        refine ⟨9168294034557730397889955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12224392046076973863853273 9168294034557730397889955)
        ·
          refine ⟨13752441051836595596834933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9168294034557730397889955 13752441051836595596834933)
          ·
            refine ⟨1289291348609680837203275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13752441051836595596834933 1289291348609680837203275)
            ·
              refine ⟨1933937022914521255804913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289291348609680837203275 1933937022914521255804913)
              ·
                refine ⟨1450452767185890941853685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933937022914521255804913 1450452767185890941853685)
                ·
                  refine ⟨135979946923677275798783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1450452767185890941853685 135979946923677275798783)
                  ·
                    rfl

theorem cell22_1191690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_1191690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191690 prefixEnd_1191690 := by exact prefixLift 1191690
  have htrace : WordTrace (prefixWord ++ tailWord_1191690) baseStart_1191690 baseEnd_1191690 := by
    simpa [prefixWord, tailWord_1191690, baseEnd_1191690] using wordTrace_append hprefix tailTrace_1191690
  have hstable : (prefixWord ++ tailWord_1191690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191690).length < 2 ^ (prefixWord ++ tailWord_1191690).sum := by decide
  have hdescent : baseEnd_1191690 < baseStart_1191690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191720 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1191720 : Nat := 118140960795 + 1191720 * 2 ^ 59
def prefixEnd_1191720 : Nat := 4983230072969 + 3 ^ 40 * 1191720 * 2
def baseEnd_1191720 : Nat := 407950110384121749146257

theorem tailTrace_1191720 : CollatzResearch.WordTrace tailWord_1191720 prefixEnd_1191720 407950110384121749146257 := by
  unfold tailWord_1191720
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732799621304722208646307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28977066161739629611528409 21732799621304722208646307)
  ·
    refine ⟨32599199431957083312969461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21732799621304722208646307 32599199431957083312969461)
    ·
      refine ⟨3056174946745976560590887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32599199431957083312969461 3056174946745976560590887)
      ·
        refine ⟨4584262420118964840886331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056174946745976560590887 4584262420118964840886331)
        ·
          refine ⟨6876393630178447261329497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584262420118964840886331 6876393630178447261329497)
          ·
            refine ⟨5157295222633835445997123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6876393630178447261329497 5157295222633835445997123)
            ·
              refine ⟨7735942833950753168995685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5157295222633835445997123 7735942833950753168995685)
              ·
                refine ⟨1450489281365766219186691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7735942833950753168995685 1450489281365766219186691)
                ·
                  refine ⟨2175733922048649328780037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450489281365766219186691 2175733922048649328780037)
                  ·
                    refine ⟨407950110384121749146257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175733922048649328780037 407950110384121749146257)
                    ·
                      rfl

theorem cell22_1191720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1191720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191720 prefixEnd_1191720 := by exact prefixLift 1191720
  have htrace : WordTrace (prefixWord ++ tailWord_1191720) baseStart_1191720 baseEnd_1191720 := by
    simpa [prefixWord, tailWord_1191720, baseEnd_1191720] using wordTrace_append hprefix tailTrace_1191720
  have hstable : (prefixWord ++ tailWord_1191720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191720).length < 2 ^ (prefixWord ++ tailWord_1191720).sum := by decide
  have hdescent : baseEnd_1191720 < baseStart_1191720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191752 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_1191752 : Nat := 118140960795 + 1191752 * 2 ^ 59
def prefixEnd_1191752 : Nat := 4983230072969 + 3 ^ 40 * 1191752 * 2
def baseEnd_1191752 : Nat := 135987021546028110782053

theorem tailTrace_1191752 : CollatzResearch.WordTrace tailWord_1191752 prefixEnd_1191752 135987021546028110782053 := by
  unfold tailWord_1191752
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733383189246756941228755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28977844252329009254971673 21733383189246756941228755)
  ·
    refine ⟨32600074783870135411843133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21733383189246756941228755 32600074783870135411843133)
    ·
      refine ⟨12225028043951300779441175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32600074783870135411843133 12225028043951300779441175)
      ·
        refine ⟨18337542065926951169161763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12225028043951300779441175 18337542065926951169161763)
        ·
          refine ⟨27506313098890426753742645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18337542065926951169161763 27506313098890426753742645)
          ·
            refine ⟨2578716853020977508163373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27506313098890426753742645 2578716853020977508163373)
            ·
              refine ⟨967018819882866565561265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2578716853020977508163373 967018819882866565561265)
              ·
                refine ⟨725264114912149924170949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967018819882866565561265 725264114912149924170949)
                ·
                  refine ⟨135987021546028110782053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 725264114912149924170949 135987021546028110782053)
                  ·
                    rfl

theorem cell22_1191752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_1191752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191752 prefixEnd_1191752 := by exact prefixLift 1191752
  have htrace : WordTrace (prefixWord ++ tailWord_1191752) baseStart_1191752 baseEnd_1191752 := by
    simpa [prefixWord, tailWord_1191752, baseEnd_1191752] using wordTrace_append hprefix tailTrace_1191752
  have hstable : (prefixWord ++ tailWord_1191752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191752).length < 2 ^ (prefixWord ++ tailWord_1191752).sum := by decide
  have hdescent : baseEnd_1191752 < baseStart_1191752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191767 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 2, 3]
def baseStart_1191767 : Nat := 118140960795 + 1191767 * 2 ^ 59
def prefixEnd_1191767 : Nat := 4983230072969 + 3 ^ 40 * 1191767 * 2
def baseEnd_1191767 : Nat := 407966199444629293221113

theorem tailTrace_1191767 : CollatzResearch.WordTrace tailWord_1191767 prefixEnd_1191767 407966199444629293221113 := by
  unfold tailWord_1191767
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467313473439171444253555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28978208982292780962835703 43467313473439171444253555)
  ·
    refine ⟨65200970210158757166380333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43467313473439171444253555 65200970210158757166380333)
    ·
      refine ⟨24450363828809533937392625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65200970210158757166380333 24450363828809533937392625)
      ·
        refine ⟨18337772871607150453044469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24450363828809533937392625 18337772871607150453044469)
        ·
          refine ⟨1719166206713170354972919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18337772871607150453044469 1719166206713170354972919)
          ·
            refine ⟨2578749310069755532459379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719166206713170354972919 2578749310069755532459379)
            ·
              refine ⟨3868123965104633298689069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578749310069755532459379 3868123965104633298689069)
              ·
                refine ⟨1450546486914237487008401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3868123965104633298689069 1450546486914237487008401)
                ·
                  refine ⟨1087909865185678115256301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1450546486914237487008401 1087909865185678115256301)
                  ·
                    refine ⟨407966199444629293221113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087909865185678115256301 407966199444629293221113)
                    ·
                      rfl

theorem cell22_1191767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_1191767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191767 prefixEnd_1191767 := by exact prefixLift 1191767
  have htrace : WordTrace (prefixWord ++ tailWord_1191767) baseStart_1191767 baseEnd_1191767 := by
    simpa [prefixWord, tailWord_1191767, baseEnd_1191767] using wordTrace_append hprefix tailTrace_1191767
  have hstable : (prefixWord ++ tailWord_1191767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191767).length < 2 ^ (prefixWord ++ tailWord_1191767).sum := by decide
  have hdescent : baseEnd_1191767 < baseStart_1191767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191855 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 1, 4]
def baseStart_1191855 : Nat := 118140960795 + 1191855 * 2 ^ 59
def prefixEnd_1191855 : Nat := 4983230072969 + 3 ^ 40 * 1191855 * 2
def baseEnd_1191855 : Nat := 407996323643026397020843

theorem tailTrace_1191855 : CollatzResearch.WordTrace tailWord_1191855 prefixEnd_1191855 407996323643026397020843 := by
  unfold tailWord_1191855
  simp only [CollatzResearch.WordTrace]
  refine ⟨43470523097120362473457019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28980348731413574982304679 43470523097120362473457019)
  ·
    refine ⟨65205784645680543710185529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43470523097120362473457019 65205784645680543710185529)
    ·
      refine ⟨48904338484260407782639147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65205784645680543710185529 48904338484260407782639147)
      ·
        refine ⟨73356507726390611673958721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48904338484260407782639147 73356507726390611673958721)
        ·
          refine ⟨55017380794792958755469041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73356507726390611673958721 55017380794792958755469041)
          ·
            refine ⟨41263035596094719066601781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55017380794792958755469041 41263035596094719066601781)
            ·
              refine ⟨3868409587133879912493917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41263035596094719066601781 3868409587133879912493917)
              ·
                refine ⟨1450653595175204967185219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3868409587133879912493917 1450653595175204967185219)
                ·
                  refine ⟨2175980392762807450777829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450653595175204967185219 2175980392762807450777829)
                  ·
                    refine ⟨407996323643026397020843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175980392762807450777829 407996323643026397020843)
                    ·
                      rfl

theorem cell22_1191855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_1191855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191855 prefixEnd_1191855 := by exact prefixLift 1191855
  have htrace : WordTrace (prefixWord ++ tailWord_1191855) baseStart_1191855 baseEnd_1191855 := by
    simpa [prefixWord, tailWord_1191855, baseEnd_1191855] using wordTrace_append hprefix tailTrace_1191855
  have hstable : (prefixWord ++ tailWord_1191855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191855).length < 2 ^ (prefixWord ++ tailWord_1191855).sum := by decide
  have hdescent : baseEnd_1191855 < baseStart_1191855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191870 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1191870 : Nat := 118140960795 + 1191870 * 2 ^ 59
def prefixEnd_1191870 : Nat := 4983230072969 + 3 ^ 40 * 1191870 * 2
def baseEnd_1191870 : Nat := 136000486149857119298599

theorem tailTrace_1191870 : CollatzResearch.WordTrace tailWord_1191870 prefixEnd_1191870 136000486149857119298599 := by
  unfold tailWord_1191870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433883774008252504406633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28980713461377346690168709 5433883774008252504406633)
  ·
    refine ⟨4075412830506189378304975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5433883774008252504406633 4075412830506189378304975)
    ·
      refine ⟨6113119245759284067457463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075412830506189378304975 6113119245759284067457463)
      ·
        refine ⟨9169678868638926101186195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113119245759284067457463 9169678868638926101186195)
        ·
          refine ⟨13754518302958389151779293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9169678868638926101186195 13754518302958389151779293)
          ·
            refine ⟨5157944363609395931917235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13754518302958389151779293 5157944363609395931917235)
            ·
              refine ⟨7736916545414093897875853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5157944363609395931917235 7736916545414093897875853)
              ·
                refine ⟨2901343704530285211703445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7736916545414093897875853 2901343704530285211703445)
                ·
                  refine ⟨136000486149857119298599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2901343704530285211703445 136000486149857119298599)
                  ·
                    rfl

theorem cell22_1191870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1191870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191870 prefixEnd_1191870 := by exact prefixLift 1191870
  have htrace : WordTrace (prefixWord ++ tailWord_1191870) baseStart_1191870 baseEnd_1191870 := by
    simpa [prefixWord, tailWord_1191870, baseEnd_1191870] using wordTrace_append hprefix tailTrace_1191870
  have hstable : (prefixWord ++ tailWord_1191870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191870).length < 2 ^ (prefixWord ++ tailWord_1191870).sum := by decide
  have hdescent : baseEnd_1191870 < baseStart_1191870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191883 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_1191883 : Nat := 118140960795 + 1191883 * 2 ^ 59
def prefixEnd_1191883 : Nat := 4983230072969 + 3 ^ 40 * 1191883 * 2
def baseEnd_1191883 : Nat := 408005908615243657320757

theorem tailTrace_1191883 : CollatzResearch.WordTrace tailWord_1191883 prefixEnd_1191883 408005908615243657320757 := by
  unfold tailWord_1191883
  simp only [CollatzResearch.WordTrace]
  refine ⟨43471544341018923255476303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28981029560679282170317535 43471544341018923255476303)
  ·
    refine ⟨65207316511528384883214455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43471544341018923255476303 65207316511528384883214455)
    ·
      refine ⟨97810974767292577324821683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65207316511528384883214455 97810974767292577324821683)
      ·
        refine ⟨146716462150938865987232525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97810974767292577324821683 146716462150938865987232525)
        ·
          refine ⟨55018673306602074745212197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146716462150938865987232525 55018673306602074745212197)
          ·
            refine ⟨10316001244987889014727287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55018673306602074745212197 10316001244987889014727287)
            ·
              refine ⟨15474001867481833522090931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10316001244987889014727287 15474001867481833522090931)
              ·
                refine ⟨23211002801222750283136397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15474001867481833522090931 23211002801222750283136397)
                ·
                  refine ⟨8704126050458531356176149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23211002801222750283136397 8704126050458531356176149)
                  ·
                    refine ⟨408005908615243657320757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8704126050458531356176149 408005908615243657320757)
                    ·
                      rfl

theorem cell22_1191883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_1191883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191883 prefixEnd_1191883 := by exact prefixLift 1191883
  have htrace : WordTrace (prefixWord ++ tailWord_1191883) baseStart_1191883 baseEnd_1191883 := by
    simpa [prefixWord, tailWord_1191883, baseEnd_1191883] using wordTrace_append hprefix tailTrace_1191883
  have hstable : (prefixWord ++ tailWord_1191883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191883).length < 2 ^ (prefixWord ++ tailWord_1191883).sum := by decide
  have hdescent : baseEnd_1191883 < baseStart_1191883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191992 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1191992 : Nat := 118140960795 + 1191992 * 2 ^ 59
def prefixEnd_1191992 : Nat := 4983230072969 + 3 ^ 40 * 1191992 * 2
def baseEnd_1191992 : Nat := 408043221542803706345423

theorem tailTrace_1191992 : CollatzResearch.WordTrace tailWord_1191992 prefixEnd_1191992 408043221542803706345423 := by
  unfold tailWord_1191992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21737759948812017435597115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28983679931749356580796153 21737759948812017435597115)
  ·
    refine ⟨32606639923218026153395673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21737759948812017435597115 32606639923218026153395673)
    ·
      refine ⟨24454979942413519615046755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32606639923218026153395673 24454979942413519615046755)
      ·
        refine ⟨36682469913620279422570133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24454979942413519615046755 36682469913620279422570133)
        ·
          refine ⟨1719490777200950597932975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36682469913620279422570133 1719490777200950597932975)
          ·
            refine ⟨2579236165801425896899463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719490777200950597932975 2579236165801425896899463)
            ·
              refine ⟨3868854248702138845349195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579236165801425896899463 3868854248702138845349195)
              ·
                refine ⟨5803281373053208268023793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868854248702138845349195 5803281373053208268023793)
                ·
                  refine ⟨4352461029789906201017845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803281373053208268023793 4352461029789906201017845)
                  ·
                    refine ⟨408043221542803706345423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4352461029789906201017845 408043221542803706345423)
                    ·
                      rfl

theorem cell22_1191992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1191992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1191992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1191992 prefixEnd_1191992 := by exact prefixLift 1191992
  have htrace : WordTrace (prefixWord ++ tailWord_1191992) baseStart_1191992 baseEnd_1191992 := by
    simpa [prefixWord, tailWord_1191992, baseEnd_1191992] using wordTrace_append hprefix tailTrace_1191992
  have hstable : (prefixWord ++ tailWord_1191992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191992).length < 2 ^ (prefixWord ++ tailWord_1191992).sum := by decide
  have hdescent : baseEnd_1191992 < baseStart_1191992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192007 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1192007 : Nat := 118140960795 + 1192007 * 2 ^ 59
def prefixEnd_1192007 : Nat := 4983230072969 + 3 ^ 40 * 1192007 * 2
def baseEnd_1192007 : Nat := 408048356349348667220377

theorem tailTrace_1192007 : CollatzResearch.WordTrace tailWord_1192007 prefixEnd_1192007 408048356349348667220377 := by
  unfold tailWord_1192007
  simp only [CollatzResearch.WordTrace]
  refine ⟨43476066992569692432990275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28984044661713128288660183 43476066992569692432990275)
  ·
    refine ⟨65214100488854538649485413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43476066992569692432990275 65214100488854538649485413)
    ·
      refine ⟨12227643841660225996778515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65214100488854538649485413 12227643841660225996778515)
      ·
        refine ⟨18341465762490338995167773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12227643841660225996778515 18341465762490338995167773)
        ·
          refine ⟨6878049660933877123187915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18341465762490338995167773 6878049660933877123187915)
          ·
            refine ⟨10317074491400815684781873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878049660933877123187915 10317074491400815684781873)
            ·
              refine ⟨7737805868550611763586405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10317074491400815684781873 7737805868550611763586405)
              ·
                refine ⟨1450838600353239705672451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7737805868550611763586405 1450838600353239705672451)
                ·
                  refine ⟨2176257900529859558508677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450838600353239705672451 2176257900529859558508677)
                  ·
                    refine ⟨408048356349348667220377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176257900529859558508677 408048356349348667220377)
                    ·
                      rfl

theorem cell22_1192007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1192007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192007 prefixEnd_1192007 := by exact prefixLift 1192007
  have htrace : WordTrace (prefixWord ++ tailWord_1192007) baseStart_1192007 baseEnd_1192007 := by
    simpa [prefixWord, tailWord_1192007, baseEnd_1192007] using wordTrace_append hprefix tailTrace_1192007
  have hstable : (prefixWord ++ tailWord_1192007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192007).length < 2 ^ (prefixWord ++ tailWord_1192007).sum := by decide
  have hdescent : baseEnd_1192007 < baseStart_1192007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192024 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_1192024 : Nat := 118140960795 + 1192024 * 2 ^ 59
def prefixEnd_1192024 : Nat := 4983230072969 + 3 ^ 40 * 1192024 * 2
def baseEnd_1192024 : Nat := 408054175796766289545325

theorem tailTrace_1192024 : CollatzResearch.WordTrace tailWord_1192024 prefixEnd_1192024 408054175796766289545325 := by
  unfold tailWord_1192024
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738343516754052168179563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28984458022338736224239417 21738343516754052168179563)
  ·
    refine ⟨32607515275131078252269345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21738343516754052168179563 32607515275131078252269345)
    ·
      refine ⟨24455636456348308689202009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32607515275131078252269345 24455636456348308689202009)
      ·
        refine ⟨18341727342261231516901507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24455636456348308689202009 18341727342261231516901507)
        ·
          refine ⟨27512591013391847275352261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18341727342261231516901507 27512591013391847275352261)
          ·
            refine ⟨5158610815010971364128549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27512591013391847275352261 5158610815010971364128549)
            ·
              refine ⟨967239527814557130774103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5158610815010971364128549 967239527814557130774103)
              ·
                refine ⟨1450859291721835696161155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967239527814557130774103 1450859291721835696161155)
                ·
                  refine ⟨2176288937582753544241733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450859291721835696161155 2176288937582753544241733)
                  ·
                    refine ⟨408054175796766289545325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176288937582753544241733 408054175796766289545325)
                    ·
                      rfl

theorem cell22_1192024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_1192024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192024 prefixEnd_1192024 := by exact prefixLift 1192024
  have htrace : WordTrace (prefixWord ++ tailWord_1192024) baseStart_1192024 baseEnd_1192024 := by
    simpa [prefixWord, tailWord_1192024, baseEnd_1192024] using wordTrace_append hprefix tailTrace_1192024
  have hstable : (prefixWord ++ tailWord_1192024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192024).length < 2 ^ (prefixWord ++ tailWord_1192024).sum := by decide
  have hdescent : baseEnd_1192024 < baseStart_1192024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192054 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1192054 : Nat := 118140960795 + 1192054 * 2 ^ 59
def prefixEnd_1192054 : Nat := 4983230072969 + 3 ^ 40 * 1192054 * 2
def baseEnd_1192054 : Nat := 408064445409856211295233

theorem tailTrace_1192054 : CollatzResearch.WordTrace tailWord_1192054 prefixEnd_1192054 408064445409856211295233 := by
  unfold tailWord_1192054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717361326462463716246951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28985187482266279639967477 2717361326462463716246951)
  ·
    refine ⟨4076041989693695574370427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717361326462463716246951 4076041989693695574370427)
    ·
      refine ⟨6114062984540543361555641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076041989693695574370427 6114062984540543361555641)
      ·
        refine ⟨4585547238405407521166731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6114062984540543361555641 4585547238405407521166731)
        ·
          refine ⟨6878320857608111281750097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585547238405407521166731 6878320857608111281750097)
          ·
            refine ⟨5158740643206083461312573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6878320857608111281750097 5158740643206083461312573)
            ·
              refine ⟨1934527741202281297992215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5158740643206083461312573 1934527741202281297992215)
              ·
                refine ⟨2901791611803421946988323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934527741202281297992215 2901791611803421946988323)
                ·
                  refine ⟨4352687417705132920482485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901791611803421946988323 4352687417705132920482485)
                  ·
                    refine ⟨408064445409856211295233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4352687417705132920482485 408064445409856211295233)
                    ·
                      rfl

theorem cell22_1192054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1192054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192054 prefixEnd_1192054 := by exact prefixLift 1192054
  have htrace : WordTrace (prefixWord ++ tailWord_1192054) baseStart_1192054 baseEnd_1192054 := by
    simpa [prefixWord, tailWord_1192054, baseEnd_1192054] using wordTrace_append hprefix tailTrace_1192054
  have hstable : (prefixWord ++ tailWord_1192054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192054).length < 2 ^ (prefixWord ++ tailWord_1192054).sum := by decide
  have hdescent : baseEnd_1192054 < baseStart_1192054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192067 : List Nat := [1, 1, 1, 3, 3, 3, 4, 6]
def baseStart_1192067 : Nat := 118140960795 + 1192067 * 2 ^ 59
def prefixEnd_1192067 : Nat := 4983230072969 + 3 ^ 40 * 1192067 * 2
def baseEnd_1192067 : Nat := 45340988397280945635577

theorem tailTrace_1192067 : CollatzResearch.WordTrace tailWord_1192067 prefixEnd_1192067 45340988397280945635577 := by
  unfold tailWord_1192067
  simp only [CollatzResearch.WordTrace]
  refine ⟨43478255372352322680174455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28985503581568215120116303 43478255372352322680174455)
  ·
    refine ⟨65217383058528484020261683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43478255372352322680174455 65217383058528484020261683)
    ·
      refine ⟨97826074587792726030392525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65217383058528484020261683 97826074587792726030392525)
      ·
        refine ⟨36684777970422272261397197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97826074587792726030392525 36684777970422272261397197)
        ·
          refine ⟨13756791738908352098023949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36684777970422272261397197 13756791738908352098023949)
          ·
            refine ⟨5158796902090632036758981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13756791738908352098023949 5158796902090632036758981)
            ·
              refine ⟨967274419141993506892309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5158796902090632036758981 967274419141993506892309)
              ·
                refine ⟨45340988397280945635577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 967274419141993506892309 45340988397280945635577)
                ·
                  rfl

theorem cell22_1192067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 6].length) (baseStart_1192067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192067 prefixEnd_1192067 := by exact prefixLift 1192067
  have htrace : WordTrace (prefixWord ++ tailWord_1192067) baseStart_1192067 baseEnd_1192067 := by
    simpa [prefixWord, tailWord_1192067, baseEnd_1192067] using wordTrace_append hprefix tailTrace_1192067
  have hstable : (prefixWord ++ tailWord_1192067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192067).length < 2 ^ (prefixWord ++ tailWord_1192067).sum := by decide
  have hdescent : baseEnd_1192067 < baseStart_1192067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192150 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1192150 : Nat := 118140960795 + 1192150 * 2 ^ 59
def prefixEnd_1192150 : Nat := 4983230072969 + 3 ^ 40 * 1192150 * 2
def baseEnd_1192150 : Nat := 408097308171743960894939

theorem tailTrace_1192150 : CollatzResearch.WordTrace tailWord_1192150 prefixEnd_1192150 408097308171743960894939 := by
  unfold tailWord_1192150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717580164440726740965369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28987521754034418570297269 2717580164440726740965369)
  ·
    refine ⟨2038185123330545055724027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2717580164440726740965369 2038185123330545055724027)
    ·
      refine ⟨3057277684995817583586041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038185123330545055724027 3057277684995817583586041)
      ·
        refine ⟨2292958263746863187689531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057277684995817583586041 2292958263746863187689531)
        ·
          refine ⟨3439437395620294781534297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292958263746863187689531 3439437395620294781534297)
          ·
            refine ⟨2579578046715221086150723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439437395620294781534297 2579578046715221086150723)
            ·
              refine ⟨3869367070072831629226085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579578046715221086150723 3869367070072831629226085)
              ·
                refine ⟨725506325638655930479891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3869367070072831629226085 725506325638655930479891)
                ·
                  refine ⟨1088259488457983895719837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725506325638655930479891 1088259488457983895719837)
                  ·
                    refine ⟨408097308171743960894939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088259488457983895719837 408097308171743960894939)
                    ·
                      rfl

theorem cell22_1192150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1192150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192150 prefixEnd_1192150 := by exact prefixLift 1192150
  have htrace : WordTrace (prefixWord ++ tailWord_1192150) baseStart_1192150 baseEnd_1192150 := by
    simpa [prefixWord, tailWord_1192150, baseEnd_1192150] using wordTrace_append hprefix tailTrace_1192150
  have hstable : (prefixWord ++ tailWord_1192150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192150).length < 2 ^ (prefixWord ++ tailWord_1192150).sum := by decide
  have hdescent : baseEnd_1192150 < baseStart_1192150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192223 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 2, 3]
def baseStart_1192223 : Nat := 118140960795 + 1192223 * 2 ^ 59
def prefixEnd_1192223 : Nat := 4983230072969 + 3 ^ 40 * 1192223 * 2
def baseEnd_1192223 : Nat := 408122297563596103819715

theorem tailTrace_1192223 : CollatzResearch.WordTrace tailWord_1192223 prefixEnd_1192223 408122297563596103819715 := by
  unfold tailWord_1192223
  simp only [CollatzResearch.WordTrace]
  refine ⟨43483945159787161322853323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28989296773191440881902215 43483945159787161322853323)
  ·
    refine ⟨65225917739680741984279985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43483945159787161322853323 65225917739680741984279985)
    ·
      refine ⟨48919438304760556488209989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65225917739680741984279985 48919438304760556488209989)
      ·
        refine ⟨9172394682142604341539373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48919438304760556488209989 9172394682142604341539373)
        ·
          refine ⟨3439648005803476628077265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9172394682142604341539373 3439648005803476628077265)
          ·
            refine ⟨2579736004352607471057949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439648005803476628077265 2579736004352607471057949)
            ·
              refine ⟨967401001632227801646731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2579736004352607471057949 967401001632227801646731)
              ·
                refine ⟨1451101502448341702470097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967401001632227801646731 1451101502448341702470097)
                ·
                  refine ⟨1088326126836256276852573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1451101502448341702470097 1088326126836256276852573)
                  ·
                    refine ⟨408122297563596103819715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088326126836256276852573 408122297563596103819715)
                    ·
                      rfl

theorem cell22_1192223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_1192223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192223 prefixEnd_1192223 := by exact prefixLift 1192223
  have htrace : WordTrace (prefixWord ++ tailWord_1192223) baseStart_1192223 baseEnd_1192223 := by
    simpa [prefixWord, tailWord_1192223, baseEnd_1192223] using wordTrace_append hprefix tailTrace_1192223
  have hstable : (prefixWord ++ tailWord_1192223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192223).length < 2 ^ (prefixWord ++ tailWord_1192223).sum := by decide
  have hdescent : baseEnd_1192223 < baseStart_1192223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192324 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1192324 : Nat := 118140960795 + 1192324 * 2 ^ 59
def prefixEnd_1192324 : Nat := 4983230072969 + 3 ^ 40 * 1192324 * 2
def baseEnd_1192324 : Nat := 408156871927665507044405

theorem tailTrace_1192324 : CollatzResearch.WordTrace tailWord_1192324 prefixEnd_1192324 408156871927665507044405 := by
  unfold tailWord_1192324
  simp only [CollatzResearch.WordTrace]
  refine ⟨21743814466210627786140013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28991752621614170381520017 21743814466210627786140013)
  ·
    refine ⟨8153930424828985419802505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21743814466210627786140013 8153930424828985419802505)
    ·
      refine ⟨6115447818621739064851879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8153930424828985419802505 6115447818621739064851879)
      ·
        refine ⟨9173171727932608597277819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6115447818621739064851879 9173171727932608597277819)
        ·
          refine ⟨13759757591898912895916729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9173171727932608597277819 13759757591898912895916729)
          ·
            refine ⟨10319818193924184671937547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13759757591898912895916729 10319818193924184671937547)
            ·
              refine ⟨15479727290886277007906321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10319818193924184671937547 15479727290886277007906321)
              ·
                refine ⟨11609795468164707755929741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15479727290886277007906321 11609795468164707755929741)
                ·
                  refine ⟨4353673300561765408473653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11609795468164707755929741 4353673300561765408473653)
                  ·
                    refine ⟨408156871927665507044405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4353673300561765408473653 408156871927665507044405)
                    ·
                      rfl

theorem cell22_1192324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1192324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192324 prefixEnd_1192324 := by exact prefixLift 1192324
  have htrace : WordTrace (prefixWord ++ tailWord_1192324) baseStart_1192324 baseEnd_1192324 := by
    simpa [prefixWord, tailWord_1192324, baseEnd_1192324] using wordTrace_append hprefix tailTrace_1192324
  have hstable : (prefixWord ++ tailWord_1192324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192324).length < 2 ^ (prefixWord ++ tailWord_1192324).sum := by decide
  have hdescent : baseEnd_1192324 < baseStart_1192324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192356 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1192356 : Nat := 118140960795 + 1192356 * 2 ^ 59
def prefixEnd_1192356 : Nat := 4983230072969 + 3 ^ 40 * 1192356 * 2
def baseEnd_1192356 : Nat := 408167826181628090244307

theorem tailTrace_1192356 : CollatzResearch.WordTrace tailWord_1192356 prefixEnd_1192356 408167826181628090244307 := by
  unfold tailWord_1192356
  simp only [CollatzResearch.WordTrace]
  refine ⟨21744398034152662518722461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28992530712203550024963281 21744398034152662518722461)
  ·
    refine ⟨8154149262807248444520923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21744398034152662518722461 8154149262807248444520923)
    ·
      refine ⟨12231223894210872666781385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8154149262807248444520923 12231223894210872666781385)
      ·
        refine ⟨9173417920658154500086039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12231223894210872666781385 9173417920658154500086039)
        ·
          refine ⟨13760126880987231750129059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9173417920658154500086039 13760126880987231750129059)
          ·
            refine ⟨20640190321480847625193589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13760126880987231750129059 20640190321480847625193589)
            ·
              refine ⟨1935017842638829464861899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20640190321480847625193589 1935017842638829464861899)
              ·
                refine ⟨2902526763958244197292849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935017842638829464861899 2902526763958244197292849)
                ·
                  refine ⟨2176895072968683147969637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2902526763958244197292849 2176895072968683147969637)
                  ·
                    refine ⟨408167826181628090244307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176895072968683147969637 408167826181628090244307)
                    ·
                      rfl

theorem cell22_1192356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1192356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192356 prefixEnd_1192356 := by exact prefixLift 1192356
  have htrace : WordTrace (prefixWord ++ tailWord_1192356) baseStart_1192356 baseEnd_1192356 := by
    simpa [prefixWord, tailWord_1192356, baseEnd_1192356] using wordTrace_append hprefix tailTrace_1192356
  have hstable : (prefixWord ++ tailWord_1192356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192356).length < 2 ^ (prefixWord ++ tailWord_1192356).sum := by decide
  have hdescent : baseEnd_1192356 < baseStart_1192356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192360 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_1192360 : Nat := 118140960795 + 1192360 * 2 ^ 59
def prefixEnd_1192360 : Nat := 4983230072969 + 3 ^ 40 * 1192360 * 2
def baseEnd_1192360 : Nat := 136056398487791137714765

theorem tailTrace_1192360 : CollatzResearch.WordTrace tailWord_1192360 prefixEnd_1192360 136056398487791137714765 := by
  unfold tailWord_1192360
  simp only [CollatzResearch.WordTrace]
  refine ⟨21744470980145416860295267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28992627973527222480393689 21744470980145416860295267)
  ·
    refine ⟨32616706470218125290442901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21744470980145416860295267 32616706470218125290442901)
    ·
      refine ⟨1528908115791474622989511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32616706470218125290442901 1528908115791474622989511)
      ·
        refine ⟨2293362173687211934484267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528908115791474622989511 2293362173687211934484267)
        ·
          refine ⟨3440043260530817901726401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293362173687211934484267 3440043260530817901726401)
          ·
            refine ⟨2580032445398113426294801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440043260530817901726401 2580032445398113426294801)
            ·
              refine ⟨1935024334048585069721101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580032445398113426294801 1935024334048585069721101)
              ·
                refine ⟨725634125268219401145413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1935024334048585069721101 725634125268219401145413)
                ·
                  refine ⟨136056398487791137714765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 725634125268219401145413 136056398487791137714765)
                  ·
                    rfl

theorem cell22_1192360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_1192360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192360 prefixEnd_1192360 := by exact prefixLift 1192360
  have htrace : WordTrace (prefixWord ++ tailWord_1192360) baseStart_1192360 baseEnd_1192360 := by
    simpa [prefixWord, tailWord_1192360, baseEnd_1192360] using wordTrace_append hprefix tailTrace_1192360
  have hstable : (prefixWord ++ tailWord_1192360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192360).length < 2 ^ (prefixWord ++ tailWord_1192360).sum := by decide
  have hdescent : baseEnd_1192360 < baseStart_1192360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192362 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1192362 : Nat := 118140960795 + 1192362 * 2 ^ 59
def prefixEnd_1192362 : Nat := 4983230072969 + 3 ^ 40 * 1192362 * 2
def baseEnd_1192362 : Nat := 408169880104246074594289

theorem tailTrace_1192362 : CollatzResearch.WordTrace tailWord_1192362 prefixEnd_1192362 408169880104246074594289 := by
  unfold tailWord_1192362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10872253726570897015540835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28992676604189058708108893 10872253726570897015540835)
  ·
    refine ⟨16308380589856345523311253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10872253726570897015540835 16308380589856345523311253)
    ·
      refine ⟨764455340149516196405215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16308380589856345523311253 764455340149516196405215)
      ·
        refine ⟨1146683010224274294607823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764455340149516196405215 1146683010224274294607823)
        ·
          refine ⟨1720024515336411441911735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146683010224274294607823 1720024515336411441911735)
          ·
            refine ⟨2580036773004617162867603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720024515336411441911735 2580036773004617162867603)
            ·
              refine ⟨3870055159506925744301405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580036773004617162867603 3870055159506925744301405)
              ·
                refine ⟨1451270684815097154113027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3870055159506925744301405 1451270684815097154113027)
                ·
                  refine ⟨2176906027222645731169541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451270684815097154113027 2176906027222645731169541)
                  ·
                    refine ⟨408169880104246074594289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176906027222645731169541 408169880104246074594289)
                    ·
                      rfl

theorem cell22_1192362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1192362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192362 prefixEnd_1192362 := by exact prefixLift 1192362
  have htrace : WordTrace (prefixWord ++ tailWord_1192362) baseStart_1192362 baseEnd_1192362 := by
    simpa [prefixWord, tailWord_1192362, baseEnd_1192362] using wordTrace_append hprefix tailTrace_1192362
  have hstable : (prefixWord ++ tailWord_1192362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192362).length < 2 ^ (prefixWord ++ tailWord_1192362).sum := by decide
  have hdescent : baseEnd_1192362 < baseStart_1192362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192437 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1192437 : Nat := 118140960795 + 1192437 * 2 ^ 59
def prefixEnd_1192437 : Nat := 4983230072969 + 3 ^ 40 * 1192437 * 2
def baseEnd_1192437 : Nat := 408195554136970878969059

theorem tailTrace_1192437 : CollatzResearch.WordTrace tailWord_1192437 prefixEnd_1192437 408195554136970878969059 := by
  unfold tailWord_1192437
  simp only [CollatzResearch.WordTrace]
  refine ⟨43491750381011875871143565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28994500254007917247429043 43491750381011875871143565)
  ·
    refine ⟨16309406392879453451678837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43491750381011875871143565 16309406392879453451678837)
    ·
      refine ⟨1529006849332448761094891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16309406392879453451678837 1529006849332448761094891)
      ·
        refine ⟨2293510273998673141642337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529006849332448761094891 2293510273998673141642337)
        ·
          refine ⟨1720132705499004856231753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2293510273998673141642337 1720132705499004856231753)
          ·
            refine ⟨1290099529124253642173815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1720132705499004856231753 1290099529124253642173815)
            ·
              refine ⟨1935149293686380463260723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290099529124253642173815 1935149293686380463260723)
              ·
                refine ⟨2902723940529570694891085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935149293686380463260723 2902723940529570694891085)
                ·
                  refine ⟨1088521477698589010584157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2902723940529570694891085 1088521477698589010584157)
                  ·
                    refine ⟨408195554136970878969059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088521477698589010584157 408195554136970878969059)
                    ·
                      rfl

theorem cell22_1192437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1192437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192437 prefixEnd_1192437 := by exact prefixLift 1192437
  have htrace : WordTrace (prefixWord ++ tailWord_1192437) baseStart_1192437 baseEnd_1192437 := by
    simpa [prefixWord, tailWord_1192437, baseEnd_1192437] using wordTrace_append hprefix tailTrace_1192437
  have hstable : (prefixWord ++ tailWord_1192437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192437).length < 2 ^ (prefixWord ++ tailWord_1192437).sum := by decide
  have hdescent : baseEnd_1192437 < baseStart_1192437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192450 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1192450 : Nat := 118140960795 + 1192450 * 2 ^ 59
def prefixEnd_1192450 : Nat := 4983230072969 + 3 ^ 40 * 1192450 * 2
def baseEnd_1192450 : Nat := 136066668100881059464673

theorem tailTrace_1192450 : CollatzResearch.WordTrace tailWord_1192450 prefixEnd_1192450 136066668100881059464673 := by
  unfold tailWord_1192450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873056132491194772841701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28994816353309852727577869 10873056132491194772841701)
  ·
    refine ⟨2038698024842099019907819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10873056132491194772841701 2038698024842099019907819)
    ·
      refine ⟨3058047037263148529861729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038698024842099019907819 3058047037263148529861729)
      ·
        refine ⟨2293535277947361397396297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3058047037263148529861729 2293535277947361397396297)
        ·
          refine ⟨1720151458460521048047223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2293535277947361397396297 1720151458460521048047223)
          ·
            refine ⟨2580227187690781572070835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720151458460521048047223 2580227187690781572070835)
            ·
              refine ⟨3870340781536172358106253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580227187690781572070835 3870340781536172358106253)
              ·
                refine ⟨1451377793076064634289845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3870340781536172358106253 1451377793076064634289845)
                ·
                  refine ⟨136066668100881059464673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451377793076064634289845 136066668100881059464673)
                  ·
                    rfl

theorem cell22_1192450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1192450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192450 prefixEnd_1192450 := by exact prefixLift 1192450
  have htrace : WordTrace (prefixWord ++ tailWord_1192450) baseStart_1192450 baseEnd_1192450 := by
    simpa [prefixWord, tailWord_1192450, baseEnd_1192450] using wordTrace_append hprefix tailTrace_1192450
  have hstable : (prefixWord ++ tailWord_1192450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192450).length < 2 ^ (prefixWord ++ tailWord_1192450).sum := by decide
  have hdescent : baseEnd_1192450 < baseStart_1192450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192476 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1192476 : Nat := 118140960795 + 1192476 * 2 ^ 59
def prefixEnd_1192476 : Nat := 4983230072969 + 3 ^ 40 * 1192476 * 2
def baseEnd_1192476 : Nat := 408208904633987777243939

theorem tailTrace_1192476 : CollatzResearch.WordTrace tailWord_1192476 prefixEnd_1192476 408208904633987777243939 := by
  unfold tailWord_1192476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21746586413935292765906641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28995448551913723687875521 21746586413935292765906641)
  ·
    refine ⟨16309939810451469574429981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21746586413935292765906641 16309939810451469574429981)
    ·
      refine ⟨6116227428919301090411243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16309939810451469574429981 6116227428919301090411243)
      ·
        refine ⟨9174341143378951635616865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6116227428919301090411243 9174341143378951635616865)
        ·
          refine ⟨6880755857534213726712649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9174341143378951635616865 6880755857534213726712649)
          ·
            refine ⟨5160566893150660295034487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6880755857534213726712649 5160566893150660295034487)
            ·
              refine ⟨7740850339725990442551731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160566893150660295034487 7740850339725990442551731)
              ·
                refine ⟨11611275509588985663827597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7740850339725990442551731 11611275509588985663827597)
                ·
                  refine ⟨4354228316095869623935349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11611275509588985663827597 4354228316095869623935349)
                  ·
                    refine ⟨408208904633987777243939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4354228316095869623935349 408208904633987777243939)
                    ·
                      rfl

theorem cell22_1192476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1192476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192476 prefixEnd_1192476 := by exact prefixLift 1192476
  have htrace : WordTrace (prefixWord ++ tailWord_1192476) baseStart_1192476 baseEnd_1192476 := by
    simpa [prefixWord, tailWord_1192476, baseEnd_1192476] using wordTrace_append hprefix tailTrace_1192476
  have hstable : (prefixWord ++ tailWord_1192476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192476).length < 2 ^ (prefixWord ++ tailWord_1192476).sum := by decide
  have hdescent : baseEnd_1192476 < baseStart_1192476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192506 : List Nat := [3, 1, 1, 1, 3, 3, 3, 7]
def baseStart_1192506 : Nat := 118140960795 + 1192506 * 2 ^ 59
def prefixEnd_1192506 : Nat := 4983230072969 + 3 ^ 40 * 1192506 * 2
def baseEnd_1192506 : Nat := 45357686027453077665983

theorem tailTrace_1192506 : CollatzResearch.WordTrace tailWord_1192506 prefixEnd_1192506 45357686027453077665983 := by
  unfold tailWord_1192506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873566754440475163851343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28996178011841267103603581 10873566754440475163851343)
  ·
    refine ⟨16310350131660712745777015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10873566754440475163851343 16310350131660712745777015)
    ·
      refine ⟨24465525197491069118665523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16310350131660712745777015 24465525197491069118665523)
      ·
        refine ⟨36698287796236603677998285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24465525197491069118665523 36698287796236603677998285)
        ·
          refine ⟨13761857923588726379249357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36698287796236603677998285 13761857923588726379249357)
          ·
            refine ⟨5160696721345772392218509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13761857923588726379249357 5160696721345772392218509)
            ·
              refine ⟨1935261270504664647081941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5160696721345772392218509 1935261270504664647081941)
              ·
                refine ⟨45357686027453077665983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1935261270504664647081941 45357686027453077665983)
                ·
                  rfl

theorem cell22_1192506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_1192506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192506 prefixEnd_1192506 := by exact prefixLift 1192506
  have htrace : WordTrace (prefixWord ++ tailWord_1192506) baseStart_1192506 baseEnd_1192506 := by
    simpa [prefixWord, tailWord_1192506, baseEnd_1192506] using wordTrace_append hprefix tailTrace_1192506
  have hstable : (prefixWord ++ tailWord_1192506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192506).length < 2 ^ (prefixWord ++ tailWord_1192506).sum := by decide
  have hdescent : baseEnd_1192506 < baseStart_1192506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192525 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1192525 : Nat := 118140960795 + 1192525 * 2 ^ 59
def prefixEnd_1192525 : Nat := 4983230072969 + 3 ^ 40 * 1192525 * 2
def baseEnd_1192525 : Nat := 408225678335367982768789

theorem tailTrace_1192525 : CollatzResearch.WordTrace tailWord_1192525 prefixEnd_1192525 408225678335367982768789 := by
  unfold tailWord_1192525
  simp only [CollatzResearch.WordTrace]
  refine ⟨43494960004693066900347029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28996640003128711266898019 43494960004693066900347029)
  ·
    refine ⟨2038826250219987510953767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43494960004693066900347029 2038826250219987510953767)
    ·
      refine ⟨3058239375329981266430651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038826250219987510953767 3058239375329981266430651)
      ·
        refine ⟨4587359062994971899645977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058239375329981266430651 4587359062994971899645977)
        ·
          refine ⟨3440519297246228924734483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4587359062994971899645977 3440519297246228924734483)
          ·
            refine ⟨5160778945869343387101725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440519297246228924734483 5160778945869343387101725)
            ·
              refine ⟨1935292104701003770163147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5160778945869343387101725 1935292104701003770163147)
              ·
                refine ⟨2902938157051505655244721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935292104701003770163147 2902938157051505655244721)
                ·
                  refine ⟨2177203617788629241433541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2902938157051505655244721 2177203617788629241433541)
                  ·
                    refine ⟨408225678335367982768789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177203617788629241433541 408225678335367982768789)
                    ·
                      rfl

theorem cell22_1192525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1192525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192525 prefixEnd_1192525 := by exact prefixLift 1192525
  have htrace : WordTrace (prefixWord ++ tailWord_1192525) baseStart_1192525 baseEnd_1192525 := by
    simpa [prefixWord, tailWord_1192525, baseEnd_1192525] using wordTrace_append hprefix tailTrace_1192525
  have hstable : (prefixWord ++ tailWord_1192525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192525).length < 2 ^ (prefixWord ++ tailWord_1192525).sum := by decide
  have hdescent : baseEnd_1192525 < baseStart_1192525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192611 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_1192611 : Nat := 118140960795 + 1192611 * 2 ^ 59
def prefixEnd_1192611 : Nat := 4983230072969 + 3 ^ 40 * 1192611 * 2
def baseEnd_1192611 : Nat := 408255117892892425118525

theorem tailTrace_1192611 : CollatzResearch.WordTrace tailWord_1192611 prefixEnd_1192611 408255117892892425118525 := by
  unfold tailWord_1192611
  simp only [CollatzResearch.WordTrace]
  refine ⟨43498096682381503587977687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28998731121587669058651791 43498096682381503587977687)
  ·
    refine ⟨65247145023572255381966531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43498096682381503587977687 65247145023572255381966531)
    ·
      refine ⟨97870717535358383072949797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65247145023572255381966531 97870717535358383072949797)
      ·
        refine ⟨18350759537879696826178087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97870717535358383072949797 18350759537879696826178087)
        ·
          refine ⟨27526139306819545239267131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18350759537879696826178087 27526139306819545239267131)
          ·
            refine ⟨41289208960229317858900697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27526139306819545239267131 41289208960229317858900697)
            ·
              refine ⟨30966906720171988394175523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41289208960229317858900697 30966906720171988394175523)
              ·
                refine ⟨46450360080257982591263285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30966906720171988394175523 46450360080257982591263285)
                ·
                  refine ⟨4354721257524185867930933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46450360080257982591263285 4354721257524185867930933)
                  ·
                    refine ⟨408255117892892425118525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4354721257524185867930933 408255117892892425118525)
                    ·
                      rfl

theorem cell22_1192611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_1192611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192611 prefixEnd_1192611 := by exact prefixLift 1192611
  have htrace : WordTrace (prefixWord ++ tailWord_1192611) baseStart_1192611 baseEnd_1192611 := by
    simpa [prefixWord, tailWord_1192611, baseEnd_1192611] using wordTrace_append hprefix tailTrace_1192611
  have hstable : (prefixWord ++ tailWord_1192611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192611).length < 2 ^ (prefixWord ++ tailWord_1192611).sum := by decide
  have hdescent : baseEnd_1192611 < baseStart_1192611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_1192656 : Nat := 118140960795 + 1192656 * 2 ^ 59
def prefixEnd_1192656 : Nat := 4983230072969 + 3 ^ 40 * 1192656 * 2
def baseEnd_1192656 : Nat := 408270522312527307743387

theorem tailTrace_1192656 : CollatzResearch.WordTrace tailWord_1192656 prefixEnd_1192656 408270522312527307743387 := by
  unfold tailWord_1192656
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749868983609238136682911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28999825311478984182243881 21749868983609238136682911)
  ·
    refine ⟨32624803475413857205024367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21749868983609238136682911 32624803475413857205024367)
    ·
      refine ⟨48937205213120785807536551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32624803475413857205024367 48937205213120785807536551)
      ·
        refine ⟨73405807819681178711304827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48937205213120785807536551 73405807819681178711304827)
        ·
          refine ⟨110108711729521768066957241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73405807819681178711304827 110108711729521768066957241)
          ·
            refine ⟨82581533797141326050217931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110108711729521768066957241 82581533797141326050217931)
            ·
              refine ⟨123872300695711989075326897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82581533797141326050217931 123872300695711989075326897)
              ·
                refine ⟨92904225521783991806495173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123872300695711989075326897 92904225521783991806495173)
                ·
                  refine ⟨17419542285334498463717845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92904225521783991806495173 17419542285334498463717845)
                  ·
                    refine ⟨408270522312527307743387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17419542285334498463717845 408270522312527307743387)
                    ·
                      rfl

theorem cell22_1192656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_1192656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192656 prefixEnd_1192656 := by exact prefixLift 1192656
  have htrace : WordTrace (prefixWord ++ tailWord_1192656) baseStart_1192656 baseEnd_1192656 := by
    simpa [prefixWord, tailWord_1192656, baseEnd_1192656] using wordTrace_append hprefix tailTrace_1192656
  have hstable : (prefixWord ++ tailWord_1192656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192656).length < 2 ^ (prefixWord ++ tailWord_1192656).sum := by decide
  have hdescent : baseEnd_1192656 < baseStart_1192656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192658 : List Nat := [3, 2, 2, 2, 3, 10]
def baseStart_1192658 : Nat := 118140960795 + 1192658 * 2 ^ 59
def prefixEnd_1192658 : Nat := 4983230072969 + 3 ^ 40 * 1192658 * 2
def baseEnd_1192658 : Nat := 5040385271029629249301

theorem tailTrace_1192658 : CollatzResearch.WordTrace tailWord_1192658 prefixEnd_1192658 5040385271029629249301 := by
  unfold tailWord_1192658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10874952728302807653734657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28999873942140820409959085 10874952728302807653734657)
  ·
    refine ⟨8156214546227105740300993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10874952728302807653734657 8156214546227105740300993)
    ·
      refine ⟨6117160909670329305225745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8156214546227105740300993 6117160909670329305225745)
      ·
        refine ⟨4587870682252746978919309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6117160909670329305225745 4587870682252746978919309)
        ·
          refine ⟨1720451505844780117094741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4587870682252746978919309 1720451505844780117094741)
          ·
            refine ⟨5040385271029629249301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1720451505844780117094741 5040385271029629249301)
            ·
              rfl

theorem cell22_1192658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 10].length) (baseStart_1192658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192658 prefixEnd_1192658 := by exact prefixLift 1192658
  have htrace : WordTrace (prefixWord ++ tailWord_1192658) baseStart_1192658 baseEnd_1192658 := by
    simpa [prefixWord, tailWord_1192658, baseEnd_1192658] using wordTrace_append hprefix tailTrace_1192658
  have hstable : (prefixWord ++ tailWord_1192658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192658).length < 2 ^ (prefixWord ++ tailWord_1192658).sum := by decide
  have hdescent : baseEnd_1192658 < baseStart_1192658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192675 : List Nat := [1, 1, 1, 7, 1, 3, 1, 7]
def baseStart_1192675 : Nat := 118140960795 + 1192675 * 2 ^ 59
def prefixEnd_1192675 : Nat := 4983230072969 + 3 ^ 40 * 1192675 * 2
def baseEnd_1192675 : Nat := 45364114044535287946481

theorem tailTrace_1192675 : CollatzResearch.WordTrace tailWord_1192675 prefixEnd_1192675 45364114044535287946481 := by
  unfold tailWord_1192675
  simp only [CollatzResearch.WordTrace]
  refine ⟨43500430954149642518307479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29000287302766428345538319 43500430954149642518307479)
  ·
    refine ⟨65250646431224463777461219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43500430954149642518307479 65250646431224463777461219)
    ·
      refine ⟨97875969646836695666191829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65250646431224463777461219 97875969646836695666191829)
      ·
        refine ⟨2293968038597735054676371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 97875969646836695666191829 2293968038597735054676371)
        ·
          refine ⟨3440952057896602582014557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293968038597735054676371 3440952057896602582014557)
          ·
            refine ⟨1290357021711225968255459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3440952057896602582014557 1290357021711225968255459)
            ·
              refine ⟨1935535532566838952383189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290357021711225968255459 1935535532566838952383189)
              ·
                refine ⟨45364114044535287946481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1935535532566838952383189 45364114044535287946481)
                ·
                  rfl

theorem cell22_1192675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 7].length) (baseStart_1192675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192675 prefixEnd_1192675 := by exact prefixLift 1192675
  have htrace : WordTrace (prefixWord ++ tailWord_1192675) baseStart_1192675 baseEnd_1192675 := by
    simpa [prefixWord, tailWord_1192675, baseEnd_1192675] using wordTrace_append hprefix tailTrace_1192675
  have hstable : (prefixWord ++ tailWord_1192675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192675).length < 2 ^ (prefixWord ++ tailWord_1192675).sum := by decide
  have hdescent : baseEnd_1192675 < baseStart_1192675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192690 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_1192690 : Nat := 118140960795 + 1192690 * 2 ^ 59
def prefixEnd_1192690 : Nat := 4983230072969 + 3 ^ 40 * 1192690 * 2
def baseEnd_1192690 : Nat := 408282161207362552393283

theorem tailTrace_1192690 : CollatzResearch.WordTrace tailWord_1192690 prefixEnd_1192690 408282161207362552393283 := by
  unfold tailWord_1192690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10875244512273825020025881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29000652032730200053402349 10875244512273825020025881)
  ·
    refine ⟨8156433384205368765019411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10875244512273825020025881 8156433384205368765019411)
    ·
      refine ⟨12234650076308053147529117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8156433384205368765019411 12234650076308053147529117)
      ·
        refine ⟨4587993778615519930323419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12234650076308053147529117 4587993778615519930323419)
        ·
          refine ⟨6881990667923279895485129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587993778615519930323419 6881990667923279895485129)
          ·
            refine ⟨5161493000942459921613847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6881990667923279895485129 5161493000942459921613847)
            ·
              refine ⟨7742239501413689882420771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161493000942459921613847 7742239501413689882420771)
              ·
                refine ⟨11613359252120534823631157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7742239501413689882420771 11613359252120534823631157)
                ·
                  refine ⟨1088752429886300139715421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11613359252120534823631157 1088752429886300139715421)
                  ·
                    refine ⟨408282161207362552393283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088752429886300139715421 408282161207362552393283)
                    ·
                      rfl

theorem cell22_1192690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_1192690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192690 prefixEnd_1192690 := by exact prefixLift 1192690
  have htrace : WordTrace (prefixWord ++ tailWord_1192690) baseStart_1192690 baseEnd_1192690 := by
    simpa [prefixWord, tailWord_1192690, baseEnd_1192690] using wordTrace_append hprefix tailTrace_1192690
  have hstable : (prefixWord ++ tailWord_1192690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192690).length < 2 ^ (prefixWord ++ tailWord_1192690).sum := by decide
  have hdescent : baseEnd_1192690 < baseStart_1192690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192748 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1192748 : Nat := 118140960795 + 1192748 * 2 ^ 59
def prefixEnd_1192748 : Nat := 4983230072969 + 3 ^ 40 * 1192748 * 2
def baseEnd_1192748 : Nat := 136100671930889911481035

theorem tailTrace_1192748 : CollatzResearch.WordTrace tailWord_1192748 prefixEnd_1192748 136100671930889911481035 := by
  unfold tailWord_1192748
  simp only [CollatzResearch.WordTrace]
  refine ⟨21751546741442587992857449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29002062321923450657143265 21751546741442587992857449)
  ·
    refine ⟨16313660056081940994643087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21751546741442587992857449 16313660056081940994643087)
    ·
      refine ⟨24470490084122911491964631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16313660056081940994643087 24470490084122911491964631)
      ·
        refine ⟨36705735126184367237946947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24470490084122911491964631 36705735126184367237946947)
        ·
          refine ⟨55058602689276550856920421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36705735126184367237946947 55058602689276550856920421)
          ·
            refine ⟨10323488004239353285672579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55058602689276550856920421 10323488004239353285672579)
            ·
              refine ⟨15485232006359029928508869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10323488004239353285672579 15485232006359029928508869)
              ·
                refine ⟨2903481001192318111595413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15485232006359029928508869 2903481001192318111595413)
                ·
                  refine ⟨136100671930889911481035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2903481001192318111595413 136100671930889911481035)
                  ·
                    rfl

theorem cell22_1192748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1192748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192748 prefixEnd_1192748 := by exact prefixLift 1192748
  have htrace : WordTrace (prefixWord ++ tailWord_1192748) baseStart_1192748 baseEnd_1192748 := by
    simpa [prefixWord, tailWord_1192748, baseEnd_1192748] using wordTrace_append hprefix tailTrace_1192748
  have hstable : (prefixWord ++ tailWord_1192748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192748).length < 2 ^ (prefixWord ++ tailWord_1192748).sum := by decide
  have hdescent : baseEnd_1192748 < baseStart_1192748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192758 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1192758 : Nat := 118140960795 + 1192758 * 2 ^ 59
def prefixEnd_1192758 : Nat := 4983230072969 + 3 ^ 40 * 1192758 * 2
def baseEnd_1192758 : Nat := 408305438997033041693075

theorem tailTrace_1192758 : CollatzResearch.WordTrace tailWord_1192758 prefixEnd_1192758 408305438997033041693075 := by
  unfold tailWord_1192758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718966138303059230848683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29002305475232631795719285 2718966138303059230848683)
  ·
    refine ⟨4078449207454588846273025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718966138303059230848683 4078449207454588846273025)
    ·
      refine ⟨3058836905590941634704769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4078449207454588846273025 3058836905590941634704769)
      ·
        refine ⟨2294127679193206226028577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3058836905590941634704769 2294127679193206226028577)
        ·
          refine ⟨1720595759394904669521433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2294127679193206226028577 1720595759394904669521433)
          ·
            refine ⟨1290446819546178502141075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1720595759394904669521433 1290446819546178502141075)
            ·
              refine ⟨1935670229319267753211613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290446819546178502141075 1935670229319267753211613)
              ·
                refine ⟨725876335994725407454355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1935670229319267753211613 725876335994725407454355)
                ·
                  refine ⟨1088814503992088111181533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725876335994725407454355 1088814503992088111181533)
                  ·
                    refine ⟨408305438997033041693075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088814503992088111181533 408305438997033041693075)
                    ·
                      rfl

theorem cell22_1192758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1192758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192758 prefixEnd_1192758 := by exact prefixLift 1192758
  have htrace : WordTrace (prefixWord ++ tailWord_1192758) baseStart_1192758 baseEnd_1192758 := by
    simpa [prefixWord, tailWord_1192758, baseEnd_1192758] using wordTrace_append hprefix tailTrace_1192758
  have hstable : (prefixWord ++ tailWord_1192758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192758).length < 2 ^ (prefixWord ++ tailWord_1192758).sum := by decide
  have hdescent : baseEnd_1192758 < baseStart_1192758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192778 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1192778 : Nat := 118140960795 + 1192778 * 2 ^ 59
def prefixEnd_1192778 : Nat := 4983230072969 + 3 ^ 40 * 1192778 * 2
def baseEnd_1192778 : Nat := 408312285405759656193013

theorem tailTrace_1192778 : CollatzResearch.WordTrace tailWord_1192778 prefixEnd_1192778 408312285405759656193013 := by
  unfold tailWord_1192778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876046918194122777326747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29002791781850994072871325 10876046918194122777326747)
  ·
    refine ⟨16314070377291184165990121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10876046918194122777326747 16314070377291184165990121)
    ·
      refine ⟨12235552782968388124492591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16314070377291184165990121 12235552782968388124492591)
      ·
        refine ⟨18353329174452582186738887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12235552782968388124492591 18353329174452582186738887)
        ·
          refine ⟨27529993761678873280108331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18353329174452582186738887 27529993761678873280108331)
          ·
            refine ⟨41294990642518309920162497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27529993761678873280108331 41294990642518309920162497)
            ·
              refine ⟨30971242981888732440121873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41294990642518309920162497 30971242981888732440121873)
              ·
                refine ⟨23228432236416549330091405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30971242981888732440121873 23228432236416549330091405)
                ·
                  refine ⟨8710662088656205998784277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23228432236416549330091405 8710662088656205998784277)
                  ·
                    refine ⟨408312285405759656193013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8710662088656205998784277 408312285405759656193013)
                    ·
                      rfl

theorem cell22_1192778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1192778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192778 prefixEnd_1192778 := by exact prefixLift 1192778
  have htrace : WordTrace (prefixWord ++ tailWord_1192778) baseStart_1192778 baseEnd_1192778 := by
    simpa [prefixWord, tailWord_1192778, baseEnd_1192778] using wordTrace_append hprefix tailTrace_1192778
  have hstable : (prefixWord ++ tailWord_1192778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192778).length < 2 ^ (prefixWord ++ tailWord_1192778).sum := by decide
  have hdescent : baseEnd_1192778 < baseStart_1192778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192793 : List Nat := [1, 2, 1, 2, 2, 4, 1, 9]
def baseStart_1192793 : Nat := 118140960795 + 1192793 * 2 ^ 59
def prefixEnd_1192793 : Nat := 4983230072969 + 3 ^ 40 * 1192793 * 2
def baseEnd_1192793 : Nat := 45368602245811624118663

theorem tailTrace_1192793 : CollatzResearch.WordTrace tailWord_1192793 prefixEnd_1192793 45368602245811624118663 := by
  unfold tailWord_1192793
  simp only [CollatzResearch.WordTrace]
  refine ⟨43504734767722148671103033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29003156511814765780735355 43504734767722148671103033)
  ·
    refine ⟨32628551075791611503327275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43504734767722148671103033 32628551075791611503327275)
    ·
      refine ⟨48942826613687417254990913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32628551075791611503327275 48942826613687417254990913)
      ·
        refine ⟨36707119960265562941243185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48942826613687417254990913 36707119960265562941243185)
        ·
          refine ⟨27530339970199172205932389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36707119960265562941243185 27530339970199172205932389)
          ·
            refine ⟨5161938744412344788612323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27530339970199172205932389 5161938744412344788612323)
            ·
              refine ⟨7742908116618517182918485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161938744412344788612323 7742908116618517182918485)
              ·
                refine ⟨45368602245811624118663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7742908116618517182918485 45368602245811624118663)
                ·
                  rfl

theorem cell22_1192793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 9].length) (baseStart_1192793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192793 prefixEnd_1192793 := by exact prefixLift 1192793
  have htrace : WordTrace (prefixWord ++ tailWord_1192793) baseStart_1192793 baseEnd_1192793 := by
    simpa [prefixWord, tailWord_1192793, baseEnd_1192793] using wordTrace_append hprefix tailTrace_1192793
  have hstable : (prefixWord ++ tailWord_1192793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192793).length < 2 ^ (prefixWord ++ tailWord_1192793).sum := by decide
  have hdescent : baseEnd_1192793 < baseStart_1192793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192823 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1192823 : Nat := 118140960795 + 1192823 * 2 ^ 59
def prefixEnd_1192823 : Nat := 4983230072969 + 3 ^ 40 * 1192823 * 2
def baseEnd_1192823 : Nat := 408327689825394538817875

theorem tailTrace_1192823 : CollatzResearch.WordTrace tailWord_1192823 prefixEnd_1192823 408327689825394538817875 := by
  unfold tailWord_1192823
  simp only [CollatzResearch.WordTrace]
  refine ⟨43505828957613463794695123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29003885971742309196463415 43505828957613463794695123)
  ·
    refine ⟨65258743436420195692042685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43505828957613463794695123 65258743436420195692042685)
    ·
      refine ⟨24472028788657573384516007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65258743436420195692042685 24472028788657573384516007)
      ·
        refine ⟨36708043182986360076774011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24472028788657573384516007 36708043182986360076774011)
        ·
          refine ⟨55062064774479540115161017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36708043182986360076774011 55062064774479540115161017)
          ·
            refine ⟨41296548580859655086370763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55062064774479540115161017 41296548580859655086370763)
            ·
              refine ⟨61944822871289482629556145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41296548580859655086370763 61944822871289482629556145)
              ·
                refine ⟨46458617153467111972167109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61944822871289482629556145 46458617153467111972167109)
                ·
                  refine ⟨8710990716275083494781333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46458617153467111972167109 8710990716275083494781333)
                  ·
                    refine ⟨408327689825394538817875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8710990716275083494781333 408327689825394538817875)
                    ·
                      rfl

theorem cell22_1192823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1192823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192823 prefixEnd_1192823 := by exact prefixLift 1192823
  have htrace : WordTrace (prefixWord ++ tailWord_1192823) baseStart_1192823 baseEnd_1192823 := by
    simpa [prefixWord, tailWord_1192823, baseEnd_1192823] using wordTrace_append hprefix tailTrace_1192823
  have hstable : (prefixWord ++ tailWord_1192823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192823).length < 2 ^ (prefixWord ++ tailWord_1192823).sum := by decide
  have hdescent : baseEnd_1192823 < baseStart_1192823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192840 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1192840 : Nat := 118140960795 + 1192840 * 2 ^ 59
def prefixEnd_1192840 : Nat := 4983230072969 + 3 ^ 40 * 1192840 * 2
def baseEnd_1192840 : Nat := 408333509272812161142823

theorem tailTrace_1192840 : CollatzResearch.WordTrace tailWord_1192840 prefixEnd_1192840 408333509272812161142823 := by
  unfold tailWord_1192840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753224499275937849031987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29004299332367917132042649 21753224499275937849031987)
  ·
    refine ⟨32629836748913906773547981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21753224499275937849031987 32629836748913906773547981)
    ·
      refine ⟨12236188780842715040080493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32629836748913906773547981 12236188780842715040080493)
      ·
        refine ⟨4588570792816018140030185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12236188780842715040080493 4588570792816018140030185)
        ·
          refine ⟨3441428094612013605022639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4588570792816018140030185 3441428094612013605022639)
          ·
            refine ⟨5162142141918020407533959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441428094612013605022639 5162142141918020407533959)
            ·
              refine ⟨7743213212877030611300939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162142141918020407533959 7743213212877030611300939)
              ·
                refine ⟨11614819819315545916951409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743213212877030611300939 11614819819315545916951409)
                ·
                  refine ⟨8711114864486659437713557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11614819819315545916951409 8711114864486659437713557)
                  ·
                    refine ⟨408333509272812161142823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8711114864486659437713557 408333509272812161142823)
                    ·
                      rfl

theorem cell22_1192840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1192840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192840 prefixEnd_1192840 := by exact prefixLift 1192840
  have htrace : WordTrace (prefixWord ++ tailWord_1192840) baseStart_1192840 baseEnd_1192840 := by
    simpa [prefixWord, tailWord_1192840, baseEnd_1192840] using wordTrace_append hprefix tailTrace_1192840
  have hstable : (prefixWord ++ tailWord_1192840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192840).length < 2 ^ (prefixWord ++ tailWord_1192840).sum := by decide
  have hdescent : baseEnd_1192840 < baseStart_1192840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192855 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 5]
def baseStart_1192855 : Nat := 118140960795 + 1192855 * 2 ^ 59
def prefixEnd_1192855 : Nat := 4983230072969 + 3 ^ 40 * 1192855 * 2
def baseEnd_1192855 : Nat := 136112881359785707339259

theorem tailTrace_1192855 : CollatzResearch.WordTrace tailWord_1192855 prefixEnd_1192855 136112881359785707339259 := by
  unfold tailWord_1192855
  simp only [CollatzResearch.WordTrace]
  refine ⟨43506996093497533259860019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29004664062331688839906679 43506996093497533259860019)
  ·
    refine ⟨65260494140246299889790029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43506996093497533259860019 65260494140246299889790029)
    ·
      refine ⟨24472685302592362458671261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65260494140246299889790029 24472685302592362458671261)
      ·
        refine ⟨9177256988472135922001723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24472685302592362458671261 9177256988472135922001723)
        ·
          refine ⟨13765885482708203883002585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177256988472135922001723 13765885482708203883002585)
          ·
            refine ⟨10324414112031152912251939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13765885482708203883002585 10324414112031152912251939)
            ·
              refine ⟨15486621168046729368377909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10324414112031152912251939 15486621168046729368377909)
              ·
                refine ⟨1451870734504380878285429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15486621168046729368377909 1451870734504380878285429)
                ·
                  refine ⟨136112881359785707339259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451870734504380878285429 136112881359785707339259)
                  ·
                    rfl

theorem cell22_1192855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 5].length) (baseStart_1192855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192855 prefixEnd_1192855 := by exact prefixLift 1192855
  have htrace : WordTrace (prefixWord ++ tailWord_1192855) baseStart_1192855 baseEnd_1192855 := by
    simpa [prefixWord, tailWord_1192855, baseEnd_1192855] using wordTrace_append hprefix tailTrace_1192855
  have hstable : (prefixWord ++ tailWord_1192855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192855).length < 2 ^ (prefixWord ++ tailWord_1192855).sum := by decide
  have hdescent : baseEnd_1192855 < baseStart_1192855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192945 : List Nat := [1, 2, 2, 2, 4, 1, 10]
def baseStart_1192945 : Nat := 118140960795 + 1192945 * 2 ^ 59
def prefixEnd_1192945 : Nat := 4983230072969 + 3 ^ 40 * 1192945 * 2
def baseEnd_1192945 : Nat := 15124794552541736565463

theorem tailTrace_1192945 : CollatzResearch.WordTrace tailWord_1192945 prefixEnd_1192945 15124794552541736565463 := by
  unfold tailWord_1192945
  simp only [CollatzResearch.WordTrace]
  refine ⟨43510278663171478630636289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29006852442114319087090859 43510278663171478630636289)
  ·
    refine ⟨32632708997378608972977217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43510278663171478630636289 32632708997378608972977217)
    ·
      refine ⟨24474531748033956729732913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32632708997378608972977217 24474531748033956729732913)
      ·
        refine ⟨18355898811025467547299685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24474531748033956729732913 18355898811025467547299685)
        ·
          refine ⟨3441731027067275165118691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18355898811025467547299685 3441731027067275165118691)
          ·
            refine ⟨5162596540600912747678037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441731027067275165118691 5162596540600912747678037)
            ·
              refine ⟨15124794552541736565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5162596540600912747678037 15124794552541736565463)
              ·
                rfl

theorem cell22_1192945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 10].length) (baseStart_1192945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192945 prefixEnd_1192945 := by exact prefixLift 1192945
  have htrace : WordTrace (prefixWord ++ tailWord_1192945) baseStart_1192945 baseEnd_1192945 := by
    simpa [prefixWord, tailWord_1192945, baseEnd_1192945] using wordTrace_append hprefix tailTrace_1192945
  have hstable : (prefixWord ++ tailWord_1192945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192945).length < 2 ^ (prefixWord ++ tailWord_1192945).sum := by decide
  have hdescent : baseEnd_1192945 < baseStart_1192945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192977 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_1192977 : Nat := 118140960795 + 1192977 * 2 ^ 59
def prefixEnd_1192977 : Nat := 4983230072969 + 3 ^ 40 * 1192977 * 2
def baseEnd_1192977 : Nat := 408380407172589470467403

theorem tailTrace_1192977 : CollatzResearch.WordTrace tailWord_1192977 prefixEnd_1192977 408380407172589470467403 := by
  unfold tailWord_1192977
  simp only [CollatzResearch.WordTrace]
  refine ⟨43511445799055548095801185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29007630532703698730534123 43511445799055548095801185)
  ·
    refine ⟨32633584349291661071850889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43511445799055548095801185 32633584349291661071850889)
    ·
      refine ⟨24475188261968745803888167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32633584349291661071850889 24475188261968745803888167)
      ·
        refine ⟨36712782392953118705832251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24475188261968745803888167 36712782392953118705832251)
        ·
          refine ⟨55069173589429678058748377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36712782392953118705832251 55069173589429678058748377)
          ·
            refine ⟨41301880192072258544061283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55069173589429678058748377 41301880192072258544061283)
            ·
              refine ⟨61952820288108387816091925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41301880192072258544061283 61952820288108387816091925)
              ·
                refine ⟨2904038451005080678879309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61952820288108387816091925 2904038451005080678879309)
                ·
                  refine ⟨1089014419126905254579741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2904038451005080678879309 1089014419126905254579741)
                  ·
                    refine ⟨408380407172589470467403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089014419126905254579741 408380407172589470467403)
                    ·
                      rfl

theorem cell22_1192977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_1192977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1192977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1192977 prefixEnd_1192977 := by exact prefixLift 1192977
  have htrace : WordTrace (prefixWord ++ tailWord_1192977) baseStart_1192977 baseEnd_1192977 := by
    simpa [prefixWord, tailWord_1192977, baseEnd_1192977] using wordTrace_append hprefix tailTrace_1192977
  have hstable : (prefixWord ++ tailWord_1192977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192977).length < 2 ^ (prefixWord ++ tailWord_1192977).sum := by decide
  have hdescent : baseEnd_1192977 < baseStart_1192977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193052 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_1193052 : Nat := 118140960795 + 1193052 * 2 ^ 59
def prefixEnd_1193052 : Nat := 4983230072969 + 3 ^ 40 * 1193052 * 2
def baseEnd_1193052 : Nat := 136135360401771424947391

theorem tailTrace_1193052 : CollatzResearch.WordTrace tailWord_1193052 prefixEnd_1193052 136135360401771424947391 := by
  unfold tailWord_1193052
  simp only [CollatzResearch.WordTrace]
  refine ⟨21757090636891917952390705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29009454182522557269854273 21757090636891917952390705)
  ·
    refine ⟨16317817977668938464293029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21757090636891917952390705 16317817977668938464293029)
    ·
      refine ⟨3059590870812925962054943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16317817977668938464293029 3059590870812925962054943)
      ·
        refine ⟨4589386306219388943082415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3059590870812925962054943 4589386306219388943082415)
        ·
          refine ⟨6884079459329083414623623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589386306219388943082415 6884079459329083414623623)
          ·
            refine ⟨10326119188993625121935435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884079459329083414623623 10326119188993625121935435)
            ·
              refine ⟨15489178783490437682903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326119188993625121935435 15489178783490437682903153)
              ·
                refine ⟨11616884087617828262177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15489178783490437682903153 11616884087617828262177365)
                ·
                  refine ⟨136135360401771424947391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11616884087617828262177365 136135360401771424947391)
                  ·
                    rfl

theorem cell22_1193052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_1193052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193052 prefixEnd_1193052 := by exact prefixLift 1193052
  have htrace : WordTrace (prefixWord ++ tailWord_1193052) baseStart_1193052 baseEnd_1193052 := by
    simpa [prefixWord, tailWord_1193052, baseEnd_1193052] using wordTrace_append hprefix tailTrace_1193052
  have hstable : (prefixWord ++ tailWord_1193052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193052).length < 2 ^ (prefixWord ++ tailWord_1193052).sum := by decide
  have hdescent : baseEnd_1193052 < baseStart_1193052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193069 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 6]
def baseStart_1193069 : Nat := 118140960795 + 1193069 * 2 ^ 59
def prefixEnd_1193069 : Nat := 4983230072969 + 3 ^ 40 * 1193069 * 2
def baseEnd_1193069 : Nat := 136137300217577299055707

theorem tailTrace_1193069 : CollatzResearch.WordTrace tailWord_1193069 prefixEnd_1193069 136137300217577299055707 := by
  unfold tailWord_1193069
  simp only [CollatzResearch.WordTrace]
  refine ⟨43514801314722247808150261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29009867543148165205433507 43514801314722247808150261)
  ·
    refine ⟨4079512623255210732014087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43514801314722247808150261 4079512623255210732014087)
    ·
      refine ⟨6119268934882816098021131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079512623255210732014087 6119268934882816098021131)
      ·
        refine ⟨9178903402324224147031697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6119268934882816098021131 9178903402324224147031697)
        ·
          refine ⟨6884177551743168110273773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9178903402324224147031697 6884177551743168110273773)
          ·
            refine ⟨2581566581903688041352665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6884177551743168110273773 2581566581903688041352665)
            ·
              refine ⟨1936174936427766031014499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581566581903688041352665 1936174936427766031014499)
              ·
                refine ⟨2904262404641649046521749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936174936427766031014499 2904262404641649046521749)
                ·
                  refine ⟨136137300217577299055707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2904262404641649046521749 136137300217577299055707)
                  ·
                    rfl

theorem cell22_1193069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_1193069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193069 prefixEnd_1193069 := by exact prefixLift 1193069
  have htrace : WordTrace (prefixWord ++ tailWord_1193069) baseStart_1193069 baseEnd_1193069 := by
    simpa [prefixWord, tailWord_1193069, baseEnd_1193069] using wordTrace_append hprefix tailTrace_1193069
  have hstable : (prefixWord ++ tailWord_1193069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193069).length < 2 ^ (prefixWord ++ tailWord_1193069).sum := by decide
  have hdescent : baseEnd_1193069 < baseStart_1193069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193097 : List Nat := [1, 2, 1, 1, 4, 4, 1, 8]
def baseStart_1193097 : Nat := 118140960795 + 1193097 * 2 ^ 59
def prefixEnd_1193097 : Nat := 4983230072969 + 3 ^ 40 * 1193097 * 2
def baseEnd_1193097 : Nat := 45380165069438795274115

theorem tailTrace_1193097 : CollatzResearch.WordTrace tailWord_1193097 prefixEnd_1193097 45380165069438795274115 := by
  unfold tailWord_1193097
  simp only [CollatzResearch.WordTrace]
  refine ⟨43515822558620808590169545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29010548372413872393446363 43515822558620808590169545)
  ·
    refine ⟨32636866918965606442627159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43515822558620808590169545 32636866918965606442627159)
    ·
      refine ⟨48955300378448409663940739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32636866918965606442627159 48955300378448409663940739)
      ·
        refine ⟨73432950567672614495911109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48955300378448409663940739 73432950567672614495911109)
        ·
          refine ⟨13768678231438615217983333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73432950567672614495911109 13768678231438615217983333)
          ·
            refine ⟨2581627168394740353371875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13768678231438615217983333 2581627168394740353371875)
            ·
              refine ⟨3872440752592110530057813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581627168394740353371875 3872440752592110530057813)
              ·
                refine ⟨45380165069438795274115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3872440752592110530057813 45380165069438795274115)
                ·
                  rfl

theorem cell22_1193097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 8].length) (baseStart_1193097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193097 prefixEnd_1193097 := by exact prefixLift 1193097
  have htrace : WordTrace (prefixWord ++ tailWord_1193097) baseStart_1193097 baseEnd_1193097 := by
    simpa [prefixWord, tailWord_1193097, baseEnd_1193097] using wordTrace_append hprefix tailTrace_1193097
  have hstable : (prefixWord ++ tailWord_1193097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193097).length < 2 ^ (prefixWord ++ tailWord_1193097).sum := by decide
  have hdescent : baseEnd_1193097 < baseStart_1193097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193114 : List Nat := [3, 1, 1, 5, 1, 3, 8]
def baseStart_1193114 : Nat := 118140960795 + 1193114 * 2 ^ 59
def prefixEnd_1193114 : Nat := 4983230072969 + 3 ^ 40 * 1193114 * 2
def baseEnd_1193114 : Nat := 15126937224902473325629

theorem tailTrace_1193114 : CollatzResearch.WordTrace tailWord_1193114 prefixEnd_1193114 15126937224902473325629 := by
  unfold tailWord_1193114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10879110649889805123384599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29010961733039480329025597 10879110649889805123384599)
  ·
    refine ⟨16318665974834707685076899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10879110649889805123384599 16318665974834707685076899)
    ·
      refine ⟨24477998962252061527615349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16318665974834707685076899 24477998962252061527615349)
      ·
        refine ⟨2294812402711130768213939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24477998962252061527615349 2294812402711130768213939)
        ·
          refine ⟨3442218604066696152320909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294812402711130768213939 3442218604066696152320909)
          ·
            refine ⟨1290831976525011057120341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3442218604066696152320909 1290831976525011057120341)
            ·
              refine ⟨15126937224902473325629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1290831976525011057120341 15126937224902473325629)
              ·
                rfl

theorem cell22_1193114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 8].length) (baseStart_1193114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193114 prefixEnd_1193114 := by exact prefixLift 1193114
  have htrace : WordTrace (prefixWord ++ tailWord_1193114) baseStart_1193114 baseEnd_1193114 := by
    simpa [prefixWord, tailWord_1193114, baseEnd_1193114] using wordTrace_append hprefix tailTrace_1193114
  have hstable : (prefixWord ++ tailWord_1193114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193114).length < 2 ^ (prefixWord ++ tailWord_1193114).sum := by decide
  have hdescent : baseEnd_1193114 < baseStart_1193114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193157 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_1193157 : Nat := 118140960795 + 1193157 * 2 ^ 59
def prefixEnd_1193157 : Nat := 4983230072969 + 3 ^ 40 * 1193157 * 2
def baseEnd_1193157 : Nat := 408442024851129000966851

theorem tailTrace_1193157 : CollatzResearch.WordTrace tailWord_1193157 prefixEnd_1193157 408442024851129000966851 := by
  unfold tailWord_1193157
  simp only [CollatzResearch.WordTrace]
  refine ⟨43518010938403438837353725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29012007292268959224902483 43518010938403438837353725)
  ·
    refine ⟨16319254101901289564007647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43518010938403438837353725 16319254101901289564007647)
    ·
      refine ⟨24478881152851934346011471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16319254101901289564007647 24478881152851934346011471)
      ·
        refine ⟨36718321729277901519017207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24478881152851934346011471 36718321729277901519017207)
        ·
          refine ⟨55077482593916852278525811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36718321729277901519017207 55077482593916852278525811)
          ·
            refine ⟨82616223890875278417788717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55077482593916852278525811 82616223890875278417788717)
            ·
              refine ⟨30981083959078229406670769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82616223890875278417788717 30981083959078229406670769)
              ·
                refine ⟨23235812969308672055003077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30981083959078229406670769 23235812969308672055003077)
                ·
                  refine ⟨4356714931745376010313077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23235812969308672055003077 4356714931745376010313077)
                  ·
                    refine ⟨408442024851129000966851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4356714931745376010313077 408442024851129000966851)
                    ·
                      rfl

theorem cell22_1193157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_1193157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193157 prefixEnd_1193157 := by exact prefixLift 1193157
  have htrace : WordTrace (prefixWord ++ tailWord_1193157) baseStart_1193157 baseEnd_1193157 := by
    simpa [prefixWord, tailWord_1193157, baseEnd_1193157] using wordTrace_append hprefix tailTrace_1193157
  have hstable : (prefixWord ++ tailWord_1193157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193157).length < 2 ^ (prefixWord ++ tailWord_1193157).sum := by decide
  have hdescent : baseEnd_1193157 < baseStart_1193157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193176 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_1193176 : Nat := 118140960795 + 1193176 * 2 ^ 59
def prefixEnd_1193176 : Nat := 4983230072969 + 3 ^ 40 * 1193176 * 2
def baseEnd_1193176 : Nat := 136149509646473094913931

theorem tailTrace_1193176 : CollatzResearch.WordTrace tailWord_1193176 prefixEnd_1193176 136149509646473094913931 := by
  unfold tailWord_1193176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21759351962667302541147691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29012469283556403388196921 21759351962667302541147691)
  ·
    refine ⟨32639027944000953811721537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21759351962667302541147691 32639027944000953811721537)
    ·
      refine ⟨24479270958000715358791153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32639027944000953811721537 24479270958000715358791153)
      ·
        refine ⟨18359453218500536519093365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24479270958000715358791153 18359453218500536519093365)
        ·
          refine ⟨1721198739234425298665003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18359453218500536519093365 1721198739234425298665003)
          ·
            refine ⟨2581798108851637947997505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721198739234425298665003 2581798108851637947997505)
            ·
              refine ⟨1936348581638728460998129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581798108851637947997505 1936348581638728460998129)
              ·
                refine ⟨1452261436229046345748597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936348581638728460998129 1452261436229046345748597)
                ·
                  refine ⟨136149509646473094913931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1452261436229046345748597 136149509646473094913931)
                  ·
                    rfl

theorem cell22_1193176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_1193176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193176 prefixEnd_1193176 := by exact prefixLift 1193176
  have htrace : WordTrace (prefixWord ++ tailWord_1193176) baseStart_1193176 baseEnd_1193176 := by
    simpa [prefixWord, tailWord_1193176, baseEnd_1193176] using wordTrace_append hprefix tailTrace_1193176
  have hstable : (prefixWord ++ tailWord_1193176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193176).length < 2 ^ (prefixWord ++ tailWord_1193176).sum := by decide
  have hdescent : baseEnd_1193176 < baseStart_1193176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193191 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1193191 : Nat := 118140960795 + 1193191 * 2 ^ 59
def prefixEnd_1193191 : Nat := 4983230072969 + 3 ^ 40 * 1193191 * 2
def baseEnd_1193191 : Nat := 408453663745964245616747

theorem tailTrace_1193191 : CollatzResearch.WordTrace tailWord_1193191 prefixEnd_1193191 408453663745964245616747 := by
  unfold tailWord_1193191
  simp only [CollatzResearch.WordTrace]
  refine ⟨43519251020280262644091427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29012834013520175096060951 43519251020280262644091427)
  ·
    refine ⟨65278876530420393966137141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43519251020280262644091427 65278876530420393966137141)
    ·
      refine ⟨6119894674726911934325357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65278876530420393966137141 6119894674726911934325357)
      ·
        refine ⟨2294960503022591975372009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6119894674726911934325357 2294960503022591975372009)
        ·
          refine ⟨1721220377266943981529007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2294960503022591975372009 1721220377266943981529007)
          ·
            refine ⟨2581830565900415972293511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721220377266943981529007 2581830565900415972293511)
            ·
              refine ⟨3872745848850623958440267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581830565900415972293511 3872745848850623958440267)
              ·
                refine ⟨5809118773275935937660401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872745848850623958440267 5809118773275935937660401)
                ·
                  refine ⟨4356839079956951953245301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5809118773275935937660401 4356839079956951953245301)
                  ·
                    refine ⟨408453663745964245616747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4356839079956951953245301 408453663745964245616747)
                    ·
                      rfl

theorem cell22_1193191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1193191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193191 prefixEnd_1193191 := by exact prefixLift 1193191
  have htrace : WordTrace (prefixWord ++ tailWord_1193191) baseStart_1193191 baseEnd_1193191 := by
    simpa [prefixWord, tailWord_1193191, baseEnd_1193191] using wordTrace_append hprefix tailTrace_1193191
  have hstable : (prefixWord ++ tailWord_1193191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193191).length < 2 ^ (prefixWord ++ tailWord_1193191).sum := by decide
  have hdescent : baseEnd_1193191 < baseStart_1193191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193206 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1193206 : Nat := 118140960795 + 1193206 * 2 ^ 59
def prefixEnd_1193206 : Nat := 4983230072969 + 3 ^ 40 * 1193206 * 2
def baseEnd_1193206 : Nat := 408458798552509206491701

theorem tailTrace_1193206 : CollatzResearch.WordTrace tailWord_1193206 prefixEnd_1193206 408458798552509206491701 := by
  unfold tailWord_1193206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719987382201620012867967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29013198743483946803924981 2719987382201620012867967)
  ·
    refine ⟨4079981073302430019301951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2719987382201620012867967 4079981073302430019301951)
    ·
      refine ⟨6119971609953645028952927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079981073302430019301951 6119971609953645028952927)
      ·
        refine ⟨9179957414930467543429391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6119971609953645028952927 9179957414930467543429391)
        ·
          refine ⟨13769936122395701315144087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9179957414930467543429391 13769936122395701315144087)
          ·
            refine ⟨20654904183593551972716131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13769936122395701315144087 20654904183593551972716131)
            ·
              refine ⟨30982356275390327959074197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20654904183593551972716131 30982356275390327959074197)
              ·
                refine ⟨1452297950408921623081603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30982356275390327959074197 1452297950408921623081603)
                ·
                  refine ⟨2178446925613382434622405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452297950408921623081603 2178446925613382434622405)
                  ·
                    refine ⟨408458798552509206491701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2178446925613382434622405 408458798552509206491701)
                    ·
                      rfl

theorem cell22_1193206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1193206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193206 prefixEnd_1193206 := by exact prefixLift 1193206
  have htrace : WordTrace (prefixWord ++ tailWord_1193206) baseStart_1193206 baseEnd_1193206 := by
    simpa [prefixWord, tailWord_1193206, baseEnd_1193206] using wordTrace_append hprefix tailTrace_1193206
  have hstable : (prefixWord ++ tailWord_1193206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193206).length < 2 ^ (prefixWord ++ tailWord_1193206).sum := by decide
  have hdescent : baseEnd_1193206 < baseStart_1193206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193219 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_1193219 : Nat := 118140960795 + 1193219 * 2 ^ 59
def prefixEnd_1193219 : Nat := 4983230072969 + 3 ^ 40 * 1193219 * 2
def baseEnd_1193219 : Nat := 408463248718181505916661

theorem tailTrace_1193219 : CollatzResearch.WordTrace tailWord_1193219 prefixEnd_1193219 408463248718181505916661 := by
  unfold tailWord_1193219
  simp only [CollatzResearch.WordTrace]
  refine ⟨43520272264178823426110711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29013514842785882284073807 43520272264178823426110711)
  ·
    refine ⟨65280408396268235139166067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43520272264178823426110711 65280408396268235139166067)
    ·
      refine ⟨97920612594402352708749101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65280408396268235139166067 97920612594402352708749101)
      ·
        refine ⟨36720229722900882265780913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97920612594402352708749101 36720229722900882265780913)
        ·
          refine ⟨27540172292175661699335685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36720229722900882265780913 27540172292175661699335685)
          ·
            refine ⟨5163782304782936568625441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27540172292175661699335685 5163782304782936568625441)
            ·
              refine ⟨3872836728587202426469081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5163782304782936568625441 3872836728587202426469081)
              ·
                refine ⟨2904627546440401819851811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3872836728587202426469081 2904627546440401819851811)
                ·
                  refine ⟨4356941319660602729777717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904627546440401819851811 4356941319660602729777717)
                  ·
                    refine ⟨408463248718181505916661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4356941319660602729777717 408463248718181505916661)
                    ·
                      rfl

theorem cell22_1193219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_1193219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193219 prefixEnd_1193219 := by exact prefixLift 1193219
  have htrace : WordTrace (prefixWord ++ tailWord_1193219) baseStart_1193219 baseEnd_1193219 := by
    simpa [prefixWord, tailWord_1193219, baseEnd_1193219] using wordTrace_append hprefix tailTrace_1193219
  have hstable : (prefixWord ++ tailWord_1193219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193219).length < 2 ^ (prefixWord ++ tailWord_1193219).sum := by decide
  have hdescent : baseEnd_1193219 < baseStart_1193219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193221 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 4]
def baseStart_1193221 : Nat := 118140960795 + 1193221 * 2 ^ 59
def prefixEnd_1193221 : Nat := 4983230072969 + 3 ^ 40 * 1193221 * 2
def baseEnd_1193221 : Nat := 136154644453018055788885

theorem tailTrace_1193221 : CollatzResearch.WordTrace tailWord_1193221 prefixEnd_1193221 136154644453018055788885 := by
  unfold tailWord_1193221
  simp only [CollatzResearch.WordTrace]
  refine ⟨43520345210171577767683517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29013563473447718511789011 43520345210171577767683517)
  ·
    refine ⟨16320129453814341662881319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43520345210171577767683517 16320129453814341662881319)
    ·
      refine ⟨24480194180721512494321979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16320129453814341662881319 24480194180721512494321979)
      ·
        refine ⟨36720291271082268741482969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24480194180721512494321979 36720291271082268741482969)
        ·
          refine ⟨27540218453311701556112227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36720291271082268741482969 27540218453311701556112227)
          ·
            refine ⟨41310327679967552334168341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27540218453311701556112227 41310327679967552334168341)
            ·
              refine ⟨1936421609998479015664141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41310327679967552334168341 1936421609998479015664141)
              ·
                refine ⟨726158103749429630874053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936421609998479015664141 726158103749429630874053)
                ·
                  refine ⟨136154644453018055788885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726158103749429630874053 136154644453018055788885)
                  ·
                    rfl

theorem cell22_1193221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_1193221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193221 prefixEnd_1193221 := by exact prefixLift 1193221
  have htrace : WordTrace (prefixWord ++ tailWord_1193221) baseStart_1193221 baseEnd_1193221 := by
    simpa [prefixWord, tailWord_1193221, baseEnd_1193221] using wordTrace_append hprefix tailTrace_1193221
  have hstable : (prefixWord ++ tailWord_1193221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193221).length < 2 ^ (prefixWord ++ tailWord_1193221).sum := by decide
  have hdescent : baseEnd_1193221 < baseStart_1193221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193266 : List Nat := [3, 2, 1, 1, 4, 1, 4, 6]
def baseStart_1193266 : Nat := 118140960795 + 1193266 * 2 ^ 59
def prefixEnd_1193266 : Nat := 4983230072969 + 3 ^ 40 * 1193266 * 2
def baseEnd_1193266 : Nat := 45386593086521005554613

theorem tailTrace_1193266 : CollatzResearch.WordTrace tailWord_1193266 prefixEnd_1193266 45386593086521005554613 := by
  unfold tailWord_1193266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880496623752137613267913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29014657663339033635381101 10880496623752137613267913)
  ·
    refine ⟨8160372467814103209950935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10880496623752137613267913 8160372467814103209950935)
    ·
      refine ⟨12240558701721154814926403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160372467814103209950935 12240558701721154814926403)
      ·
        refine ⟨18360838052581732222389605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240558701721154814926403 18360838052581732222389605)
        ·
          refine ⟨3442657134859074791698051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18360838052581732222389605 3442657134859074791698051)
          ·
            refine ⟨5163985702288612187547077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442657134859074791698051 5163985702288612187547077)
            ·
              refine ⟨968247319179114785165077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5163985702288612187547077 968247319179114785165077)
              ·
                refine ⟨45386593086521005554613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 968247319179114785165077 45386593086521005554613)
                ·
                  rfl

theorem cell22_1193266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_1193266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193266 prefixEnd_1193266 := by exact prefixLift 1193266
  have htrace : WordTrace (prefixWord ++ tailWord_1193266) baseStart_1193266 baseEnd_1193266 := by
    simpa [prefixWord, tailWord_1193266, baseEnd_1193266] using wordTrace_append hprefix tailTrace_1193266
  have hstable : (prefixWord ++ tailWord_1193266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193266).length < 2 ^ (prefixWord ++ tailWord_1193266).sum := by decide
  have hdescent : baseEnd_1193266 < baseStart_1193266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193294 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1193294 : Nat := 118140960795 + 1193294 * 2 ^ 59
def prefixEnd_1193294 : Nat := 4983230072969 + 3 ^ 40 * 1193294 * 2
def baseEnd_1193294 : Nat := 136162974250302103430477

theorem tailTrace_1193294 : CollatzResearch.WordTrace tailWord_1193294 prefixEnd_1193294 136162974250302103430477 := by
  unfold tailWord_1193294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440375967363388904386367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29015338492604740823393957 5440375967363388904386367)
  ·
    refine ⟨8160563951045083356579551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5440375967363388904386367 8160563951045083356579551)
    ·
      refine ⟨12240845926567625034869327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160563951045083356579551 12240845926567625034869327)
      ·
        refine ⟨18361268889851437552303991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240845926567625034869327 18361268889851437552303991)
        ·
          refine ⟨27541903334777156328455987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18361268889851437552303991 27541903334777156328455987)
          ·
            refine ⟨41312855002165734492683981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27541903334777156328455987 41312855002165734492683981)
            ·
              refine ⟨15492320625812150434756493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41312855002165734492683981 15492320625812150434756493)
              ·
                refine ⟨5809620234679556413033685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15492320625812150434756493 5809620234679556413033685)
                ·
                  refine ⟨136162974250302103430477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5809620234679556413033685 136162974250302103430477)
                  ·
                    rfl

theorem cell22_1193294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1193294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193294 prefixEnd_1193294 := by exact prefixLift 1193294
  have htrace : WordTrace (prefixWord ++ tailWord_1193294) baseStart_1193294 baseEnd_1193294 := by
    simpa [prefixWord, tailWord_1193294, baseEnd_1193294] using wordTrace_append hprefix tailTrace_1193294
  have hstable : (prefixWord ++ tailWord_1193294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193294).length < 2 ^ (prefixWord ++ tailWord_1193294).sum := by decide
  have hdescent : baseEnd_1193294 < baseStart_1193294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193401 : List Nat := [1, 2, 1, 4, 4, 1, 9]
def baseStart_1193401 : Nat := 118140960795 + 1193401 * 2 ^ 59
def prefixEnd_1193401 : Nat := 4983230072969 + 3 ^ 40 * 1193401 * 2
def baseEnd_1193401 : Nat := 15130575964355322143189

theorem tailTrace_1193401 : CollatzResearch.WordTrace tailWord_1193401 prefixEnd_1193401 15130575964355322143189 := by
  unfold tailWord_1193401
  simp only [CollatzResearch.WordTrace]
  refine ⟨43526910349519468509236057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29017940233012979006157371 43526910349519468509236057)
  ·
    refine ⟨32645182762139601381927043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43526910349519468509236057 32645182762139601381927043)
    ·
      refine ⟨48967774143209402072890565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32645182762139601381927043 48967774143209402072890565)
      ·
        refine ⟨9181457651851762888666981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48967774143209402072890565 9181457651851762888666981)
        ·
          refine ⟨1721523309722205541625059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9181457651851762888666981 1721523309722205541625059)
          ·
            refine ⟨2582284964583308312437589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721523309722205541625059 2582284964583308312437589)
            ·
              refine ⟨15130575964355322143189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2582284964583308312437589 15130575964355322143189)
              ·
                rfl

theorem cell22_1193401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 9].length) (baseStart_1193401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193401 prefixEnd_1193401 := by exact prefixLift 1193401
  have htrace : WordTrace (prefixWord ++ tailWord_1193401) baseStart_1193401 baseEnd_1193401 := by
    simpa [prefixWord, tailWord_1193401, baseEnd_1193401] using wordTrace_append hprefix tailTrace_1193401
  have hstable : (prefixWord ++ tailWord_1193401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193401).length < 2 ^ (prefixWord ++ tailWord_1193401).sum := by decide
  have hdescent : baseEnd_1193401 < baseStart_1193401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193433 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_1193433 : Nat := 118140960795 + 1193433 * 2 ^ 59
def prefixEnd_1193433 : Nat := 4983230072969 + 3 ^ 40 * 1193433 * 2
def baseEnd_1193433 : Nat := 408536505291556281066005

theorem tailTrace_1193433 : CollatzResearch.WordTrace tailWord_1193433 prefixEnd_1193433 408536505291556281066005 := by
  unfold tailWord_1193433
  simp only [CollatzResearch.WordTrace]
  refine ⟨43528077485403537974400953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29018718323602358649600635 43528077485403537974400953)
  ·
    refine ⟨32646058114052653480800715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43528077485403537974400953 32646058114052653480800715)
    ·
      refine ⟨48969087171078980221201073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32646058114052653480800715 48969087171078980221201073)
      ·
        refine ⟨36726815378309235165900805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48969087171078980221201073 36726815378309235165900805)
        ·
          refine ⟨6886277883432981593606401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36726815378309235165900805 6886277883432981593606401)
          ·
            refine ⟨5164708412574736195204801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6886277883432981593606401 5164708412574736195204801)
            ·
              refine ⟨3873531309431052146403601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5164708412574736195204801 3873531309431052146403601)
              ·
                refine ⟨2905148482073289109802701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873531309431052146403601 2905148482073289109802701)
                ·
                  refine ⟨1089430680777483416176013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2905148482073289109802701 1089430680777483416176013)
                  ·
                    refine ⟨408536505291556281066005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089430680777483416176013 408536505291556281066005)
                    ·
                      rfl

theorem cell22_1193433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_1193433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193433 prefixEnd_1193433 := by exact prefixLift 1193433
  have htrace : WordTrace (prefixWord ++ tailWord_1193433) baseStart_1193433 baseEnd_1193433 := by
    simpa [prefixWord, tailWord_1193433, baseEnd_1193433] using wordTrace_append hprefix tailTrace_1193433
  have hstable : (prefixWord ++ tailWord_1193433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193433).length < 2 ^ (prefixWord ++ tailWord_1193433).sum := by decide
  have hdescent : baseEnd_1193433 < baseStart_1193433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193493 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1193493 : Nat := 118140960795 + 1193493 * 2 ^ 59
def prefixEnd_1193493 : Nat := 4983230072969 + 3 ^ 40 * 1193493 * 2
def baseEnd_1193493 : Nat := 408557044517736124565821

theorem tailTrace_1193493 : CollatzResearch.WordTrace tailWord_1193493 prefixEnd_1193493 408557044517736124565821 := by
  unfold tailWord_1193493
  simp only [CollatzResearch.WordTrace]
  refine ⟨43530265865186168221585133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29020177243457445481056755 43530265865186168221585133)
  ·
    refine ⟨16323849699444813083094425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43530265865186168221585133 16323849699444813083094425)
    ·
      refine ⟨12242887274583609812320819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16323849699444813083094425 12242887274583609812320819)
      ·
        refine ⟨18364330911875414718481229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12242887274583609812320819 18364330911875414718481229)
        ·
          refine ⟨6886624091953280519430461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18364330911875414718481229 6886624091953280519430461)
          ·
            refine ⟨2582484034482480194786423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6886624091953280519430461 2582484034482480194786423)
            ·
              refine ⟨3873726051723720292179635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582484034482480194786423 3873726051723720292179635)
              ·
                refine ⟨5810589077585580438269453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873726051723720292179635 5810589077585580438269453)
                ·
                  refine ⟨2178970904094592664351045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5810589077585580438269453 2178970904094592664351045)
                  ·
                    refine ⟨408557044517736124565821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2178970904094592664351045 408557044517736124565821)
                    ·
                      rfl

theorem cell22_1193493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1193493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193493 prefixEnd_1193493 := by exact prefixLift 1193493
  have htrace : WordTrace (prefixWord ++ tailWord_1193493) baseStart_1193493 baseEnd_1193493 := by
    simpa [prefixWord, tailWord_1193493, baseEnd_1193493] using wordTrace_append hprefix tailTrace_1193493
  have hstable : (prefixWord ++ tailWord_1193493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193493).length < 2 ^ (prefixWord ++ tailWord_1193493).sum := by decide
  have hdescent : baseEnd_1193493 < baseStart_1193493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193521 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1193521 : Nat := 118140960795 + 1193521 * 2 ^ 59
def prefixEnd_1193521 : Nat := 4983230072969 + 3 ^ 40 * 1193521 * 2
def baseEnd_1193521 : Nat := 408566629489953384865735

theorem tailTrace_1193521 : CollatzResearch.WordTrace tailWord_1193521 prefixEnd_1193521 408566629489953384865735 := by
  unfold tailWord_1193521
  simp only [CollatzResearch.WordTrace]
  refine ⟨43531287109084729003604417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29020858072723152669069611 43531287109084729003604417)
  ·
    refine ⟨32648465331813546752703313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43531287109084729003604417 32648465331813546752703313)
    ·
      refine ⟨24486348998860160064527485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32648465331813546752703313 24486348998860160064527485)
      ·
        refine ⟨9182380874572560024197807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24486348998860160064527485 9182380874572560024197807)
        ·
          refine ⟨13773571311858840036296711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9182380874572560024197807 13773571311858840036296711)
          ·
            refine ⟨20660356967788260054445067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13773571311858840036296711 20660356967788260054445067)
            ·
              refine ⟨30990535451682390081667601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20660356967788260054445067 30990535451682390081667601)
              ·
                refine ⟨23242901588761792561250701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30990535451682390081667601 23242901588761792561250701)
                ·
                  refine ⟨8716088095785672210469013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23242901588761792561250701 8716088095785672210469013)
                  ·
                    refine ⟨408566629489953384865735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8716088095785672210469013 408566629489953384865735)
                    ·
                      rfl

theorem cell22_1193521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1193521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193521 prefixEnd_1193521 := by exact prefixLift 1193521
  have htrace : WordTrace (prefixWord ++ tailWord_1193521) baseStart_1193521 baseEnd_1193521 := by
    simpa [prefixWord, tailWord_1193521, baseEnd_1193521] using wordTrace_append hprefix tailTrace_1193521
  have hstable : (prefixWord ++ tailWord_1193521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193521).length < 2 ^ (prefixWord ++ tailWord_1193521).sum := by decide
  have hdescent : baseEnd_1193521 < baseStart_1193521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193525 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 4]
def baseStart_1193525 : Nat := 118140960795 + 1193525 * 2 ^ 59
def prefixEnd_1193525 : Nat := 4983230072969 + 3 ^ 40 * 1193525 * 2
def baseEnd_1193525 : Nat := 136189332923899569255241

theorem tailTrace_1193525 : CollatzResearch.WordTrace tailWord_1193525 prefixEnd_1193525 136189332923899569255241 := by
  unfold tailWord_1193525
  simp only [CollatzResearch.WordTrace]
  refine ⟨43531433001070237686750029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29020955334046825124500019 43531433001070237686750029)
  ·
    refine ⟨16324287375401339132531261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43531433001070237686750029 16324287375401339132531261)
    ·
      refine ⟨6121607765775502174699223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16324287375401339132531261 6121607765775502174699223)
      ·
        refine ⟨9182411648663253262048835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121607765775502174699223 9182411648663253262048835)
        ·
          refine ⟨13773617472994879893073253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9182411648663253262048835 13773617472994879893073253)
          ·
            refine ⟨2582553276186539979951235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13773617472994879893073253 2582553276186539979951235)
            ·
              refine ⟨3873829914279809969926853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582553276186539979951235 3873829914279809969926853)
              ·
                refine ⟨726343108927464369361285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3873829914279809969926853 726343108927464369361285)
                ·
                  refine ⟨136189332923899569255241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726343108927464369361285 136189332923899569255241)
                  ·
                    rfl

theorem cell22_1193525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_1193525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193525 prefixEnd_1193525 := by exact prefixLift 1193525
  have htrace : WordTrace (prefixWord ++ tailWord_1193525) baseStart_1193525 baseEnd_1193525 := by
    simpa [prefixWord, tailWord_1193525, baseEnd_1193525] using wordTrace_append hprefix tailTrace_1193525
  have hstable : (prefixWord ++ tailWord_1193525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193525).length < 2 ^ (prefixWord ++ tailWord_1193525).sum := by decide
  have hdescent : baseEnd_1193525 < baseStart_1193525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193542 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1193542 : Nat := 118140960795 + 1193542 * 2 ^ 59
def prefixEnd_1193542 : Nat := 4983230072969 + 3 ^ 40 * 1193542 * 2
def baseEnd_1193542 : Nat := 136191272739705443363557

theorem tailTrace_1193542 : CollatzResearch.WordTrace tailWord_1193542 prefixEnd_1193542 136191272739705443363557 := by
  unfold tailWord_1193542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360376657562770299691215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29021368694672433060079253 1360376657562770299691215)
  ·
    refine ⟨2040564986344155449536823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360376657562770299691215 2040564986344155449536823)
    ·
      refine ⟨3060847479516233174305235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040564986344155449536823 3060847479516233174305235)
      ·
        refine ⟨4591271219274349761457853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060847479516233174305235 4591271219274349761457853)
        ·
          refine ⟨1721726707227881160546695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4591271219274349761457853 1721726707227881160546695)
          ·
            refine ⟨2582590060841821740820043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721726707227881160546695 2582590060841821740820043)
            ·
              refine ⟨3873885091262732611230065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582590060841821740820043 3873885091262732611230065)
              ·
                refine ⟨2905413818447049458422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873885091262732611230065 2905413818447049458422549)
                ·
                  refine ⟨136191272739705443363557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2905413818447049458422549 136191272739705443363557)
                  ·
                    rfl

theorem cell22_1193542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1193542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193542 prefixEnd_1193542 := by exact prefixLift 1193542
  have htrace : WordTrace (prefixWord ++ tailWord_1193542) baseStart_1193542 baseEnd_1193542 := by
    simpa [prefixWord, tailWord_1193542, baseEnd_1193542] using wordTrace_append hprefix tailTrace_1193542
  have hstable : (prefixWord ++ tailWord_1193542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193542).length < 2 ^ (prefixWord ++ tailWord_1193542).sum := by decide
  have hdescent : baseEnd_1193542 < baseStart_1193542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193553 : List Nat := [1, 2, 2, 1, 3, 2, 5, 6]
def baseStart_1193553 : Nat := 118140960795 + 1193553 * 2 ^ 59
def prefixEnd_1193553 : Nat := 4983230072969 + 3 ^ 40 * 1193553 * 2
def baseEnd_1193553 : Nat := 45397509304879552007293

theorem tailTrace_1193553 : CollatzResearch.WordTrace tailWord_1193553 prefixEnd_1193553 45397509304879552007293 := by
  unfold tailWord_1193553
  simp only [CollatzResearch.WordTrace]
  refine ⟨43532454244968798468769313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29021636163312532312512875 43532454244968798468769313)
  ·
    refine ⟨32649340683726598851576985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43532454244968798468769313 32649340683726598851576985)
    ·
      refine ⟨24487005512794949138682739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32649340683726598851576985 24487005512794949138682739)
      ·
        refine ⟨36730508269192423708024109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24487005512794949138682739 36730508269192423708024109)
        ·
          refine ⟨13773940600947158890509041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36730508269192423708024109 13773940600947158890509041)
          ·
            refine ⟨10330455450710369167881781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13773940600947158890509041 10330455450710369167881781)
            ·
              refine ⟨968480198504097109488917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10330455450710369167881781 968480198504097109488917)
              ·
                refine ⟨45397509304879552007293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 968480198504097109488917 45397509304879552007293)
                ·
                  rfl

theorem cell22_1193553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 6].length) (baseStart_1193553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193553 prefixEnd_1193553 := by exact prefixLift 1193553
  have htrace : WordTrace (prefixWord ++ tailWord_1193553) baseStart_1193553 baseEnd_1193553 := by
    simpa [prefixWord, tailWord_1193553, baseEnd_1193553] using wordTrace_append hprefix tailTrace_1193553
  have hstable : (prefixWord ++ tailWord_1193553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193553).length < 2 ^ (prefixWord ++ tailWord_1193553).sum := by decide
  have hdescent : baseEnd_1193553 < baseStart_1193553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193568 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_1193568 : Nat := 118140960795 + 1193568 * 2 ^ 59
def prefixEnd_1193568 : Nat := 4983230072969 + 3 ^ 40 * 1193568 * 2
def baseEnd_1193568 : Nat := 408582718550460928940591

theorem tailTrace_1193568 : CollatzResearch.WordTrace tailWord_1193568 prefixEnd_1193568 408582718550460928940591 := by
  unfold tailWord_1193568
  simp only [CollatzResearch.WordTrace]
  refine ⟨21766500669957228015282679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29022000893276304020376905 21766500669957228015282679)
  ·
    refine ⟨32649751004935842022924019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21766500669957228015282679 32649751004935842022924019)
    ·
      refine ⟨48974626507403763034386029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32649751004935842022924019 48974626507403763034386029)
      ·
        refine ⟨18365484940276411137894761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48974626507403763034386029 18365484940276411137894761)
        ·
          refine ⟨13774113705207308353421071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18365484940276411137894761 13774113705207308353421071)
          ·
            refine ⟨20661170557810962530131607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13774113705207308353421071 20661170557810962530131607)
            ·
              refine ⟨30991755836716443795197411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20661170557810962530131607 30991755836716443795197411)
              ·
                refine ⟨46487633755074665692796117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30991755836716443795197411 46487633755074665692796117)
                ·
                  refine ⟨1089553916134562477174909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46487633755074665692796117 1089553916134562477174909)
                  ·
                    refine ⟨408582718550460928940591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089553916134562477174909 408582718550460928940591)
                    ·
                      rfl

theorem cell22_1193568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_1193568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193568 prefixEnd_1193568 := by exact prefixLift 1193568
  have htrace : WordTrace (prefixWord ++ tailWord_1193568) baseStart_1193568 baseEnd_1193568 := by
    simpa [prefixWord, tailWord_1193568, baseEnd_1193568] using wordTrace_append hprefix tailTrace_1193568
  have hstable : (prefixWord ++ tailWord_1193568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193568).length < 2 ^ (prefixWord ++ tailWord_1193568).sum := by decide
  have hdescent : baseEnd_1193568 < baseStart_1193568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193645 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1193645 : Nat := 118140960795 + 1193645 * 2 ^ 59
def prefixEnd_1193645 : Nat := 4983230072969 + 3 ^ 40 * 1193645 * 2
def baseEnd_1193645 : Nat := 408609077224058394765355

theorem tailTrace_1193645 : CollatzResearch.WordTrace tailWord_1193645 prefixEnd_1193645 408609077224058394765355 := by
  unfold tailWord_1193645
  simp only [CollatzResearch.WordTrace]
  refine ⟨43535809760635498181118389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29023873173756998787412259 43535809760635498181118389)
  ·
    refine ⟨4081482165059577954479849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43535809760635498181118389 4081482165059577954479849)
    ·
      refine ⟨3061111623794683465859887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4081482165059577954479849 3061111623794683465859887)
      ·
        refine ⟨4591667435692025198789831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061111623794683465859887 4591667435692025198789831)
        ·
          refine ⟨6887501153538037798184747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591667435692025198789831 6887501153538037798184747)
          ·
            refine ⟨10331251730307056697277121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887501153538037798184747 10331251730307056697277121)
            ·
              refine ⟨7748438797730292522957841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10331251730307056697277121 7748438797730292522957841)
              ·
                refine ⟨5811329098297719392218381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7748438797730292522957841 5811329098297719392218381)
                ·
                  refine ⟨2179248411861644772081893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5811329098297719392218381 2179248411861644772081893)
                  ·
                    refine ⟨408609077224058394765355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179248411861644772081893 408609077224058394765355)
                    ·
                      rfl

theorem cell22_1193645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1193645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193645 prefixEnd_1193645 := by exact prefixLift 1193645
  have htrace : WordTrace (prefixWord ++ tailWord_1193645) baseStart_1193645 baseEnd_1193645 := by
    simpa [prefixWord, tailWord_1193645, baseEnd_1193645] using wordTrace_append hprefix tailTrace_1193645
  have hstable : (prefixWord ++ tailWord_1193645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193645).length < 2 ^ (prefixWord ++ tailWord_1193645).sum := by decide
  have hdescent : baseEnd_1193645 < baseStart_1193645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193662 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1193662 : Nat := 118140960795 + 1193662 * 2 ^ 59
def prefixEnd_1193662 : Nat := 4983230072969 + 3 ^ 40 * 1193662 * 2
def baseEnd_1193662 : Nat := 408614896671476017090303

theorem tailTrace_1193662 : CollatzResearch.WordTrace tailWord_1193662 prefixEnd_1193662 408614896671476017090303 := by
  unfold tailWord_1193662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442053725196738760560905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29024286534382606722991493 5442053725196738760560905)
  ·
    refine ⟨4081540293897554070420679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5442053725196738760560905 4081540293897554070420679)
    ·
      refine ⟨6122310440846331105631019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081540293897554070420679 6122310440846331105631019)
      ·
        refine ⟨9183465661269496658446529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122310440846331105631019 9183465661269496658446529)
        ·
          refine ⟨6887599245952122493834897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9183465661269496658446529 6887599245952122493834897)
          ·
            refine ⟨5165699434464091870376173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6887599245952122493834897 5165699434464091870376173)
            ·
              refine ⟨1937137287924034451391065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5165699434464091870376173 1937137287924034451391065)
              ·
                refine ⟨1452852965943025838543299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937137287924034451391065 1452852965943025838543299)
                ·
                  refine ⟨2179279448914538757814949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452852965943025838543299 2179279448914538757814949)
                  ·
                    refine ⟨408614896671476017090303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179279448914538757814949 408614896671476017090303)
                    ·
                      rfl

theorem cell22_1193662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1193662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193662 prefixEnd_1193662 := by exact prefixLift 1193662
  have htrace : WordTrace (prefixWord ++ tailWord_1193662) baseStart_1193662 baseEnd_1193662 := by
    simpa [prefixWord, tailWord_1193662, baseEnd_1193662] using wordTrace_append hprefix tailTrace_1193662
  have hstable : (prefixWord ++ tailWord_1193662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193662).length < 2 ^ (prefixWord ++ tailWord_1193662).sum := by decide
  have hdescent : baseEnd_1193662 < baseStart_1193662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193690 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_1193690 : Nat := 118140960795 + 1193690 * 2 ^ 59
def prefixEnd_1193690 : Nat := 4983230072969 + 3 ^ 40 * 1193690 * 2
def baseEnd_1193690 : Nat := 408624481643693277390217

theorem tailTrace_1193690 : CollatzResearch.WordTrace tailWord_1193690 prefixEnd_1193690 408624481643693277390217 := by
  unfold tailWord_1193690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884362761368117716626631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29024967363648313911004349 10884362761368117716626631)
  ·
    refine ⟨16326544142052176574939947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10884362761368117716626631 16326544142052176574939947)
    ·
      refine ⟨24489816213078264862409921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16326544142052176574939947 24489816213078264862409921)
      ·
        refine ⟨18367362159808698646807441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24489816213078264862409921 18367362159808698646807441)
        ·
          refine ⟨13775521619856523985105581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18367362159808698646807441 13775521619856523985105581)
          ·
            refine ⟨5165820607446196494414593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13775521619856523985105581 5165820607446196494414593)
            ·
              refine ⟨3874365455584647370810945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165820607446196494414593 3874365455584647370810945)
              ·
                refine ⟨2905774091688485528108209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874365455584647370810945 2905774091688485528108209)
                ·
                  refine ⟨2179330568766364146081157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2905774091688485528108209 2179330568766364146081157)
                  ·
                    refine ⟨408624481643693277390217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179330568766364146081157 408624481643693277390217)
                    ·
                      rfl

theorem cell22_1193690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_1193690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193690 prefixEnd_1193690 := by exact prefixLift 1193690
  have htrace : WordTrace (prefixWord ++ tailWord_1193690) baseStart_1193690 baseEnd_1193690 := by
    simpa [prefixWord, tailWord_1193690, baseEnd_1193690] using wordTrace_append hprefix tailTrace_1193690
  have hstable : (prefixWord ++ tailWord_1193690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193690).length < 2 ^ (prefixWord ++ tailWord_1193690).sum := by decide
  have hdescent : baseEnd_1193690 < baseStart_1193690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193754 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_1193754 : Nat := 118140960795 + 1193754 * 2 ^ 59
def prefixEnd_1193754 : Nat := 4983230072969 + 3 ^ 40 * 1193754 * 2
def baseEnd_1193754 : Nat := 408646390151618443790021

theorem tailTrace_1193754 : CollatzResearch.WordTrace tailWord_1193754 prefixEnd_1193754 408646390151618443790021 := by
  unfold tailWord_1193754
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884946329310152449209079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29026523544827073197890877 10884946329310152449209079)
  ·
    refine ⟨16327419493965228673813619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10884946329310152449209079 16327419493965228673813619)
    ·
      refine ⟨24491129240947843010720429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16327419493965228673813619 24491129240947843010720429)
      ·
        refine ⟨9184173465355441129020161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24491129240947843010720429 9184173465355441129020161)
        ·
          refine ⟨6888130099016580846765121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9184173465355441129020161 6888130099016580846765121)
          ·
            refine ⟨5166097574262435635073841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6888130099016580846765121 5166097574262435635073841)
            ·
              refine ⟨3874573180696826726305381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166097574262435635073841 3874573180696826726305381)
              ·
                refine ⟨726482471380655011182259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3874573180696826726305381 726482471380655011182259)
                ·
                  refine ⟨1089723707070982516773389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726482471380655011182259 1089723707070982516773389)
                  ·
                    refine ⟨408646390151618443790021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089723707070982516773389 408646390151618443790021)
                    ·
                      rfl

theorem cell22_1193754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_1193754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193754 prefixEnd_1193754 := by exact prefixLift 1193754
  have htrace : WordTrace (prefixWord ++ tailWord_1193754) baseStart_1193754 baseEnd_1193754 := by
    simpa [prefixWord, tailWord_1193754, baseEnd_1193754] using wordTrace_append hprefix tailTrace_1193754
  have hstable : (prefixWord ++ tailWord_1193754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193754).length < 2 ^ (prefixWord ++ tailWord_1193754).sum := by decide
  have hdescent : baseEnd_1193754 < baseStart_1193754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193765 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_1193765 : Nat := 118140960795 + 1193765 * 2 ^ 59
def prefixEnd_1193765 : Nat := 4983230072969 + 3 ^ 40 * 1193765 * 2
def baseEnd_1193765 : Nat := 408650155676418081764987

theorem tailTrace_1193765 : CollatzResearch.WordTrace tailWord_1193765 prefixEnd_1193765 408650155676418081764987 := by
  unfold tailWord_1193765
  simp only [CollatzResearch.WordTrace]
  refine ⟨43540186520200758675486749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29026791013467172450324499 43540186520200758675486749)
  ·
    refine ⟨16327569945075284503307531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43540186520200758675486749 16327569945075284503307531)
    ·
      refine ⟨24491354917612926754961297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16327569945075284503307531 24491354917612926754961297)
      ·
        refine ⟨18368516188209695066220973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24491354917612926754961297 18368516188209695066220973)
        ·
          refine ⟨6888193570578635649832865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18368516188209695066220973 6888193570578635649832865)
          ·
            refine ⟨5166145177933976737374649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6888193570578635649832865 5166145177933976737374649)
            ·
              refine ⟨3874608883450482553030987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166145177933976737374649 3874608883450482553030987)
              ·
                refine ⟨5811913325175723829546481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874608883450482553030987 5811913325175723829546481)
                ·
                  refine ⟨4358934993881792872159861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811913325175723829546481 4358934993881792872159861)
                  ·
                    refine ⟨408650155676418081764987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4358934993881792872159861 408650155676418081764987)
                    ·
                      rfl

theorem cell22_1193765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_1193765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193765 prefixEnd_1193765 := by exact prefixLift 1193765
  have htrace : WordTrace (prefixWord ++ tailWord_1193765) baseStart_1193765 baseEnd_1193765 := by
    simpa [prefixWord, tailWord_1193765, baseEnd_1193765] using wordTrace_append hprefix tailTrace_1193765
  have hstable : (prefixWord ++ tailWord_1193765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193765).length < 2 ^ (prefixWord ++ tailWord_1193765).sum := by decide
  have hdescent : baseEnd_1193765 < baseStart_1193765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193812 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1193812 : Nat := 118140960795 + 1193812 * 2 ^ 59
def prefixEnd_1193812 : Nat := 4983230072969 + 3 ^ 40 * 1193812 * 2
def baseEnd_1193812 : Nat := 136222081578975208613281

theorem tailTrace_1193812 : CollatzResearch.WordTrace tailWord_1193812 prefixEnd_1193812 136222081578975208613281 := by
  unfold tailWord_1193812
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770950375515242851223845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29027933834020323801631793 21770950375515242851223845)
  ·
    refine ⟨4082053195409108034604471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21770950375515242851223845 4082053195409108034604471)
    ·
      refine ⟨6123079793113662051906707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4082053195409108034604471 6123079793113662051906707)
      ·
        refine ⟨9184619689670493077860061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6123079793113662051906707 9184619689670493077860061)
        ·
          refine ⟨3444232383626434904197523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9184619689670493077860061 3444232383626434904197523)
          ·
            refine ⟨5166348575439652356296285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444232383626434904197523 5166348575439652356296285)
            ·
              refine ⟨1937380715789869633611107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5166348575439652356296285 1937380715789869633611107)
              ·
                refine ⟨2906071073684804450416661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937380715789869633611107 2906071073684804450416661)
                ·
                  refine ⟨136222081578975208613281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2906071073684804450416661 136222081578975208613281)
                  ·
                    rfl

theorem cell22_1193812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1193812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193812 prefixEnd_1193812 := by exact prefixLift 1193812
  have htrace : WordTrace (prefixWord ++ tailWord_1193812) baseStart_1193812 baseEnd_1193812 := by
    simpa [prefixWord, tailWord_1193812, baseEnd_1193812] using wordTrace_append hprefix tailTrace_1193812
  have hstable : (prefixWord ++ tailWord_1193812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193812).length < 2 ^ (prefixWord ++ tailWord_1193812).sum := by decide
  have hdescent : baseEnd_1193812 < baseStart_1193812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193825 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1193825 : Nat := 118140960795 + 1193825 * 2 ^ 59
def prefixEnd_1193825 : Nat := 4983230072969 + 3 ^ 40 * 1193825 * 2
def baseEnd_1193825 : Nat := 408670694902597925264803

theorem tailTrace_1193825 : CollatzResearch.WordTrace tailWord_1193825 prefixEnd_1193825 408670694902597925264803 := by
  unfold tailWord_1193825
  simp only [CollatzResearch.WordTrace]
  refine ⟨43542374899983388922670929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29028249933322259281780619 43542374899983388922670929)
  ·
    refine ⟨32656781174987541692003197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43542374899983388922670929 32656781174987541692003197)
    ·
      refine ⟨12246292940620328134501199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32656781174987541692003197 12246292940620328134501199)
      ·
        refine ⟨18369439410930492201751799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12246292940620328134501199 18369439410930492201751799)
        ·
          refine ⟨27554159116395738302627699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18369439410930492201751799 27554159116395738302627699)
          ·
            refine ⟨41331238674593607453941549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27554159116395738302627699 41331238674593607453941549)
            ·
              refine ⟨15499214502972602795228081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41331238674593607453941549 15499214502972602795228081)
              ·
                refine ⟨11624410877229452096421061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15499214502972602795228081 11624410877229452096421061)
                ·
                  refine ⟨2179577039480522268078949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11624410877229452096421061 2179577039480522268078949)
                  ·
                    refine ⟨408670694902597925264803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179577039480522268078949 408670694902597925264803)
                    ·
                      rfl

theorem cell22_1193825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1193825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193825 prefixEnd_1193825 := by exact prefixLift 1193825
  have htrace : WordTrace (prefixWord ++ tailWord_1193825) baseStart_1193825 baseEnd_1193825 := by
    simpa [prefixWord, tailWord_1193825, baseEnd_1193825] using wordTrace_append hprefix tailTrace_1193825
  have hstable : (prefixWord ++ tailWord_1193825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193825).length < 2 ^ (prefixWord ++ tailWord_1193825).sum := by decide
  have hdescent : baseEnd_1193825 < baseStart_1193825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193857 : List Nat := [1, 2, 4, 4, 1, 10]
def baseStart_1193857 : Nat := 118140960795 + 1193857 * 2 ^ 59
def prefixEnd_1193857 : Nat := 4983230072969 + 3 ^ 40 * 1193857 * 2
def baseEnd_1193857 : Nat := 5045452458722969240305

theorem tailTrace_1193857 : CollatzResearch.WordTrace tailWord_1193857 prefixEnd_1193857 5045452458722969240305 := by
  unfold tailWord_1193857
  simp only [CollatzResearch.WordTrace]
  refine ⟨43543542035867458387835825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29029028023911638925223883 43543542035867458387835825)
  ·
    refine ⟨32657656526900593790876869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43543542035867458387835825 32657656526900593790876869)
    ·
      refine ⟨6123310598793861335789413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32657656526900593790876869 6123310598793861335789413)
      ·
        refine ⟨1148120737273849000460515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6123310598793861335789413 1148120737273849000460515)
        ·
          refine ⟨1722181105910773500690773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148120737273849000460515 1722181105910773500690773)
          ·
            refine ⟨5045452458722969240305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1722181105910773500690773 5045452458722969240305)
            ·
              rfl

theorem cell22_1193857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 10].length) (baseStart_1193857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193857 prefixEnd_1193857 := by exact prefixLift 1193857
  have htrace : WordTrace (prefixWord ++ tailWord_1193857) baseStart_1193857 baseEnd_1193857 := by
    simpa [prefixWord, tailWord_1193857, baseEnd_1193857] using wordTrace_append hprefix tailTrace_1193857
  have hstable : (prefixWord ++ tailWord_1193857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193857).length < 2 ^ (prefixWord ++ tailWord_1193857).sum := by decide
  have hdescent : baseEnd_1193857 < baseStart_1193857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193863 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 4]
def baseStart_1193863 : Nat := 118140960795 + 1193863 * 2 ^ 59
def prefixEnd_1193863 : Nat := 4983230072969 + 3 ^ 40 * 1193863 * 2
def baseEnd_1193863 : Nat := 136227901026392830938229

theorem tailTrace_1193863 : CollatzResearch.WordTrace tailWord_1193863 prefixEnd_1193863 136227901026392830938229 := by
  unfold tailWord_1193863
  simp only [CollatzResearch.WordTrace]
  refine ⟨43543760873845721412554243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29029173915897147608369495 43543760873845721412554243)
  ·
    refine ⟨65315641310768582118831365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43543760873845721412554243 65315641310768582118831365)
    ·
      refine ⟨12246682745769109147280881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65315641310768582118831365 12246682745769109147280881)
      ·
        refine ⟨9185012059326831860460661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12246682745769109147280881 9185012059326831860460661)
        ·
          refine ⟨861094880561890486918187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9185012059326831860460661 861094880561890486918187)
          ·
            refine ⟨1291642320842835730377281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861094880561890486918187 1291642320842835730377281)
            ·
              refine ⟨968731740632126797782961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291642320842835730377281 968731740632126797782961)
              ·
                refine ⟨726548805474095098337221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968731740632126797782961 726548805474095098337221)
                ·
                  refine ⟨136227901026392830938229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726548805474095098337221 136227901026392830938229)
                  ·
                    rfl

theorem cell22_1193863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 4].length) (baseStart_1193863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193863 prefixEnd_1193863 := by exact prefixLift 1193863
  have htrace : WordTrace (prefixWord ++ tailWord_1193863) baseStart_1193863 baseEnd_1193863 := by
    simpa [prefixWord, tailWord_1193863, baseEnd_1193863] using wordTrace_append hprefix tailTrace_1193863
  have hstable : (prefixWord ++ tailWord_1193863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193863).length < 2 ^ (prefixWord ++ tailWord_1193863).sum := by decide
  have hdescent : baseEnd_1193863 < baseStart_1193863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193874 : List Nat := [3, 2, 3, 2, 1, 3, 1, 7]
def baseStart_1193874 : Nat := 118140960795 + 1193874 * 2 ^ 59
def prefixEnd_1193874 : Nat := 4983230072969 + 3 ^ 40 * 1193874 * 2
def baseEnd_1193874 : Nat := 45409718733775347865517

theorem tailTrace_1193874 : CollatzResearch.WordTrace tailWord_1193874 prefixEnd_1193874 45409718733775347865517 := by
  unfold tailWord_1193874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10886040519201467572801169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29029441384537246860803117 10886040519201467572801169)
  ·
    refine ⟨8164530389401100679600877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10886040519201467572801169 8164530389401100679600877)
    ·
      refine ⟨3061698896025412754850329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8164530389401100679600877 3061698896025412754850329)
      ·
        refine ⟨2296274172019059566137747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061698896025412754850329 2296274172019059566137747)
        ·
          refine ⟨3444411258028589349206621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296274172019059566137747 3444411258028589349206621)
          ·
            refine ⟨1291654221760721005952483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3444411258028589349206621 1291654221760721005952483)
            ·
              refine ⟨1937481332641081508928725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291654221760721005952483 1937481332641081508928725)
              ·
                refine ⟨45409718733775347865517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1937481332641081508928725 45409718733775347865517)
                ·
                  rfl

theorem cell22_1193874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_1193874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193874 prefixEnd_1193874 := by exact prefixLift 1193874
  have htrace : WordTrace (prefixWord ++ tailWord_1193874) baseStart_1193874 baseEnd_1193874 := by
    simpa [prefixWord, tailWord_1193874, baseEnd_1193874] using wordTrace_append hprefix tailTrace_1193874
  have hstable : (prefixWord ++ tailWord_1193874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193874).length < 2 ^ (prefixWord ++ tailWord_1193874).sum := by decide
  have hdescent : baseEnd_1193874 < baseStart_1193874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193878 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1193878 : Nat := 118140960795 + 1193878 * 2 ^ 59
def prefixEnd_1193878 : Nat := 4983230072969 + 3 ^ 40 * 1193878 * 2
def baseEnd_1193878 : Nat := 408688837885723453689641

theorem tailTrace_1193878 : CollatzResearch.WordTrace tailWord_1193878 prefixEnd_1193878 408688837885723453689641 := by
  unfold tailWord_1193878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721519248049461185896893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29029538645860919316233525 2721519248049461185896893)
  ·
    refine ⟨1020569718018547944711335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2721519248049461185896893 1020569718018547944711335)
    ·
      refine ⟨1530854577027821917067003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020569718018547944711335 1530854577027821917067003)
      ·
        refine ⟨2296281865541732875600505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530854577027821917067003 2296281865541732875600505)
        ·
          refine ⟨1722211399156299656700379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296281865541732875600505 1722211399156299656700379)
          ·
            refine ⟨2583317098734449485050569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722211399156299656700379 2583317098734449485050569)
            ·
              refine ⟨1937487824050837113787927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583317098734449485050569 1937487824050837113787927)
              ·
                refine ⟨2906231736076255670681891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937487824050837113787927 2906231736076255670681891)
                ·
                  refine ⟨4359347604114383506022837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906231736076255670681891 4359347604114383506022837)
                  ·
                    refine ⟨408688837885723453689641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4359347604114383506022837 408688837885723453689641)
                    ·
                      rfl

theorem cell22_1193878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1193878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193878 prefixEnd_1193878 := by exact prefixLift 1193878
  have htrace : WordTrace (prefixWord ++ tailWord_1193878) baseStart_1193878 baseEnd_1193878 := by
    simpa [prefixWord, tailWord_1193878, baseEnd_1193878] using wordTrace_append hprefix tailTrace_1193878
  have hstable : (prefixWord ++ tailWord_1193878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193878).length < 2 ^ (prefixWord ++ tailWord_1193878).sum := by decide
  have hdescent : baseEnd_1193878 < baseStart_1193878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193900 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1193900 : Nat := 118140960795 + 1193900 * 2 ^ 59
def prefixEnd_1193900 : Nat := 4983230072969 + 3 ^ 40 * 1193900 * 2
def baseEnd_1193900 : Nat := 408696368935322729639573

theorem tailTrace_1193900 : CollatzResearch.WordTrace tailWord_1193900 prefixEnd_1193900 408696368935322729639573 := by
  unfold tailWord_1193900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21772555187355838365825577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29030073583141117821100769 21772555187355838365825577)
  ·
    refine ⟨16329416390516878774369183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21772555187355838365825577 16329416390516878774369183)
    ·
      refine ⟨24494124585775318161553775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16329416390516878774369183 24494124585775318161553775)
      ·
        refine ⟨36741186878662977242330663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24494124585775318161553775 36741186878662977242330663)
        ·
          refine ⟨55111780317994465863495995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36741186878662977242330663 55111780317994465863495995)
          ·
            refine ⟨82667670476991698795243993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55111780317994465863495995 82667670476991698795243993)
            ·
              refine ⟨62000752857743774096432995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82667670476991698795243993 62000752857743774096432995)
              ·
                refine ⟨93001129286615661144649493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62000752857743774096432995 93001129286615661144649493)
                ·
                  refine ⟨4359427935310109116155445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93001129286615661144649493 4359427935310109116155445)
                  ·
                    refine ⟨408696368935322729639573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4359427935310109116155445 408696368935322729639573)
                    ·
                      rfl

theorem cell22_1193900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1193900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193900 prefixEnd_1193900 := by exact prefixLift 1193900
  have htrace : WordTrace (prefixWord ++ tailWord_1193900) baseStart_1193900 baseEnd_1193900 := by
    simpa [prefixWord, tailWord_1193900, baseEnd_1193900] using wordTrace_append hprefix tailTrace_1193900
  have hstable : (prefixWord ++ tailWord_1193900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193900).length < 2 ^ (prefixWord ++ tailWord_1193900).sum := by decide
  have hdescent : baseEnd_1193900 < baseStart_1193900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193917 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1193917 : Nat := 118140960795 + 1193917 * 2 ^ 59
def prefixEnd_1193917 : Nat := 4983230072969 + 3 ^ 40 * 1193917 * 2
def baseEnd_1193917 : Nat := 408702188382740351964521

theorem tailTrace_1193917 : CollatzResearch.WordTrace tailWord_1193917 prefixEnd_1193917 408702188382740351964521 := by
  unfold tailWord_1193917
  simp only [CollatzResearch.WordTrace]
  refine ⟨43545730415650088635020005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29030486943766725756680003 43545730415650088635020005)
  ·
    refine ⟨8164824452934391619066251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43545730415650088635020005 8164824452934391619066251)
    ·
      refine ⟨12247236679401587428599377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8164824452934391619066251 12247236679401587428599377)
      ·
        refine ⟨9185427509551190571449533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12247236679401587428599377 9185427509551190571449533)
        ·
          refine ⟨3444535316081696464293575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9185427509551190571449533 3444535316081696464293575)
          ·
            refine ⟨5166802974122544696440363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444535316081696464293575 5166802974122544696440363)
            ·
              refine ⟨7750204461183817044660545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166802974122544696440363 7750204461183817044660545)
              ·
                refine ⟨5812653345887862783495409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7750204461183817044660545 5812653345887862783495409)
                ·
                  refine ⟨4359490009415897087621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812653345887862783495409 4359490009415897087621557)
                  ·
                    refine ⟨408702188382740351964521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4359490009415897087621557 408702188382740351964521)
                    ·
                      rfl

theorem cell22_1193917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1193917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193917 prefixEnd_1193917 := by exact prefixLift 1193917
  have htrace : WordTrace (prefixWord ++ tailWord_1193917) baseStart_1193917 baseEnd_1193917 := by
    simpa [prefixWord, tailWord_1193917, baseEnd_1193917] using wordTrace_append hprefix tailTrace_1193917
  have hstable : (prefixWord ++ tailWord_1193917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193917).length < 2 ^ (prefixWord ++ tailWord_1193917).sum := by decide
  have hdescent : baseEnd_1193917 < baseStart_1193917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193962 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1193962 : Nat := 118140960795 + 1193962 * 2 ^ 59
def prefixEnd_1193962 : Nat := 4983230072969 + 3 ^ 40 * 1193962 * 2
def baseEnd_1193962 : Nat := 408717592802375234589383

theorem tailTrace_1193962 : CollatzResearch.WordTrace tailWord_1193962 prefixEnd_1193962 408717592802375234589383 := by
  unfold tailWord_1193962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10886842925121765330102035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29031581133658040880272093 10886842925121765330102035)
  ·
    refine ⟨16330264387682647995153053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10886842925121765330102035 16330264387682647995153053)
    ·
      refine ⟨6123849145380992998182395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16330264387682647995153053 6123849145380992998182395)
      ·
        refine ⟨9185773718071489497273593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6123849145380992998182395 9185773718071489497273593)
        ·
          refine ⟨6889330288553617122955195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9185773718071489497273593 6889330288553617122955195)
          ·
            refine ⟨10333995432830425684432793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889330288553617122955195 10333995432830425684432793)
            ·
              refine ⟨7750496574622819263324595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10333995432830425684432793 7750496574622819263324595)
              ·
                refine ⟨11625744861934228894986893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7750496574622819263324595 11625744861934228894986893)
                ·
                  refine ⟨4359654323225335835620085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11625744861934228894986893 4359654323225335835620085)
                  ·
                    refine ⟨408717592802375234589383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4359654323225335835620085 408717592802375234589383)
                    ·
                      rfl

theorem cell22_1193962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1193962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193962 prefixEnd_1193962 := by exact prefixLift 1193962
  have htrace : WordTrace (prefixWord ++ tailWord_1193962) baseStart_1193962 baseEnd_1193962 := by
    simpa [prefixWord, tailWord_1193962, baseEnd_1193962] using wordTrace_append hprefix tailTrace_1193962
  have hstable : (prefixWord ++ tailWord_1193962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193962).length < 2 ^ (prefixWord ++ tailWord_1193962).sum := by decide
  have hdescent : baseEnd_1193962 < baseStart_1193962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193977 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_1193977 : Nat := 118140960795 + 1193977 * 2 ^ 59
def prefixEnd_1193977 : Nat := 4983230072969 + 3 ^ 40 * 1193977 * 2
def baseEnd_1193977 : Nat := 408722727608920195464337

theorem tailTrace_1193977 : CollatzResearch.WordTrace tailWord_1193977 prefixEnd_1193977 408722727608920195464337 := by
  unfold tailWord_1193977
  simp only [CollatzResearch.WordTrace]
  refine ⟨43547918795432718882204185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29031945863621812588136123 43547918795432718882204185)
  ·
    refine ⟨32660939096574539161653139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43547918795432718882204185 32660939096574539161653139)
    ·
      refine ⟨48991408644861808742479709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32660939096574539161653139 48991408644861808742479709)
      ·
        refine ⟨18371778241823178278429891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48991408644861808742479709 18371778241823178278429891)
        ·
          refine ⟨27557667362734767417644837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18371778241823178278429891 27557667362734767417644837)
          ·
            refine ⟨5167062630512768890808407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27557667362734767417644837 5167062630512768890808407)
            ·
              refine ⟨7750593945769153336212611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167062630512768890808407 7750593945769153336212611)
              ·
                refine ⟨11625890918653730004318917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7750593945769153336212611 11625890918653730004318917)
                ·
                  refine ⟨2179854547247574375809797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11625890918653730004318917 2179854547247574375809797)
                  ·
                    refine ⟨408722727608920195464337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179854547247574375809797 408722727608920195464337)
                    ·
                      rfl

theorem cell22_1193977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_1193977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193977 prefixEnd_1193977 := by exact prefixLift 1193977
  have htrace : WordTrace (prefixWord ++ tailWord_1193977) baseStart_1193977 baseEnd_1193977 := by
    simpa [prefixWord, tailWord_1193977, baseEnd_1193977] using wordTrace_append hprefix tailTrace_1193977
  have hstable : (prefixWord ++ tailWord_1193977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193977).length < 2 ^ (prefixWord ++ tailWord_1193977).sum := by decide
  have hdescent : baseEnd_1193977 < baseStart_1193977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193992 : List Nat := [2, 1, 3, 2, 1, 2, 4, 7]
def baseStart_1193992 : Nat := 118140960795 + 1193992 * 2 ^ 59
def prefixEnd_1193992 : Nat := 4983230072969 + 3 ^ 40 * 1193992 * 2
def baseEnd_1193992 : Nat := 45414206935051684037699

theorem tailTrace_1193992 : CollatzResearch.WordTrace tailWord_1193992 prefixEnd_1193992 45414206935051684037699 := by
  unfold tailWord_1193992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774232945189188222000115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29032310593585584296000153 21774232945189188222000115)
  ·
    refine ⟨32661349417783782333000173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21774232945189188222000115 32661349417783782333000173)
    ·
      refine ⟨12248006031668918374875065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32661349417783782333000173 12248006031668918374875065)
      ·
        refine ⟨9186004523751688781156299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12248006031668918374875065 9186004523751688781156299)
        ·
          refine ⟨13779006785627533171734449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186004523751688781156299 13779006785627533171734449)
          ·
            refine ⟨10334255089220649878800837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13779006785627533171734449 10334255089220649878800837)
            ·
              refine ⟨1937672829228871852275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10334255089220649878800837 1937672829228871852275157)
              ·
                refine ⟨45414206935051684037699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1937672829228871852275157 45414206935051684037699)
                ·
                  rfl

theorem cell22_1193992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_1193992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1193992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1193992 prefixEnd_1193992 := by exact prefixLift 1193992
  have htrace : WordTrace (prefixWord ++ tailWord_1193992) baseStart_1193992 baseEnd_1193992 := by
    simpa [prefixWord, tailWord_1193992, baseEnd_1193992] using wordTrace_append hprefix tailTrace_1193992
  have hstable : (prefixWord ++ tailWord_1193992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193992).length < 2 ^ (prefixWord ++ tailWord_1193992).sum := by decide
  have hdescent : baseEnd_1193992 < baseStart_1193992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194037 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 7]
def baseStart_1194037 : Nat := 118140960795 + 1194037 * 2 ^ 59
def prefixEnd_1194037 : Nat := 4983230072969 + 3 ^ 40 * 1194037 * 2
def baseEnd_1194037 : Nat := 136247755611700012988051

theorem tailTrace_1194037 : CollatzResearch.WordTrace tailWord_1194037 prefixEnd_1194037 136247755611700012988051 := by
  unfold tailWord_1194037
  simp only [CollatzResearch.WordTrace]
  refine ⟨43550107175215349129388365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29033404783476899419592243 43550107175215349129388365)
  ·
    refine ⟨16331290190705755923520637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43550107175215349129388365 16331290190705755923520637)
    ·
      refine ⟨6124233821514658471320239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16331290190705755923520637 6124233821514658471320239)
      ·
        refine ⟨9186350732271987706980359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124233821514658471320239 9186350732271987706980359)
        ·
          refine ⟨13779526098407981560470539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186350732271987706980359 13779526098407981560470539)
          ·
            refine ⟨20669289147611972340705809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13779526098407981560470539 20669289147611972340705809)
            ·
              refine ⟨15501966860708979255529357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20669289147611972340705809 15501966860708979255529357)
              ·
                refine ⟨5813237572765867220823509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15501966860708979255529357 5813237572765867220823509)
                ·
                  refine ⟨136247755611700012988051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5813237572765867220823509 136247755611700012988051)
                  ·
                    rfl

theorem cell22_1194037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_1194037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194037 prefixEnd_1194037 := by exact prefixLift 1194037
  have htrace : WordTrace (prefixWord ++ tailWord_1194037) baseStart_1194037 baseEnd_1194037 := by
    simpa [prefixWord, tailWord_1194037, baseEnd_1194037] using wordTrace_append hprefix tailTrace_1194037
  have hstable : (prefixWord ++ tailWord_1194037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194037).length < 2 ^ (prefixWord ++ tailWord_1194037).sum := by decide
  have hdescent : baseEnd_1194037 < baseStart_1194037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_1194067 : Nat := 118140960795 + 1194067 * 2 ^ 59
def prefixEnd_1194067 : Nat := 4983230072969 + 3 ^ 40 * 1194067 * 2
def baseEnd_1194067 : Nat := 408753536448189960714061

theorem tailTrace_1194067 : CollatzResearch.WordTrace tailWord_1194067 prefixEnd_1194067 408753536448189960714061 := by
  unfold tailWord_1194067
  simp only [CollatzResearch.WordTrace]
  refine ⟨43551201365106664252980455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29034134243404442835320303 43551201365106664252980455)
  ·
    refine ⟨65326802047659996379470683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43551201365106664252980455 65326802047659996379470683)
    ·
      refine ⟨97990203071489994569206025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65326802047659996379470683 97990203071489994569206025)
      ·
        refine ⟨73492652303617495926904519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97990203071489994569206025 73492652303617495926904519)
        ·
          refine ⟨110238978455426243890356779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73492652303617495926904519 110238978455426243890356779)
          ·
            refine ⟨165358467683139365835535169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110238978455426243890356779 165358467683139365835535169)
            ·
              refine ⟨124018850762354524376651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165358467683139365835535169 124018850762354524376651377)
              ·
                refine ⟨93014138071765893282488533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124018850762354524376651377 93014138071765893282488533)
                ·
                  refine ⟨2180018861057013123808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93014138071765893282488533 2180018861057013123808325)
                  ·
                    refine ⟨408753536448189960714061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180018861057013123808325 408753536448189960714061)
                    ·
                      rfl

theorem cell22_1194067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_1194067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194067 prefixEnd_1194067 := by exact prefixLift 1194067
  have htrace : WordTrace (prefixWord ++ tailWord_1194067) baseStart_1194067 baseEnd_1194067 := by
    simpa [prefixWord, tailWord_1194067, baseEnd_1194067] using wordTrace_append hprefix tailTrace_1194067
  have hstable : (prefixWord ++ tailWord_1194067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194067).length < 2 ^ (prefixWord ++ tailWord_1194067).sum := by decide
  have hdescent : baseEnd_1194067 < baseStart_1194067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194144 : List Nat := [2, 1, 1, 4, 2, 4, 8]
def baseStart_1194144 : Nat := 118140960795 + 1194144 * 2 ^ 59
def prefixEnd_1194144 : Nat := 4983230072969 + 3 ^ 40 * 1194144 * 2
def baseEnd_1194144 : Nat := 15139996115621756538475

theorem tailTrace_1194144 : CollatzResearch.WordTrace tailWord_1194144 prefixEnd_1194144 15139996115621756538475 := by
  unfold tailWord_1194144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21777004892913853201766743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29036006523885137602355657 21777004892913853201766743)
  ·
    refine ⟨32665507339370779802650115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21777004892913853201766743 32665507339370779802650115)
    ·
      refine ⟨48998261009056169703975173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32665507339370779802650115 48998261009056169703975173)
      ·
        refine ⟨9187173939198031819495345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48998261009056169703975173 9187173939198031819495345)
        ·
          refine ⟨6890380454398523864621509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9187173939198031819495345 6890380454398523864621509)
          ·
            refine ⟨1291946335199723224616533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6890380454398523864621509 1291946335199723224616533)
            ·
              refine ⟨15139996115621756538475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1291946335199723224616533 15139996115621756538475)
              ·
                rfl

theorem cell22_1194144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 8].length) (baseStart_1194144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194144 prefixEnd_1194144 := by exact prefixLift 1194144
  have htrace : WordTrace (prefixWord ++ tailWord_1194144) baseStart_1194144 baseEnd_1194144 := by
    simpa [prefixWord, tailWord_1194144, baseEnd_1194144] using wordTrace_append hprefix tailTrace_1194144
  have hstable : (prefixWord ++ tailWord_1194144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194144).length < 2 ^ (prefixWord ++ tailWord_1194144).sum := by decide
  have hdescent : baseEnd_1194144 < baseStart_1194144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194146 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1194146 : Nat := 118140960795 + 1194146 * 2 ^ 59
def prefixEnd_1194146 : Nat := 4983230072969 + 3 ^ 40 * 1194146 * 2
def baseEnd_1194146 : Nat := 408780579762660087988819

theorem tailTrace_1194146 : CollatzResearch.WordTrace tailWord_1194146 prefixEnd_1194146 408780579762660087988819 := by
  unfold tailWord_1194146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888520682955115186276573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29036055154546973830070861 10888520682955115186276573)
  ·
    refine ⟨4083195256108168194853715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10888520682955115186276573 4083195256108168194853715)
    ·
      refine ⟨6124792884162252292280573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083195256108168194853715 6124792884162252292280573)
      ·
        refine ⟨2296797331560844609605215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6124792884162252292280573 2296797331560844609605215)
        ·
          refine ⟨3445195997341266914407823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296797331560844609605215 3445195997341266914407823)
          ·
            refine ⟨5167793996011900371611735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445195997341266914407823 5167793996011900371611735)
            ·
              refine ⟨7751690994017850557417603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167793996011900371611735 7751690994017850557417603)
              ·
                refine ⟨11627536491026775836126405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751690994017850557417603 11627536491026775836126405)
                ·
                  refine ⟨2180163092067520469273701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11627536491026775836126405 2180163092067520469273701)
                  ·
                    refine ⟨408780579762660087988819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180163092067520469273701 408780579762660087988819)
                    ·
                      rfl

theorem cell22_1194146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1194146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194146 prefixEnd_1194146 := by exact prefixLift 1194146
  have htrace : WordTrace (prefixWord ++ tailWord_1194146) baseStart_1194146 baseEnd_1194146 := by
    simpa [prefixWord, tailWord_1194146, baseEnd_1194146] using wordTrace_append hprefix tailTrace_1194146
  have hstable : (prefixWord ++ tailWord_1194146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194146).length < 2 ^ (prefixWord ++ tailWord_1194146).sum := by decide
  have hdescent : baseEnd_1194146 < baseStart_1194146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194161 : List Nat := [1, 2, 2, 5, 2, 1, 2, 7]
def baseStart_1194161 : Nat := 118140960795 + 1194161 * 2 ^ 59
def prefixEnd_1194161 : Nat := 4983230072969 + 3 ^ 40 * 1194161 * 2
def baseEnd_1194161 : Nat := 45420634952133894318197

theorem tailTrace_1194161 : CollatzResearch.WordTrace tailWord_1194161 prefixEnd_1194161 45420634952133894318197 := by
  unfold tailWord_1194161
  simp only [CollatzResearch.WordTrace]
  refine ⟨43554629826766118306902337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29036419884510745537934891 43554629826766118306902337)
  ·
    refine ⟨32665972370074588730176753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43554629826766118306902337 32665972370074588730176753)
    ·
      refine ⟨24499479277555941547632565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32665972370074588730176753 24499479277555941547632565)
      ·
        refine ⟨2296826182270869520090553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24499479277555941547632565 2296826182270869520090553)
        ·
          refine ⟨1722619636703152140067915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296826182270869520090553 1722619636703152140067915)
          ·
            refine ⟨2583929455054728210101873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722619636703152140067915 2583929455054728210101873)
            ·
              refine ⟨1937947091291046157576405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583929455054728210101873 1937947091291046157576405)
              ·
                refine ⟨45420634952133894318197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1937947091291046157576405 45420634952133894318197)
                ·
                  rfl

theorem cell22_1194161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 7].length) (baseStart_1194161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194161 prefixEnd_1194161 := by exact prefixLift 1194161
  have htrace : WordTrace (prefixWord ++ tailWord_1194161) baseStart_1194161 baseEnd_1194161 := by
    simpa [prefixWord, tailWord_1194161, baseEnd_1194161] using wordTrace_append hprefix tailTrace_1194161
  have hstable : (prefixWord ++ tailWord_1194161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194161).length < 2 ^ (prefixWord ++ tailWord_1194161).sum := by decide
  have hdescent : baseEnd_1194161 < baseStart_1194161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194165 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1194165 : Nat := 118140960795 + 1194165 * 2 ^ 59
def prefixEnd_1194165 : Nat := 4983230072969 + 3 ^ 40 * 1194165 * 2
def baseEnd_1194165 : Nat := 408787083850950371763761

theorem tailTrace_1194165 : CollatzResearch.WordTrace tailWord_1194165 prefixEnd_1194165 408787083850950371763761 := by
  unfold tailWord_1194165
  simp only [CollatzResearch.WordTrace]
  refine ⟨43554775718751626990047949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29036517145834417993365299 43554775718751626990047949)
  ·
    refine ⟨16333040894531860121267981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43554775718751626990047949 16333040894531860121267981)
    ·
      refine ⟨6124890335449447545475493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16333040894531860121267981 6124890335449447545475493)
      ·
        refine ⟨1148416937896771414776655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6124890335449447545475493 1148416937896771414776655)
        ·
          refine ⟨1722625406845157122164983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148416937896771414776655 1722625406845157122164983)
          ·
            refine ⟨2583938110267735683247475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722625406845157122164983 2583938110267735683247475)
            ·
              refine ⟨3875907165401603524871213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583938110267735683247475 3875907165401603524871213)
              ·
                refine ⟨1453465187025601321826705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3875907165401603524871213 1453465187025601321826705)
                ·
                  refine ⟨1090098890269200991370029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1453465187025601321826705 1090098890269200991370029)
                  ·
                    refine ⟨408787083850950371763761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090098890269200991370029 408787083850950371763761)
                    ·
                      rfl

theorem cell22_1194165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1194165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194165 prefixEnd_1194165 := by exact prefixLift 1194165
  have htrace : WordTrace (prefixWord ++ tailWord_1194165) baseStart_1194165 baseEnd_1194165 := by
    simpa [prefixWord, tailWord_1194165, baseEnd_1194165] using wordTrace_append hprefix tailTrace_1194165
  have hstable : (prefixWord ++ tailWord_1194165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194165).length < 2 ^ (prefixWord ++ tailWord_1194165).sum := by decide
  have hdescent : baseEnd_1194165 < baseStart_1194165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194178 : List Nat := [3, 5, 1, 1, 1, 1, 2, 8]
def baseStart_1194178 : Nat := 118140960795 + 1194178 * 2 ^ 59
def prefixEnd_1194178 : Nat := 4983230072969 + 3 ^ 40 * 1194178 * 2
def baseEnd_1194178 : Nat := 45421281557402519020969

theorem tailTrace_1194178 : CollatzResearch.WordTrace tailWord_1194178 prefixEnd_1194178 45421281557402519020969 := by
  unfold tailWord_1194178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888812466926132552567797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29036833245136353473514125 10888812466926132552567797)
  ·
    refine ⟨1020826168774324926803231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10888812466926132552567797 1020826168774324926803231)
    ·
      refine ⟨1531239253161487390204847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020826168774324926803231 1531239253161487390204847)
      ·
        refine ⟨2296858879742231085307271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531239253161487390204847 2296858879742231085307271)
        ·
          refine ⟨3445288319613346627960907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296858879742231085307271 3445288319613346627960907)
          ·
            refine ⟨5167932479420019941941361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445288319613346627960907 5167932479420019941941361)
            ·
              refine ⟨3875949359565014956456021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167932479420019941941361 3875949359565014956456021)
              ·
                refine ⟨45421281557402519020969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3875949359565014956456021 45421281557402519020969)
                ·
                  rfl

theorem cell22_1194178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_1194178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194178 prefixEnd_1194178 := by exact prefixLift 1194178
  have htrace : WordTrace (prefixWord ++ tailWord_1194178) baseStart_1194178 baseEnd_1194178 := by
    simpa [prefixWord, tailWord_1194178, baseEnd_1194178] using wordTrace_append hprefix tailTrace_1194178
  have hstable : (prefixWord ++ tailWord_1194178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194178).length < 2 ^ (prefixWord ++ tailWord_1194178).sum := by decide
  have hdescent : baseEnd_1194178 < baseStart_1194178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194219 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_1194219 : Nat := 118140960795 + 1194219 * 2 ^ 59
def prefixEnd_1194219 : Nat := 4983230072969 + 3 ^ 40 * 1194219 * 2
def baseEnd_1194219 : Nat := 408805569154512230913595

theorem tailTrace_1194219 : CollatzResearch.WordTrace tailWord_1194219 prefixEnd_1194219 408805569154512230913595 := by
  unfold tailWord_1194219
  simp only [CollatzResearch.WordTrace]
  refine ⟨43556745260555994212513711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29037830173703996141675807 43556745260555994212513711)
  ·
    refine ⟨65335117890833991318770567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43556745260555994212513711 65335117890833991318770567)
    ·
      refine ⟨98002676836250986978155851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65335117890833991318770567 98002676836250986978155851)
      ·
        refine ⟨147004015254376480467233777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98002676836250986978155851 147004015254376480467233777)
        ·
          refine ⟨110253011440782360350425333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147004015254376480467233777 110253011440782360350425333)
          ·
            refine ⟨10336219822573346282852375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110253011440782360350425333 10336219822573346282852375)
            ·
              refine ⟨15504329733860019424278563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10336219822573346282852375 15504329733860019424278563)
              ·
                refine ⟨23256494600790029136417845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15504329733860019424278563 23256494600790029136417845)
                ·
                  refine ⟨2180296368824065231539173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23256494600790029136417845 2180296368824065231539173)
                  ·
                    refine ⟨408805569154512230913595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180296368824065231539173 408805569154512230913595)
                    ·
                      rfl

theorem cell22_1194219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_1194219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194219 prefixEnd_1194219 := by exact prefixLift 1194219
  have htrace : WordTrace (prefixWord ++ tailWord_1194219) baseStart_1194219 baseEnd_1194219 := by
    simpa [prefixWord, tailWord_1194219, baseEnd_1194219] using wordTrace_append hprefix tailTrace_1194219
  have hstable : (prefixWord ++ tailWord_1194219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194219).length < 2 ^ (prefixWord ++ tailWord_1194219).sum := by decide
  have hdescent : baseEnd_1194219 < baseStart_1194219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194234 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_1194234 : Nat := 118140960795 + 1194234 * 2 ^ 59
def prefixEnd_1194234 : Nat := 4983230072969 + 3 ^ 40 * 1194234 * 2
def baseEnd_1194234 : Nat := 136270234653685730596183

theorem tailTrace_1194234 : CollatzResearch.WordTrace tailWord_1194234 prefixEnd_1194234 136270234653685730596183 := by
  unfold tailWord_1194234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889323088875412943577439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29038194903667767849539837 10889323088875412943577439)
  ·
    refine ⟨16333984633313119415366159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10889323088875412943577439 16333984633313119415366159)
    ·
      refine ⟨24500976949969679123049239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16333984633313119415366159 24500976949969679123049239)
      ·
        refine ⟨36751465424954518684573859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24500976949969679123049239 36751465424954518684573859)
        ·
          refine ⟨55127198137431778026860789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36751465424954518684573859 55127198137431778026860789)
          ·
            refine ⟨5168174825384229190018199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55127198137431778026860789 5168174825384229190018199)
            ·
              refine ⟨7752262238076343785027299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168174825384229190018199 7752262238076343785027299)
              ·
                refine ⟨11628393357114515677540949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7752262238076343785027299 11628393357114515677540949)
                ·
                  refine ⟨136270234653685730596183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11628393357114515677540949 136270234653685730596183)
                  ·
                    rfl

theorem cell22_1194234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_1194234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194234 prefixEnd_1194234 := by exact prefixLift 1194234
  have htrace : WordTrace (prefixWord ++ tailWord_1194234) baseStart_1194234 baseEnd_1194234 := by
    simpa [prefixWord, tailWord_1194234, baseEnd_1194234] using wordTrace_append hprefix tailTrace_1194234
  have hstable : (prefixWord ++ tailWord_1194234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194234).length < 2 ^ (prefixWord ++ tailWord_1194234).sum := by decide
  have hdescent : baseEnd_1194234 < baseStart_1194234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194236 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1194236 : Nat := 118140960795 + 1194236 * 2 ^ 59
def prefixEnd_1194236 : Nat := 4983230072969 + 3 ^ 40 * 1194236 * 2
def baseEnd_1194236 : Nat := 408811388601929853238543

theorem tailTrace_1194236 : CollatzResearch.WordTrace tailWord_1194236 prefixEnd_1194236 408811388601929853238543 := by
  unfold tailWord_1194236
  simp only [CollatzResearch.WordTrace]
  refine ⟨21778682650747203057941281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29038243534329604077255041 21778682650747203057941281)
  ·
    refine ⟨16334011988060402293455961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21778682650747203057941281 16334011988060402293455961)
    ·
      refine ⟨12250508991045301720091971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16334011988060402293455961 12250508991045301720091971)
      ·
        refine ⟨18375763486567952580137957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12250508991045301720091971 18375763486567952580137957)
        ·
          refine ⟨3445455653731491108775867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18375763486567952580137957 3445455653731491108775867)
          ·
            refine ⟨5168183480597236663163801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445455653731491108775867 5168183480597236663163801)
            ·
              refine ⟨3876137610447927497372851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5168183480597236663163801 3876137610447927497372851)
              ·
                refine ⟨5814206415671891246059277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876137610447927497372851 5814206415671891246059277)
                ·
                  refine ⟨2180327405876959217272229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5814206415671891246059277 2180327405876959217272229)
                  ·
                    refine ⟨408811388601929853238543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180327405876959217272229 408811388601929853238543)
                    ·
                      rfl

theorem cell22_1194236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1194236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194236 prefixEnd_1194236 := by exact prefixLift 1194236
  have htrace : WordTrace (prefixWord ++ tailWord_1194236) baseStart_1194236 baseEnd_1194236 := by
    simpa [prefixWord, tailWord_1194236, baseEnd_1194236] using wordTrace_append hprefix tailTrace_1194236
  have hstable : (prefixWord ++ tailWord_1194236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194236).length < 2 ^ (prefixWord ++ tailWord_1194236).sum := by decide
  have hdescent : baseEnd_1194236 < baseStart_1194236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194296 : List Nat := [2, 1, 2, 1, 3, 1, 6, 6]
def baseStart_1194296 : Nat := 118140960795 + 1194296 * 2 ^ 59
def prefixEnd_1194296 : Nat := 4983230072969 + 3 ^ 40 * 1194296 * 2
def baseEnd_1194296 : Nat := 45425769758678855193151

theorem tailTrace_1194296 : CollatzResearch.WordTrace tailWord_1194296 prefixEnd_1194296 45425769758678855193151 := by
  unfold tailWord_1194296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21779776840638518181533371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29039702454184690908711161 21779776840638518181533371)
  ·
    refine ⟨32669665260957777272300057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21779776840638518181533371 32669665260957777272300057)
    ·
      refine ⟨24502248945718332954225043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32669665260957777272300057 24502248945718332954225043)
      ·
        refine ⟨36753373418577499431337565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24502248945718332954225043 36753373418577499431337565)
        ·
          refine ⟨13782515031966562286751587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36753373418577499431337565 13782515031966562286751587)
          ·
            refine ⟨20673772547949843430127381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782515031966562286751587 20673772547949843430127381)
            ·
              refine ⟨969083088185148910787221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20673772547949843430127381 969083088185148910787221)
              ·
                refine ⟨45425769758678855193151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 969083088185148910787221 45425769758678855193151)
                ·
                  rfl

theorem cell22_1194296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_1194296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194296 prefixEnd_1194296 := by exact prefixLift 1194296
  have htrace : WordTrace (prefixWord ++ tailWord_1194296) baseStart_1194296 baseEnd_1194296 := by
    simpa [prefixWord, tailWord_1194296, baseEnd_1194296] using wordTrace_append hprefix tailTrace_1194296
  have hstable : (prefixWord ++ tailWord_1194296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194296).length < 2 ^ (prefixWord ++ tailWord_1194296).sum := by decide
  have hdescent : baseEnd_1194296 < baseStart_1194296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194309 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_1194309 : Nat := 118140960795 + 1194309 * 2 ^ 59
def prefixEnd_1194309 : Nat := 4983230072969 + 3 ^ 40 * 1194309 * 2
def baseEnd_1194309 : Nat := 408836377993781996163319

theorem tailTrace_1194309 : CollatzResearch.WordTrace tailWord_1194309 prefixEnd_1194309 408836377993781996163319 := by
  unfold tailWord_1194309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43560027830229939583289981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29040018553486626388859987 43560027830229939583289981)
  ·
    refine ⟨16335010436336227343733743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43560027830229939583289981 16335010436336227343733743)
    ·
      refine ⟨24502515654504341015600615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16335010436336227343733743 24502515654504341015600615)
      ·
        refine ⟨36753773481756511523400923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24502515654504341015600615 36753773481756511523400923)
        ·
          refine ⟨55130660222634767285101385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36753773481756511523400923 55130660222634767285101385)
          ·
            refine ⟨41347995166976075463826039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55130660222634767285101385 41347995166976075463826039)
            ·
              refine ⟨62021992750464113195739059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41347995166976075463826039 62021992750464113195739059)
              ·
                refine ⟨93032989125696169793608589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62021992750464113195739059 93032989125696169793608589)
                ·
                  refine ⟨34887370922136063672603221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93032989125696169793608589 34887370922136063672603221)
                  ·
                    refine ⟨408836377993781996163319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34887370922136063672603221 408836377993781996163319)
                    ·
                      rfl

theorem cell22_1194309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_1194309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194309 prefixEnd_1194309 := by exact prefixLift 1194309
  have htrace : WordTrace (prefixWord ++ tailWord_1194309) baseStart_1194309 baseEnd_1194309 := by
    simpa [prefixWord, tailWord_1194309, baseEnd_1194309] using wordTrace_append hprefix tailTrace_1194309
  have hstable : (prefixWord ++ tailWord_1194309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194309).length < 2 ^ (prefixWord ++ tailWord_1194309).sum := by decide
  have hdescent : baseEnd_1194309 < baseStart_1194309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194418 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_1194418 : Nat := 118140960795 + 1194418 * 2 ^ 59
def prefixEnd_1194418 : Nat := 4983230072969 + 3 ^ 40 * 1194418 * 2
def baseEnd_1194418 : Nat := 408873690921342045187985

theorem tailTrace_1194418 : CollatzResearch.WordTrace tailWord_1194418 prefixEnd_1194418 408873690921342045187985 := by
  unfold tailWord_1194418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891000846708762799751977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29042668924556700799338605 10891000846708762799751977)
  ·
    refine ⟨8168250635031572099813983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10891000846708762799751977 8168250635031572099813983)
    ·
      refine ⟨12252375952547358149720975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168250635031572099813983 12252375952547358149720975)
      ·
        refine ⟨18378563928821037224581463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12252375952547358149720975 18378563928821037224581463)
        ·
          refine ⟨27567845893231555836872195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18378563928821037224581463 27567845893231555836872195)
          ·
            refine ⟨41351768839847333755308293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27567845893231555836872195 41351768839847333755308293)
            ·
              refine ⟨7753456657471375079120305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41351768839847333755308293 7753456657471375079120305)
              ·
                refine ⟨5815092493103531309340229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7753456657471375079120305 5815092493103531309340229)
                ·
                  refine ⟨1090329842456912120501293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5815092493103531309340229 1090329842456912120501293)
                  ·
                    refine ⟨408873690921342045187985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090329842456912120501293 408873690921342045187985)
                    ·
                      rfl

theorem cell22_1194418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_1194418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194418 prefixEnd_1194418 := by exact prefixLift 1194418
  have htrace : WordTrace (prefixWord ++ tailWord_1194418) baseStart_1194418 baseEnd_1194418 := by
    simpa [prefixWord, tailWord_1194418, baseEnd_1194418] using wordTrace_append hprefix tailTrace_1194418
  have hstable : (prefixWord ++ tailWord_1194418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194418).length < 2 ^ (prefixWord ++ tailWord_1194418).sum := by decide
  have hdescent : baseEnd_1194418 < baseStart_1194418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194476 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1194476 : Nat := 118140960795 + 1194476 * 2 ^ 59
def prefixEnd_1194476 : Nat := 4983230072969 + 3 ^ 40 * 1194476 * 2
def baseEnd_1194476 : Nat := 136297848502216409079269

theorem tailTrace_1194476 : CollatzResearch.WordTrace tailWord_1194476 prefixEnd_1194476 136297848502216409079269 := by
  unfold tailWord_1194476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21783059410312463552309641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29044079213749951403079521 21783059410312463552309641)
  ·
    refine ⟨16337294557734347664232231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21783059410312463552309641 16337294557734347664232231)
    ·
      refine ⟨24505941836601521496348347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16337294557734347664232231 24505941836601521496348347)
      ·
        refine ⟨36758912754902282244522521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24505941836601521496348347 36758912754902282244522521)
        ·
          refine ⟨27569184566176711683391891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36758912754902282244522521 27569184566176711683391891)
          ·
            refine ⟨41353776849265067525087837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27569184566176711683391891 41353776849265067525087837)
            ·
              refine ⟨15507666318474400321907939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41353776849265067525087837 15507666318474400321907939)
              ·
                refine ⟨23261499477711600482861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15507666318474400321907939 23261499477711600482861909)
                ·
                  refine ⟨136297848502216409079269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23261499477711600482861909 136297848502216409079269)
                  ·
                    rfl

theorem cell22_1194476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1194476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194476 prefixEnd_1194476 := by exact prefixLift 1194476
  have htrace : WordTrace (prefixWord ++ tailWord_1194476) baseStart_1194476 baseEnd_1194476 := by
    simpa [prefixWord, tailWord_1194476, baseEnd_1194476] using wordTrace_append hprefix tailTrace_1194476
  have hstable : (prefixWord ++ tailWord_1194476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194476).length < 2 ^ (prefixWord ++ tailWord_1194476).sum := by decide
  have hdescent : baseEnd_1194476 < baseStart_1194476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194493 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 5]
def baseStart_1194493 : Nat := 118140960795 + 1194493 * 2 ^ 59
def prefixEnd_1194493 : Nat := 4983230072969 + 3 ^ 40 * 1194493 * 2
def baseEnd_1194493 : Nat := 136299788318022283187585

theorem tailTrace_1194493 : CollatzResearch.WordTrace tailWord_1194493 prefixEnd_1194493 136299788318022283187585 := by
  unfold tailWord_1194493
  simp only [CollatzResearch.WordTrace]
  refine ⟨43566738861563339007988133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29044492574375559338658755 43566738861563339007988133)
  ·
    refine ⟨8168763536543126063997775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43566738861563339007988133 8168763536543126063997775)
    ·
      refine ⟨12253145304814689095996663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168763536543126063997775 12253145304814689095996663)
      ·
        refine ⟨18379717957222033643994995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253145304814689095996663 18379717957222033643994995)
        ·
          refine ⟨27569576935833050465992493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18379717957222033643994995 27569576935833050465992493)
          ·
            refine ⟨10338591350937393924747185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27569576935833050465992493 10338591350937393924747185)
            ·
              refine ⟨7753943513203045443560389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10338591350937393924747185 7753943513203045443560389)
              ·
                refine ⟨1453864408725571020667573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7753943513203045443560389 1453864408725571020667573)
                ·
                  refine ⟨136299788318022283187585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453864408725571020667573 136299788318022283187585)
                  ·
                    rfl

theorem cell22_1194493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_1194493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194493 prefixEnd_1194493 := by exact prefixLift 1194493
  have htrace : WordTrace (prefixWord ++ tailWord_1194493) baseStart_1194493 baseEnd_1194493 := by
    simpa [prefixWord, tailWord_1194493, baseEnd_1194493] using wordTrace_append hprefix tailTrace_1194493
  have hstable : (prefixWord ++ tailWord_1194493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194493).length < 2 ^ (prefixWord ++ tailWord_1194493).sum := by decide
  have hdescent : baseEnd_1194493 < baseStart_1194493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194497 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1194497 : Nat := 118140960795 + 1194497 * 2 ^ 59
def prefixEnd_1194497 : Nat := 4983230072969 + 3 ^ 40 * 1194497 * 2
def baseEnd_1194497 : Nat := 408900734235812172462743

theorem tailTrace_1194497 : CollatzResearch.WordTrace tailWord_1194497 prefixEnd_1194497 408900734235812172462743 := by
  unfold tailWord_1194497
  simp only [CollatzResearch.WordTrace]
  refine ⟨43566884753548847691133745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29044589835699231794089163 43566884753548847691133745)
  ·
    refine ⟨32675163565161635768350309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43566884753548847691133745 32675163565161635768350309)
    ·
      refine ⟨6126593168467806706565683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32675163565161635768350309 6126593168467806706565683)
      ·
        refine ⟨9189889752701710059848525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6126593168467806706565683 9189889752701710059848525)
        ·
          refine ⟨3446208657263141272443197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9189889752701710059848525 3446208657263141272443197)
          ·
            refine ⟨1292328246473677977166199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3446208657263141272443197 1292328246473677977166199)
            ·
              refine ⟨1938492369710516965749299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292328246473677977166199 1938492369710516965749299)
              ·
                refine ⟨2907738554565775448623949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938492369710516965749299 2907738554565775448623949)
                ·
                  refine ⟨1090401957962165793233981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2907738554565775448623949 1090401957962165793233981)
                  ·
                    refine ⟨408900734235812172462743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090401957962165793233981 408900734235812172462743)
                    ·
                      rfl

theorem cell22_1194497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1194497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194497 prefixEnd_1194497 := by exact prefixLift 1194497
  have htrace : WordTrace (prefixWord ++ tailWord_1194497) baseStart_1194497 baseEnd_1194497 := by
    simpa [prefixWord, tailWord_1194497, baseEnd_1194497] using wordTrace_append hprefix tailTrace_1194497
  have hstable : (prefixWord ++ tailWord_1194497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194497).length < 2 ^ (prefixWord ++ tailWord_1194497).sum := by decide
  have hdescent : baseEnd_1194497 < baseStart_1194497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194510 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_1194510 : Nat := 118140960795 + 1194510 * 2 ^ 59
def prefixEnd_1194510 : Nat := 4983230072969 + 3 ^ 40 * 1194510 * 2
def baseEnd_1194510 : Nat := 136301728133828157295901

theorem tailTrace_1194510 : CollatzResearch.WordTrace tailWord_1194510 prefixEnd_1194510 136301728133828157295901 := by
  unfold tailWord_1194510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445919862812718863919623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29044905935001167274237989 5445919862812718863919623)
  ·
    refine ⟨8168879794219078295879435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5445919862812718863919623 8168879794219078295879435)
    ·
      refine ⟨12253319691328617443819153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168879794219078295879435 12253319691328617443819153)
      ·
        refine ⟨9189989768496463082864365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12253319691328617443819153 9189989768496463082864365)
        ·
          refine ⟨3446246163186173656074137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9189989768496463082864365 3446246163186173656074137)
          ·
            refine ⟨2584684622389630242055603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3446246163186173656074137 2584684622389630242055603)
            ·
              refine ⟨3877026933584445363083405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584684622389630242055603 3877026933584445363083405)
              ·
                refine ⟨1453885100094167011156277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3877026933584445363083405 1453885100094167011156277)
                ·
                  refine ⟨136301728133828157295901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453885100094167011156277 136301728133828157295901)
                  ·
                    rfl

theorem cell22_1194510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_1194510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194510 prefixEnd_1194510 := by exact prefixLift 1194510
  have htrace : WordTrace (prefixWord ++ tailWord_1194510) baseStart_1194510 baseEnd_1194510 := by
    simpa [prefixWord, tailWord_1194510, baseEnd_1194510] using wordTrace_append hprefix tailTrace_1194510
  have hstable : (prefixWord ++ tailWord_1194510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194510).length < 2 ^ (prefixWord ++ tailWord_1194510).sum := by decide
  have hdescent : baseEnd_1194510 < baseStart_1194510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194553 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1194553 : Nat := 118140960795 + 1194553 * 2 ^ 59
def prefixEnd_1194553 : Nat := 4983230072969 + 3 ^ 40 * 1194553 * 2
def baseEnd_1194553 : Nat := 408919904180246693062571

theorem tailTrace_1194553 : CollatzResearch.WordTrace tailWord_1194553 prefixEnd_1194553 408919904180246693062571 := by
  unfold tailWord_1194553
  simp only [CollatzResearch.WordTrace]
  refine ⟨43568927241345969255172313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29045951494230646170114875 43568927241345969255172313)
  ·
    refine ⟨32676695431009476941379235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43568927241345969255172313 32676695431009476941379235)
    ·
      refine ⟨49015043146514215412068853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32676695431009476941379235 49015043146514215412068853)
      ·
        refine ⟨4595160294985707694881455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49015043146514215412068853 4595160294985707694881455)
        ·
          refine ⟨6892740442478561542322183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595160294985707694881455 6892740442478561542322183)
          ·
            refine ⟨10339110663717842313483275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892740442478561542322183 10339110663717842313483275)
            ·
              refine ⟨15508665995576763470224913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339110663717842313483275 15508665995576763470224913)
              ·
                refine ⟨11631499496682572602668685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15508665995576763470224913 11631499496682572602668685)
                ·
                  refine ⟨4361812311255964726000757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11631499496682572602668685 4361812311255964726000757)
                  ·
                    refine ⟨408919904180246693062571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4361812311255964726000757 408919904180246693062571)
                    ·
                      rfl

theorem cell22_1194553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1194553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194553 prefixEnd_1194553 := by exact prefixLift 1194553
  have htrace : WordTrace (prefixWord ++ tailWord_1194553) baseStart_1194553 baseEnd_1194553 := by
    simpa [prefixWord, tailWord_1194553, baseEnd_1194553] using wordTrace_append hprefix tailTrace_1194553
  have hstable : (prefixWord ++ tailWord_1194553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194553).length < 2 ^ (prefixWord ++ tailWord_1194553).sum := by decide
  have hdescent : baseEnd_1194553 < baseStart_1194553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194568 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1194568 : Nat := 118140960795 + 1194568 * 2 ^ 59
def prefixEnd_1194568 : Nat := 4983230072969 + 3 ^ 40 * 1194568 * 2
def baseEnd_1194568 : Nat := 408925038986791653937525

theorem tailTrace_1194568 : CollatzResearch.WordTrace tailWord_1194568 prefixEnd_1194568 408925038986791653937525 := by
  unfold tailWord_1194568
  simp only [CollatzResearch.WordTrace]
  refine ⟨21784737168145813408484179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29046316224194417877978905 21784737168145813408484179)
  ·
    refine ⟨32677105752218720112726269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21784737168145813408484179 32677105752218720112726269)
    ·
      refine ⟨12253914657082020042272351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32677105752218720112726269 12253914657082020042272351)
      ·
        refine ⟨18380871985623030063408527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253914657082020042272351 18380871985623030063408527)
        ·
          refine ⟨27571307978434545095112791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18380871985623030063408527 27571307978434545095112791)
          ·
            refine ⟨41356961967651817642669187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27571307978434545095112791 41356961967651817642669187)
            ·
              refine ⟨62035442951477726464003781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41356961967651817642669187 62035442951477726464003781)
              ·
                refine ⟨11631645553402073712000709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62035442951477726464003781 11631645553402073712000709)
                ·
                  refine ⟨2180933541262888821000133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11631645553402073712000709 2180933541262888821000133)
                  ·
                    refine ⟨408925038986791653937525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180933541262888821000133 408925038986791653937525)
                    ·
                      rfl

theorem cell22_1194568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1194568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194568 prefixEnd_1194568 := by exact prefixLift 1194568
  have htrace : WordTrace (prefixWord ++ tailWord_1194568) baseStart_1194568 baseEnd_1194568 := by
    simpa [prefixWord, tailWord_1194568, baseEnd_1194568] using wordTrace_append hprefix tailTrace_1194568
  have hstable : (prefixWord ++ tailWord_1194568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194568).length < 2 ^ (prefixWord ++ tailWord_1194568).sum := by decide
  have hdescent : baseEnd_1194568 < baseStart_1194568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194570 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1194570 : Nat := 118140960795 + 1194570 * 2 ^ 59
def prefixEnd_1194570 : Nat := 4983230072969 + 3 ^ 40 * 1194570 * 2
def baseEnd_1194570 : Nat := 408925723627664315387519

theorem tailTrace_1194570 : CollatzResearch.WordTrace tailWord_1194570 prefixEnd_1194570 408925723627664315387519 := by
  unfold tailWord_1194570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10892386820571095289635291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29046364854856254105694109 10892386820571095289635291)
  ·
    refine ⟨16338580230856642934452937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10892386820571095289635291 16338580230856642934452937)
    ·
      refine ⟨12253935173142482200839703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16338580230856642934452937 12253935173142482200839703)
      ·
        refine ⟨18380902759713723301259555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253935173142482200839703 18380902759713723301259555)
        ·
          refine ⟨27571354139570584951889333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18380902759713723301259555 27571354139570584951889333)
          ·
            refine ⟨2584814450584742339239625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27571354139570584951889333 2584814450584742339239625)
            ·
              refine ⟨1938610837938556754429719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584814450584742339239625 1938610837938556754429719)
              ·
                refine ⟨2907916256907835131644579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938610837938556754429719 2907916256907835131644579)
                ·
                  refine ⟨4361874385361752697466869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907916256907835131644579 4361874385361752697466869)
                  ·
                    refine ⟨408925723627664315387519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4361874385361752697466869 408925723627664315387519)
                    ·
                      rfl

theorem cell22_1194570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1194570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194570 prefixEnd_1194570 := by exact prefixLift 1194570
  have htrace : WordTrace (prefixWord ++ tailWord_1194570) baseStart_1194570 baseEnd_1194570 := by
    simpa [prefixWord, tailWord_1194570, baseEnd_1194570] using wordTrace_append hprefix tailTrace_1194570
  have hstable : (prefixWord ++ tailWord_1194570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194570).length < 2 ^ (prefixWord ++ tailWord_1194570).sum := by decide
  have hdescent : baseEnd_1194570 < baseStart_1194570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194600 : List Nat := [2, 1, 4, 3, 2, 1, 9]
def baseStart_1194600 : Nat := 118140960795 + 1194600 * 2 ^ 59
def prefixEnd_1194600 : Nat := 4983230072969 + 3 ^ 40 * 1194600 * 2
def baseEnd_1194600 : Nat := 15145777527435342116201

theorem tailTrace_1194600 : CollatzResearch.WordTrace tailWord_1194600 prefixEnd_1194600 15145777527435342116201 := by
  unfold tailWord_1194600
  simp only [CollatzResearch.WordTrace]
  refine ⟨21785320736087848141066627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29047094314783797521422169 21785320736087848141066627)
  ·
    refine ⟨32677981104131772211599941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21785320736087848141066627 32677981104131772211599941)
    ·
      refine ⟨6127121457024707289674989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32677981104131772211599941 6127121457024707289674989)
      ·
        refine ⟨2297670546384265233628121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6127121457024707289674989 2297670546384265233628121)
        ·
          refine ⟨1723252909788198925221091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2297670546384265233628121 1723252909788198925221091)
          ·
            refine ⟨2584879364682298387831637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723252909788198925221091 2584879364682298387831637)
            ·
              refine ⟨15145777527435342116201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2584879364682298387831637 15145777527435342116201)
              ·
                rfl

theorem cell22_1194600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 9].length) (baseStart_1194600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194600 prefixEnd_1194600 := by exact prefixLift 1194600
  have htrace : WordTrace (prefixWord ++ tailWord_1194600) baseStart_1194600 baseEnd_1194600 := by
    simpa [prefixWord, tailWord_1194600, baseEnd_1194600] using wordTrace_append hprefix tailTrace_1194600
  have hstable : (prefixWord ++ tailWord_1194600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194600).length < 2 ^ (prefixWord ++ tailWord_1194600).sum := by decide
  have hdescent : baseEnd_1194600 < baseStart_1194600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194615 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 3, 3]
def baseStart_1194615 : Nat := 118140960795 + 1194615 * 2 ^ 59
def prefixEnd_1194615 : Nat := 4983230072969 + 3 ^ 40 * 1194615 * 2
def baseEnd_1194615 : Nat := 408941128047299198012381

theorem tailTrace_1194615 : CollatzResearch.WordTrace tailWord_1194615 prefixEnd_1194615 408941128047299198012381 := by
  unfold tailWord_1194615
  simp only [CollatzResearch.WordTrace]
  refine ⟨43571188567121353843929299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29047459044747569229286199 43571188567121353843929299)
  ·
    refine ⟨65356782850682030765893949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43571188567121353843929299 65356782850682030765893949)
    ·
      refine ⟨24508793569005761537210231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65356782850682030765893949 24508793569005761537210231)
      ·
        refine ⟨36763190353508642305815347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24508793569005761537210231 36763190353508642305815347)
        ·
          refine ⟨55144785530262963458723021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36763190353508642305815347 55144785530262963458723021)
          ·
            refine ⟨20679294573848611297021133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55144785530262963458723021 20679294573848611297021133)
            ·
              refine ⟨7754735465193229236382925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20679294573848611297021133 7754735465193229236382925)
              ·
                refine ⟨2908025799447460963643597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7754735465193229236382925 2908025799447460963643597)
                ·
                  refine ⟨1090509674792797861366349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2908025799447460963643597 1090509674792797861366349)
                  ·
                    refine ⟨408941128047299198012381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090509674792797861366349 408941128047299198012381)
                    ·
                      rfl

theorem cell22_1194615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_1194615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194615 prefixEnd_1194615 := by exact prefixLift 1194615
  have htrace : WordTrace (prefixWord ++ tailWord_1194615) baseStart_1194615 baseEnd_1194615 := by
    simpa [prefixWord, tailWord_1194615, baseEnd_1194615] using wordTrace_append hprefix tailTrace_1194615
  have hstable : (prefixWord ++ tailWord_1194615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194615).length < 2 ^ (prefixWord ++ tailWord_1194615).sum := by decide
  have hdescent : baseEnd_1194615 < baseStart_1194615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194634 : List Nat := [3, 1, 2, 3, 4, 1, 2, 6]
def baseStart_1194634 : Nat := 118140960795 + 1194634 * 2 ^ 59
def prefixEnd_1194634 : Nat := 4983230072969 + 3 ^ 40 * 1194634 * 2
def baseEnd_1194634 : Nat := 45438625792843275754147

theorem tailTrace_1194634 : CollatzResearch.WordTrace tailWord_1194634 prefixEnd_1194634 45438625792843275754147 := by
  unfold tailWord_1194634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10892970388513130022217739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29047921036035013392580637 10892970388513130022217739)
  ·
    refine ⟨16339455582769695033326609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10892970388513130022217739 16339455582769695033326609)
    ·
      refine ⟨12254591687077271274994957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16339455582769695033326609 12254591687077271274994957)
      ·
        refine ⟨4595471882653976728123109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12254591687077271274994957 4595471882653976728123109)
        ·
          refine ⟨861650977997620636523083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4595471882653976728123109 861650977997620636523083)
          ·
            refine ⟨1292476466996430954784625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861650977997620636523083 1292476466996430954784625)
            ·
              refine ⟨969357350247323216088469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292476466996430954784625 969357350247323216088469)
              ·
                refine ⟨45438625792843275754147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 969357350247323216088469 45438625792843275754147)
                ·
                  rfl

theorem cell22_1194634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_1194634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194634 prefixEnd_1194634 := by exact prefixLift 1194634
  have htrace : WordTrace (prefixWord ++ tailWord_1194634) baseStart_1194634 baseEnd_1194634 := by
    simpa [prefixWord, tailWord_1194634, baseEnd_1194634] using wordTrace_append hprefix tailTrace_1194634
  have hstable : (prefixWord ++ tailWord_1194634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194634).length < 2 ^ (prefixWord ++ tailWord_1194634).sum := by decide
  have hdescent : baseEnd_1194634 < baseStart_1194634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194679 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 5]
def baseStart_1194679 : Nat := 118140960795 + 1194679 * 2 ^ 59
def prefixEnd_1194679 : Nat := 4983230072969 + 3 ^ 40 * 1194679 * 2
def baseEnd_1194679 : Nat := 136321012185074788137395

theorem tailTrace_1194679 : CollatzResearch.WordTrace tailWord_1194679 prefixEnd_1194679 136321012185074788137395 := by
  unfold tailWord_1194679
  simp only [CollatzResearch.WordTrace]
  refine ⟨43573522838889492774259091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29049015225926328516172727 43573522838889492774259091)
  ·
    refine ⟨65360284258334239161388637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43573522838889492774259091 65360284258334239161388637)
    ·
      refine ⟨24510106596875339685520739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65360284258334239161388637 24510106596875339685520739)
      ·
        refine ⟨36765159895313009528281109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24510106596875339685520739 36765159895313009528281109)
        ·
          refine ⟨1723366870092797321638177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36765159895313009528281109 1723366870092797321638177)
          ·
            refine ⟨1292525152569597991228633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1723366870092797321638177 1292525152569597991228633)
            ·
              refine ⟨969393864427198493421475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292525152569597991228633 969393864427198493421475)
              ·
                refine ⟨1454090796640797740132213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969393864427198493421475 1454090796640797740132213)
                ·
                  refine ⟨136321012185074788137395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1454090796640797740132213 136321012185074788137395)
                  ·
                    rfl

theorem cell22_1194679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 5].length) (baseStart_1194679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194679 prefixEnd_1194679 := by exact prefixLift 1194679
  have htrace : WordTrace (prefixWord ++ tailWord_1194679) baseStart_1194679 baseEnd_1194679 := by
    simpa [prefixWord, tailWord_1194679, baseEnd_1194679] using wordTrace_append hprefix tailTrace_1194679
  have hstable : (prefixWord ++ tailWord_1194679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194679).length < 2 ^ (prefixWord ++ tailWord_1194679).sum := by decide
  have hdescent : baseEnd_1194679 < baseStart_1194679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194692 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1194692 : Nat := 118140960795 + 1194692 * 2 ^ 59
def prefixEnd_1194692 : Nat := 4983230072969 + 3 ^ 40 * 1194692 * 2
def baseEnd_1194692 : Nat := 408967486720896663837145

theorem tailTrace_1194692 : CollatzResearch.WordTrace tailWord_1194692 prefixEnd_1194692 408967486720896663837145 := by
  unfold tailWord_1194692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21786998493921197997241165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29049331325228263996321553 21786998493921197997241165)
  ·
    refine ⟨8170124435220449248965437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21786998493921197997241165 8170124435220449248965437)
    ·
      refine ⟨3063796663207668468362039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8170124435220449248965437 3063796663207668468362039)
      ·
        refine ⟨4595694994811502702543059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063796663207668468362039 4595694994811502702543059)
        ·
          refine ⟨6893542492217254053814589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595694994811502702543059 6893542492217254053814589)
          ·
            refine ⟨2585078434581470270180471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6893542492217254053814589 2585078434581470270180471)
            ·
              refine ⟨3877617651872205405270707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585078434581470270180471 3877617651872205405270707)
              ·
                refine ⟨5816426477808308107906061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877617651872205405270707 5816426477808308107906061)
                ·
                  refine ⟨2181159929178115540464773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5816426477808308107906061 2181159929178115540464773)
                  ·
                    refine ⟨408967486720896663837145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2181159929178115540464773 408967486720896663837145)
                    ·
                      rfl

theorem cell22_1194692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1194692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194692 prefixEnd_1194692 := by exact prefixLift 1194692
  have htrace : WordTrace (prefixWord ++ tailWord_1194692) baseStart_1194692 baseEnd_1194692 := by
    simpa [prefixWord, tailWord_1194692, baseEnd_1194692] using wordTrace_append hprefix tailTrace_1194692
  have hstable : (prefixWord ++ tailWord_1194692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194692).length < 2 ^ (prefixWord ++ tailWord_1194692).sum := by decide
  have hdescent : baseEnd_1194692 < baseStart_1194692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194705 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1194705 : Nat := 118140960795 + 1194705 * 2 ^ 59
def prefixEnd_1194705 : Nat := 4983230072969 + 3 ^ 40 * 1194705 * 2
def baseEnd_1194705 : Nat := 408971936886568963262105

theorem tailTrace_1194705 : CollatzResearch.WordTrace tailWord_1194705 prefixEnd_1194705 408971936886568963262105 := by
  unfold tailWord_1194705
  simp only [CollatzResearch.WordTrace]
  refine ⟨43574471136795299214705569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29049647424530199476470379 43574471136795299214705569)
  ·
    refine ⟨32680853352596474411029177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43574471136795299214705569 32680853352596474411029177)
    ·
      refine ⟨24510640014447355808271883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32680853352596474411029177 24510640014447355808271883)
      ·
        refine ⟨36765960021671033712407825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24510640014447355808271883 36765960021671033712407825)
        ·
          refine ⟨27574470016253275284305869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36765960021671033712407825 27574470016253275284305869)
          ·
            refine ⟨10340426256094978231614701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27574470016253275284305869 10340426256094978231614701)
            ·
              refine ⟨3877659846035616836855513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10340426256094978231614701 3877659846035616836855513)
              ·
                refine ⟨2908244884526712627641635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877659846035616836855513 2908244884526712627641635)
                ·
                  refine ⟨4362367326790068941462453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908244884526712627641635 4362367326790068941462453)
                  ·
                    refine ⟨408971936886568963262105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4362367326790068941462453 408971936886568963262105)
                    ·
                      rfl

theorem cell22_1194705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1194705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194705 prefixEnd_1194705 := by exact prefixLift 1194705
  have htrace : WordTrace (prefixWord ++ tailWord_1194705) baseStart_1194705 baseEnd_1194705 := by
    simpa [prefixWord, tailWord_1194705, baseEnd_1194705] using wordTrace_append hprefix tailTrace_1194705
  have hstable : (prefixWord ++ tailWord_1194705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194705).length < 2 ^ (prefixWord ++ tailWord_1194705).sum := by decide
  have hdescent : baseEnd_1194705 < baseStart_1194705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194724 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1194724 : Nat := 118140960795 + 1194724 * 2 ^ 59
def prefixEnd_1194724 : Nat := 4983230072969 + 3 ^ 40 * 1194724 * 2
def baseEnd_1194724 : Nat := 136326146991619749012349

theorem tailTrace_1194724 : CollatzResearch.WordTrace tailWord_1194724 prefixEnd_1194724 136326146991619749012349 := by
  unfold tailWord_1194724
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787582061863232729823613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29050109415817643639764817 21787582061863232729823613)
  ·
    refine ⟨8170343273198712273683855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21787582061863232729823613 8170343273198712273683855)
    ·
      refine ⟨12255514909798068410525783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8170343273198712273683855 12255514909798068410525783)
      ·
        refine ⟨18383272364697102615788675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12255514909798068410525783 18383272364697102615788675)
        ·
          refine ⟨27574908547045653923683013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18383272364697102615788675 27574908547045653923683013)
          ·
            refine ⟨5170295352571060110690565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27574908547045653923683013 5170295352571060110690565)
            ·
              refine ⟨969430378607073770754481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5170295352571060110690565 969430378607073770754481)
              ·
                refine ⟨727072783955305328065861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969430378607073770754481 727072783955305328065861)
                ·
                  refine ⟨136326146991619749012349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727072783955305328065861 136326146991619749012349)
                  ·
                    rfl

theorem cell22_1194724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1194724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194724 prefixEnd_1194724 := by exact prefixLift 1194724
  have htrace : WordTrace (prefixWord ++ tailWord_1194724) baseStart_1194724 baseEnd_1194724 := by
    simpa [prefixWord, tailWord_1194724, baseEnd_1194724] using wordTrace_append hprefix tailTrace_1194724
  have hstable : (prefixWord ++ tailWord_1194724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194724).length < 2 ^ (prefixWord ++ tailWord_1194724).sum := by decide
  have hdescent : baseEnd_1194724 < baseStart_1194724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194735 : List Nat := [1, 1, 2, 1, 5, 2, 3, 7]
def baseStart_1194735 : Nat := 118140960795 + 1194735 * 2 ^ 59
def prefixEnd_1194735 : Nat := 4983230072969 + 3 ^ 40 * 1194735 * 2
def baseEnd_1194735 : Nat := 45442467388850987223557

theorem tailTrace_1194735 : CollatzResearch.WordTrace tailWord_1194735 prefixEnd_1194735 45442467388850987223557 := by
  unfold tailWord_1194735
  simp only [CollatzResearch.WordTrace]
  refine ⟨43575565326686614338297659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29050376884457742892198439 43575565326686614338297659)
  ·
    refine ⟨65363347990029921507446489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43575565326686614338297659 65363347990029921507446489)
    ·
      refine ⟨49022510992522441130584867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65363347990029921507446489 49022510992522441130584867)
      ·
        refine ⟨73533766488783661695877301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49022510992522441130584867 73533766488783661695877301)
        ·
          refine ⟨6893790608323468283988497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73533766488783661695877301 6893790608323468283988497)
          ·
            refine ⟨5170342956242601212991373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6893790608323468283988497 5170342956242601212991373)
            ·
              refine ⟨1938878608590975454871765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5170342956242601212991373 1938878608590975454871765)
              ·
                refine ⟨45442467388850987223557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1938878608590975454871765 45442467388850987223557)
                ·
                  rfl

theorem cell22_1194735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 7].length) (baseStart_1194735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194735 prefixEnd_1194735 := by exact prefixLift 1194735
  have htrace : WordTrace (prefixWord ++ tailWord_1194735) baseStart_1194735 baseEnd_1194735 := by
    simpa [prefixWord, tailWord_1194735, baseEnd_1194735] using wordTrace_append hprefix tailTrace_1194735
  have hstable : (prefixWord ++ tailWord_1194735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194735).length < 2 ^ (prefixWord ++ tailWord_1194735).sum := by decide
  have hdescent : baseEnd_1194735 < baseStart_1194735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194741 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 6]
def baseStart_1194741 : Nat := 118140960795 + 1194741 * 2 ^ 59
def prefixEnd_1194741 : Nat := 4983230072969 + 3 ^ 40 * 1194741 * 2
def baseEnd_1194741 : Nat := 136328086807425623120665

theorem tailTrace_1194741 : CollatzResearch.WordTrace tailWord_1194741 prefixEnd_1194741 136328086807425623120665 := by
  unfold tailWord_1194741
  simp only [CollatzResearch.WordTrace]
  refine ⟨43575784164664877363016077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29050522776443251575344051 43575784164664877363016077)
  ·
    refine ⟨16340919061749329011131029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43575784164664877363016077 16340919061749329011131029)
    ·
      refine ⟨765980581019499797396767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16340919061749329011131029 765980581019499797396767)
      ·
        refine ⟨1148970871529249696095151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765980581019499797396767 1148970871529249696095151)
        ·
          refine ⟨1723456307293874544142727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148970871529249696095151 1723456307293874544142727)
          ·
            refine ⟨2585184460940811816214091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723456307293874544142727 2585184460940811816214091)
            ·
              refine ⟨3877776691411217724321137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585184460940811816214091 3877776691411217724321137)
              ·
                refine ⟨2908332518558413293240853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877776691411217724321137 2908332518558413293240853)
                ·
                  refine ⟨136328086807425623120665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2908332518558413293240853 136328086807425623120665)
                  ·
                    rfl

theorem cell22_1194741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_1194741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194741 prefixEnd_1194741 := by exact prefixLift 1194741
  have htrace : WordTrace (prefixWord ++ tailWord_1194741) baseStart_1194741 baseEnd_1194741 := by
    simpa [prefixWord, tailWord_1194741, baseEnd_1194741] using wordTrace_append hprefix tailTrace_1194741
  have hstable : (prefixWord ++ tailWord_1194741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194741).length < 2 ^ (prefixWord ++ tailWord_1194741).sum := by decide
  have hdescent : baseEnd_1194741 < baseStart_1194741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194754 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1194754 : Nat := 118140960795 + 1194754 * 2 ^ 59
def prefixEnd_1194754 : Nat := 4983230072969 + 3 ^ 40 * 1194754 * 2
def baseEnd_1194754 : Nat := 408988710587949168786955

theorem tailTrace_1194754 : CollatzResearch.WordTrace tailWord_1194754 prefixEnd_1194754 408988710587949168786955 := by
  unfold tailWord_1194754
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894064578404445145809829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29050838875745187055492877 10894064578404445145809829)
  ·
    refine ⟨2042637108450833464839343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10894064578404445145809829 2042637108450833464839343)
    ·
      refine ⟨3063955662676250197259015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042637108450833464839343 3063955662676250197259015)
      ·
        refine ⟨4595933494014375295888523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063955662676250197259015 4595933494014375295888523)
        ·
          refine ⟨6893900241021562943832785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595933494014375295888523 6893900241021562943832785)
          ·
            refine ⟨5170425180766172207874589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6893900241021562943832785 5170425180766172207874589)
            ·
              refine ⟨1938909442787314577952971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5170425180766172207874589 1938909442787314577952971)
              ·
                refine ⟨2908364164180971866929457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938909442787314577952971 2908364164180971866929457)
                ·
                  refine ⟨2181273123135728900197093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2908364164180971866929457 2181273123135728900197093)
                  ·
                    refine ⟨408988710587949168786955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2181273123135728900197093 408988710587949168786955)
                    ·
                      rfl

theorem cell22_1194754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1194754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194754 prefixEnd_1194754 := by exact prefixLift 1194754
  have htrace : WordTrace (prefixWord ++ tailWord_1194754) baseStart_1194754 baseEnd_1194754 := by
    simpa [prefixWord, tailWord_1194754, baseEnd_1194754] using wordTrace_append hprefix tailTrace_1194754
  have hstable : (prefixWord ++ tailWord_1194754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194754).length < 2 ^ (prefixWord ++ tailWord_1194754).sum := by decide
  have hdescent : baseEnd_1194754 < baseStart_1194754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194784 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_1194784 : Nat := 118140960795 + 1194784 * 2 ^ 59
def prefixEnd_1194784 : Nat := 4983230072969 + 3 ^ 40 * 1194784 * 2
def baseEnd_1194784 : Nat := 408998980201039090536863

theorem tailTrace_1194784 : CollatzResearch.WordTrace tailWord_1194784 prefixEnd_1194784 408998980201039090536863 := by
  unfold tailWord_1194784
  simp only [CollatzResearch.WordTrace]
  refine ⟨21788676251754547853415703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29051568335672730471220937 21788676251754547853415703)
  ·
    refine ⟨32683014377631821780123555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21788676251754547853415703 32683014377631821780123555)
    ·
      refine ⟨49024521566447732670185333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32683014377631821780123555 49024521566447732670185333)
      ·
        refine ⟨4596048896854474937829875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49024521566447732670185333 4596048896854474937829875)
        ·
          refine ⟨6894073345281712406744813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596048896854474937829875 6894073345281712406744813)
          ·
            refine ⟨2585277504480642152529305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6894073345281712406744813 2585277504480642152529305)
            ·
              refine ⟨1938958128360481614396979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2585277504480642152529305 1938958128360481614396979)
              ·
                refine ⟨2908437192540722421595469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938958128360481614396979 2908437192540722421595469)
                ·
                  refine ⟨1090663947202770908098301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2908437192540722421595469 1090663947202770908098301)
                  ·
                    refine ⟨408998980201039090536863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090663947202770908098301 408998980201039090536863)
                    ·
                      rfl

theorem cell22_1194784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_1194784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194784 prefixEnd_1194784 := by exact prefixLift 1194784
  have htrace : WordTrace (prefixWord ++ tailWord_1194784) baseStart_1194784 baseEnd_1194784 := by
    simpa [prefixWord, tailWord_1194784, baseEnd_1194784] using wordTrace_append hprefix tailTrace_1194784
  have hstable : (prefixWord ++ tailWord_1194784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194784).length < 2 ^ (prefixWord ++ tailWord_1194784).sum := by decide
  have hdescent : baseEnd_1194784 < baseStart_1194784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194842 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_1194842 : Nat := 118140960795 + 1194842 * 2 ^ 59
def prefixEnd_1194842 : Nat := 4983230072969 + 3 ^ 40 * 1194842 * 2
def baseEnd_1194842 : Nat := 136339611595448757528895

theorem tailTrace_1194842 : CollatzResearch.WordTrace tailWord_1194842 prefixEnd_1194842 136339611595448757528895 := by
  unfold tailWord_1194842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894866984324742903110695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29052978624865981074961853 10894866984324742903110695)
  ·
    refine ⟨16342300476487114354666043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10894866984324742903110695 16342300476487114354666043)
    ·
      refine ⟨24513450714730671531999065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16342300476487114354666043 24513450714730671531999065)
      ·
        refine ⟨18385088036048003648999299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24513450714730671531999065 18385088036048003648999299)
        ·
          refine ⟨27577632054072005473498949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18385088036048003648999299 27577632054072005473498949)
          ·
            refine ⟨5170806010138501026281053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27577632054072005473498949 5170806010138501026281053)
            ·
              refine ⟨1939052253801937884855395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5170806010138501026281053 1939052253801937884855395)
              ·
                refine ⟨2908578380702906827283093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939052253801937884855395 2908578380702906827283093)
                ·
                  refine ⟨136339611595448757528895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2908578380702906827283093 136339611595448757528895)
                  ·
                    rfl

theorem cell22_1194842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_1194842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194842 prefixEnd_1194842 := by exact prefixLift 1194842
  have htrace : WordTrace (prefixWord ++ tailWord_1194842) baseStart_1194842 baseEnd_1194842 := by
    simpa [prefixWord, tailWord_1194842, baseEnd_1194842] using wordTrace_append hprefix tailTrace_1194842
  have hstable : (prefixWord ++ tailWord_1194842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194842).length < 2 ^ (prefixWord ++ tailWord_1194842).sum := by decide
  have hdescent : baseEnd_1194842 < baseStart_1194842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194936 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 1, 3]
def baseStart_1194936 : Nat := 118140960795 + 1194936 * 2 ^ 59
def prefixEnd_1194936 : Nat := 4983230072969 + 3 ^ 40 * 1194936 * 2
def baseEnd_1194936 : Nat := 409051012907361360736397

theorem tailTrace_1194936 : CollatzResearch.WordTrace tailWord_1194936 prefixEnd_1194936 409051012907361360736397 := by
  unfold tailWord_1194936
  simp only [CollatzResearch.WordTrace]
  refine ⟨21791448199479212833182331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29055264265972283777576441 21791448199479212833182331)
  ·
    refine ⟨32687172299218819249773497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21791448199479212833182331 32687172299218819249773497)
    ·
      refine ⟨24515379224414114437330123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32687172299218819249773497 24515379224414114437330123)
      ·
        refine ⟨36773068836621171655995185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24515379224414114437330123 36773068836621171655995185)
        ·
          refine ⟨27579801627465878741996389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36773068836621171655995185 27579801627465878741996389)
          ·
            refine ⟨5171212805149852264124323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27579801627465878741996389 5171212805149852264124323)
            ·
              refine ⟨7756819207724778396186485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171212805149852264124323 7756819207724778396186485)
              ·
                refine ⟨727201800724197974642483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7756819207724778396186485 727201800724197974642483)
                ·
                  refine ⟨1090802701086296961963725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727201800724197974642483 1090802701086296961963725)
                  ·
                    refine ⟨409051012907361360736397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090802701086296961963725 409051012907361360736397)
                    ·
                      rfl

theorem cell22_1194936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_1194936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194936 prefixEnd_1194936 := by exact prefixLift 1194936
  have htrace : WordTrace (prefixWord ++ tailWord_1194936) baseStart_1194936 baseEnd_1194936 := by
    simpa [prefixWord, tailWord_1194936, baseEnd_1194936] using wordTrace_append hprefix tailTrace_1194936
  have hstable : (prefixWord ++ tailWord_1194936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194936).length < 2 ^ (prefixWord ++ tailWord_1194936).sum := by decide
  have hdescent : baseEnd_1194936 < baseStart_1194936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194964 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1194964 : Nat := 118140960795 + 1194964 * 2 ^ 59
def prefixEnd_1194964 : Nat := 4983230072969 + 3 ^ 40 * 1194964 * 2
def baseEnd_1194964 : Nat := 409060597879578621036311

theorem tailTrace_1194964 : CollatzResearch.WordTrace tailWord_1194964 prefixEnd_1194964 409060597879578621036311 := by
  unfold tailWord_1194964
  simp only [CollatzResearch.WordTrace]
  refine ⟨21791958821428493224191973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29055945095237990965589297 21791958821428493224191973)
  ·
    refine ⟨4085992279017842479535995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21791958821428493224191973 4085992279017842479535995)
    ·
      refine ⟨6128988418526763719303993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4085992279017842479535995 6128988418526763719303993)
      ·
        refine ⟨4596741313895072789477995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6128988418526763719303993 4596741313895072789477995)
        ·
          refine ⟨6895111970842609184216993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596741313895072789477995 6895111970842609184216993)
          ·
            refine ⟨5171333978131956888162745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6895111970842609184216993 5171333978131956888162745)
            ·
              refine ⟨3878500483598967666122059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5171333978131956888162745 3878500483598967666122059)
              ·
                refine ⟨5817750725398451499183089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878500483598967666122059 5817750725398451499183089)
                ·
                  refine ⟨4363313044048838624387317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5817750725398451499183089 4363313044048838624387317)
                  ·
                    refine ⟨409060597879578621036311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4363313044048838624387317 409060597879578621036311)
                    ·
                      rfl

theorem cell22_1194964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1194964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194964 prefixEnd_1194964 := by exact prefixLift 1194964
  have htrace : WordTrace (prefixWord ++ tailWord_1194964) baseStart_1194964 baseEnd_1194964 := by
    simpa [prefixWord, tailWord_1194964, baseEnd_1194964] using wordTrace_append hprefix tailTrace_1194964
  have hstable : (prefixWord ++ tailWord_1194964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194964).length < 2 ^ (prefixWord ++ tailWord_1194964).sum := by decide
  have hdescent : baseEnd_1194964 < baseStart_1194964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194992 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_1194992 : Nat := 118140960795 + 1194992 * 2 ^ 59
def prefixEnd_1194992 : Nat := 4983230072969 + 3 ^ 40 * 1194992 * 2
def baseEnd_1194992 : Nat := 409070182851795881336225

theorem tailTrace_1194992 : CollatzResearch.WordTrace tailWord_1194992 prefixEnd_1194992 409070182851795881336225 := by
  unfold tailWord_1194992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21792469443377773615201615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29056625924503698153602153 21792469443377773615201615)
  ·
    refine ⟨32688704165066660422802423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21792469443377773615201615 32688704165066660422802423)
    ·
      refine ⟨49033056247599990634203635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32688704165066660422802423 49033056247599990634203635)
      ·
        refine ⟨73549584371399985951305453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49033056247599990634203635 73549584371399985951305453)
        ·
          refine ⟨27581094139274994731739545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73549584371399985951305453 27581094139274994731739545)
          ·
            refine ⟨20685820604456246048804659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27581094139274994731739545 20685820604456246048804659)
            ·
              refine ⟨31028730906684369073206989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20685820604456246048804659 31028730906684369073206989)
              ·
                refine ⟨11635774090006638402452621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31028730906684369073206989 11635774090006638402452621)
                ·
                  refine ⟨4363415283752489400919733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11635774090006638402452621 4363415283752489400919733)
                  ·
                    refine ⟨409070182851795881336225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4363415283752489400919733 409070182851795881336225)
                    ·
                      rfl

theorem cell22_1194992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_1194992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1194992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1194992 prefixEnd_1194992 := by exact prefixLift 1194992
  have htrace : WordTrace (prefixWord ++ tailWord_1194992) baseStart_1194992 baseEnd_1194992 := by
    simpa [prefixWord, tailWord_1194992, baseEnd_1194992] using wordTrace_append hprefix tailTrace_1194992
  have hstable : (prefixWord ++ tailWord_1194992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194992).length < 2 ^ (prefixWord ++ tailWord_1194992).sum := by decide
  have hdescent : baseEnd_1194992 < baseStart_1194992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195041 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1195041 : Nat := 118140960795 + 1195041 * 2 ^ 59
def prefixEnd_1195041 : Nat := 4983230072969 + 3 ^ 40 * 1195041 * 2
def baseEnd_1195041 : Nat := 409086956553176086861075

theorem tailTrace_1195041 : CollatzResearch.WordTrace tailWord_1195041 prefixEnd_1195041 409086956553176086861075 := by
  unfold tailWord_1195041
  simp only [CollatzResearch.WordTrace]
  refine ⟨43586726063578028598936977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29057817375718685732624651 43586726063578028598936977)
  ·
    refine ⟨32690044547683521449202733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43586726063578028598936977 32690044547683521449202733)
    ·
      refine ⟨12258766705381320543451025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32690044547683521449202733 12258766705381320543451025)
      ·
        refine ⟨9194075029035990407588269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12258766705381320543451025 9194075029035990407588269)
        ·
          refine ⟨3447778135888496402845601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9194075029035990407588269 3447778135888496402845601)
          ·
            refine ⟨2585833601916372302134201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447778135888496402845601 2585833601916372302134201)
            ·
              refine ⟨1939375201437279226600651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2585833601916372302134201 1939375201437279226600651)
              ·
                refine ⟨2909062802155918839900977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939375201437279226600651 2909062802155918839900977)
                ·
                  refine ⟨2181797101616939129925733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2909062802155918839900977 2181797101616939129925733)
                  ·
                    refine ⟨409086956553176086861075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2181797101616939129925733 409086956553176086861075)
                    ·
                      rfl

theorem cell22_1195041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1195041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195041 prefixEnd_1195041 := by exact prefixLift 1195041
  have htrace : WordTrace (prefixWord ++ tailWord_1195041) baseStart_1195041 baseEnd_1195041 := by
    simpa [prefixWord, tailWord_1195041, baseEnd_1195041] using wordTrace_append hprefix tailTrace_1195041
  have hstable : (prefixWord ++ tailWord_1195041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195041).length < 2 ^ (prefixWord ++ tailWord_1195041).sum := by decide
  have hdescent : baseEnd_1195041 < baseStart_1195041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195060 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1195060 : Nat := 118140960795 + 1195060 * 2 ^ 59
def prefixEnd_1195060 : Nat := 4983230072969 + 3 ^ 40 * 1195060 * 2
def baseEnd_1195060 : Nat := 409093460641466370636017

theorem tailTrace_1195060 : CollatzResearch.WordTrace tailWord_1195060 prefixEnd_1195060 409093460641466370636017 := by
  unfold tailWord_1195060
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793709525254597421939317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29058279367006129895919089 21793709525254597421939317)
  ·
    refine ⟨2043160267992618508306811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21793709525254597421939317 2043160267992618508306811)
    ·
      refine ⟨3064740401988927762460217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043160267992618508306811 3064740401988927762460217)
      ·
        refine ⟨2298555301491695821845163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3064740401988927762460217 2298555301491695821845163)
        ·
          refine ⟨3447832952237543732767745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298555301491695821845163 3447832952237543732767745)
          ·
            refine ⟨2585874714178157799575809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447832952237543732767745 2585874714178157799575809)
            ·
              refine ⟨1939406035633618349681857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2585874714178157799575809 1939406035633618349681857)
              ·
                refine ⟨1454554526725213762261393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1939406035633618349681857 1454554526725213762261393)
                ·
                  refine ⟨1090915895043910321696045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1454554526725213762261393 1090915895043910321696045)
                  ·
                    refine ⟨409093460641466370636017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1090915895043910321696045 409093460641466370636017)
                    ·
                      rfl

theorem cell22_1195060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1195060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195060 prefixEnd_1195060 := by exact prefixLift 1195060
  have htrace : WordTrace (prefixWord ++ tailWord_1195060) baseStart_1195060 baseEnd_1195060 := by
    simpa [prefixWord, tailWord_1195060, baseEnd_1195060] using wordTrace_append hprefix tailTrace_1195060
  have hstable : (prefixWord ++ tailWord_1195060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195060).length < 2 ^ (prefixWord ++ tailWord_1195060).sum := by decide
  have hdescent : baseEnd_1195060 < baseStart_1195060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195069 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1195069 : Nat := 118140960795 + 1195069 * 2 ^ 59
def prefixEnd_1195069 : Nat := 4983230072969 + 3 ^ 40 * 1195069 * 2
def baseEnd_1195069 : Nat := 409096541525393347160989

theorem tailTrace_1195069 : CollatzResearch.WordTrace tailWord_1195069 prefixEnd_1195069 409096541525393347160989 := by
  unfold tailWord_1195069
  simp only [CollatzResearch.WordTrace]
  refine ⟨43587747307476589380956261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29058498204984392920637507 43587747307476589380956261)
  ·
    refine ⟨8172702620151860508929299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43587747307476589380956261 8172702620151860508929299)
    ·
      refine ⟨12259053930227790763393949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8172702620151860508929299 12259053930227790763393949)
      ·
        refine ⟨4597145223835421536272731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12259053930227790763393949 4597145223835421536272731)
        ·
          refine ⟨6895717835753132304409097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597145223835421536272731 6895717835753132304409097)
          ·
            refine ⟨5171788376814849228306823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6895717835753132304409097 5171788376814849228306823)
            ·
              refine ⟨7757682565222273842460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171788376814849228306823 7757682565222273842460235)
              ·
                refine ⟨11636523847833410763690353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757682565222273842460235 11636523847833410763690353)
                ·
                  refine ⟨8727392885875058072767765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11636523847833410763690353 8727392885875058072767765)
                  ·
                    refine ⟨409096541525393347160989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8727392885875058072767765 409096541525393347160989)
                    ·
                      rfl

theorem cell22_1195069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1195069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195069 prefixEnd_1195069 := by exact prefixLift 1195069
  have htrace : WordTrace (prefixWord ++ tailWord_1195069) baseStart_1195069 baseEnd_1195069 := by
    simpa [prefixWord, tailWord_1195069, baseEnd_1195069] using wordTrace_append hprefix tailTrace_1195069
  have hstable : (prefixWord ++ tailWord_1195069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195069).length < 2 ^ (prefixWord ++ tailWord_1195069).sum := by decide
  have hdescent : baseEnd_1195069 < baseStart_1195069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195073 : List Nat := [1, 2, 5, 1, 4, 1, 1, 7]
def baseStart_1195073 : Nat := 118140960795 + 1195073 * 2 ^ 59
def prefixEnd_1195073 : Nat := 4983230072969 + 3 ^ 40 * 1195073 * 2
def baseEnd_1195073 : Nat := 45455323423015407784553

theorem tailTrace_1195073 : CollatzResearch.WordTrace tailWord_1195073 prefixEnd_1195073 45455323423015407784553 := by
  unfold tailWord_1195073
  simp only [CollatzResearch.WordTrace]
  refine ⟨43587893199462098064101873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29058595466308065376067915 43587893199462098064101873)
  ·
    refine ⟨32690919899596573548076405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43587893199462098064101873 32690919899596573548076405)
    ·
      refine ⟨3064773740587178770132163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32690919899596573548076405 3064773740587178770132163)
      ·
        refine ⟨4597160610880768155198245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3064773740587178770132163 4597160610880768155198245)
        ·
          refine ⟨861967614540144029099671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4597160610880768155198245 861967614540144029099671)
          ·
            refine ⟨1292951421810216043649507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861967614540144029099671 1292951421810216043649507)
            ·
              refine ⟨1939427132715324065474261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292951421810216043649507 1939427132715324065474261)
              ·
                refine ⟨45455323423015407784553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1939427132715324065474261 45455323423015407784553)
                ·
                  rfl

theorem cell22_1195073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 7].length) (baseStart_1195073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195073 prefixEnd_1195073 := by exact prefixLift 1195073
  have htrace : WordTrace (prefixWord ++ tailWord_1195073) baseStart_1195073 baseEnd_1195073 := by
    simpa [prefixWord, tailWord_1195073, baseEnd_1195073] using wordTrace_append hprefix tailTrace_1195073
  have hstable : (prefixWord ++ tailWord_1195073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195073).length < 2 ^ (prefixWord ++ tailWord_1195073).sum := by decide
  have hdescent : baseEnd_1195073 < baseStart_1195073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195118 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_1195118 : Nat := 118140960795 + 1195118 * 2 ^ 59
def prefixEnd_1195118 : Nat := 4983230072969 + 3 ^ 40 * 1195118 * 2
def baseEnd_1195118 : Nat := 136371105075591184228613

theorem tailTrace_1195118 : CollatzResearch.WordTrace tailWord_1195118 prefixEnd_1195118 136371105075591184228613 := by
  unfold tailWord_1195118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448691810537383843686251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29059689656199380499660005 5448691810537383843686251)
  ·
    refine ⟨8173037715806075765529377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5448691810537383843686251 8173037715806075765529377)
    ·
      refine ⟨6129778286854556824147033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8173037715806075765529377 6129778286854556824147033)
      ·
        refine ⟨4597333715140917618110275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6129778286854556824147033 4597333715140917618110275)
        ·
          refine ⟨6896000572711376427165413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597333715140917618110275 6896000572711376427165413)
          ·
            refine ⟨1293000107383383080093515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6896000572711376427165413 1293000107383383080093515)
            ·
              refine ⟨1939500161075074620140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293000107383383080093515 1939500161075074620140273)
              ·
                refine ⟨1454625120806305965105205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1939500161075074620140273 1454625120806305965105205)
                ·
                  refine ⟨136371105075591184228613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1454625120806305965105205 136371105075591184228613)
                  ·
                    rfl

theorem cell22_1195118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_1195118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195118 prefixEnd_1195118 := by exact prefixLift 1195118
  have htrace : WordTrace (prefixWord ++ tailWord_1195118) baseStart_1195118 baseEnd_1195118 := by
    simpa [prefixWord, tailWord_1195118, baseEnd_1195118] using wordTrace_append hprefix tailTrace_1195118
  have hstable : (prefixWord ++ tailWord_1195118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195118).length < 2 ^ (prefixWord ++ tailWord_1195118).sum := by decide
  have hdescent : baseEnd_1195118 < baseStart_1195118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195236 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1195236 : Nat := 118140960795 + 1195236 * 2 ^ 59
def prefixEnd_1195236 : Nat := 4983230072969 + 3 ^ 40 * 1195236 * 2
def baseEnd_1195236 : Nat := 136384569679420192745159

theorem tailTrace_1195236 : CollatzResearch.WordTrace tailWord_1195236 prefixEnd_1195236 136384569679420192745159 := by
  unfold tailWord_1195236
  simp only [CollatzResearch.WordTrace]
  refine ⟨21796919148935788451142781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29062558865247717934857041 21796919148935788451142781)
  ·
    refine ⟨8173844680850920669178543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21796919148935788451142781 8173844680850920669178543)
    ·
      refine ⟨12260767021276381003767815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8173844680850920669178543 12260767021276381003767815)
      ·
        refine ⟨18391150531914571505651723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12260767021276381003767815 18391150531914571505651723)
        ·
          refine ⟨27586725797871857258477585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18391150531914571505651723 27586725797871857258477585)
          ·
            refine ⟨20690044348403892943858189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27586725797871857258477585 20690044348403892943858189)
            ·
              refine ⟨7758766630651459853946821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20690044348403892943858189 7758766630651459853946821)
              ·
                refine ⟨1454768743247148722615029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7758766630651459853946821 1454768743247148722615029)
                ·
                  refine ⟨136384569679420192745159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1454768743247148722615029 136384569679420192745159)
                  ·
                    rfl

theorem cell22_1195236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1195236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195236 prefixEnd_1195236 := by exact prefixLift 1195236
  have htrace : WordTrace (prefixWord ++ tailWord_1195236) baseStart_1195236 baseEnd_1195236 := by
    simpa [prefixWord, tailWord_1195236, baseEnd_1195236] using wordTrace_append hprefix tailTrace_1195236
  have hstable : (prefixWord ++ tailWord_1195236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195236).length < 2 ^ (prefixWord ++ tailWord_1195236).sum := by decide
  have hdescent : baseEnd_1195236 < baseStart_1195236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195240 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1195240 : Nat := 118140960795 + 1195240 * 2 ^ 59
def prefixEnd_1195240 : Nat := 4983230072969 + 3 ^ 40 * 1195240 * 2
def baseEnd_1195240 : Nat := 409155078320005901135465

theorem tailTrace_1195240 : CollatzResearch.WordTrace tailWord_1195240 prefixEnd_1195240 409155078320005901135465 := by
  unfold tailWord_1195240
  simp only [CollatzResearch.WordTrace]
  refine ⟨21796992094928542792715587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29062656126571390390287449 21796992094928542792715587)
  ·
    refine ⟨32695488142392814189073381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21796992094928542792715587 32695488142392814189073381)
    ·
      refine ⟨6130404026698652660451259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32695488142392814189073381 6130404026698652660451259)
      ·
        refine ⟨9195606040047978990676889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130404026698652660451259 9195606040047978990676889)
        ·
          refine ⟨6896704530035984243007667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9195606040047978990676889 6896704530035984243007667)
          ·
            refine ⟨10345056795053976364511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896704530035984243007667 10345056795053976364511501)
            ·
              refine ⟨3879396298145241136691813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10345056795053976364511501 3879396298145241136691813)
              ·
                refine ⟨727386805902232713129715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3879396298145241136691813 727386805902232713129715)
                ·
                  refine ⟨1091080208853349069694573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727386805902232713129715 1091080208853349069694573)
                  ·
                    refine ⟨409155078320005901135465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091080208853349069694573 409155078320005901135465)
                    ·
                      rfl

theorem cell22_1195240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1195240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195240 prefixEnd_1195240 := by exact prefixLift 1195240
  have htrace : WordTrace (prefixWord ++ tailWord_1195240) baseStart_1195240 baseEnd_1195240 := by
    simpa [prefixWord, tailWord_1195240, baseEnd_1195240] using wordTrace_append hprefix tailTrace_1195240
  have hstable : (prefixWord ++ tailWord_1195240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195240).length < 2 ^ (prefixWord ++ tailWord_1195240).sum := by decide
  have hdescent : baseEnd_1195240 < baseStart_1195240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195251 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_1195251 : Nat := 118140960795 + 1195251 * 2 ^ 59
def prefixEnd_1195251 : Nat := 4983230072969 + 3 ^ 40 * 1195251 * 2
def baseEnd_1195251 : Nat := 409158843844805539110431

theorem tailTrace_1195251 : CollatzResearch.WordTrace tailWord_1195251 prefixEnd_1195251 409158843844805539110431 := by
  unfold tailWord_1195251
  simp only [CollatzResearch.WordTrace]
  refine ⟨43594385392817234464081607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29062923595211489642721071 43594385392817234464081607)
  ·
    refine ⟨65391578089225851696122411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43594385392817234464081607 65391578089225851696122411)
    ·
      refine ⟨98087367133838777544183617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65391578089225851696122411 98087367133838777544183617)
      ·
        refine ⟨73565525350379083158137713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98087367133838777544183617 73565525350379083158137713)
        ·
          refine ⟨55174144012784312368603285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73565525350379083158137713 55174144012784312368603285)
          ·
            refine ⟨2586288000599264642278279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55174144012784312368603285 2586288000599264642278279)
            ·
              refine ⟨3879432000898896963417419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586288000599264642278279 3879432000898896963417419)
              ·
                refine ⟨5819148001348345445126129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879432000898896963417419 5819148001348345445126129)
                ·
                  refine ⟨4364361001011259083844597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5819148001348345445126129 4364361001011259083844597)
                  ·
                    refine ⟨409158843844805539110431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4364361001011259083844597 409158843844805539110431)
                    ·
                      rfl

theorem cell22_1195251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_1195251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195251 prefixEnd_1195251 := by exact prefixLift 1195251
  have htrace : WordTrace (prefixWord ++ tailWord_1195251) baseStart_1195251 baseEnd_1195251 := by
    simpa [prefixWord, tailWord_1195251, baseEnd_1195251] using wordTrace_append hprefix tailTrace_1195251
  have hstable : (prefixWord ++ tailWord_1195251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195251).length < 2 ^ (prefixWord ++ tailWord_1195251).sum := by decide
  have hdescent : baseEnd_1195251 < baseStart_1195251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195313 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_1195313 : Nat := 118140960795 + 1195313 * 2 ^ 59
def prefixEnd_1195313 : Nat := 4983230072969 + 3 ^ 40 * 1195313 * 2
def baseEnd_1195313 : Nat := 409180067711858044060241

theorem tailTrace_1195313 : CollatzResearch.WordTrace tailWord_1195313 prefixEnd_1195313 409180067711858044060241 := by
  unfold tailWord_1195313
  simp only [CollatzResearch.WordTrace]
  refine ⟨43596646718592619052838593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29064431145728412701892395 43596646718592619052838593)
  ·
    refine ⟨32697485038944464289628945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43596646718592619052838593 32697485038944464289628945)
    ·
      refine ⟨24523113779208348217221709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32697485038944464289628945 24523113779208348217221709)
      ·
        refine ⟨9196167667203130581458141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24523113779208348217221709 9196167667203130581458141)
        ·
          refine ⟨3448562875201173968046803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9196167667203130581458141 3448562875201173968046803)
          ·
            refine ⟨5172844312801760952070205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448562875201173968046803 5172844312801760952070205)
            ·
              refine ⟨1939816617300660357026327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5172844312801760952070205 1939816617300660357026327)
              ·
                refine ⟨2909724925950990535539491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939816617300660357026327 2909724925950990535539491)
                ·
                  refine ⟨4364587388926485803309237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909724925950990535539491 4364587388926485803309237)
                  ·
                    refine ⟨409180067711858044060241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4364587388926485803309237 409180067711858044060241)
                    ·
                      rfl

theorem cell22_1195313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_1195313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195313 prefixEnd_1195313 := by exact prefixLift 1195313
  have htrace : WordTrace (prefixWord ++ tailWord_1195313) baseStart_1195313 baseEnd_1195313 := by
    simpa [prefixWord, tailWord_1195313, baseEnd_1195313] using wordTrace_append hprefix tailTrace_1195313
  have hstable : (prefixWord ++ tailWord_1195313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195313).length < 2 ^ (prefixWord ++ tailWord_1195313).sum := by decide
  have hdescent : baseEnd_1195313 < baseStart_1195313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195332 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_1195332 : Nat := 118140960795 + 1195332 * 2 ^ 59
def prefixEnd_1195332 : Nat := 4983230072969 + 3 ^ 40 * 1195332 * 2
def baseEnd_1195332 : Nat := 136395523933382775945061

theorem tailTrace_1195332 : CollatzResearch.WordTrace tailWord_1195332 prefixEnd_1195332 136395523933382775945061 := by
  unfold tailWord_1195332
  simp only [CollatzResearch.WordTrace]
  refine ⟨21798669852761892648890125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29064893137015856865186833 21798669852761892648890125)
  ·
    refine ⟨8174501194785709743333797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21798669852761892648890125 8174501194785709743333797)
    ·
      refine ⟨1532718974022320576875087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8174501194785709743333797 1532718974022320576875087)
      ·
        refine ⟨2299078461033480865312631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532718974022320576875087 2299078461033480865312631)
        ·
          refine ⟨3448617691550221297968947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299078461033480865312631 3448617691550221297968947)
          ·
            refine ⟨5172926537325331946953421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448617691550221297968947 5172926537325331946953421)
            ·
              refine ⟨1939847451496999480107533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5172926537325331946953421 1939847451496999480107533)
              ·
                refine ⟨727442794311374805040325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1939847451496999480107533 727442794311374805040325)
                ·
                  refine ⟨136395523933382775945061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727442794311374805040325 136395523933382775945061)
                  ·
                    rfl

theorem cell22_1195332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_1195332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195332 prefixEnd_1195332 := by exact prefixLift 1195332
  have htrace : WordTrace (prefixWord ++ tailWord_1195332) baseStart_1195332 baseEnd_1195332 := by
    simpa [prefixWord, tailWord_1195332, baseEnd_1195332] using wordTrace_append hprefix tailTrace_1195332
  have hstable : (prefixWord ++ tailWord_1195332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195332).length < 2 ^ (prefixWord ++ tailWord_1195332).sum := by decide
  have hdescent : baseEnd_1195332 < baseStart_1195332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195386 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1195386 : Nat := 118140960795 + 1195386 * 2 ^ 59
def prefixEnd_1195386 : Nat := 4983230072969 + 3 ^ 40 * 1195386 * 2
def baseEnd_1195386 : Nat := 409205057103710186985017

theorem tailTrace_1195386 : CollatzResearch.WordTrace tailWord_1195386 prefixEnd_1195386 409205057103710186985017 := by
  unfold tailWord_1195386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899827311832038130061503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29066206164885435013497341 10899827311832038130061503)
  ·
    refine ⟨16349740967748057195092255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10899827311832038130061503 16349740967748057195092255)
    ·
      refine ⟨24524611451622085792638383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16349740967748057195092255 24524611451622085792638383)
      ·
        refine ⟨36786917177433128688957575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24524611451622085792638383 36786917177433128688957575)
        ·
          refine ⟨55180375766149693033436363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36786917177433128688957575 55180375766149693033436363)
          ·
            refine ⟨82770563649224539550154545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55180375766149693033436363 82770563649224539550154545)
            ·
              refine ⟨62077922736918404662615909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82770563649224539550154545 62077922736918404662615909)
              ·
                refine ⟨11639610513172200874240483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62077922736918404662615909 11639610513172200874240483)
                ·
                  refine ⟨17459415769758301311360725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11639610513172200874240483 17459415769758301311360725)
                  ·
                    refine ⟨409205057103710186985017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17459415769758301311360725 409205057103710186985017)
                    ·
                      rfl

theorem cell22_1195386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1195386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195386 prefixEnd_1195386 := by exact prefixLift 1195386
  have htrace : WordTrace (prefixWord ++ tailWord_1195386) baseStart_1195386 baseEnd_1195386 := by
    simpa [prefixWord, tailWord_1195386, baseEnd_1195386] using wordTrace_append hprefix tailTrace_1195386
  have hstable : (prefixWord ++ tailWord_1195386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195386).length < 2 ^ (prefixWord ++ tailWord_1195386).sum := by decide
  have hdescent : baseEnd_1195386 < baseStart_1195386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195418 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_1195418 : Nat := 118140960795 + 1195418 * 2 ^ 59
def prefixEnd_1195418 : Nat := 4983230072969 + 3 ^ 40 * 1195418 * 2
def baseEnd_1195418 : Nat := 409216011357672770184919

theorem tailTrace_1195418 : CollatzResearch.WordTrace tailWord_1195418 prefixEnd_1195418 409216011357672770184919 := by
  unfold tailWord_1195418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10900119095803055496352727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29066984255474814656940605 10900119095803055496352727)
  ·
    refine ⟨16350178643704583244529091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10900119095803055496352727 16350178643704583244529091)
    ·
      refine ⟨24525267965556874866793637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16350178643704583244529091 24525267965556874866793637)
      ·
        refine ⟨4598487743541914037523807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24525267965556874866793637 4598487743541914037523807)
        ·
          refine ⟨6897731615312871056285711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598487743541914037523807 6897731615312871056285711)
          ·
            refine ⟨10346597422969306584428567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897731615312871056285711 10346597422969306584428567)
            ·
              refine ⟨15519896134453959876642851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10346597422969306584428567 15519896134453959876642851)
              ·
                refine ⟨23279844201680939814964277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15519896134453959876642851 23279844201680939814964277)
                ·
                  refine ⟨2182485393907588107652901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23279844201680939814964277 2182485393907588107652901)
                  ·
                    refine ⟨409216011357672770184919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182485393907588107652901 409216011357672770184919)
                    ·
                      rfl

theorem cell22_1195418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_1195418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195418 prefixEnd_1195418 := by exact prefixLift 1195418
  have htrace : WordTrace (prefixWord ++ tailWord_1195418) baseStart_1195418 baseEnd_1195418 := by
    simpa [prefixWord, tailWord_1195418, baseEnd_1195418] using wordTrace_append hprefix tailTrace_1195418
  have hstable : (prefixWord ++ tailWord_1195418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195418).length < 2 ^ (prefixWord ++ tailWord_1195418).sum := by decide
  have hdescent : baseEnd_1195418 < baseStart_1195418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195448 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1195448 : Nat := 118140960795 + 1195448 * 2 ^ 59
def prefixEnd_1195448 : Nat := 4983230072969 + 3 ^ 40 * 1195448 * 2
def baseEnd_1195448 : Nat := 409226280970762691934827

theorem tailTrace_1195448 : CollatzResearch.WordTrace tailWord_1195448 prefixEnd_1195448 409226280970762691934827 := by
  unfold tailWord_1195448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21800785286551768554501499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29067713715402358072668665 21800785286551768554501499)
  ·
    refine ⟨32701177929827652831752249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21800785286551768554501499 32701177929827652831752249)
    ·
      refine ⟨24525883447370739623814187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32701177929827652831752249 24525883447370739623814187)
      ·
        refine ⟨36788825171056109435721281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24525883447370739623814187 36788825171056109435721281)
        ·
          refine ⟨27591618878292082076790961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36788825171056109435721281 27591618878292082076790961)
          ·
            refine ⟨20693714158719061557593221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27591618878292082076790961 20693714158719061557593221)
            ·
              refine ⟨3880071404759824042048729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20693714158719061557593221 3880071404759824042048729)
              ·
                refine ⟨2910053553569868031536547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880071404759824042048729 2910053553569868031536547)
                ·
                  refine ⟨4365080330354802047304821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910053553569868031536547 4365080330354802047304821)
                  ·
                    refine ⟨409226280970762691934827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4365080330354802047304821 409226280970762691934827)
                    ·
                      rfl

theorem cell22_1195448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1195448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195448 prefixEnd_1195448 := by exact prefixLift 1195448
  have htrace : WordTrace (prefixWord ++ tailWord_1195448) baseStart_1195448 baseEnd_1195448 := by
    simpa [prefixWord, tailWord_1195448, baseEnd_1195448] using wordTrace_append hprefix tailTrace_1195448
  have hstable : (prefixWord ++ tailWord_1195448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195448).length < 2 ^ (prefixWord ++ tailWord_1195448).sum := by decide
  have hdescent : baseEnd_1195448 < baseStart_1195448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195452 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1195452 : Nat := 118140960795 + 1195452 * 2 ^ 59
def prefixEnd_1195452 : Nat := 4983230072969 + 3 ^ 40 * 1195452 * 2
def baseEnd_1195452 : Nat := 409227650252508014834815

theorem tailTrace_1195452 : CollatzResearch.WordTrace tailWord_1195452 prefixEnd_1195452 409227650252508014834815 := by
  unfold tailWord_1195452
  simp only [CollatzResearch.WordTrace]
  refine ⟨21800858232544522896074305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29067810976726030528099073 21800858232544522896074305)
  ·
    refine ⟨16350643674408392172055729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21800858232544522896074305 16350643674408392172055729)
    ·
      refine ⟨12262982755806294129041797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16350643674408392172055729 12262982755806294129041797)
      ·
        refine ⟨2299309266713680149195337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12262982755806294129041797 2299309266713680149195337)
        ·
          refine ⟨1724481950035260111896503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299309266713680149195337 1724481950035260111896503)
          ·
            refine ⟨2586722925052890167844755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724481950035260111896503 2586722925052890167844755)
            ·
              refine ⟨3880084387579335251767133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586722925052890167844755 3880084387579335251767133)
              ·
                refine ⟨1455031645342250719412675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3880084387579335251767133 1455031645342250719412675)
                ·
                  refine ⟨2182547468013376079119013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455031645342250719412675 2182547468013376079119013)
                  ·
                    refine ⟨409227650252508014834815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182547468013376079119013 409227650252508014834815)
                    ·
                      rfl

theorem cell22_1195452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1195452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195452 prefixEnd_1195452 := by exact prefixLift 1195452
  have htrace : WordTrace (prefixWord ++ tailWord_1195452) baseStart_1195452 baseEnd_1195452 := by
    simpa [prefixWord, tailWord_1195452, baseEnd_1195452] using wordTrace_append hprefix tailTrace_1195452
  have hstable : (prefixWord ++ tailWord_1195452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195452).length < 2 ^ (prefixWord ++ tailWord_1195452).sum := by decide
  have hdescent : baseEnd_1195452 < baseStart_1195452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195463 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1195463 : Nat := 118140960795 + 1195463 * 2 ^ 59
def prefixEnd_1195463 : Nat := 4983230072969 + 3 ^ 40 * 1195463 * 2
def baseEnd_1195463 : Nat := 409231415777307652809781

theorem tailTrace_1195463 : CollatzResearch.WordTrace tailWord_1195463 prefixEnd_1195463 409231415777307652809781 := by
  unfold tailWord_1195463
  simp only [CollatzResearch.WordTrace]
  refine ⟨43602117668049194670799043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29068078445366129780532695 43602117668049194670799043)
  ·
    refine ⟨65403176502073792006198565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43602117668049194670799043 65403176502073792006198565)
    ·
      refine ⟨12263095594138836001162231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65403176502073792006198565 12263095594138836001162231)
      ·
        refine ⟨18394643391208254001743347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12263095594138836001162231 18394643391208254001743347)
        ·
          refine ⟨27591965086812381002615021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18394643391208254001743347 27591965086812381002615021)
          ·
            refine ⟨10346986907554642875980633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27591965086812381002615021 10346986907554642875980633)
            ·
              refine ⟨7760240180665982156985475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10346986907554642875980633 7760240180665982156985475)
              ·
                refine ⟨11640360270998973235478213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760240180665982156985475 11640360270998973235478213)
                ·
                  refine ⟨2182567550812307481652165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11640360270998973235478213 2182567550812307481652165)
                  ·
                    refine ⟨409231415777307652809781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182567550812307481652165 409231415777307652809781)
                    ·
                      rfl

theorem cell22_1195463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1195463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195463 prefixEnd_1195463 := by exact prefixLift 1195463
  have htrace : WordTrace (prefixWord ++ tailWord_1195463) baseStart_1195463 baseEnd_1195463 := by
    simpa [prefixWord, tailWord_1195463, baseEnd_1195463] using wordTrace_append hprefix tailTrace_1195463
  have hstable : (prefixWord ++ tailWord_1195463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195463).length < 2 ^ (prefixWord ++ tailWord_1195463).sum := by decide
  have hdescent : baseEnd_1195463 < baseStart_1195463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195495 : List Nat := [1, 1, 5, 2, 1, 2, 4, 6]
def baseStart_1195495 : Nat := 118140960795 + 1195495 * 2 ^ 59
def prefixEnd_1195495 : Nat := 4983230072969 + 3 ^ 40 * 1195495 * 2
def baseEnd_1195495 : Nat := 45471374447918915112187

theorem tailTrace_1195495 : CollatzResearch.WordTrace tailWord_1195495 prefixEnd_1195495 45471374447918915112187 := by
  unfold tailWord_1195495
  simp only [CollatzResearch.WordTrace]
  refine ⟨43603284803933264135963939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29068856535955509423975959 43603284803933264135963939)
  ·
    refine ⟨65404927205899896203945909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43603284803933264135963939 65404927205899896203945909)
    ·
      refine ⟨6131711925553115269119929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65404927205899896203945909 6131711925553115269119929)
      ·
        refine ⟨4598783944164836451839947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6131711925553115269119929 4598783944164836451839947)
        ·
          refine ⟨6898175916247254677759921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598783944164836451839947 6898175916247254677759921)
          ·
            refine ⟨5173631937185441008319941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6898175916247254677759921 5173631937185441008319941)
            ·
              refine ⟨970055988222270189059989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5173631937185441008319941 970055988222270189059989)
              ·
                refine ⟨45471374447918915112187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 970055988222270189059989 45471374447918915112187)
                ·
                  rfl

theorem cell22_1195495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 6].length) (baseStart_1195495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195495 prefixEnd_1195495 := by exact prefixLift 1195495
  have htrace : WordTrace (prefixWord ++ tailWord_1195495) baseStart_1195495 baseEnd_1195495 := by
    simpa [prefixWord, tailWord_1195495, baseEnd_1195495] using wordTrace_append hprefix tailTrace_1195495
  have hstable : (prefixWord ++ tailWord_1195495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195495).length < 2 ^ (prefixWord ++ tailWord_1195495).sum := by decide
  have hdescent : baseEnd_1195495 < baseStart_1195495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195501 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1195501 : Nat := 118140960795 + 1195501 * 2 ^ 59
def prefixEnd_1195501 : Nat := 4983230072969 + 3 ^ 40 * 1195501 * 2
def baseEnd_1195501 : Nat := 136414807984629406786555

theorem tailTrace_1195501 : CollatzResearch.WordTrace tailWord_1195501 prefixEnd_1195501 136414807984629406786555 := by
  unfold tailWord_1195501
  simp only [CollatzResearch.WordTrace]
  refine ⟨43603503641911527160682357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29069002427941018107121571 43603503641911527160682357)
  ·
    refine ⟨4087828466429205671313971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43603503641911527160682357 4087828466429205671313971)
    ·
      refine ⟨6131742699643808506970957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4087828466429205671313971 6131742699643808506970957)
      ·
        refine ⟨2299403512366428190114109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6131742699643808506970957 2299403512366428190114109)
        ·
          refine ⟨862276317137410571292791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2299403512366428190114109 862276317137410571292791)
          ·
            refine ⟨1293414475706115856939187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862276317137410571292791 1293414475706115856939187)
            ·
              refine ⟨1940121713559173785408781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293414475706115856939187 1940121713559173785408781)
              ·
                refine ⟨727545642584690169528293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1940121713559173785408781 727545642584690169528293)
                ·
                  refine ⟨136414807984629406786555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727545642584690169528293 136414807984629406786555)
                  ·
                    rfl

theorem cell22_1195501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1195501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195501 prefixEnd_1195501 := by exact prefixLift 1195501
  have htrace : WordTrace (prefixWord ++ tailWord_1195501) baseStart_1195501 baseEnd_1195501 := by
    simpa [prefixWord, tailWord_1195501, baseEnd_1195501] using wordTrace_append hprefix tailTrace_1195501
  have hstable : (prefixWord ++ tailWord_1195501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195501).length < 2 ^ (prefixWord ++ tailWord_1195501).sum := by decide
  have hdescent : baseEnd_1195501 < baseStart_1195501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195527 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 3, 3]
def baseStart_1195527 : Nat := 118140960795 + 1195527 * 2 ^ 59
def prefixEnd_1195527 : Nat := 4983230072969 + 3 ^ 40 * 1195527 * 2
def baseEnd_1195527 : Nat := 409253324285232819209585

theorem tailTrace_1195527 : CollatzResearch.WordTrace tailWord_1195527 prefixEnd_1195527 409253324285232819209585 := by
  unfold tailWord_1195527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43604451939817333601128835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29069634626544889067419223 43604451939817333601128835)
  ·
    refine ⟨65406677909726000401693253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43604451939817333601128835 65406677909726000401693253)
    ·
      refine ⟨12263752108073625075317485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65406677909726000401693253 12263752108073625075317485)
      ·
        refine ⟨4598907040527609403244057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12263752108073625075317485 4598907040527609403244057)
        ·
          refine ⟨3449180280395707052433043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598907040527609403244057 3449180280395707052433043)
          ·
            refine ⟨5173770420593560578649565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449180280395707052433043 5173770420593560578649565)
            ·
              refine ⟨1940163907722585216993587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5173770420593560578649565 1940163907722585216993587)
              ·
                refine ⟨2910245861583877825490381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940163907722585216993587 2910245861583877825490381)
                ·
                  refine ⟨1091342198093954184558893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2910245861583877825490381 1091342198093954184558893)
                  ·
                    refine ⟨409253324285232819209585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091342198093954184558893 409253324285232819209585)
                    ·
                      rfl

theorem cell22_1195527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_1195527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195527 prefixEnd_1195527 := by exact prefixLift 1195527
  have htrace : WordTrace (prefixWord ++ tailWord_1195527) baseStart_1195527 baseEnd_1195527 := by
    simpa [prefixWord, tailWord_1195527, baseEnd_1195527] using wordTrace_append hprefix tailTrace_1195527
  have hstable : (prefixWord ++ tailWord_1195527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195527).length < 2 ^ (prefixWord ++ tailWord_1195527).sum := by decide
  have hdescent : baseEnd_1195527 < baseStart_1195527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195574 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1195574 : Nat := 118140960795 + 1195574 * 2 ^ 59
def prefixEnd_1195574 : Nat := 4983230072969 + 3 ^ 40 * 1195574 * 2
def baseEnd_1195574 : Nat := 136423137781913454428147

theorem tailTrace_1195574 : CollatzResearch.WordTrace tailWord_1195574 prefixEnd_1195574 136423137781913454428147 := by
  unfold tailWord_1195574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725385385665441289255611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29070777447098040418726517 2725385385665441289255611)
  ·
    refine ⟨4088078078498161933883417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725385385665441289255611 4088078078498161933883417)
    ·
      refine ⟨3066058558873621450412563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4088078078498161933883417 3066058558873621450412563)
      ·
        refine ⟨4599087838310432175618845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066058558873621450412563 4599087838310432175618845)
        ·
          refine ⟨1724657939366412065857067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4599087838310432175618845 1724657939366412065857067)
          ·
            refine ⟨2586986909049618098785601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724657939366412065857067 2586986909049618098785601)
            ·
              refine ⟨1940240181787213574089201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586986909049618098785601 1940240181787213574089201)
              ·
                refine ⟨1455180136340410180566901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940240181787213574089201 1455180136340410180566901)
                ·
                  refine ⟨136423137781913454428147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455180136340410180566901 136423137781913454428147)
                  ·
                    rfl

theorem cell22_1195574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1195574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195574 prefixEnd_1195574 := by exact prefixLift 1195574
  have htrace : WordTrace (prefixWord ++ tailWord_1195574) baseStart_1195574 baseEnd_1195574 := by
    simpa [prefixWord, tailWord_1195574, baseEnd_1195574] using wordTrace_append hprefix tailTrace_1195574
  have hstable : (prefixWord ++ tailWord_1195574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195574).length < 2 ^ (prefixWord ++ tailWord_1195574).sum := by decide
  have hdescent : baseEnd_1195574 < baseStart_1195574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195585 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 6]
def baseStart_1195585 : Nat := 118140960795 + 1195585 * 2 ^ 59
def prefixEnd_1195585 : Nat := 4983230072969 + 3 ^ 40 * 1195585 * 2
def baseEnd_1195585 : Nat := 136424392956846667086469

theorem tailTrace_1195585 : CollatzResearch.WordTrace tailWord_1195585 prefixEnd_1195585 136424392956846667086469 := by
  unfold tailWord_1195585
  simp only [CollatzResearch.WordTrace]
  refine ⟨43606567373607209506740209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29071044915738139671160139 43606567373607209506740209)
  ·
    refine ⟨32704925530205407130055157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43606567373607209506740209 32704925530205407130055157)
    ·
      refine ⟨3066086768456756918442671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32704925530205407130055157 3066086768456756918442671)
      ·
        refine ⟨4599130152685135377664007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066086768456756918442671 4599130152685135377664007)
        ·
          refine ⟨6898695229027703066496011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599130152685135377664007 6898695229027703066496011)
          ·
            refine ⟨10348042843541554599744017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898695229027703066496011 10348042843541554599744017)
            ·
              refine ⟨7761032132656165949808013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10348042843541554599744017 7761032132656165949808013)
              ·
                refine ⟨2910387049746062231178005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7761032132656165949808013 2910387049746062231178005)
                ·
                  refine ⟨136424392956846667086469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2910387049746062231178005 136424392956846667086469)
                  ·
                    rfl

theorem cell22_1195585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_1195585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195585 prefixEnd_1195585 := by exact prefixLift 1195585
  have htrace : WordTrace (prefixWord ++ tailWord_1195585) baseStart_1195585 baseEnd_1195585 := by
    simpa [prefixWord, tailWord_1195585, baseEnd_1195585] using wordTrace_append hprefix tailTrace_1195585
  have hstable : (prefixWord ++ tailWord_1195585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195585).length < 2 ^ (prefixWord ++ tailWord_1195585).sum := by decide
  have hdescent : baseEnd_1195585 < baseStart_1195585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195600 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_1195600 : Nat := 118140960795 + 1195600 * 2 ^ 59
def prefixEnd_1195600 : Nat := 4983230072969 + 3 ^ 40 * 1195600 * 2
def baseEnd_1195600 : Nat := 409278313677084962134361

theorem tailTrace_1195600 : CollatzResearch.WordTrace tailWord_1195600 prefixEnd_1195600 409278313677084962134361 := by
  unfold tailWord_1195600
  simp only [CollatzResearch.WordTrace]
  refine ⟨21803557234276433534268127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29071409645701911379024169 21803557234276433534268127)
  ·
    refine ⟨32705335851414650301402191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21803557234276433534268127 32705335851414650301402191)
    ·
      refine ⟨49058003777121975452103287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32705335851414650301402191 49058003777121975452103287)
      ·
        refine ⟨73587005665682963178154931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49058003777121975452103287 73587005665682963178154931)
        ·
          refine ⟨110380508498524444767232397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73587005665682963178154931 110380508498524444767232397)
          ·
            refine ⟨41392690686946666787712149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110380508498524444767232397 41392690686946666787712149)
            ·
              refine ⟨1940282375950625005674007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41392690686946666787712149 1940282375950625005674007)
              ·
                refine ⟨2910423563925937508511011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940282375950625005674007 2910423563925937508511011)
                ·
                  refine ⟨4365635345888906262766517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910423563925937508511011 4365635345888906262766517)
                  ·
                    refine ⟨409278313677084962134361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4365635345888906262766517 409278313677084962134361)
                    ·
                      rfl

theorem cell22_1195600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_1195600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195600 prefixEnd_1195600 := by exact prefixLift 1195600
  have htrace : WordTrace (prefixWord ++ tailWord_1195600) baseStart_1195600 baseEnd_1195600 := by
    simpa [prefixWord, tailWord_1195600, baseEnd_1195600] using wordTrace_append hprefix tailTrace_1195600
  have hstable : (prefixWord ++ tailWord_1195600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195600).length < 2 ^ (prefixWord ++ tailWord_1195600).sum := by decide
  have hdescent : baseEnd_1195600 < baseStart_1195600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195634 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_1195634 : Nat := 118140960795 + 1195634 * 2 ^ 59
def prefixEnd_1195634 : Nat := 4983230072969 + 3 ^ 40 * 1195634 * 2
def baseEnd_1195634 : Nat := 409289952571920206784257

theorem tailTrace_1195634 : CollatzResearch.WordTrace tailWord_1195634 prefixEnd_1195634 409289952571920206784257 := by
  unfold tailWord_1195634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902088637607422718818489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29072236366953127250182637 10902088637607422718818489)
  ·
    refine ⟨8176566478205567039113867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10902088637607422718818489 8176566478205567039113867)
    ·
      refine ⟨12264849717308350558670801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8176566478205567039113867 12264849717308350558670801)
      ·
        refine ⟨9198637287981262919003101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12264849717308350558670801 9198637287981262919003101)
        ·
          refine ⟨3449488982992973594626163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9198637287981262919003101 3449488982992973594626163)
          ·
            refine ⟨5174233474489460391939245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449488982992973594626163 5174233474489460391939245)
            ·
              refine ⟨1940337552933547646977217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5174233474489460391939245 1940337552933547646977217)
              ·
                refine ⟨1455253164700160735232913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940337552933547646977217 1455253164700160735232913)
                ·
                  refine ⟨1091439873525120551424685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1455253164700160735232913 1091439873525120551424685)
                  ·
                    refine ⟨409289952571920206784257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091439873525120551424685 409289952571920206784257)
                    ·
                      rfl

theorem cell22_1195634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_1195634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195634 prefixEnd_1195634 := by exact prefixLift 1195634
  have htrace : WordTrace (prefixWord ++ tailWord_1195634) baseStart_1195634 baseEnd_1195634 := by
    simpa [prefixWord, tailWord_1195634, baseEnd_1195634] using wordTrace_append hprefix tailTrace_1195634
  have hstable : (prefixWord ++ tailWord_1195634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195634).length < 2 ^ (prefixWord ++ tailWord_1195634).sum := by decide
  have hdescent : baseEnd_1195634 < baseStart_1195634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195720 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_1195720 : Nat := 118140960795 + 1195720 * 2 ^ 59
def prefixEnd_1195720 : Nat := 4983230072969 + 3 ^ 40 * 1195720 * 2
def baseEnd_1195720 : Nat := 136439797376481549711331

theorem tailTrace_1195720 : CollatzResearch.WordTrace tailWord_1195720 prefixEnd_1195720 136439797376481549711331 := by
  unfold tailWord_1195720
  simp only [CollatzResearch.WordTrace]
  refine ⟨21805745614059063781452307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29074327485412085041936409 21805745614059063781452307)
  ·
    refine ⟨32708618421088595672178461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21805745614059063781452307 32708618421088595672178461)
    ·
      refine ⟨12265731907908223377066923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32708618421088595672178461 12265731907908223377066923)
      ·
        refine ⟨18398597861862335065600385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12265731907908223377066923 18398597861862335065600385)
        ·
          refine ⟨13798948396396751299200289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18398597861862335065600385 13798948396396751299200289)
          ·
            refine ⟨10349211297297563474400217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13798948396396751299200289 10349211297297563474400217)
            ·
              refine ⟨7761908472973172605800163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10349211297297563474400217 7761908472973172605800163)
              ·
                refine ⟨11642862709459758908700245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7761908472973172605800163 11642862709459758908700245)
                ·
                  refine ⟨136439797376481549711331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11642862709459758908700245 136439797376481549711331)
                  ·
                    rfl

theorem cell22_1195720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_1195720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195720 prefixEnd_1195720 := by exact prefixLift 1195720
  have htrace : WordTrace (prefixWord ++ tailWord_1195720) baseStart_1195720 baseEnd_1195720 := by
    simpa [prefixWord, tailWord_1195720, baseEnd_1195720] using wordTrace_append hprefix tailTrace_1195720
  have hstable : (prefixWord ++ tailWord_1195720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195720).length < 2 ^ (prefixWord ++ tailWord_1195720).sum := by decide
  have hdescent : baseEnd_1195720 < baseStart_1195720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195795 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_1195795 : Nat := 118140960795 + 1195795 * 2 ^ 59
def prefixEnd_1195795 : Nat := 4983230072969 + 3 ^ 40 * 1195795 * 2
def baseEnd_1195795 : Nat := 409345066162169453508763

theorem tailTrace_1195795 : CollatzResearch.WordTrace tailWord_1195795 prefixEnd_1195795 409345066162169453508763 := by
  unfold tailWord_1195795
  simp only [CollatzResearch.WordTrace]
  refine ⟨43614226702846415371884839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29076151135230943581256559 43614226702846415371884839)
  ·
    refine ⟨65421340054269623057827259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43614226702846415371884839 65421340054269623057827259)
    ·
      refine ⟨98132010081404434586740889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65421340054269623057827259 98132010081404434586740889)
      ·
        refine ⟨73599007561053325940055667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98132010081404434586740889 73599007561053325940055667)
        ·
          refine ⟨110398511341579988910083501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73599007561053325940055667 110398511341579988910083501)
          ·
            refine ⟨41399441753092495841281313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110398511341579988910083501 41399441753092495841281313)
            ·
              refine ⟨31049581314819371880960985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41399441753092495841281313 31049581314819371880960985)
              ·
                refine ⟨23287185986114528910720739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31049581314819371880960985 23287185986114528910720739)
                ·
                  refine ⟨34930778979171793366081109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23287185986114528910720739 34930778979171793366081109)
                  ·
                    refine ⟨409345066162169453508763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34930778979171793366081109 409345066162169453508763)
                    ·
                      rfl

theorem cell22_1195795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_1195795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195795 prefixEnd_1195795 := by exact prefixLift 1195795
  have htrace : WordTrace (prefixWord ++ tailWord_1195795) baseStart_1195795 baseEnd_1195795 := by
    simpa [prefixWord, tailWord_1195795, baseEnd_1195795] using wordTrace_append hprefix tailTrace_1195795
  have hstable : (prefixWord ++ tailWord_1195795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195795).length < 2 ^ (prefixWord ++ tailWord_1195795).sum := by decide
  have hdescent : baseEnd_1195795 < baseStart_1195795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195833 : List Nat := [1, 2, 1, 7, 2, 1, 2, 6]
def baseStart_1195833 : Nat := 118140960795 + 1195833 * 2 ^ 59
def prefixEnd_1195833 : Nat := 4983230072969 + 3 ^ 40 * 1195833 * 2
def baseEnd_1195833 : Nat := 45484230482083335673183

theorem tailTrace_1195833 : CollatzResearch.WordTrace tailWord_1195833 prefixEnd_1195833 45484230482083335673183 := by
  unfold tailWord_1195833
  simp only [CollatzResearch.WordTrace]
  refine ⟨43615612676708747861768153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29077075117805831907845435 43615612676708747861768153)
  ·
    refine ⟨32711709507531560896326115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43615612676708747861768153 32711709507531560896326115)
    ·
      refine ⟨49067564261297341344489173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32711709507531560896326115 49067564261297341344489173)
      ·
        refine ⟨1150021037374156437761465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49067564261297341344489173 1150021037374156437761465)
        ·
          refine ⟨862515778030617328321099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150021037374156437761465 862515778030617328321099)
          ·
            refine ⟨1293773667045925992481649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862515778030617328321099 1293773667045925992481649)
            ·
              refine ⟨970330250284444494361237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293773667045925992481649 970330250284444494361237)
              ·
                refine ⟨45484230482083335673183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 970330250284444494361237 45484230482083335673183)
                ·
                  rfl

theorem cell22_1195833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 6].length) (baseStart_1195833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195833 prefixEnd_1195833 := by exact prefixLift 1195833
  have htrace : WordTrace (prefixWord ++ tailWord_1195833) baseStart_1195833 baseEnd_1195833 := by
    simpa [prefixWord, tailWord_1195833, baseEnd_1195833] using wordTrace_append hprefix tailTrace_1195833
  have hstable : (prefixWord ++ tailWord_1195833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195833).length < 2 ^ (prefixWord ++ tailWord_1195833).sum := by decide
  have hdescent : baseEnd_1195833 < baseStart_1195833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195848 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 1, 3]
def baseStart_1195848 : Nat := 118140960795 + 1195848 * 2 ^ 59
def prefixEnd_1195848 : Nat := 4983230072969 + 3 ^ 40 * 1195848 * 2
def baseEnd_1195848 : Nat := 409363209145294981933601

theorem tailTrace_1195848 : CollatzResearch.WordTrace tailWord_1195848 prefixEnd_1195848 409363209145294981933601 := by
  unfold tailWord_1195848
  simp only [CollatzResearch.WordTrace]
  refine ⟨21808079885827202711782099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29077439847769603615709465 21808079885827202711782099)
  ·
    refine ⟨32712119828740804067673149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21808079885827202711782099 32712119828740804067673149)
    ·
      refine ⟨12267044935777801525377431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32712119828740804067673149 12267044935777801525377431)
      ·
        refine ⟨18400567403666702288066147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12267044935777801525377431 18400567403666702288066147)
        ·
          refine ⟨27600851105500053432099221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18400567403666702288066147 27600851105500053432099221)
          ·
            refine ⟨1293789895570315004629651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27600851105500053432099221 1293789895570315004629651)
            ·
              refine ⟨1940684843355472506944477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293789895570315004629651 1940684843355472506944477)
              ·
                refine ⟨727756816258302190104179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1940684843355472506944477 727756816258302190104179)
                ·
                  refine ⟨1091635224387453285156269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727756816258302190104179 1091635224387453285156269)
                  ·
                    refine ⟨409363209145294981933601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091635224387453285156269 409363209145294981933601)
                    ·
                      rfl

theorem cell22_1195848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_1195848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195848 prefixEnd_1195848 := by exact prefixLift 1195848
  have htrace : WordTrace (prefixWord ++ tailWord_1195848) baseStart_1195848 baseEnd_1195848 := by
    simpa [prefixWord, tailWord_1195848, baseEnd_1195848] using wordTrace_append hprefix tailTrace_1195848
  have hstable : (prefixWord ++ tailWord_1195848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195848).length < 2 ^ (prefixWord ++ tailWord_1195848).sum := by decide
  have hdescent : baseEnd_1195848 < baseStart_1195848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195977 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1195977 : Nat := 118140960795 + 1195977 * 2 ^ 59
def prefixEnd_1195977 : Nat := 4983230072969 + 3 ^ 40 * 1195977 * 2
def baseEnd_1195977 : Nat := 409407368481581645458205

theorem tailTrace_1195977 : CollatzResearch.WordTrace tailWord_1195977 prefixEnd_1195977 409407368481581645458205 := by
  unfold tailWord_1195977
  simp only [CollatzResearch.WordTrace]
  refine ⟨43620864788187060455010185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29080576525458040303340123 43620864788187060455010185)
  ·
    refine ⟨32715648591140295341257639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43620864788187060455010185 32715648591140295341257639)
    ·
      refine ⟨49073472886710443011886459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32715648591140295341257639 49073472886710443011886459)
      ·
        refine ⟨73610209330065664517829689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49073472886710443011886459 73610209330065664517829689)
        ·
          refine ⟨55207656997549248388372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73610209330065664517829689 55207656997549248388372267)
          ·
            refine ⟨82811485496323872582558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55207656997549248388372267 82811485496323872582558401)
            ·
              refine ⟨62108614122242904436918801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82811485496323872582558401 62108614122242904436918801)
              ·
                refine ⟨46581460591682178327689101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62108614122242904436918801 46581460591682178327689101)
                ·
                  refine ⟨17468047721880816872883413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46581460591682178327689101 17468047721880816872883413)
                  ·
                    refine ⟨409407368481581645458205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17468047721880816872883413 409407368481581645458205)
                    ·
                      rfl

theorem cell22_1195977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1195977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1195977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1195977 prefixEnd_1195977 := by exact prefixLift 1195977
  have htrace : WordTrace (prefixWord ++ tailWord_1195977) baseStart_1195977 baseEnd_1195977 := by
    simpa [prefixWord, tailWord_1195977, baseEnd_1195977] using wordTrace_append hprefix tailTrace_1195977
  have hstable : (prefixWord ++ tailWord_1195977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195977).length < 2 ^ (prefixWord ++ tailWord_1195977).sum := by decide
  have hdescent : baseEnd_1195977 < baseStart_1195977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196017 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 1, 3]
def baseStart_1196017 : Nat := 118140960795 + 1196017 * 2 ^ 59
def prefixEnd_1196017 : Nat := 4983230072969 + 3 ^ 40 * 1196017 * 2
def baseEnd_1196017 : Nat := 409421061299034874458083

theorem tailTrace_1196017 : CollatzResearch.WordTrace tailWord_1196017 prefixEnd_1196017 409421061299034874458083 := by
  unfold tailWord_1196017
  simp only [CollatzResearch.WordTrace]
  refine ⟨43622323708042147286466305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29081549138694764857644203 43622323708042147286466305)
  ·
    refine ⟨32716742781031610464849729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43622323708042147286466305 32716742781031610464849729)
    ·
      refine ⟨24537557085773707848637297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32716742781031610464849729 24537557085773707848637297)
      ·
        refine ⟨18403167814330280886477973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24537557085773707848637297 18403167814330280886477973)
        ·
          refine ⟨862648491296731916553655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18403167814330280886477973 862648491296731916553655)
          ·
            refine ⟨1293972736945097874830483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862648491296731916553655 1293972736945097874830483)
            ·
              refine ⟨1940959105417646812245725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293972736945097874830483 1940959105417646812245725)
              ·
                refine ⟨727859664531617554592147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1940959105417646812245725 727859664531617554592147)
                ·
                  refine ⟨1091789496797426331888221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727859664531617554592147 1091789496797426331888221)
                  ·
                    refine ⟨409421061299034874458083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091789496797426331888221 409421061299034874458083)
                    ·
                      rfl

theorem cell22_1196017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_1196017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196017 prefixEnd_1196017 := by exact prefixLift 1196017
  have htrace : WordTrace (prefixWord ++ tailWord_1196017) baseStart_1196017 baseEnd_1196017 := by
    simpa [prefixWord, tailWord_1196017, baseEnd_1196017] using wordTrace_append hprefix tailTrace_1196017
  have hstable : (prefixWord ++ tailWord_1196017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196017).length < 2 ^ (prefixWord ++ tailWord_1196017).sum := by decide
  have hdescent : baseEnd_1196017 < baseStart_1196017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196069 : List Nat := [1, 3, 1, 2, 2, 3, 2, 8]
def baseStart_1196069 : Nat := 118140960795 + 1196069 * 2 ^ 59
def prefixEnd_1196069 : Nat := 4983230072969 + 3 ^ 40 * 1196069 * 2
def baseEnd_1196069 : Nat := 45493206884636008017547

theorem tailTrace_1196069 : CollatzResearch.WordTrace tailWord_1196069 prefixEnd_1196069 45493206884636008017547 := by
  unfold tailWord_1196069
  simp only [CollatzResearch.WordTrace]
  refine ⟨43624220303853760167359261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29082813535902506778239507 43624220303853760167359261)
  ·
    refine ⟨16359082613945160062759723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43624220303853760167359261 16359082613945160062759723)
    ·
      refine ⟨24538623920917740094139585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16359082613945160062759723 24538623920917740094139585)
      ·
        refine ⟨18403967940688305070604689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24538623920917740094139585 18403967940688305070604689)
        ·
          refine ⟨13802975955516228802953517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18403967940688305070604689 13802975955516228802953517)
          ·
            refine ⟨5176115983318585801107569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13802975955516228802953517 5176115983318585801107569)
            ·
              refine ⟨3882086987488939350830677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176115983318585801107569 3882086987488939350830677)
              ·
                refine ⟨45493206884636008017547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3882086987488939350830677 45493206884636008017547)
                ·
                  rfl

theorem cell22_1196069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 8].length) (baseStart_1196069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196069 prefixEnd_1196069 := by exact prefixLift 1196069
  have htrace : WordTrace (prefixWord ++ tailWord_1196069) baseStart_1196069 baseEnd_1196069 := by
    simpa [prefixWord, tailWord_1196069, baseEnd_1196069] using wordTrace_append hprefix tailTrace_1196069
  have hstable : (prefixWord ++ tailWord_1196069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196069).length < 2 ^ (prefixWord ++ tailWord_1196069).sum := by decide
  have hdescent : baseEnd_1196069 < baseStart_1196069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196101 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_1196101 : Nat := 118140960795 + 1196101 * 2 ^ 59
def prefixEnd_1196101 : Nat := 4983230072969 + 3 ^ 40 * 1196101 * 2
def baseEnd_1196101 : Nat := 409449816215686655357825

theorem tailTrace_1196101 : CollatzResearch.WordTrace tailWord_1196101 prefixEnd_1196101 409449816215686655357825 := by
  unfold tailWord_1196101
  simp only [CollatzResearch.WordTrace]
  refine ⟨43625387439737829632524157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29083591626491886421682771 43625387439737829632524157)
  ·
    refine ⟨16359520289901686112196559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43625387439737829632524157 16359520289901686112196559)
    ·
      refine ⟨24539280434852529168294839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16359520289901686112196559 24539280434852529168294839)
      ·
        refine ⟨36808920652278793752442259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24539280434852529168294839 36808920652278793752442259)
        ·
          refine ⟨55213380978418190628663389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36808920652278793752442259 55213380978418190628663389)
          ·
            refine ⟨20705017866906821485748771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55213380978418190628663389 20705017866906821485748771)
            ·
              refine ⟨31057526800360232228623157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20705017866906821485748771 31057526800360232228623157)
              ·
                refine ⟨2911643137533771771433421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31057526800360232228623157 2911643137533771771433421)
                ·
                  refine ⟨1091866176575164414287533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2911643137533771771433421 1091866176575164414287533)
                  ·
                    refine ⟨409449816215686655357825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091866176575164414287533 409449816215686655357825)
                    ·
                      rfl

theorem cell22_1196101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_1196101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196101 prefixEnd_1196101 := by exact prefixLift 1196101
  have htrace : WordTrace (prefixWord ++ tailWord_1196101) baseStart_1196101 baseEnd_1196101 := by
    simpa [prefixWord, tailWord_1196101, baseEnd_1196101] using wordTrace_append hprefix tailTrace_1196101
  have hstable : (prefixWord ++ tailWord_1196101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196101).length < 2 ^ (prefixWord ++ tailWord_1196101).sum := by decide
  have hdescent : baseEnd_1196101 < baseStart_1196101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196129 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1196129 : Nat := 118140960795 + 1196129 * 2 ^ 59
def prefixEnd_1196129 : Nat := 4983230072969 + 3 ^ 40 * 1196129 * 2
def baseEnd_1196129 : Nat := 409459401187903915657739

theorem tailTrace_1196129 : CollatzResearch.WordTrace tailWord_1196129 prefixEnd_1196129 409459401187903915657739 := by
  unfold tailWord_1196129
  simp only [CollatzResearch.WordTrace]
  refine ⟨43626408683636390414543441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29084272455757593609695627 43626408683636390414543441)
  ·
    refine ⟨32719806512727292810907581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43626408683636390414543441 32719806512727292810907581)
    ·
      refine ⟨12269927442272734804090343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32719806512727292810907581 12269927442272734804090343)
      ·
        refine ⟨18404891163409102206135515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269927442272734804090343 18404891163409102206135515)
        ·
          refine ⟨27607336745113653309203273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18404891163409102206135515 27607336745113653309203273)
          ·
            refine ⟨20705502558835239981902455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27607336745113653309203273 20705502558835239981902455)
            ·
              refine ⟨31058253838252859972853683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20705502558835239981902455 31058253838252859972853683)
              ·
                refine ⟨46587380757379289959280525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31058253838252859972853683 46587380757379289959280525)
                ·
                  refine ⟨17470267784017233734730197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46587380757379289959280525 17470267784017233734730197)
                  ·
                    refine ⟨409459401187903915657739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17470267784017233734730197 409459401187903915657739)
                    ·
                      rfl

theorem cell22_1196129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1196129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196129 prefixEnd_1196129 := by exact prefixLift 1196129
  have htrace : WordTrace (prefixWord ++ tailWord_1196129) baseStart_1196129 baseEnd_1196129 := by
    simpa [prefixWord, tailWord_1196129, baseEnd_1196129] using wordTrace_append hprefix tailTrace_1196129
  have hstable : (prefixWord ++ tailWord_1196129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196129).length < 2 ^ (prefixWord ++ tailWord_1196129).sum := by decide
  have hdescent : baseEnd_1196129 < baseStart_1196129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196135 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1196135 : Nat := 118140960795 + 1196135 * 2 ^ 59
def prefixEnd_1196135 : Nat := 4983230072969 + 3 ^ 40 * 1196135 * 2
def baseEnd_1196135 : Nat := 409461455110521900007721

theorem tailTrace_1196135 : CollatzResearch.WordTrace tailWord_1196135 prefixEnd_1196135 409461455110521900007721 := by
  unfold tailWord_1196135
  simp only [CollatzResearch.WordTrace]
  refine ⟨43626627521614653439261859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29084418347743102292841239 43626627521614653439261859)
  ·
    refine ⟨65439941282421980158892789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43626627521614653439261859 65439941282421980158892789)
    ·
      refine ⟨6134994495227060639896199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65439941282421980158892789 6134994495227060639896199)
      ·
        refine ⟨9202491742840590959844299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6134994495227060639896199 9202491742840590959844299)
        ·
          refine ⟨13803737614260886439766449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202491742840590959844299 13803737614260886439766449)
          ·
            refine ⟨10352803210695664829824837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13803737614260886439766449 10352803210695664829824837)
            ·
              refine ⟨1941150602005437155592157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10352803210695664829824837 1941150602005437155592157)
              ·
                refine ⟨727931475752038933347059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941150602005437155592157 727931475752038933347059)
                ·
                  refine ⟨1091897213628058400020589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727931475752038933347059 1091897213628058400020589)
                  ·
                    refine ⟨409461455110521900007721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091897213628058400020589 409461455110521900007721)
                    ·
                      rfl

theorem cell22_1196135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1196135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196135 prefixEnd_1196135 := by exact prefixLift 1196135
  have htrace : WordTrace (prefixWord ++ tailWord_1196135) baseStart_1196135 baseEnd_1196135 := by
    simpa [prefixWord, tailWord_1196135, baseEnd_1196135] using wordTrace_append hprefix tailTrace_1196135
  have hstable : (prefixWord ++ tailWord_1196135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196135).length < 2 ^ (prefixWord ++ tailWord_1196135).sum := by decide
  have hdescent : baseEnd_1196135 < baseStart_1196135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196146 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1196146 : Nat := 118140960795 + 1196146 * 2 ^ 59
def prefixEnd_1196146 : Nat := 4983230072969 + 3 ^ 40 * 1196146 * 2
def baseEnd_1196146 : Nat := 409465220635321537982687

theorem tailTrace_1196146 : CollatzResearch.WordTrace tailWord_1196146 prefixEnd_1196146 409465220635321537982687 := by
  unfold tailWord_1196146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906757181143700579478073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29084685816383201545274861 10906757181143700579478073)
  ·
    refine ⟨8180067885857775434608555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10906757181143700579478073 8180067885857775434608555)
    ·
      refine ⟨12270101828786663151912833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8180067885857775434608555 12270101828786663151912833)
      ·
        refine ⟨9202576371589997363934625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12270101828786663151912833 9202576371589997363934625)
        ·
          refine ⟨6901932278692498022950969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9202576371589997363934625 6901932278692498022950969)
          ·
            refine ⟨5176449209019373517213227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6901932278692498022950969 5176449209019373517213227)
            ·
              refine ⟨7764673813529060275819841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176449209019373517213227 7764673813529060275819841)
              ·
                refine ⟨5823505360146795206864881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764673813529060275819841 5823505360146795206864881)
                ·
                  refine ⟨4367629020110096405148661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823505360146795206864881 4367629020110096405148661)
                  ·
                    refine ⟨409465220635321537982687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4367629020110096405148661 409465220635321537982687)
                    ·
                      rfl

theorem cell22_1196146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1196146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196146 prefixEnd_1196146 := by exact prefixLift 1196146
  have htrace : WordTrace (prefixWord ++ tailWord_1196146) baseStart_1196146 baseEnd_1196146 := by
    simpa [prefixWord, tailWord_1196146, baseEnd_1196146] using wordTrace_append hprefix tailTrace_1196146
  have hstable : (prefixWord ++ tailWord_1196146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196146).length < 2 ^ (prefixWord ++ tailWord_1196146).sum := by decide
  have hdescent : baseEnd_1196146 < baseStart_1196146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196210 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1196210 : Nat := 118140960795 + 1196210 * 2 ^ 59
def prefixEnd_1196210 : Nat := 4983230072969 + 3 ^ 40 * 1196210 * 2
def baseEnd_1196210 : Nat := 136495709714415568127497

theorem tailTrace_1196210 : CollatzResearch.WordTrace tailWord_1196210 prefixEnd_1196210 136495709714415568127497 := by
  unfold tailWord_1196210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907340749085735312060521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29086241997561960832161389 10907340749085735312060521)
  ·
    refine ⟨8180505561814301484045391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10907340749085735312060521 8180505561814301484045391)
    ·
      refine ⟨12270758342721452226068087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8180505561814301484045391 12270758342721452226068087)
      ·
        refine ⟨18406137514082178339102131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12270758342721452226068087 18406137514082178339102131)
        ·
          refine ⟨27609206271123267508653197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18406137514082178339102131 27609206271123267508653197)
          ·
            refine ⟨10353452351671225315744949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27609206271123267508653197 10353452351671225315744949)
            ·
              refine ⟨970636157969177373351089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10353452351671225315744949 970636157969177373351089)
              ·
                refine ⟨727977118476883030013317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970636157969177373351089 727977118476883030013317)
                ·
                  refine ⟨136495709714415568127497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727977118476883030013317 136495709714415568127497)
                  ·
                    rfl

theorem cell22_1196210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1196210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196210 prefixEnd_1196210 := by exact prefixLift 1196210
  have htrace : WordTrace (prefixWord ++ tailWord_1196210) baseStart_1196210 baseEnd_1196210 := by
    simpa [prefixWord, tailWord_1196210, baseEnd_1196210] using wordTrace_append hprefix tailTrace_1196210
  have hstable : (prefixWord ++ tailWord_1196210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196210).length < 2 ^ (prefixWord ++ tailWord_1196210).sum := by decide
  have hdescent : baseEnd_1196210 < baseStart_1196210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196317 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 5]
def baseStart_1196317 : Nat := 118140960795 + 1196317 * 2 ^ 59
def prefixEnd_1196317 : Nat := 4983230072969 + 3 ^ 40 * 1196317 * 2
def baseEnd_1196317 : Nat := 136507919143311363985721

theorem tailTrace_1196317 : CollatzResearch.WordTrace tailWord_1196317 prefixEnd_1196317 136507919143311363985721 := by
  unfold tailWord_1196317
  simp only [CollatzResearch.WordTrace]
  refine ⟨43633265606955298522387205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29088843737970199014924803 43633265606955298522387205)
  ·
    refine ⟨8181237301304118472947601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43633265606955298522387205 8181237301304118472947601)
    ·
      refine ⟨6135927975978088854710701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8181237301304118472947601 6135927975978088854710701)
      ·
        refine ⟨2300972990991783320516513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6135927975978088854710701 2300972990991783320516513)
        ·
          refine ⟨1725729743243837490387385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2300972990991783320516513 1725729743243837490387385)
          ·
            refine ⟨1294297307432878117790539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1725729743243837490387385 1294297307432878117790539)
            ·
              refine ⟨1941445961149317176685809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294297307432878117790539 1941445961149317176685809)
              ·
                refine ⟨1456084470861987882514357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941445961149317176685809 1456084470861987882514357)
                ·
                  refine ⟨136507919143311363985721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456084470861987882514357 136507919143311363985721)
                  ·
                    rfl

theorem cell22_1196317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_1196317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196317 prefixEnd_1196317 := by exact prefixLift 1196317
  have htrace : WordTrace (prefixWord ++ tailWord_1196317) baseStart_1196317 baseEnd_1196317 := by
    simpa [prefixWord, tailWord_1196317, baseEnd_1196317] using wordTrace_append hprefix tailTrace_1196317
  have hstable : (prefixWord ++ tailWord_1196317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196317).length < 2 ^ (prefixWord ++ tailWord_1196317).sum := by decide
  have hdescent : baseEnd_1196317 < baseStart_1196317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196334 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_1196334 : Nat := 118140960795 + 1196334 * 2 ^ 59
def prefixEnd_1196334 : Nat := 4983230072969 + 3 ^ 40 * 1196334 * 2
def baseEnd_1196334 : Nat := 136509858959117238094037

theorem tailTrace_1196334 : CollatzResearch.WordTrace tailWord_1196334 prefixEnd_1196334 136509858959117238094037 := by
  unfold tailWord_1196334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454235705986713803219507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29089257098595806950504037 5454235705986713803219507)
  ·
    refine ⟨8181353558980070704829261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454235705986713803219507 8181353558980070704829261)
    ·
      refine ⟨3068007584617526514310973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8181353558980070704829261 3068007584617526514310973)
      ·
        refine ⟨1150502844231572442866615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3068007584617526514310973 1150502844231572442866615)
        ·
          refine ⟨1725754266347358664299923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150502844231572442866615 1725754266347358664299923)
          ·
            refine ⟨2588631399521037996449885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725754266347358664299923 2588631399521037996449885)
            ·
              refine ⟨970736774820389248668707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2588631399521037996449885 970736774820389248668707)
              ·
                refine ⟨1456105162230583873003061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970736774820389248668707 1456105162230583873003061)
                ·
                  refine ⟨136509858959117238094037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456105162230583873003061 136509858959117238094037)
                  ·
                    rfl

theorem cell22_1196334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_1196334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196334 prefixEnd_1196334 := by exact prefixLift 1196334
  have htrace : WordTrace (prefixWord ++ tailWord_1196334) baseStart_1196334 baseEnd_1196334 := by
    simpa [prefixWord, tailWord_1196334, baseEnd_1196334] using wordTrace_append hprefix tailTrace_1196334
  have hstable : (prefixWord ++ tailWord_1196334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196334).length < 2 ^ (prefixWord ++ tailWord_1196334).sum := by decide
  have hdescent : baseEnd_1196334 < baseStart_1196334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196394 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1196394 : Nat := 118140960795 + 1196394 * 2 ^ 59
def prefixEnd_1196394 : Nat := 4983230072969 + 3 ^ 40 * 1196394 * 2
def baseEnd_1196394 : Nat := 409550116103531557781927

theorem tailTrace_1196394 : CollatzResearch.WordTrace tailWord_1196394 prefixEnd_1196394 409550116103531557781927 := by
  unfold tailWord_1196394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909018506919085168235059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29090716018450893781960157 10909018506919085168235059)
  ·
    refine ⟨16363527760378627752352589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10909018506919085168235059 16363527760378627752352589)
    ·
      refine ⟨6136322910141985407132221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16363527760378627752352589 6136322910141985407132221)
      ·
        refine ⟨2301121091303244527674583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6136322910141985407132221 2301121091303244527674583)
        ·
          refine ⟨3451681636954866791511875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301121091303244527674583 3451681636954866791511875)
          ·
            refine ⟨5177522455432300187267813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451681636954866791511875 5177522455432300187267813)
            ·
              refine ⟨970785460393556285112715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5177522455432300187267813 970785460393556285112715)
              ·
                refine ⟨1456178190590334427669073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970785460393556285112715 1456178190590334427669073)
                ·
                  refine ⟨1092133642942750820751805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1456178190590334427669073 1092133642942750820751805)
                  ·
                    refine ⟨409550116103531557781927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1092133642942750820751805 409550116103531557781927)
                    ·
                      rfl

theorem cell22_1196394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1196394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196394 prefixEnd_1196394 := by exact prefixLift 1196394
  have htrace : WordTrace (prefixWord ++ tailWord_1196394) baseStart_1196394 baseEnd_1196394 := by
    simpa [prefixWord, tailWord_1196394, baseEnd_1196394] using wordTrace_append hprefix tailTrace_1196394
  have hstable : (prefixWord ++ tailWord_1196394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196394).length < 2 ^ (prefixWord ++ tailWord_1196394).sum := by decide
  have hdescent : baseEnd_1196394 < baseStart_1196394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196439 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 1, 3]
def baseStart_1196439 : Nat := 118140960795 + 1196439 * 2 ^ 59
def prefixEnd_1196439 : Nat := 4983230072969 + 3 ^ 40 * 1196439 * 2
def baseEnd_1196439 : Nat := 409565520523166440406789

theorem tailTrace_1196439 : CollatzResearch.WordTrace tailWord_1196439 prefixEnd_1196439 409565520523166440406789 := by
  unfold tailWord_1196439
  simp only [CollatzResearch.WordTrace]
  refine ⟨43637715312513313358328371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29091810208342208905552247 43637715312513313358328371)
  ·
    refine ⟨65456572968769970037492557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43637715312513313358328371 65456572968769970037492557)
    ·
      refine ⟨24546214863288738764059709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65456572968769970037492557 24546214863288738764059709)
      ·
        refine ⟨9204830573733277036522391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24546214863288738764059709 9204830573733277036522391)
        ·
          refine ⟨13807245860599915554783587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9204830573733277036522391 13807245860599915554783587)
          ·
            refine ⟨20710868790899873332175381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13807245860599915554783587 20710868790899873332175381)
            ·
              refine ⟨970821974573431562445721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20710868790899873332175381 970821974573431562445721)
              ·
                refine ⟨728116480930073671834291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970821974573431562445721 728116480930073671834291)
                ·
                  refine ⟨1092174721395110507751437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728116480930073671834291 1092174721395110507751437)
                  ·
                    refine ⟨409565520523166440406789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1092174721395110507751437 409565520523166440406789)
                    ·
                      rfl

theorem cell22_1196439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_1196439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196439 prefixEnd_1196439 := by exact prefixLift 1196439
  have htrace : WordTrace (prefixWord ++ tailWord_1196439) baseStart_1196439 baseEnd_1196439 := by
    simpa [prefixWord, tailWord_1196439, baseEnd_1196439] using wordTrace_append hprefix tailTrace_1196439
  have hstable : (prefixWord ++ tailWord_1196439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196439).length < 2 ^ (prefixWord ++ tailWord_1196439).sum := by decide
  have hdescent : baseEnd_1196439 < baseStart_1196439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196450 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1196450 : Nat := 118140960795 + 1196450 * 2 ^ 59
def prefixEnd_1196450 : Nat := 4983230072969 + 3 ^ 40 * 1196450 * 2
def baseEnd_1196450 : Nat := 409569286047966078381755

theorem tailTrace_1196450 : CollatzResearch.WordTrace tailWord_1196450 prefixEnd_1196450 409569286047966078381755 := by
  unfold tailWord_1196450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909529128868365559244701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29092077676982308157985869 10909529128868365559244701)
  ·
    refine ⟨4091073423325637084716763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10909529128868365559244701 4091073423325637084716763)
    ·
      refine ⟨6136610134988455627075145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4091073423325637084716763 6136610134988455627075145)
      ·
        refine ⟨4602457601241341720306359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6136610134988455627075145 4602457601241341720306359)
        ·
          refine ⟨6903686401862012580459539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602457601241341720306359 6903686401862012580459539)
          ·
            refine ⟨10355529602793018870689309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6903686401862012580459539 10355529602793018870689309)
            ·
              refine ⟨3883323601047382076508491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10355529602793018870689309 3883323601047382076508491)
              ·
                refine ⟨5824985401571073114762737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883323601047382076508491 5824985401571073114762737)
                ·
                  refine ⟨4368739051178304836072053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5824985401571073114762737 4368739051178304836072053)
                  ·
                    refine ⟨409569286047966078381755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4368739051178304836072053 409569286047966078381755)
                    ·
                      rfl

theorem cell22_1196450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1196450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196450 prefixEnd_1196450 := by exact prefixLift 1196450
  have htrace : WordTrace (prefixWord ++ tailWord_1196450) baseStart_1196450 baseEnd_1196450 := by
    simpa [prefixWord, tailWord_1196450, baseEnd_1196450] using wordTrace_append hprefix tailTrace_1196450
  have hstable : (prefixWord ++ tailWord_1196450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196450).length < 2 ^ (prefixWord ++ tailWord_1196450).sum := by decide
  have hdescent : baseEnd_1196450 < baseStart_1196450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
