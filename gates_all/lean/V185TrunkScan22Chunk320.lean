import V185TrunkScan22Chunk319

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2856672 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_2856672 : Nat := 118140960795 + 2856672 * 2 ^ 59
def prefixEnd_2856672 : Nat := 4983230072969 + 3 ^ 40 * 2856672 * 2
def baseEnd_2856672 : Nat := 977897205493834994241607

theorem tailTrace_2856672 : CollatzResearch.WordTrace tailWord_2856672 prefixEnd_2856672 977897205493834994241607 := by
  unfold tailWord_2856672
  simp only [CollatzResearch.WordTrace]
  refine ⟨52095693753386349790270135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69460925004515133053693513 52095693753386349790270135)
  ·
    refine ⟨78143540630079524685405203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52095693753386349790270135 78143540630079524685405203)
    ·
      refine ⟨117215310945119287028107805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78143540630079524685405203 117215310945119287028107805)
      ·
        refine ⟨43955741604419732635540427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117215310945119287028107805 43955741604419732635540427)
        ·
          refine ⟨65933612406629598953310641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43955741604419732635540427 65933612406629598953310641)
          ·
            refine ⟨49450209304972199214982981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65933612406629598953310641 49450209304972199214982981)
            ·
              refine ⟨9271914244682287352809309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49450209304972199214982981 9271914244682287352809309)
              ·
                refine ⟨3476967841755857757303491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9271914244682287352809309 3476967841755857757303491)
                ·
                  refine ⟨5215451762633786635955237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476967841755857757303491 5215451762633786635955237)
                  ·
                    refine ⟨977897205493834994241607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5215451762633786635955237 977897205493834994241607)
                    ·
                      rfl

theorem cell22_2856672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_2856672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856672 prefixEnd_2856672 := by exact prefixLift 2856672
  have htrace : WordTrace (prefixWord ++ tailWord_2856672) baseStart_2856672 baseEnd_2856672 := by
    simpa [prefixWord, tailWord_2856672, baseEnd_2856672] using wordTrace_append hprefix tailTrace_2856672
  have hstable : (prefixWord ++ tailWord_2856672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856672).length < 2 ^ (prefixWord ++ tailWord_2856672).sum := by decide
  have hdescent : baseEnd_2856672 < baseStart_2856672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856715 : List Nat := [1, 1, 1, 1, 5, 1, 4, 8]
def baseStart_2856715 : Nat := 118140960795 + 2856715 * 2 ^ 59
def prefixEnd_2856715 : Nat := 4983230072969 + 3 ^ 40 * 2856715 * 2
def baseEnd_2856715 : Nat := 108656880585844135046275

theorem tailTrace_2856715 : CollatzResearch.WordTrace tailWord_2856715 prefixEnd_2856715 108656880585844135046275 := by
  unfold tailWord_2856715
  simp only [CollatzResearch.WordTrace]
  refine ⟨104192955845616917924355599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69461970563744611949570399 104192955845616917924355599)
  ·
    refine ⟨156289433768425376886533399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104192955845616917924355599 156289433768425376886533399)
    ·
      refine ⟨234434150652638065329800099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156289433768425376886533399 234434150652638065329800099)
      ·
        refine ⟨351651225978957097994700149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234434150652638065329800099 351651225978957097994700149)
        ·
          refine ⟨32967302435527227937003139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351651225978957097994700149 32967302435527227937003139)
          ·
            refine ⟨49450953653290841905504709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32967302435527227937003139 49450953653290841905504709)
            ·
              refine ⟨9272053809992032857282133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49450953653290841905504709 9272053809992032857282133)
              ·
                refine ⟨108656880585844135046275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9272053809992032857282133 108656880585844135046275)
                ·
                  rfl

theorem cell22_2856715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 8].length) (baseStart_2856715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856715 prefixEnd_2856715 := by exact prefixLift 2856715
  have htrace : WordTrace (prefixWord ++ tailWord_2856715) baseStart_2856715 baseEnd_2856715 := by
    simpa [prefixWord, tailWord_2856715, baseEnd_2856715] using wordTrace_append hprefix tailTrace_2856715
  have hstable : (prefixWord ++ tailWord_2856715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856715).length < 2 ^ (prefixWord ++ tailWord_2856715).sum := by decide
  have hdescent : baseEnd_2856715 < baseStart_2856715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856837 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_2856837 : Nat := 118140960795 + 2856837 * 2 ^ 59
def prefixEnd_2856837 : Nat := 4983230072969 + 3 ^ 40 * 2856837 * 2
def baseEnd_2856837 : Nat := 977953688365829563866101

theorem tailTrace_2856837 : CollatzResearch.WordTrace tailWord_2856837 prefixEnd_2856837 977953688365829563866101 := by
  unfold tailWord_2856837
  simp only [CollatzResearch.WordTrace]
  refine ⟨104197405551174932760296765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69464937034116621840197843 104197405551174932760296765)
  ·
    refine ⟨39074027081690599785111287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104197405551174932760296765 39074027081690599785111287)
    ·
      refine ⟨58611040622535899677666931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39074027081690599785111287 58611040622535899677666931)
      ·
        refine ⟨87916560933803849516500397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58611040622535899677666931 87916560933803849516500397)
        ·
          refine ⟨32968710350176443568687649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87916560933803849516500397 32968710350176443568687649)
          ·
            refine ⟨24726532762632332676515737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32968710350176443568687649 24726532762632332676515737)
            ·
              refine ⟨18544899571974249507386803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24726532762632332676515737 18544899571974249507386803)
              ·
                refine ⟨27817349357961374261080205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18544899571974249507386803 27817349357961374261080205)
                ·
                  refine ⟨10431506009235515347905077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27817349357961374261080205 10431506009235515347905077)
                  ·
                    refine ⟨977953688365829563866101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10431506009235515347905077 977953688365829563866101)
                    ·
                      rfl

theorem cell22_2856837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_2856837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856837 prefixEnd_2856837 := by exact prefixLift 2856837
  have htrace : WordTrace (prefixWord ++ tailWord_2856837) baseStart_2856837 baseEnd_2856837 := by
    simpa [prefixWord, tailWord_2856837, baseEnd_2856837] using wordTrace_append hprefix tailTrace_2856837
  have hstable : (prefixWord ++ tailWord_2856837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856837).length < 2 ^ (prefixWord ++ tailWord_2856837).sum := by decide
  have hdescent : baseEnd_2856837 < baseStart_2856837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856862 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2856862 : Nat := 118140960795 + 2856862 * 2 ^ 59
def prefixEnd_2856862 : Nat := 4983230072969 + 3 ^ 40 * 2856862 * 2
def baseEnd_2856862 : Nat := 325987415458912610663675

theorem tailTrace_2856862 : CollatzResearch.WordTrace tailWord_2856862 prefixEnd_2856862 325987415458912610663675 := by
  unfold tailWord_2856862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13024789672010545253744605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69465544917389574686637893 13024789672010545253744605)
  ·
    refine ⟨4884296127003954470154227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13024789672010545253744605 4884296127003954470154227)
    ·
      refine ⟨7326444190505931705231341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4884296127003954470154227 7326444190505931705231341)
      ·
        refine ⟨2747416571439724389461753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7326444190505931705231341 2747416571439724389461753)
        ·
          refine ⟨2060562428579793292096315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2747416571439724389461753 2060562428579793292096315)
          ·
            refine ⟨3090843642869689938144473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060562428579793292096315 3090843642869689938144473)
            ·
              refine ⟨2318132732152267453608355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090843642869689938144473 2318132732152267453608355)
              ·
                refine ⟨3477199098228401180412533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318132732152267453608355 3477199098228401180412533)
                ·
                  refine ⟨325987415458912610663675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3477199098228401180412533 325987415458912610663675)
                  ·
                    rfl

theorem cell22_2856862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2856862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856862 prefixEnd_2856862 := by exact prefixLift 2856862
  have htrace : WordTrace (prefixWord ++ tailWord_2856862) baseStart_2856862 baseEnd_2856862 := by
    simpa [prefixWord, tailWord_2856862, baseEnd_2856862] using wordTrace_append hprefix tailTrace_2856862
  have hstable : (prefixWord ++ tailWord_2856862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856862).length < 2 ^ (prefixWord ++ tailWord_2856862).sum := by decide
  have hdescent : baseEnd_2856862 < baseStart_2856862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856882 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2856882 : Nat := 118140960795 + 2856882 * 2 ^ 59
def prefixEnd_2856882 : Nat := 4983230072969 + 3 ^ 40 * 2856882 * 2
def baseEnd_2856882 : Nat := 977969092785464446490963

theorem tailTrace_2856882 : CollatzResearch.WordTrace tailWord_2856882 prefixEnd_2856882 977969092785464446490963 := by
  unfold tailWord_2856882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26049761709002976361421225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69466031224007936963789933 26049761709002976361421225)
  ·
    refine ⟨19537321281752232271065919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26049761709002976361421225 19537321281752232271065919)
    ·
      refine ⟨29305981922628348406598879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19537321281752232271065919 29305981922628348406598879)
      ·
        refine ⟨43958972883942522609898319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29305981922628348406598879 43958972883942522609898319)
        ·
          refine ⟨65938459325913783914847479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43958972883942522609898319 65938459325913783914847479)
          ·
            refine ⟨98907688988870675872271219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65938459325913783914847479 98907688988870675872271219)
            ·
              refine ⟨148361533483306013808406829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98907688988870675872271219 148361533483306013808406829)
              ·
                refine ⟨55635575056239755178152561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148361533483306013808406829 55635575056239755178152561)
                ·
                  refine ⟨41726681292179816383614421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55635575056239755178152561 41726681292179816383614421)
                  ·
                    refine ⟨977969092785464446490963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41726681292179816383614421 977969092785464446490963)
                    ·
                      rfl

theorem cell22_2856882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2856882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856882 prefixEnd_2856882 := by exact prefixLift 2856882
  have htrace : WordTrace (prefixWord ++ tailWord_2856882) baseStart_2856882 baseEnd_2856882 := by
    simpa [prefixWord, tailWord_2856882, baseEnd_2856882] using wordTrace_append hprefix tailTrace_2856882
  have hstable : (prefixWord ++ tailWord_2856882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856882).length < 2 ^ (prefixWord ++ tailWord_2856882).sum := by decide
  have hdescent : baseEnd_2856882 < baseStart_2856882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856912 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_2856912 : Nat := 118140960795 + 2856912 * 2 ^ 59
def prefixEnd_2856912 : Nat := 4983230072969 + 3 ^ 40 * 2856912 * 2
def baseEnd_2856912 : Nat := 325993120799518122746957

theorem tailTrace_2856912 : CollatzResearch.WordTrace tailWord_2856912 prefixEnd_2856912 325993120799518122746957 := by
  unfold tailWord_2856912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52100070512951610284638495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69466760683935480379517993 52100070512951610284638495)
  ·
    refine ⟨78150105769427415426957743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52100070512951610284638495 78150105769427415426957743)
    ·
      refine ⟨117225158654141123140436615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78150105769427415426957743 117225158654141123140436615)
      ·
        refine ⟨175837737981211684710654923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117225158654141123140436615 175837737981211684710654923)
        ·
          refine ⟨263756606971817527065982385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175837737981211684710654923 263756606971817527065982385)
          ·
            refine ⟨197817455228863145299486789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263756606971817527065982385 197817455228863145299486789)
            ·
              refine ⟨37090772855411839743653773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197817455228863145299486789 37090772855411839743653773)
              ·
                refine ⟨13909039820779439903870165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37090772855411839743653773 13909039820779439903870165)
                ·
                  refine ⟨325993120799518122746957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13909039820779439903870165 325993120799518122746957)
                  ·
                    rfl

theorem cell22_2856912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_2856912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856912 prefixEnd_2856912 := by exact prefixLift 2856912
  have htrace : WordTrace (prefixWord ++ tailWord_2856912) baseStart_2856912 baseEnd_2856912 := by
    simpa [prefixWord, tailWord_2856912, baseEnd_2856912] using wordTrace_append hprefix tailTrace_2856912
  have hstable : (prefixWord ++ tailWord_2856912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856912).length < 2 ^ (prefixWord ++ tailWord_2856912).sum := by decide
  have hdescent : baseEnd_2856912 < baseStart_2856912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856916 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_2856916 : Nat := 118140960795 + 2856916 * 2 ^ 59
def prefixEnd_2856916 : Nat := 4983230072969 + 3 ^ 40 * 2856916 * 2
def baseEnd_2856916 : Nat := 977980731680299691140859

theorem tailTrace_2856916 : CollatzResearch.WordTrace tailWord_2856916 prefixEnd_2856916 977980731680299691140859 := by
  unfold tailWord_2856916
  simp only [CollatzResearch.WordTrace]
  refine ⟨52100143458944364626211301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69466857945259152834948401 52100143458944364626211301)
  ·
    refine ⟨9768776898552068367414619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52100143458944364626211301 9768776898552068367414619)
    ·
      refine ⟨14653165347828102551121929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9768776898552068367414619 14653165347828102551121929)
      ·
        refine ⟨10989874010871076913341447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14653165347828102551121929 10989874010871076913341447)
        ·
          refine ⟨16484811016306615370012171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10989874010871076913341447 16484811016306615370012171)
          ·
            refine ⟨24727216524459923055018257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16484811016306615370012171 24727216524459923055018257)
            ·
              refine ⟨18545412393344942291263693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24727216524459923055018257 18545412393344942291263693)
              ·
                refine ⟨6954529647504353359223885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18545412393344942291263693 6954529647504353359223885)
                ·
                  refine ⟨2607948617814132509708957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6954529647504353359223885 2607948617814132509708957)
                  ·
                    refine ⟨977980731680299691140859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2607948617814132509708957 977980731680299691140859)
                    ·
                      rfl

theorem cell22_2856916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_2856916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856916 prefixEnd_2856916 := by exact prefixLift 2856916
  have htrace : WordTrace (prefixWord ++ tailWord_2856916) baseStart_2856916 baseEnd_2856916 := by
    simpa [prefixWord, tailWord_2856916, baseEnd_2856916] using wordTrace_append hprefix tailTrace_2856916
  have hstable : (prefixWord ++ tailWord_2856916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856916).length < 2 ^ (prefixWord ++ tailWord_2856916).sum := by decide
  have hdescent : baseEnd_2856916 < baseStart_2856916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856918 : List Nat := [5, 2, 1, 1, 3, 2, 1, 7]
def baseStart_2856918 : Nat := 118140960795 + 2856918 * 2 ^ 59
def prefixEnd_2856918 : Nat := 4983230072969 + 3 ^ 40 * 2856918 * 2
def baseEnd_2856918 : Nat := 108664601813463594732317

theorem tailTrace_2856918 : CollatzResearch.WordTrace tailWord_2856918 prefixEnd_2856918 108664601813463594732317 := by
  unfold tailWord_2856918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512522491492592724624713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69466906575920989062663605 6512522491492592724624713)
  ·
    refine ⟨4884391868619444543468535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6512522491492592724624713 4884391868619444543468535)
    ·
      refine ⟨7326587802929166815202803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4884391868619444543468535 7326587802929166815202803)
      ·
        refine ⟨10989881704393750222804205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326587802929166815202803 10989881704393750222804205)
        ·
          refine ⟨4121205639147656333551577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10989881704393750222804205 4121205639147656333551577)
          ·
            refine ⟨3090904229360742250163683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121205639147656333551577 3090904229360742250163683)
            ·
              refine ⟨4636356344041113375245525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090904229360742250163683 4636356344041113375245525)
              ·
                refine ⟨108664601813463594732317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4636356344041113375245525 108664601813463594732317)
                ·
                  rfl

theorem cell22_2856918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_2856918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856918 prefixEnd_2856918 := by exact prefixLift 2856918
  have htrace : WordTrace (prefixWord ++ tailWord_2856918) baseStart_2856918 baseEnd_2856918 := by
    simpa [prefixWord, tailWord_2856918, baseEnd_2856918] using wordTrace_append hprefix tailTrace_2856918
  have hstable : (prefixWord ++ tailWord_2856918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856918).length < 2 ^ (prefixWord ++ tailWord_2856918).sum := by decide
  have hdescent : baseEnd_2856918 < baseStart_2856918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856929 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 5]
def baseStart_2856929 : Nat := 118140960795 + 2856929 * 2 ^ 59
def prefixEnd_2856929 : Nat := 4983230072969 + 3 ^ 40 * 2856929 * 2
def baseEnd_2856929 : Nat := 325995060615323996855273

theorem tailTrace_2856929 : CollatzResearch.WordTrace tailWord_2856929 prefixEnd_2856929 325995060615323996855273 := by
  unfold tailWord_2856929
  simp only [CollatzResearch.WordTrace]
  refine ⟨104200761066841632472645841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69467174044561088315097227 104200761066841632472645841)
  ·
    refine ⟨78150570800131224354484381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104200761066841632472645841 78150570800131224354484381)
    ·
      refine ⟨29306464050049209132931643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78150570800131224354484381 29306464050049209132931643)
      ·
        refine ⟨43959696075073813699397465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29306464050049209132931643 43959696075073813699397465)
        ·
          refine ⟨32969772056305360274548099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43959696075073813699397465 32969772056305360274548099)
          ·
            refine ⟨49454658084458040411822149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32969772056305360274548099 49454658084458040411822149)
            ·
              refine ⟨9272748390835882577216653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49454658084458040411822149 9272748390835882577216653)
              ·
                refine ⟨3477280646563455966456245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9272748390835882577216653 3477280646563455966456245)
                ·
                  refine ⟨325995060615323996855273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3477280646563455966456245 325995060615323996855273)
                  ·
                    rfl

theorem cell22_2856929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_2856929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856929 prefixEnd_2856929 := by exact prefixLift 2856929
  have htrace : WordTrace (prefixWord ++ tailWord_2856929) baseStart_2856929 baseEnd_2856929 := by
    simpa [prefixWord, tailWord_2856929, baseEnd_2856929] using wordTrace_append hprefix tailTrace_2856929
  have hstable : (prefixWord ++ tailWord_2856929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856929).length < 2 ^ (prefixWord ++ tailWord_2856929).sum := by decide
  have hdescent : baseEnd_2856929 < baseStart_2856929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856993 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2856993 : Nat := 118140960795 + 2856993 * 2 ^ 59
def prefixEnd_2856993 : Nat := 4983230072969 + 3 ^ 40 * 2856993 * 2
def baseEnd_2856993 : Nat := 978007090353897156965623

theorem tailTrace_2856993 : CollatzResearch.WordTrace tailWord_2856993 prefixEnd_2856993 978007090353897156965623 := by
  unfold tailWord_2856993
  simp only [CollatzResearch.WordTrace]
  refine ⟨104203095338609771402975633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69468730225739847601983755 104203095338609771402975633)
  ·
    refine ⟨78152321503957328552231725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104203095338609771402975633 78152321503957328552231725)
    ·
      refine ⟨29307120563983998207086897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78152321503957328552231725 29307120563983998207086897)
      ·
        refine ⟨21980340422987998655315173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29307120563983998207086897 21980340422987998655315173)
        ·
          refine ⟨4121313829310249747871595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21980340422987998655315173 4121313829310249747871595)
          ·
            refine ⟨6181970743965374621807393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121313829310249747871595 6181970743965374621807393)
            ·
              refine ⟨4636478057974030966355545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6181970743965374621807393 4636478057974030966355545)
              ·
                refine ⟨3477358543480523224766659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636478057974030966355545 3477358543480523224766659)
                ·
                  refine ⟨5216037815220784837149989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477358543480523224766659 5216037815220784837149989)
                  ·
                    refine ⟨978007090353897156965623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216037815220784837149989 978007090353897156965623)
                    ·
                      rfl

theorem cell22_2856993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2856993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856993 prefixEnd_2856993 := by exact prefixLift 2856993
  have htrace : WordTrace (prefixWord ++ tailWord_2856993) baseStart_2856993 baseEnd_2856993 := by
    simpa [prefixWord, tailWord_2856993, baseEnd_2856993] using wordTrace_append hprefix tailTrace_2856993
  have hstable : (prefixWord ++ tailWord_2856993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856993).length < 2 ^ (prefixWord ++ tailWord_2856993).sum := by decide
  have hdescent : baseEnd_2856993 < baseStart_2856993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857008 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_2857008 : Nat := 118140960795 + 2857008 * 2 ^ 59
def prefixEnd_2857008 : Nat := 4983230072969 + 3 ^ 40 * 2857008 * 2
def baseEnd_2857008 : Nat := 326004075053480705946859

theorem tailTrace_2857008 : CollatzResearch.WordTrace tailWord_2857008 prefixEnd_2857008 326004075053480705946859 := by
  unfold tailWord_2857008
  simp only [CollatzResearch.WordTrace]
  refine ⟨52101821216777714482385839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69469094955703619309847785 52101821216777714482385839)
  ·
    refine ⟨78152731825166571723578759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52101821216777714482385839 78152731825166571723578759)
    ·
      refine ⟨117229097737749857585368139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78152731825166571723578759 117229097737749857585368139)
      ·
        refine ⟨175843646606624786378052209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117229097737749857585368139 175843646606624786378052209)
        ·
          refine ⟨131882734954968589783539157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175843646606624786378052209 131882734954968589783539157)
          ·
            refine ⟨3091001600507076323051699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 131882734954968589783539157 3091001600507076323051699)
            ·
              refine ⟨4636502400760614484577549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091001600507076323051699 4636502400760614484577549)
              ·
                refine ⟨1738688400285230431716581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4636502400760614484577549 1738688400285230431716581)
                ·
                  refine ⟨326004075053480705946859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738688400285230431716581 326004075053480705946859)
                  ·
                    rfl

theorem cell22_2857008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_2857008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857008 prefixEnd_2857008 := by exact prefixLift 2857008
  have htrace : WordTrace (prefixWord ++ tailWord_2857008) baseStart_2857008 baseEnd_2857008 := by
    simpa [prefixWord, tailWord_2857008, baseEnd_2857008] using wordTrace_append hprefix tailTrace_2857008
  have hstable : (prefixWord ++ tailWord_2857008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857008).length < 2 ^ (prefixWord ++ tailWord_2857008).sum := by decide
  have hdescent : baseEnd_2857008 < baseStart_2857008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857021 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2857021 : Nat := 118140960795 + 2857021 * 2 ^ 59
def prefixEnd_2857021 : Nat := 4983230072969 + 3 ^ 40 * 2857021 * 2
def baseEnd_2857021 : Nat := 978016675326114417265537

theorem tailTrace_2857021 : CollatzResearch.WordTrace tailWord_2857021 prefixEnd_2857021 978016675326114417265537 := by
  unfold tailWord_2857021
  simp only [CollatzResearch.WordTrace]
  refine ⟨104204116582508332184994917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69469411055005554789996611 104204116582508332184994917)
  ·
    refine ⟨19538271859220312284686547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104204116582508332184994917 19538271859220312284686547)
    ·
      refine ⟨29307407788830468427029821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19538271859220312284686547 29307407788830468427029821)
      ·
        refine ⟨10990277920811425660136183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29307407788830468427029821 10990277920811425660136183)
        ·
          refine ⟨16485416881217138490204275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10990277920811425660136183 16485416881217138490204275)
          ·
            refine ⟨24728125321825707735306413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485416881217138490204275 24728125321825707735306413)
            ·
              refine ⟨9273046995684640400739905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24728125321825707735306413 9273046995684640400739905)
              ·
                refine ⟨6954785246763480300554929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273046995684640400739905 6954785246763480300554929)
                ·
                  refine ⟨5216088935072610225416197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6954785246763480300554929 5216088935072610225416197)
                  ·
                    refine ⟨978016675326114417265537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216088935072610225416197 978016675326114417265537)
                    ·
                      rfl

theorem cell22_2857021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2857021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857021 prefixEnd_2857021 := by exact prefixLift 2857021
  have htrace : WordTrace (prefixWord ++ tailWord_2857021) baseStart_2857021 baseEnd_2857021 := by
    simpa [prefixWord, tailWord_2857021, baseEnd_2857021] using wordTrace_append hprefix tailTrace_2857021
  have hstable : (prefixWord ++ tailWord_2857021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857021).length < 2 ^ (prefixWord ++ tailWord_2857021).sum := by decide
  have hdescent : baseEnd_2857021 < baseStart_2857021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857025 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 4]
def baseStart_2857025 : Nat := 118140960795 + 2857025 * 2 ^ 59
def prefixEnd_2857025 : Nat := 4983230072969 + 3 ^ 40 * 2857025 * 2
def baseEnd_2857025 : Nat := 326006014869286580055175

theorem tailTrace_2857025 : CollatzResearch.WordTrace tailWord_2857025 prefixEnd_2857025 326006014869286580055175 := by
  unfold tailWord_2857025
  simp only [CollatzResearch.WordTrace]
  refine ⟨104204262474493840868140529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69469508316329227245427019 104204262474493840868140529)
  ·
    refine ⟨78153196855870380651105397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104204262474493840868140529 78153196855870380651105397)
    ·
      refine ⟨7326862205237848186041131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78153196855870380651105397 7326862205237848186041131)
      ·
        refine ⟨10990293307856772279061697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326862205237848186041131 10990293307856772279061697)
        ·
          refine ⟨8242719980892579209296273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10990293307856772279061697 8242719980892579209296273)
          ·
            refine ⟨6182039985669434406972205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8242719980892579209296273 6182039985669434406972205)
            ·
              refine ⟨2318264994626037902614577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6182039985669434406972205 2318264994626037902614577)
              ·
                refine ⟨1738698745969528426960933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318264994626037902614577 1738698745969528426960933)
                ·
                  refine ⟨326006014869286580055175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738698745969528426960933 326006014869286580055175)
                  ·
                    rfl

theorem cell22_2857025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_2857025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857025 prefixEnd_2857025 := by exact prefixLift 2857025
  have htrace : WordTrace (prefixWord ++ tailWord_2857025) baseStart_2857025 baseEnd_2857025 := by
    simpa [prefixWord, tailWord_2857025, baseEnd_2857025] using wordTrace_append hprefix tailTrace_2857025
  have hstable : (prefixWord ++ tailWord_2857025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857025).length < 2 ^ (prefixWord ++ tailWord_2857025).sum := by decide
  have hdescent : baseEnd_2857025 < baseStart_2857025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857081 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 5]
def baseStart_2857081 : Nat := 118140960795 + 2857081 * 2 ^ 59
def prefixEnd_2857081 : Nat := 4983230072969 + 3 ^ 40 * 2857081 * 2
def baseEnd_2857081 : Nat := 326012404850764753588451

theorem tailTrace_2857081 : CollatzResearch.WordTrace tailWord_2857081 prefixEnd_2857081 326012404850764753588451 := by
  unfold tailWord_2857081
  simp only [CollatzResearch.WordTrace]
  refine ⟨104206304962290962432179097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69470869974860641621452731 104206304962290962432179097)
  ·
    refine ⟨78154728721718221824134323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104206304962290962432179097 78154728721718221824134323)
    ·
      refine ⟨117232093082577332736201485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78154728721718221824134323 117232093082577332736201485)
      ·
        refine ⟨43962034905966499776075557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117232093082577332736201485 43962034905966499776075557)
        ·
          refine ⟨8242881544868718708014167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43962034905966499776075557 8242881544868718708014167)
          ·
            refine ⟨12364322317303078062021251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8242881544868718708014167 12364322317303078062021251)
            ·
              refine ⟨18546483475954617093031877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364322317303078062021251 18546483475954617093031877)
              ·
                refine ⟨3477465651741490704943477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18546483475954617093031877 3477465651741490704943477)
                ·
                  refine ⟨326012404850764753588451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3477465651741490704943477 326012404850764753588451)
                  ·
                    rfl

theorem cell22_2857081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_2857081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857081 prefixEnd_2857081 := by exact prefixLift 2857081
  have htrace : WordTrace (prefixWord ++ tailWord_2857081) baseStart_2857081 baseEnd_2857081 := by
    simpa [prefixWord, tailWord_2857081, baseEnd_2857081] using wordTrace_append hprefix tailTrace_2857081
  have hstable : (prefixWord ++ tailWord_2857081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857081).length < 2 ^ (prefixWord ++ tailWord_2857081).sum := by decide
  have hdescent : baseEnd_2857081 < baseStart_2857081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857085 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_2857085 : Nat := 118140960795 + 2857085 * 2 ^ 59
def prefixEnd_2857085 : Nat := 4983230072969 + 3 ^ 40 * 2857085 * 2
def baseEnd_2857085 : Nat := 978038583834039583665341

theorem tailTrace_2857085 : CollatzResearch.WordTrace tailWord_2857085 prefixEnd_2857085 978038583834039583665341 := by
  unfold tailWord_2857085
  simp only [CollatzResearch.WordTrace]
  refine ⟨104206450854276471115324709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69470967236184314076883139 104206450854276471115324709)
  ·
    refine ⟨19538709535176838334123383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104206450854276471115324709 19538709535176838334123383)
    ·
      refine ⟨29308064302765257501185075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19538709535176838334123383 29308064302765257501185075)
      ·
        refine ⟨43962096454147886251777613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29308064302765257501185075 43962096454147886251777613)
        ·
          refine ⟨16485786170305457344416605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43962096454147886251777613 16485786170305457344416605)
          ·
            refine ⟨6182169813864546504156227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16485786170305457344416605 6182169813864546504156227)
            ·
              refine ⟨9273254720796819756234341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182169813864546504156227 9273254720796819756234341)
              ·
                refine ⟨1738735260149403704293939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9273254720796819756234341 1738735260149403704293939)
                ·
                  refine ⟨2608102890224105556440909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738735260149403704293939 2608102890224105556440909)
                  ·
                    refine ⟨978038583834039583665341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608102890224105556440909 978038583834039583665341)
                    ·
                      rfl

theorem cell22_2857085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_2857085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857085 prefixEnd_2857085 := by exact prefixLift 2857085
  have htrace : WordTrace (prefixWord ++ tailWord_2857085) baseStart_2857085 baseEnd_2857085 := by
    simpa [prefixWord, tailWord_2857085, baseEnd_2857085] using wordTrace_append hprefix tailTrace_2857085
  have hstable : (prefixWord ++ tailWord_2857085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857085).length < 2 ^ (prefixWord ++ tailWord_2857085).sum := by decide
  have hdescent : baseEnd_2857085 < baseStart_2857085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857096 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_2857096 : Nat := 118140960795 + 2857096 * 2 ^ 59
def prefixEnd_2857096 : Nat := 4983230072969 + 3 ^ 40 * 2857096 * 2
def baseEnd_2857096 : Nat := 978042349358839221640307

theorem tailTrace_2857096 : CollatzResearch.WordTrace tailWord_2857096 prefixEnd_2857096 978042349358839221640307 := by
  unfold tailWord_2857096
  simp only [CollatzResearch.WordTrace]
  refine ⟨52103426028618309996987571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69471234704824413329316761 52103426028618309996987571)
  ·
    refine ⟨78155139042927464995481357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52103426028618309996987571 78155139042927464995481357)
    ·
      refine ⟨29308177141097799373305509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78155139042927464995481357 29308177141097799373305509)
      ·
        refine ⟨5495283213955837382494783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29308177141097799373305509 5495283213955837382494783)
        ·
          refine ⟨8242924820933756073742175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5495283213955837382494783 8242924820933756073742175)
          ·
            refine ⟨12364387231400634110613263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8242924820933756073742175 12364387231400634110613263)
            ·
              refine ⟨18546580847100951165919895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364387231400634110613263 18546580847100951165919895)
              ·
                refine ⟨27819871270651426748879843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18546580847100951165919895 27819871270651426748879843)
                ·
                  refine ⟨41729806905977140123319765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27819871270651426748879843 41729806905977140123319765)
                  ·
                    refine ⟨978042349358839221640307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41729806905977140123319765 978042349358839221640307)
                    ·
                      rfl

theorem cell22_2857096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_2857096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857096 prefixEnd_2857096 := by exact prefixLift 2857096
  have htrace : WordTrace (prefixWord ++ tailWord_2857096) baseStart_2857096 baseEnd_2857096 := by
    simpa [prefixWord, tailWord_2857096, baseEnd_2857096] using wordTrace_append hprefix tailTrace_2857096
  have hstable : (prefixWord ++ tailWord_2857096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857096).length < 2 ^ (prefixWord ++ tailWord_2857096).sum := by decide
  have hdescent : baseEnd_2857096 < baseStart_2857096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857143 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 4]
def baseStart_2857143 : Nat := 118140960795 + 2857143 * 2 ^ 59
def prefixEnd_2857143 : Nat := 4983230072969 + 3 ^ 40 * 2857143 * 2
def baseEnd_2857143 : Nat := 326019479473115588571721

theorem tailTrace_2857143 : CollatzResearch.WordTrace tailWord_2857143 prefixEnd_2857143 326019479473115588571721 := by
  unfold tailWord_2857143
  simp only [CollatzResearch.WordTrace]
  refine ⟨104208566288066347020936083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69472377525377564680624055 104208566288066347020936083)
  ·
    refine ⟨156312849432099520531404125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104208566288066347020936083 156312849432099520531404125)
    ·
      refine ⟨58617318537037320199276547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156312849432099520531404125 58617318537037320199276547)
      ·
        refine ⟨87925977805555980298914821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58617318537037320199276547 87925977805555980298914821)
        ·
          refine ⟨16486120838541746306046529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87925977805555980298914821 16486120838541746306046529)
          ·
            refine ⟨12364590628906309729534897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16486120838541746306046529 12364590628906309729534897)
            ·
              refine ⟨9273442971679732297151173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12364590628906309729534897 9273442971679732297151173)
              ·
                refine ⟨1738770557189949805715845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9273442971679732297151173 1738770557189949805715845)
                ·
                  refine ⟨326019479473115588571721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738770557189949805715845 326019479473115588571721)
                  ·
                    rfl

theorem cell22_2857143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 4].length) (baseStart_2857143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857143 prefixEnd_2857143 := by exact prefixLift 2857143
  have htrace : WordTrace (prefixWord ++ tailWord_2857143) baseStart_2857143 baseEnd_2857143 := by
    simpa [prefixWord, tailWord_2857143, baseEnd_2857143] using wordTrace_append hprefix tailTrace_2857143
  have hstable : (prefixWord ++ tailWord_2857143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857143).length < 2 ^ (prefixWord ++ tailWord_2857143).sum := by decide
  have hdescent : baseEnd_2857143 < baseStart_2857143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857250 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2857250 : Nat := 118140960795 + 2857250 * 2 ^ 59
def prefixEnd_2857250 : Nat := 4983230072969 + 3 ^ 40 * 2857250 * 2
def baseEnd_2857250 : Nat := 326031688902011384429945

theorem tailTrace_2857250 : CollatzResearch.WordTrace tailWord_2857250 prefixEnd_2857250 326031688902011384429945 := by
  unfold tailWord_2857250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26053117224669676073770301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69474979265785802863387469 26053117224669676073770301)
  ·
    refine ⟨9769918959251128527663863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26053117224669676073770301 9769918959251128527663863)
    ·
      refine ⟨14654878438876692791495795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9769918959251128527663863 14654878438876692791495795)
      ·
        refine ⟨21982317658315039187243693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14654878438876692791495795 21982317658315039187243693)
        ·
          refine ⟨8243369121868139695216385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21982317658315039187243693 8243369121868139695216385)
          ·
            refine ⟨6182526841401104771412289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8243369121868139695216385 6182526841401104771412289)
            ·
              refine ⟨4636895131050828578559217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6182526841401104771412289 4636895131050828578559217)
              ·
                refine ⟨3477671348288121433919413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636895131050828578559217 3477671348288121433919413)
                ·
                  refine ⟨326031688902011384429945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3477671348288121433919413 326031688902011384429945)
                  ·
                    rfl

theorem cell22_2857250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2857250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857250 prefixEnd_2857250 := by exact prefixLift 2857250
  have htrace : WordTrace (prefixWord ++ tailWord_2857250) baseStart_2857250 baseEnd_2857250 := by
    simpa [prefixWord, tailWord_2857250, baseEnd_2857250] using wordTrace_append hprefix tailTrace_2857250
  have hstable : (prefixWord ++ tailWord_2857250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857250).length < 2 ^ (prefixWord ++ tailWord_2857250).sum := by decide
  have hdescent : baseEnd_2857250 < baseStart_2857250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857278 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2857278 : Nat := 118140960795 + 2857278 * 2 ^ 59
def prefixEnd_2857278 : Nat := 4983230072969 + 3 ^ 40 * 2857278 * 2
def baseEnd_2857278 : Nat := 326034883892750471196583

theorem tailTrace_2857278 : CollatzResearch.WordTrace tailWord_2857278 prefixEnd_2857278 326034883892750471196583 := by
  unfold tailWord_2857278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026686267822158134637561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69475660095051510051400325 13026686267822158134637561)
  ·
    refine ⟨9770014700866618600978171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13026686267822158134637561 9770014700866618600978171)
    ·
      refine ⟨14655022051299927901467257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770014700866618600978171 14655022051299927901467257)
      ·
        refine ⟨10991266538474945926100443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14655022051299927901467257 10991266538474945926100443)
        ·
          refine ⟨16486899807712418889150665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10991266538474945926100443 16486899807712418889150665)
          ·
            refine ⟨12365174855784314166862999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16486899807712418889150665 12365174855784314166862999)
            ·
              refine ⟨18547762283676471250294499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365174855784314166862999 18547762283676471250294499)
              ·
                refine ⟨27821643425514706875441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18547762283676471250294499 27821643425514706875441749)
                ·
                  refine ⟨326034883892750471196583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27821643425514706875441749 326034883892750471196583)
                  ·
                    rfl

theorem cell22_2857278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2857278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857278 prefixEnd_2857278 := by exact prefixLift 2857278
  have htrace : WordTrace (prefixWord ++ tailWord_2857278) baseStart_2857278 baseEnd_2857278 := by
    simpa [prefixWord, tailWord_2857278, baseEnd_2857278] using wordTrace_append hprefix tailTrace_2857278
  have hstable : (prefixWord ++ tailWord_2857278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857278).length < 2 ^ (prefixWord ++ tailWord_2857278).sum := by decide
  have hdescent : baseEnd_2857278 < baseStart_2857278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857297 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_2857297 : Nat := 118140960795 + 2857297 * 2 ^ 59
def prefixEnd_2857297 : Nat := 4983230072969 + 3 ^ 40 * 2857297 * 2
def baseEnd_2857297 : Nat := 978111155766541697364691

theorem tailTrace_2857297 : CollatzResearch.WordTrace tailWord_2857297 prefixEnd_2857297 978111155766541697364691 := by
  unfold tailWord_2857297
  simp only [CollatzResearch.WordTrace]
  refine ⟨104214183129508431322042145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69476122086338954214694763 104214183129508431322042145)
  ·
    refine ⟨78160637347131323491531609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104214183129508431322042145 78160637347131323491531609)
    ·
      refine ⟨58620478010348492618648707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78160637347131323491531609 58620478010348492618648707)
      ·
        refine ⟨87930717015522738927973061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58620478010348492618648707 87930717015522738927973061)
        ·
          refine ⟨16487009440410513548994949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87930717015522738927973061 16487009440410513548994949)
          ·
            refine ⟨3091314270076971290436553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16487009440410513548994949 3091314270076971290436553)
            ·
              refine ⟨2318485702557728467827415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3091314270076971290436553 2318485702557728467827415)
              ·
                refine ⟨3477728553836592701741123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318485702557728467827415 3477728553836592701741123)
                ·
                  refine ⟨5216592830754889052611685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477728553836592701741123 5216592830754889052611685)
                  ·
                    refine ⟨978111155766541697364691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216592830754889052611685 978111155766541697364691)
                    ·
                      rfl

theorem cell22_2857297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_2857297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857297 prefixEnd_2857297 := by exact prefixLift 2857297
  have htrace : WordTrace (prefixWord ++ tailWord_2857297) baseStart_2857297 baseEnd_2857297 := by
    simpa [prefixWord, tailWord_2857297, baseEnd_2857297] using wordTrace_append hprefix tailTrace_2857297
  have hstable : (prefixWord ++ tailWord_2857297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857297).length < 2 ^ (prefixWord ++ tailWord_2857297).sum := by decide
  have hdescent : baseEnd_2857297 < baseStart_2857297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857346 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2857346 : Nat := 118140960795 + 2857346 * 2 ^ 59
def prefixEnd_2857346 : Nat := 4983230072969 + 3 ^ 40 * 2857346 * 2
def baseEnd_2857346 : Nat := 326042643155973967629847

theorem tailTrace_2857346 : CollatzResearch.WordTrace tailWord_2857346 prefixEnd_2857346 326042643155973967629847 := by
  unfold tailWord_2857346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26053992576582728172643973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69477313537553941793717261 26053992576582728172643973)
  ·
    refine ⟨4885123608109261532370745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26053992576582728172643973 4885123608109261532370745)
    ·
      refine ⟨3663842706081946149278059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4885123608109261532370745 3663842706081946149278059)
      ·
        refine ⟨5495764059122919223917089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663842706081946149278059 5495764059122919223917089)
        ·
          refine ⟨4121823044342189417937817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495764059122919223917089 4121823044342189417937817)
          ·
            refine ⟨3091367283256642063453363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121823044342189417937817 3091367283256642063453363)
            ·
              refine ⟨4637050924884963095180045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091367283256642063453363 4637050924884963095180045)
              ·
                refine ⟨1738894096831861160692517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4637050924884963095180045 1738894096831861160692517)
                ·
                  refine ⟨326042643155973967629847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738894096831861160692517 326042643155973967629847)
                  ·
                    rfl

theorem cell22_2857346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2857346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857346 prefixEnd_2857346 := by exact prefixLift 2857346
  have htrace : WordTrace (prefixWord ++ tailWord_2857346) baseStart_2857346 baseEnd_2857346 := by
    simpa [prefixWord, tailWord_2857346, baseEnd_2857346] using wordTrace_append hprefix tailTrace_2857346
  have hstable : (prefixWord ++ tailWord_2857346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857346).length < 2 ^ (prefixWord ++ tailWord_2857346).sum := by decide
  have hdescent : baseEnd_2857346 < baseStart_2857346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857462 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2857462 : Nat := 118140960795 + 2857462 * 2 ^ 59
def prefixEnd_2857462 : Nat := 4983230072969 + 3 ^ 40 * 2857462 * 2
def baseEnd_2857462 : Nat := 978167638638536266989185

theorem tailTrace_2857462 : CollatzResearch.WordTrace tailWord_2857462 prefixEnd_2857462 978167638638536266989185 := by
  unfold tailWord_2857462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513762573369416531362415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69480134115940443001199093 6513762573369416531362415)
  ·
    refine ⟨9770643860054124797043623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6513762573369416531362415 9770643860054124797043623)
    ·
      refine ⟨14655965790081187195565435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770643860054124797043623 14655965790081187195565435)
      ·
        refine ⟨21983948685121780793348153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14655965790081187195565435 21983948685121780793348153)
        ·
          refine ⟨16487961513841335595011115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21983948685121780793348153 16487961513841335595011115)
          ·
            refine ⟨24731942270762003392516673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16487961513841335595011115 24731942270762003392516673)
            ·
              refine ⟨18548956703071502544387505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24731942270762003392516673 18548956703071502544387505)
              ·
                refine ⟨13911717527303626908290629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18548956703071502544387505 13911717527303626908290629)
                ·
                  refine ⟨2608447036369430045304493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13911717527303626908290629 2608447036369430045304493)
                  ·
                    refine ⟨978167638638536266989185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608447036369430045304493 978167638638536266989185)
                    ·
                      rfl

theorem cell22_2857462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2857462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857462 prefixEnd_2857462 := by exact prefixLift 2857462
  have htrace : WordTrace (prefixWord ++ tailWord_2857462) baseStart_2857462 baseEnd_2857462 := by
    simpa [prefixWord, tailWord_2857462, baseEnd_2857462] using wordTrace_append hprefix tailTrace_2857462
  have hstable : (prefixWord ++ tailWord_2857462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857462).length < 2 ^ (prefixWord ++ tailWord_2857462).sum := by decide
  have hdescent : baseEnd_2857462 < baseStart_2857462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857488 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_2857488 : Nat := 118140960795 + 2857488 * 2 ^ 59
def prefixEnd_2857488 : Nat := 4983230072969 + 3 ^ 40 * 2857488 * 2
def baseEnd_2857488 : Nat := 978176538969880865839105

theorem tailTrace_2857488 : CollatzResearch.WordTrace tailWord_2857488 prefixEnd_2857488 978176538969880865839105 := by
  unfold tailWord_2857488
  simp only [CollatzResearch.WordTrace]
  refine ⟨52110574735908235471122559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69480766314544313961496745 52110574735908235471122559)
  ·
    refine ⟨78165862103862353206683839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52110574735908235471122559 78165862103862353206683839)
    ·
      refine ⟨117248793155793529810025759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78165862103862353206683839 117248793155793529810025759)
      ·
        refine ⟨175873189733690294715038639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117248793155793529810025759 175873189733690294715038639)
        ·
          refine ⟨263809784600535442072557959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175873189733690294715038639 263809784600535442072557959)
          ·
            refine ⟨395714676900803163108836939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263809784600535442072557959 395714676900803163108836939)
            ·
              refine ⟨593572015351204744663255409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395714676900803163108836939 593572015351204744663255409)
              ·
                refine ⟨445179011513403558497441557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593572015351204744663255409 445179011513403558497441557)
                ·
                  refine ⟨20867766164690791804567573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 445179011513403558497441557 20867766164690791804567573)
                  ·
                    refine ⟨978176538969880865839105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20867766164690791804567573 978176538969880865839105)
                    ·
                      rfl

theorem cell22_2857488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_2857488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857488 prefixEnd_2857488 := by exact prefixLift 2857488
  have htrace : WordTrace (prefixWord ++ tailWord_2857488) baseStart_2857488 baseEnd_2857488 := by
    simpa [prefixWord, tailWord_2857488, baseEnd_2857488] using wordTrace_append hprefix tailTrace_2857488
  have hstable : (prefixWord ++ tailWord_2857488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857488).length < 2 ^ (prefixWord ++ tailWord_2857488).sum := by decide
  have hdescent : baseEnd_2857488 < baseStart_2857488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857507 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 3, 3]
def baseStart_2857507 : Nat := 118140960795 + 2857507 * 2 ^ 59
def prefixEnd_2857507 : Nat := 4983230072969 + 3 ^ 40 * 2857507 * 2
def baseEnd_2857507 : Nat := 978183043058171149614047

theorem tailTrace_2857507 : CollatzResearch.WordTrace tailWord_2857507 prefixEnd_2857507 978183043058171149614047 := by
  unfold tailWord_2857507
  simp only [CollatzResearch.WordTrace]
  refine ⟨104221842458747637187186775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69481228305831758124791183 104221842458747637187186775)
  ·
    refine ⟨156332763688121455780780163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104221842458747637187186775 156332763688121455780780163)
    ·
      refine ⟨234499145532182183671170245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156332763688121455780780163 234499145532182183671170245)
      ·
        refine ⟨43968589787284159438344421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234499145532182183671170245 43968589787284159438344421)
        ·
          refine ⟨8244110585115779894689579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43968589787284159438344421 8244110585115779894689579)
          ·
            refine ⟨12366165877673669842034369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244110585115779894689579 12366165877673669842034369)
            ·
              refine ⟨9274624408255252381525777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12366165877673669842034369 9274624408255252381525777)
              ·
                refine ⟨6955968306191439286144333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9274624408255252381525777 6955968306191439286144333)
                ·
                  refine ⟨2608488114821789732304125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6955968306191439286144333 2608488114821789732304125)
                  ·
                    refine ⟨978183043058171149614047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608488114821789732304125 978183043058171149614047)
                    ·
                      rfl

theorem cell22_2857507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3].length) (baseStart_2857507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857507 prefixEnd_2857507 := by exact prefixLift 2857507
  have htrace : WordTrace (prefixWord ++ tailWord_2857507) baseStart_2857507 baseEnd_2857507 := by
    simpa [prefixWord, tailWord_2857507, baseEnd_2857507] using wordTrace_append hprefix tailTrace_2857507
  have hstable : (prefixWord ++ tailWord_2857507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857507).length < 2 ^ (prefixWord ++ tailWord_2857507).sum := by decide
  have hdescent : baseEnd_2857507 < baseStart_2857507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857541 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_2857541 : Nat := 118140960795 + 2857541 * 2 ^ 59
def prefixEnd_2857541 : Nat := 4983230072969 + 3 ^ 40 * 2857541 * 2
def baseEnd_2857541 : Nat := 978194681953006394263943

theorem tailTrace_2857541 : CollatzResearch.WordTrace tailWord_2857541 prefixEnd_2857541 978194681953006394263943 := by
  unfold tailWord_2857541
  simp only [CollatzResearch.WordTrace]
  refine ⟨104223082540624460993924477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69482055027082973995949651 104223082540624460993924477)
  ·
    refine ⟨39083655952734172872721679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104223082540624460993924477 39083655952734172872721679)
    ·
      refine ⟨58625483929101259309082519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39083655952734172872721679 58625483929101259309082519)
      ·
        refine ⟨87938225893651888963623779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58625483929101259309082519 87938225893651888963623779)
        ·
          refine ⟨131907338840477833445435669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87938225893651888963623779 131907338840477833445435669)
          ·
            refine ⟨6183156508147398442754797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131907338840477833445435669 6183156508147398442754797)
            ·
              refine ⟨2318683690555274416033049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183156508147398442754797 2318683690555274416033049)
              ·
                refine ⟨1739012767916455812024787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318683690555274416033049 1739012767916455812024787)
                ·
                  refine ⟨2608519151874683718037181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739012767916455812024787 2608519151874683718037181)
                  ·
                    refine ⟨978194681953006394263943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608519151874683718037181 978194681953006394263943)
                    ·
                      rfl

theorem cell22_2857541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_2857541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857541 prefixEnd_2857541 := by exact prefixLift 2857541
  have htrace : WordTrace (prefixWord ++ tailWord_2857541) baseStart_2857541 baseEnd_2857541 := by
    simpa [prefixWord, tailWord_2857541, baseEnd_2857541] using wordTrace_append hprefix tailTrace_2857541
  have hstable : (prefixWord ++ tailWord_2857541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857541).length < 2 ^ (prefixWord ++ tailWord_2857541).sum := by decide
  have hdescent : baseEnd_2857541 < baseStart_2857541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857580 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_2857580 : Nat := 118140960795 + 2857580 * 2 ^ 59
def prefixEnd_2857580 : Nat := 4983230072969 + 3 ^ 40 * 2857580 * 2
def baseEnd_2857580 : Nat := 978208032450023292538823

theorem tailTrace_2857580 : CollatzResearch.WordTrace tailWord_2857580 prefixEnd_2857580 978208032450023292538823 := by
  unfold tailWord_2857580
  simp only [CollatzResearch.WordTrace]
  refine ⟨52112252493741585327297097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69483003324988780436396129 52112252493741585327297097)
  ·
    refine ⟨39084189370306188995472823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52112252493741585327297097 39084189370306188995472823)
    ·
      refine ⟨58626284055459283493209235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39084189370306188995472823 58626284055459283493209235)
      ·
        refine ⟨87939426083188925239813853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58626284055459283493209235 87939426083188925239813853)
        ·
          refine ⟨32977284781195846964930195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87939426083188925239813853 32977284781195846964930195)
          ·
            refine ⟨49465927171793770447395293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32977284781195846964930195 49465927171793770447395293)
            ·
              refine ⟨18549722689422663917773235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49465927171793770447395293 18549722689422663917773235)
              ·
                refine ⟨27824584034133995876659853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18549722689422663917773235 27824584034133995876659853)
                ·
                  refine ⟨10434219012800248453747445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27824584034133995876659853 10434219012800248453747445)
                  ·
                    refine ⟨978208032450023292538823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10434219012800248453747445 978208032450023292538823)
                    ·
                      rfl

theorem cell22_2857580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_2857580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857580 prefixEnd_2857580 := by exact prefixLift 2857580
  have htrace : WordTrace (prefixWord ++ tailWord_2857580) baseStart_2857580 baseEnd_2857580 := by
    simpa [prefixWord, tailWord_2857580, baseEnd_2857580] using wordTrace_append hprefix tailTrace_2857580
  have hstable : (prefixWord ++ tailWord_2857580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857580).length < 2 ^ (prefixWord ++ tailWord_2857580).sum := by decide
  have hdescent : baseEnd_2857580 < baseStart_2857580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857595 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_2857595 : Nat := 118140960795 + 2857595 * 2 ^ 59
def prefixEnd_2857595 : Nat := 4983230072969 + 3 ^ 40 * 2857595 * 2
def baseEnd_2857595 : Nat := 978213167256568253413777

theorem tailTrace_2857595 : CollatzResearch.WordTrace tailWord_2857595 prefixEnd_2857595 978213167256568253413777 := by
  unfold tailWord_2857595
  simp only [CollatzResearch.WordTrace]
  refine ⟨104225052082428828216390239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69483368054952552144260159 104225052082428828216390239)
  ·
    refine ⟨156337578123643242324585359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104225052082428828216390239 156337578123643242324585359)
    ·
      refine ⟨234506367185464863486878039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156337578123643242324585359 234506367185464863486878039)
      ·
        refine ⟨351759550778197295230317059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234506367185464863486878039 351759550778197295230317059)
        ·
          refine ⟨527639326167295942845475589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351759550778197295230317059 527639326167295942845475589)
          ·
            refine ⟨98932373656367989283526673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 527639326167295942845475589 98932373656367989283526673)
            ·
              refine ⟨74199280242275991962645005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98932373656367989283526673 74199280242275991962645005)
              ·
                refine ⟨27824730090853496985991877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74199280242275991962645005 27824730090853496985991877)
                ·
                  refine ⟨5217136892035030684873477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27824730090853496985991877 5217136892035030684873477)
                  ·
                    refine ⟨978213167256568253413777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217136892035030684873477 978213167256568253413777)
                    ·
                      rfl

theorem cell22_2857595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_2857595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857595 prefixEnd_2857595 := by exact prefixLift 2857595
  have htrace : WordTrace (prefixWord ++ tailWord_2857595) baseStart_2857595 baseEnd_2857595 := by
    simpa [prefixWord, tailWord_2857595, baseEnd_2857595] using wordTrace_append hprefix tailTrace_2857595
  have hstable : (prefixWord ++ tailWord_2857595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857595).length < 2 ^ (prefixWord ++ tailWord_2857595).sum := by decide
  have hdescent : baseEnd_2857595 < baseStart_2857595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857614 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_2857614 : Nat := 118140960795 + 2857614 * 2 ^ 59
def prefixEnd_2857614 : Nat := 4983230072969 + 3 ^ 40 * 2857614 * 2
def baseEnd_2857614 : Nat := 978219671344858537188719

theorem tailTrace_2857614 : CollatzResearch.WordTrace tailWord_2857614 prefixEnd_2857614 978219671344858537188719 := by
  unfold tailWord_2857614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13028218133669999307666487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69483830046239996307554597 13028218133669999307666487)
  ·
    refine ⟨19542327200504998961499731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13028218133669999307666487 19542327200504998961499731)
    ·
      refine ⟨29313490800757498442249597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19542327200504998961499731 29313490800757498442249597)
      ·
        refine ⟨10992559050284061915843599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29313490800757498442249597 10992559050284061915843599)
        ·
          refine ⟨16488838575426092873765399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10992559050284061915843599 16488838575426092873765399)
          ·
            refine ⟨24733257863139139310648099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16488838575426092873765399 24733257863139139310648099)
            ·
              refine ⟨37099886794708708965972149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24733257863139139310648099 37099886794708708965972149)
              ·
                refine ⟨3478114387003941465559889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37099886794708708965972149 3478114387003941465559889)
                ·
                  refine ⟨2608585790252956099169917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478114387003941465559889 2608585790252956099169917)
                  ·
                    refine ⟨978219671344858537188719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608585790252956099169917 978219671344858537188719)
                    ·
                      rfl

theorem cell22_2857614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_2857614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857614 prefixEnd_2857614 := by exact prefixLift 2857614
  have htrace : WordTrace (prefixWord ++ tailWord_2857614) baseStart_2857614 baseEnd_2857614 := by
    simpa [prefixWord, tailWord_2857614, baseEnd_2857614] using wordTrace_append hprefix tailTrace_2857614
  have hstable : (prefixWord ++ tailWord_2857614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857614).length < 2 ^ (prefixWord ++ tailWord_2857614).sum := by decide
  have hdescent : baseEnd_2857614 < baseStart_2857614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857665 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2857665 : Nat := 118140960795 + 2857665 * 2 ^ 59
def prefixEnd_2857665 : Nat := 4983230072969 + 3 ^ 40 * 2857665 * 2
def baseEnd_2857665 : Nat := 978237129687111404163563

theorem tailTrace_2857665 : CollatzResearch.WordTrace tailWord_2857665 prefixEnd_2857665 978237129687111404163563 := by
  unfold tailWord_2857665
  simp only [CollatzResearch.WordTrace]
  refine ⟨104227605192175230171438449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69485070128116820114292299 104227605192175230171438449)
  ·
    refine ⟨78170703894131422628578837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104227605192175230171438449 78170703894131422628578837)
    ·
      refine ⟨3664251745037410435714633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78170703894131422628578837 3664251745037410435714633)
      ·
        refine ⟨2748188808778057826785975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3664251745037410435714633 2748188808778057826785975)
        ·
          refine ⟨4122283213167086740178963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748188808778057826785975 4122283213167086740178963)
          ·
            refine ⟨6183424819750630110268445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122283213167086740178963 6183424819750630110268445)
            ·
              refine ⟨2318784307406486291350667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183424819750630110268445 2318784307406486291350667)
              ·
                refine ⟨3478176461109729437026001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318784307406486291350667 3478176461109729437026001)
                ·
                  refine ⟨2608632345832297077769501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478176461109729437026001 2608632345832297077769501)
                  ·
                    refine ⟨978237129687111404163563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608632345832297077769501 978237129687111404163563)
                    ·
                      rfl

theorem cell22_2857665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2857665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857665 prefixEnd_2857665 := by exact prefixLift 2857665
  have htrace : WordTrace (prefixWord ++ tailWord_2857665) baseStart_2857665 baseEnd_2857665 := by
    simpa [prefixWord, tailWord_2857665, baseEnd_2857665] using wordTrace_append hprefix tailTrace_2857665
  have hstable : (prefixWord ++ tailWord_2857665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857665).length < 2 ^ (prefixWord ++ tailWord_2857665).sum := by decide
  have hdescent : baseEnd_2857665 < baseStart_2857665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857736 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_2857736 : Nat := 118140960795 + 2857736 * 2 ^ 59
def prefixEnd_2857736 : Nat := 4983230072969 + 3 ^ 40 * 2857736 * 2
def baseEnd_2857736 : Nat := 978261434438090885638345

theorem tailTrace_2857736 : CollatzResearch.WordTrace tailWord_2857736 prefixEnd_2857736 978261434438090885638345 := by
  unfold tailWord_2857736
  simp only [CollatzResearch.WordTrace]
  refine ⟨52115097387459004648636531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69486796516612006198182041 52115097387459004648636531)
  ·
    refine ⟨78172646081188506972954797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52115097387459004648636531 78172646081188506972954797)
    ·
      refine ⟨29314742280445690114858049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78172646081188506972954797 29314742280445690114858049)
      ·
        refine ⟨21986056710334267586143537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29314742280445690114858049 21986056710334267586143537)
        ·
          refine ⟨16489542532750700689607653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21986056710334267586143537 16489542532750700689607653)
          ·
            refine ⟨3091789224890756379301435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16489542532750700689607653 3091789224890756379301435)
            ·
              refine ⟨4637683837336134568952153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091789224890756379301435 4637683837336134568952153)
              ·
                refine ⟨3478262878002100926714115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637683837336134568952153 3478262878002100926714115)
                ·
                  refine ⟨5217394317003151390071173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478262878002100926714115 5217394317003151390071173)
                  ·
                    refine ⟨978261434438090885638345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217394317003151390071173 978261434438090885638345)
                    ·
                      rfl

theorem cell22_2857736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_2857736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857736 prefixEnd_2857736 := by exact prefixLift 2857736
  have htrace : WordTrace (prefixWord ++ tailWord_2857736) baseStart_2857736 baseEnd_2857736 := by
    simpa [prefixWord, tailWord_2857736, baseEnd_2857736] using wordTrace_append hprefix tailTrace_2857736
  have hstable : (prefixWord ++ tailWord_2857736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857736).length < 2 ^ (prefixWord ++ tailWord_2857736).sum := by decide
  have hdescent : baseEnd_2857736 < baseStart_2857736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857762 : List Nat := [3, 3, 1, 1, 2, 12]
def baseStart_2857762 : Nat := 118140960795 + 2857762 * 2 ^ 59
def prefixEnd_2857762 : Nat := 4983230072969 + 3 ^ 40 * 2857762 * 2
def baseEnd_2857762 : Nat := 12077411540363401043065

theorem tailTrace_2857762 : CollatzResearch.WordTrace tailWord_2857762 prefixEnd_2857762 12077411540363401043065 := by
  unfold tailWord_2857762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057785768205953934429885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69487428715215877158479693 26057785768205953934429885)
  ·
    refine ⟨9771669663077232725411207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26057785768205953934429885 9771669663077232725411207)
    ·
      refine ⟨14657504494615849088116811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9771669663077232725411207 14657504494615849088116811)
      ·
        refine ⟨21986256741923773632175217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657504494615849088116811 21986256741923773632175217)
        ·
          refine ⟨16489692556442830224131413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21986256741923773632175217 16489692556442830224131413)
          ·
            refine ⟨12077411540363401043065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16489692556442830224131413 12077411540363401043065)
            ·
              rfl

theorem cell22_2857762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 12].length) (baseStart_2857762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857762 prefixEnd_2857762 := by exact prefixLift 2857762
  have htrace : WordTrace (prefixWord ++ tailWord_2857762) baseStart_2857762 baseEnd_2857762 := by
    simpa [prefixWord, tailWord_2857762, baseEnd_2857762] using wordTrace_append hprefix tailTrace_2857762
  have hstable : (prefixWord ++ tailWord_2857762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857762).length < 2 ^ (prefixWord ++ tailWord_2857762).sum := by decide
  have hdescent : baseEnd_2857762 < baseStart_2857762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857779 : List Nat := [1, 1, 1, 2, 6, 3, 1, 7]
def baseStart_2857779 : Nat := 118140960795 + 2857779 * 2 ^ 59
def prefixEnd_2857779 : Nat := 4983230072969 + 3 ^ 40 * 2857779 * 2
def baseEnd_2857779 : Nat := 108697350468539234090357

theorem tailTrace_2857779 : CollatzResearch.WordTrace tailWord_2857779 prefixEnd_2857779 108697350468539234090357 := by
  unfold tailWord_2857779
  simp only [CollatzResearch.WordTrace]
  refine ⟨104231763113762227641088391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69487842075841485094058927 104231763113762227641088391)
  ·
    refine ⟨156347644670643341461632587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104231763113762227641088391 156347644670643341461632587)
    ·
      refine ⟨234521467005965012192448881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156347644670643341461632587 234521467005965012192448881)
      ·
        refine ⟨175891100254473759144336661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234521467005965012192448881 175891100254473759144336661)
        ·
          refine ⟨8244895324428457459890781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175891100254473759144336661 8244895324428457459890781)
          ·
            refine ⟨3091835746660671547459043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8244895324428457459890781 3091835746660671547459043)
            ·
              refine ⟨4637753619991007321188565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091835746660671547459043 4637753619991007321188565)
              ·
                refine ⟨108697350468539234090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4637753619991007321188565 108697350468539234090357)
                ·
                  rfl

theorem cell22_2857779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 7].length) (baseStart_2857779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857779 prefixEnd_2857779 := by exact prefixLift 2857779
  have htrace : WordTrace (prefixWord ++ tailWord_2857779) baseStart_2857779 baseEnd_2857779 := by
    simpa [prefixWord, tailWord_2857779, baseEnd_2857779] using wordTrace_append hprefix tailTrace_2857779
  have hstable : (prefixWord ++ tailWord_2857779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857779).length < 2 ^ (prefixWord ++ tailWord_2857779).sum := by decide
  have hdescent : baseEnd_2857779 < baseStart_2857779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857798 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2857798 : Nat := 118140960795 + 2857798 * 2 ^ 59
def prefixEnd_2857798 : Nat := 4983230072969 + 3 ^ 40 * 2857798 * 2
def baseEnd_2857798 : Nat := 978282658305143390588155

theorem tailTrace_2857798 : CollatzResearch.WordTrace tailWord_2857798 prefixEnd_2857798 978282658305143390588155 := by
  unfold tailWord_2857798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257264253146668558938439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69488304067128929257353365 3257264253146668558938439)
  ·
    refine ⟨4885896379720002838407659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257264253146668558938439 4885896379720002838407659)
    ·
      refine ⟨7328844569580004257611489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885896379720002838407659 7328844569580004257611489)
      ·
        refine ⟨5496633427185003193208617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7328844569580004257611489 5496633427185003193208617)
        ·
          refine ⟨4122475070388752394906463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5496633427185003193208617 4122475070388752394906463)
          ·
            refine ⟨6183712605583128592359695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122475070388752394906463 6183712605583128592359695)
            ·
              refine ⟨9275568908374692888539543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183712605583128592359695 9275568908374692888539543)
              ·
                refine ⟨13913353362562039332809315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9275568908374692888539543 13913353362562039332809315)
                ·
                  refine ⟨20870030043843058999213973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13913353362562039332809315 20870030043843058999213973)
                  ·
                    refine ⟨978282658305143390588155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20870030043843058999213973 978282658305143390588155)
                    ·
                      rfl

theorem cell22_2857798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2857798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857798 prefixEnd_2857798 := by exact prefixLift 2857798
  have htrace : WordTrace (prefixWord ++ tailWord_2857798) baseStart_2857798 baseEnd_2857798 := by
    simpa [prefixWord, tailWord_2857798, baseEnd_2857798] using wordTrace_append hprefix tailTrace_2857798
  have hstable : (prefixWord ++ tailWord_2857798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857798).length < 2 ^ (prefixWord ++ tailWord_2857798).sum := by decide
  have hdescent : baseEnd_2857798 < baseStart_2857798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857828 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_2857828 : Nat := 118140960795 + 2857828 * 2 ^ 59
def prefixEnd_2857828 : Nat := 4983230072969 + 3 ^ 40 * 2857828 * 2
def baseEnd_2857828 : Nat := 978292927918233312338063

theorem tailTrace_2857828 : CollatzResearch.WordTrace tailWord_2857828 prefixEnd_2857828 978292927918233312338063 := by
  unfold tailWord_2857828
  simp only [CollatzResearch.WordTrace]
  refine ⟨52116775145292354504811069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69489033527056472673081425 52116775145292354504811069)
  ·
    refine ⟨19543790679484632939304151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52116775145292354504811069 19543790679484632939304151)
    ·
      refine ⟨29315686019226949408956227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19543790679484632939304151 29315686019226949408956227)
      ·
        refine ⟨43973529028840424113434341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29315686019226949408956227 43973529028840424113434341)
        ·
          refine ⟨8245036692907579521268939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43973529028840424113434341 8245036692907579521268939)
          ·
            refine ⟨12367555039361369281903409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245036692907579521268939 12367555039361369281903409)
            ·
              refine ⟨9275666279521026961427557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12367555039361369281903409 9275666279521026961427557)
              ·
                refine ⟨1739187427410192555267667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9275666279521026961427557 1739187427410192555267667)
                ·
                  refine ⟨2608781141115288832901501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739187427410192555267667 2608781141115288832901501)
                  ·
                    refine ⟨978292927918233312338063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608781141115288832901501 978292927918233312338063)
                    ·
                      rfl

theorem cell22_2857828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_2857828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857828 prefixEnd_2857828 := by exact prefixLift 2857828
  have htrace : WordTrace (prefixWord ++ tailWord_2857828) baseStart_2857828 baseEnd_2857828 := by
    simpa [prefixWord, tailWord_2857828, baseEnd_2857828] using wordTrace_append hprefix tailTrace_2857828
  have hstable : (prefixWord ++ tailWord_2857828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857828).length < 2 ^ (prefixWord ++ tailWord_2857828).sum := by decide
  have hdescent : baseEnd_2857828 < baseStart_2857828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857841 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 5]
def baseStart_2857841 : Nat := 118140960795 + 2857841 * 2 ^ 59
def prefixEnd_2857841 : Nat := 4983230072969 + 3 ^ 40 * 2857841 * 2
def baseEnd_2857841 : Nat := 326099126027968537254341

theorem tailTrace_2857841 : CollatzResearch.WordTrace tailWord_2857841 prefixEnd_2857841 326099126027968537254341 := by
  unfold tailWord_2857841
  simp only [CollatzResearch.WordTrace]
  refine ⟨104234024439537612229845377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69489349626358408153230251 104234024439537612229845377)
  ·
    refine ⟨78175518329653209172384033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104234024439537612229845377 78175518329653209172384033)
    ·
      refine ⟨58631638747239906879288025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78175518329653209172384033 58631638747239906879288025)
      ·
        refine ⟨43973729060429930159466019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58631638747239906879288025 43973729060429930159466019)
        ·
          refine ⟨65960593590644895239199029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43973729060429930159466019 65960593590644895239199029)
          ·
            refine ⟨6183805649122958928674909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65960593590644895239199029 6183805649122958928674909)
            ·
              refine ⟨2318927118421109598253091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183805649122958928674909 2318927118421109598253091)
              ·
                refine ⟨3478390677631664397379637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318927118421109598253091 3478390677631664397379637)
                ·
                  refine ⟨326099126027968537254341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478390677631664397379637 326099126027968537254341)
                  ·
                    rfl

theorem cell22_2857841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_2857841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857841 prefixEnd_2857841 := by exact prefixLift 2857841
  have htrace : WordTrace (prefixWord ++ tailWord_2857841) baseStart_2857841 baseEnd_2857841 := by
    simpa [prefixWord, tailWord_2857841, baseEnd_2857841] using wordTrace_append hprefix tailTrace_2857841
  have hstable : (prefixWord ++ tailWord_2857841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857841).length < 2 ^ (prefixWord ++ tailWord_2857841).sum := by decide
  have hdescent : baseEnd_2857841 < baseStart_2857841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857905 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_2857905 : Nat := 118140960795 + 2857905 * 2 ^ 59
def prefixEnd_2857905 : Nat := 4983230072969 + 3 ^ 40 * 2857905 * 2
def baseEnd_2857905 : Nat := 978319286591830778162827

theorem tailTrace_2857905 : CollatzResearch.WordTrace tailWord_2857905 prefixEnd_2857905 978319286591830778162827 := by
  unfold tailWord_2857905
  simp only [CollatzResearch.WordTrace]
  refine ⟨104236358711305751160175169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69490905807537167440116779 104236358711305751160175169)
  ·
    refine ⟨78177269033479313370131377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104236358711305751160175169 78177269033479313370131377)
    ·
      refine ⟨58632951775109485027598533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78177269033479313370131377 58632951775109485027598533)
      ·
        refine ⟨10993678457833028442674725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58632951775109485027598533 10993678457833028442674725)
        ·
          refine ⟨2061314710843692833001511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10993678457833028442674725 2061314710843692833001511)
          ·
            refine ⟨3091972066265539249502267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061314710843692833001511 3091972066265539249502267)
            ·
              refine ⟨4637958099398308874253401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091972066265539249502267 4637958099398308874253401)
              ·
                refine ⟨3478468574548731655690051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637958099398308874253401 3478468574548731655690051)
                ·
                  refine ⟨5217702861823097483535077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478468574548731655690051 5217702861823097483535077)
                  ·
                    refine ⟨978319286591830778162827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217702861823097483535077 978319286591830778162827)
                    ·
                      rfl

theorem cell22_2857905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_2857905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857905 prefixEnd_2857905 := by exact prefixLift 2857905
  have htrace : WordTrace (prefixWord ++ tailWord_2857905) baseStart_2857905 baseEnd_2857905 := by
    simpa [prefixWord, tailWord_2857905, baseEnd_2857905] using wordTrace_append hprefix tailTrace_2857905
  have hstable : (prefixWord ++ tailWord_2857905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857905).length < 2 ^ (prefixWord ++ tailWord_2857905).sum := by decide
  have hdescent : baseEnd_2857905 < baseStart_2857905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857944 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_2857944 : Nat := 118140960795 + 2857944 * 2 ^ 59
def prefixEnd_2857944 : Nat := 4983230072969 + 3 ^ 40 * 2857944 * 2
def baseEnd_2857944 : Nat := 978332637088847676437707

theorem tailTrace_2857944 : CollatzResearch.WordTrace tailWord_2857944 prefixEnd_2857944 978332637088847676437707 := by
  unfold tailWord_2857944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52118890579082230410422443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69491854105442973880563257 52118890579082230410422443)
  ·
    refine ⟨78178335868623345615633665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52118890579082230410422443 78178335868623345615633665)
    ·
      refine ⟨58633751901467509211725249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78178335868623345615633665 58633751901467509211725249)
      ·
        refine ⟨43975313926100631908793937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58633751901467509211725249 43975313926100631908793937)
        ·
          refine ⟨32981485444575473931595453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43975313926100631908793937 32981485444575473931595453)
          ·
            refine ⟨12368057041715802724348295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32981485444575473931595453 12368057041715802724348295)
            ·
              refine ⟨18552085562573704086522443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12368057041715802724348295 18552085562573704086522443)
              ·
                refine ⟨27828128343860556129783665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18552085562573704086522443 27828128343860556129783665)
                ·
                  refine ⟨20871096257895417097337749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27828128343860556129783665 20871096257895417097337749)
                  ·
                    refine ⟨978332637088847676437707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20871096257895417097337749 978332637088847676437707)
                    ·
                      rfl

theorem cell22_2857944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_2857944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857944 prefixEnd_2857944 := by exact prefixLift 2857944
  have htrace : WordTrace (prefixWord ++ tailWord_2857944) baseStart_2857944 baseEnd_2857944 := by
    simpa [prefixWord, tailWord_2857944, baseEnd_2857944] using wordTrace_append hprefix tailTrace_2857944
  have hstable : (prefixWord ++ tailWord_2857944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857944).length < 2 ^ (prefixWord ++ tailWord_2857944).sum := by decide
  have hdescent : baseEnd_2857944 < baseStart_2857944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857980 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_2857980 : Nat := 118140960795 + 2857980 * 2 ^ 59
def prefixEnd_2857980 : Nat := 4983230072969 + 3 ^ 40 * 2857980 * 2
def baseEnd_2857980 : Nat := 978344960624555582537597

theorem tailTrace_2857980 : CollatzResearch.WordTrace tailWord_2857980 prefixEnd_2857980 978344960624555582537597 := by
  unfold tailWord_2857980
  simp only [CollatzResearch.WordTrace]
  refine ⟨52119547093017019484577697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69492729457356025979436929 52119547093017019484577697)
  ·
    refine ⟨39089660319762764613433273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52119547093017019484577697 39089660319762764613433273)
    ·
      refine ⟨29317245239822073460074955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39089660319762764613433273 29317245239822073460074955)
      ·
        refine ⟨43975867859733110190112433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29317245239822073460074955 43975867859733110190112433)
        ·
          refine ⟨32981900894799832642584325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43975867859733110190112433 32981900894799832642584325)
          ·
            refine ⟨6184106417774968620484561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32981900894799832642584325 6184106417774968620484561)
            ·
              refine ⟨4638079813331226465363421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6184106417774968620484561 4638079813331226465363421)
              ·
                refine ⟨1739279929999209924511283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4638079813331226465363421 1739279929999209924511283)
                ·
                  refine ⟨2608919894998814886766925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739279929999209924511283 2608919894998814886766925)
                  ·
                    refine ⟨978344960624555582537597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608919894998814886766925 978344960624555582537597)
                    ·
                      rfl

theorem cell22_2857980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_2857980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2857980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2857980 prefixEnd_2857980 := by exact prefixLift 2857980
  have htrace : WordTrace (prefixWord ++ tailWord_2857980) baseStart_2857980 baseEnd_2857980 := by
    simpa [prefixWord, tailWord_2857980, baseEnd_2857980] using wordTrace_append hprefix tailTrace_2857980
  have hstable : (prefixWord ++ tailWord_2857980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857980).length < 2 ^ (prefixWord ++ tailWord_2857980).sum := by decide
  have hdescent : baseEnd_2857980 < baseStart_2857980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858051 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_2858051 : Nat := 118140960795 + 2858051 * 2 ^ 59
def prefixEnd_2858051 : Nat := 4983230072969 + 3 ^ 40 * 2858051 * 2
def baseEnd_2858051 : Nat := 978369265375535064012379

theorem tailTrace_2858051 : CollatzResearch.WordTrace tailWord_2858051 prefixEnd_2858051 978369265375535064012379 := by
  unfold tailWord_2858051
  simp only [CollatzResearch.WordTrace]
  refine ⟨104241683768776818094990007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69494455845851212063326671 104241683768776818094990007)
  ·
    refine ⟨156362525653165227142485011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104241683768776818094990007 156362525653165227142485011)
    ·
      refine ⟨234543788479747840713727517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156362525653165227142485011 234543788479747840713727517)
      ·
        refine ⟨87953920679905440267647819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234543788479747840713727517 87953920679905440267647819)
        ·
          refine ⟨131930881019858160401471729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87953920679905440267647819 131930881019858160401471729)
          ·
            refine ⟨98948160764893620301103797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131930881019858160401471729 98948160764893620301103797)
            ·
              refine ⟨9276390071708776903228481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98948160764893620301103797 9276390071708776903228481)
              ·
                refine ⟨6957292553781582677421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9276390071708776903228481 6957292553781582677421361)
                ·
                  refine ⟨5217969415336187008066021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6957292553781582677421361 5217969415336187008066021)
                  ·
                    refine ⟨978369265375535064012379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217969415336187008066021 978369265375535064012379)
                    ·
                      rfl

theorem cell22_2858051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_2858051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858051 prefixEnd_2858051 := by exact prefixLift 2858051
  have htrace : WordTrace (prefixWord ++ tailWord_2858051) baseStart_2858051 baseEnd_2858051 := by
    simpa [prefixWord, tailWord_2858051, baseEnd_2858051] using wordTrace_append hprefix tailTrace_2858051
  have hstable : (prefixWord ++ tailWord_2858051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858051).length < 2 ^ (prefixWord ++ tailWord_2858051).sum := by decide
  have hdescent : baseEnd_2858051 < baseStart_2858051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858055 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 4]
def baseStart_2858055 : Nat := 118140960795 + 2858055 * 2 ^ 59
def prefixEnd_2858055 : Nat := 4983230072969 + 3 ^ 40 * 2858055 * 2
def baseEnd_2858055 : Nat := 326123544885760128970789

theorem tailTrace_2858055 : CollatzResearch.WordTrace tailWord_2858055 prefixEnd_2858055 326123544885760128970789 := by
  unfold tailWord_2858055
  simp only [CollatzResearch.WordTrace]
  refine ⟨104241829660762326778135619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69494553107174884518757079 104241829660762326778135619)
  ·
    refine ⟨156362744491143490167203429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104241829660762326778135619 156362744491143490167203429)
    ·
      refine ⟨29318014592089404406350643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156362744491143490167203429 29318014592089404406350643)
      ·
        refine ⟨43977021888134106609525965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29318014592089404406350643 43977021888134106609525965)
        ·
          refine ⟨16491383208050289978572237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43977021888134106609525965 16491383208050289978572237)
          ·
            refine ⟨6184268703018858741964589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16491383208050289978572237 6184268703018858741964589)
            ·
              refine ⟨2319100763632072028236721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6184268703018858741964589 2319100763632072028236721)
              ·
                refine ⟨1739325572724054021177541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319100763632072028236721 1739325572724054021177541)
                ·
                  refine ⟨326123544885760128970789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739325572724054021177541 326123544885760128970789)
                  ·
                    rfl

theorem cell22_2858055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 4].length) (baseStart_2858055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858055 prefixEnd_2858055 := by exact prefixLift 2858055
  have htrace : WordTrace (prefixWord ++ tailWord_2858055) baseStart_2858055 baseEnd_2858055 := by
    simpa [prefixWord, tailWord_2858055, baseEnd_2858055] using wordTrace_append hprefix tailTrace_2858055
  have hstable : (prefixWord ++ tailWord_2858055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858055).length < 2 ^ (prefixWord ++ tailWord_2858055).sum := by decide
  have hdescent : baseEnd_2858055 < baseStart_2858055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858066 : List Nat := [3, 2, 2, 1, 3, 1, 1, 9]
def baseStart_2858066 : Nat := 118140960795 + 2858066 * 2 ^ 59
def prefixEnd_2858066 : Nat := 4983230072969 + 3 ^ 40 * 2858066 * 2
def baseEnd_2858066 : Nat := 108708266686897780543037

theorem tailTrace_2858066 : CollatzResearch.WordTrace tailWord_2858066 prefixEnd_2858066 108708266686897780543037 := by
  unfold tailWord_2858066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26060557715930618914196513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69494820575814983771190701 26060557715930618914196513)
  ·
    refine ⟨19545418286947964185647385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26060557715930618914196513 19545418286947964185647385)
    ·
      refine ⟨14659063715210973139235539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19545418286947964185647385 14659063715210973139235539)
      ·
        refine ⟨21988595572816459708853309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14659063715210973139235539 21988595572816459708853309)
        ·
          refine ⟨8245723339806172390819991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21988595572816459708853309 8245723339806172390819991)
          ·
            refine ⟨12368585009709258586229987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245723339806172390819991 12368585009709258586229987)
            ·
              refine ⟨18552877514563887879344981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12368585009709258586229987 18552877514563887879344981)
              ·
                refine ⟨108708266686897780543037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18552877514563887879344981 108708266686897780543037)
                ·
                  rfl

theorem cell22_2858066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_2858066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858066 prefixEnd_2858066 := by exact prefixLift 2858066
  have htrace : WordTrace (prefixWord ++ tailWord_2858066) baseStart_2858066 baseEnd_2858066 := by
    simpa [prefixWord, tailWord_2858066, baseEnd_2858066] using wordTrace_append hprefix tailTrace_2858066
  have hstable : (prefixWord ++ tailWord_2858066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858066).length < 2 ^ (prefixWord ++ tailWord_2858066).sum := by decide
  have hdescent : baseEnd_2858066 < baseStart_2858066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858115 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 1, 3]
def baseStart_2858115 : Nat := 118140960795 + 2858115 * 2 ^ 59
def prefixEnd_2858115 : Nat := 4983230072969 + 3 ^ 40 * 2858115 * 2
def baseEnd_2858115 : Nat := 978391173883460230412183

theorem tailTrace_2858115 : CollatzResearch.WordTrace tailWord_2858115 prefixEnd_2858115 978391173883460230412183 := by
  unfold tailWord_2858115
  simp only [CollatzResearch.WordTrace]
  refine ⟨104244018040544957025319799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69496012027029971350213199 104244018040544957025319799)
  ·
    refine ⟨156366027060817435537979699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104244018040544957025319799 156366027060817435537979699)
    ·
      refine ⟨234549040591226153306969549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156366027060817435537979699 234549040591226153306969549)
      ·
        refine ⟨87955890221709807490113581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234549040591226153306969549 87955890221709807490113581)
        ·
          refine ⟨32983458833141177808792593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87955890221709807490113581 32983458833141177808792593)
          ·
            refine ⟨24737594124855883356594445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32983458833141177808792593 24737594124855883356594445)
            ·
              refine ⟨9276597796820956258722917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24737594124855883356594445 9276597796820956258722917)
              ·
                refine ⟨1739362086903929298510547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9276597796820956258722917 1739362086903929298510547)
                ·
                  refine ⟨2609043130355893947765821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739362086903929298510547 2609043130355893947765821)
                  ·
                    refine ⟨978391173883460230412183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609043130355893947765821 978391173883460230412183)
                    ·
                      rfl

theorem cell22_2858115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 3].length) (baseStart_2858115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858115 prefixEnd_2858115 := by exact prefixLift 2858115
  have htrace : WordTrace (prefixWord ++ tailWord_2858115) baseStart_2858115 baseEnd_2858115 := by
    simpa [prefixWord, tailWord_2858115, baseEnd_2858115] using wordTrace_append hprefix tailTrace_2858115
  have hstable : (prefixWord ++ tailWord_2858115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858115).length < 2 ^ (prefixWord ++ tailWord_2858115).sum := by decide
  have hdescent : baseEnd_2858115 < baseStart_2858115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858218 : List Nat := [3, 1, 3, 1, 1, 5, 8]
def baseStart_2858218 : Nat := 118140960795 + 2858218 * 2 ^ 59
def prefixEnd_2858218 : Nat := 4983230072969 + 3 ^ 40 * 2858218 * 2
def baseEnd_2858218 : Nat := 36238016032903788706921

theorem tailTrace_2858218 : CollatzResearch.WordTrace tailWord_2858218 prefixEnd_2858218 36238016032903788706921 := by
  unfold tailWord_2858218
  simp only [CollatzResearch.WordTrace]
  refine ⟨26061943689792951404079827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69498516506114537077546205 26061943689792951404079827)
  ·
    refine ⟨39092915534689427106119741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26061943689792951404079827 39092915534689427106119741)
    ·
      refine ⟨14659843325508535164794903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39092915534689427106119741 14659843325508535164794903)
      ·
        refine ⟨21989764988262802747192355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14659843325508535164794903 21989764988262802747192355)
        ·
          refine ⟨32984647482394204120788533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21989764988262802747192355 32984647482394204120788533)
          ·
            refine ⟨3092310701474456636323925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32984647482394204120788533 3092310701474456636323925)
            ·
              refine ⟨36238016032903788706921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3092310701474456636323925 36238016032903788706921)
              ·
                rfl

theorem cell22_2858218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 8].length) (baseStart_2858218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858218 prefixEnd_2858218 := by exact prefixLift 2858218
  have htrace : WordTrace (prefixWord ++ tailWord_2858218) baseStart_2858218 baseEnd_2858218 := by
    simpa [prefixWord, tailWord_2858218, baseEnd_2858218] using wordTrace_append hprefix tailTrace_2858218
  have hstable : (prefixWord ++ tailWord_2858218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858218).length < 2 ^ (prefixWord ++ tailWord_2858218).sum := by decide
  have hdescent : baseEnd_2858218 < baseStart_2858218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858231 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2858231 : Nat := 118140960795 + 2858231 * 2 ^ 59
def prefixEnd_2858231 : Nat := 4983230072969 + 3 ^ 40 * 2858231 * 2
def baseEnd_2858231 : Nat := 978430883054074594511827

theorem tailTrace_2858231 : CollatzResearch.WordTrace tailWord_2858231 prefixEnd_2858231 978430883054074594511827 := by
  unfold tailWord_2858231
  simp only [CollatzResearch.WordTrace]
  refine ⟨104248248908124708836542547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69498832605416472557695031 104248248908124708836542547)
  ·
    refine ⟨156372373362187063254813821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104248248908124708836542547 156372373362187063254813821)
    ·
      refine ⟨58639640010820148720555183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156372373362187063254813821 58639640010820148720555183)
      ·
        refine ⟨87959460016230223080832775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58639640010820148720555183 87959460016230223080832775)
        ·
          refine ⟨131939190024345334621249163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87959460016230223080832775 131939190024345334621249163)
          ·
            refine ⟨197908785036518001931873745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131939190024345334621249163 197908785036518001931873745)
            ·
              refine ⟨148431588777388501448905309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197908785036518001931873745 148431588777388501448905309)
              ·
                refine ⟨55661845791520688043339491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148431588777388501448905309 55661845791520688043339491)
                ·
                  refine ⟨83492768687281032065009237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55661845791520688043339491 83492768687281032065009237)
                  ·
                    refine ⟨978430883054074594511827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83492768687281032065009237 978430883054074594511827)
                    ·
                      rfl

theorem cell22_2858231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2858231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858231 prefixEnd_2858231 := by exact prefixLift 2858231
  have htrace : WordTrace (prefixWord ++ tailWord_2858231) baseStart_2858231 baseEnd_2858231 := by
    simpa [prefixWord, tailWord_2858231, baseEnd_2858231] using wordTrace_append hprefix tailTrace_2858231
  have hstable : (prefixWord ++ tailWord_2858231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858231).length < 2 ^ (prefixWord ++ tailWord_2858231).sum := by decide
  have hdescent : baseEnd_2858231 < baseStart_2858231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858280 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_2858280 : Nat := 118140960795 + 2858280 * 2 ^ 59
def prefixEnd_2858280 : Nat := 4983230072969 + 3 ^ 40 * 2858280 * 2
def baseEnd_2858280 : Nat := 326149218918484933345559

theorem tailTrace_2858280 : CollatzResearch.WordTrace tailWord_2858280 prefixEnd_2858280 326149218918484933345559 := by
  unfold tailWord_2858280
  simp only [CollatzResearch.WordTrace]
  refine ⟨52125018042473595102538147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69500024056631460136717529 52125018042473595102538147)
  ·
    refine ⟨78187527063710392653807221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52125018042473595102538147 78187527063710392653807221)
    ·
      refine ⟨7330080662222849311294427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78187527063710392653807221 7330080662222849311294427)
      ·
        refine ⟨10995120993334273966941641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330080662222849311294427 10995120993334273966941641)
        ·
          refine ⟨8246340745000705475206231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10995120993334273966941641 8246340745000705475206231)
          ·
            refine ⟨12369511117501058212809347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246340745000705475206231 12369511117501058212809347)
            ·
              refine ⟨18554266676251587319214021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12369511117501058212809347 18554266676251587319214021)
              ·
                refine ⟨3478925001797172622352629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18554266676251587319214021 3478925001797172622352629)
                ·
                  refine ⟨326149218918484933345559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478925001797172622352629 326149218918484933345559)
                  ·
                    rfl

theorem cell22_2858280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_2858280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858280 prefixEnd_2858280 := by exact prefixLift 2858280
  have htrace : WordTrace (prefixWord ++ tailWord_2858280) baseStart_2858280 baseEnd_2858280 := by
    simpa [prefixWord, tailWord_2858280, baseEnd_2858280] using wordTrace_append hprefix tailTrace_2858280
  have hstable : (prefixWord ++ tailWord_2858280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858280).length < 2 ^ (prefixWord ++ tailWord_2858280).sum := by decide
  have hdescent : baseEnd_2858280 < baseStart_2858280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858323 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_2858323 : Nat := 118140960795 + 2858323 * 2 ^ 59
def prefixEnd_2858323 : Nat := 4983230072969 + 3 ^ 40 * 2858323 * 2
def baseEnd_2858323 : Nat := 978462376534217021211545

theorem tailTrace_2858323 : CollatzResearch.WordTrace tailWord_2858323 prefixEnd_2858323 978462376534217021211545 := by
  unfold tailWord_2858323
  simp only [CollatzResearch.WordTrace]
  refine ⟨104251604423791408548891623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69501069615860939032594415 104251604423791408548891623)
  ·
    refine ⟨156377406635687112823337435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104251604423791408548891623 156377406635687112823337435)
    ·
      refine ⟨234566109953530669235006153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156377406635687112823337435 234566109953530669235006153)
      ·
        refine ⟨175924582465148001926254615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234566109953530669235006153 175924582465148001926254615)
        ·
          refine ⟨263886873697722002889381923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175924582465148001926254615 263886873697722002889381923)
          ·
            refine ⟨395830310546583004334072885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263886873697722002889381923 395830310546583004334072885)
            ·
              refine ⟨37109091613742156656319333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 395830310546583004334072885 37109091613742156656319333)
              ·
                refine ⟨6957954677576654373059875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37109091613742156656319333 6957954677576654373059875)
                ·
                  refine ⟨10436932016364981559589813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957954677576654373059875 10436932016364981559589813)
                  ·
                    refine ⟨978462376534217021211545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10436932016364981559589813 978462376534217021211545)
                    ·
                      rfl

theorem cell22_2858323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_2858323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858323 prefixEnd_2858323 := by exact prefixLift 2858323
  have htrace : WordTrace (prefixWord ++ tailWord_2858323) baseStart_2858323 baseEnd_2858323 := by
    simpa [prefixWord, tailWord_2858323, baseEnd_2858323] using wordTrace_append hprefix tailTrace_2858323
  have hstable : (prefixWord ++ tailWord_2858323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858323).length < 2 ^ (prefixWord ++ tailWord_2858323).sum := by decide
  have hdescent : baseEnd_2858323 < baseStart_2858323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858327 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 1, 4]
def baseStart_2858327 : Nat := 118140960795 + 2858327 * 2 ^ 59
def prefixEnd_2858327 : Nat := 4983230072969 + 3 ^ 40 * 2858327 * 2
def baseEnd_2858327 : Nat := 978463745815962344111533

theorem tailTrace_2858327 : CollatzResearch.WordTrace tailWord_2858327 prefixEnd_2858327 978463745815962344111533 := by
  unfold tailWord_2858327
  simp only [CollatzResearch.WordTrace]
  refine ⟨104251750315776917232037235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69501166877184611488024823 104251750315776917232037235)
  ·
    refine ⟨156377625473665375848055853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104251750315776917232037235 156377625473665375848055853)
    ·
      refine ⟨58641609552624515943020945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156377625473665375848055853 58641609552624515943020945)
      ·
        refine ⟨43981207164468386957265709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58641609552624515943020945 43981207164468386957265709)
        ·
          refine ⟨16492952686675645108974641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43981207164468386957265709 16492952686675645108974641)
          ·
            refine ⟨12369714515006733831730981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16492952686675645108974641 12369714515006733831730981)
            ·
              refine ⟨2319321471563762593449559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12369714515006733831730981 2319321471563762593449559)
              ·
                refine ⟨3478982207345643890174339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319321471563762593449559 3478982207345643890174339)
                ·
                  refine ⟨5218473311018465835261509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478982207345643890174339 5218473311018465835261509)
                  ·
                    refine ⟨978463745815962344111533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5218473311018465835261509 978463745815962344111533)
                    ·
                      rfl

theorem cell22_2858327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_2858327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858327 prefixEnd_2858327 := by exact prefixLift 2858327
  have htrace : WordTrace (prefixWord ++ tailWord_2858327) baseStart_2858327 baseEnd_2858327 := by
    simpa [prefixWord, tailWord_2858327, baseEnd_2858327] using wordTrace_append hprefix tailTrace_2858327
  have hstable : (prefixWord ++ tailWord_2858327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858327).length < 2 ^ (prefixWord ++ tailWord_2858327).sum := by decide
  have hdescent : baseEnd_2858327 < baseStart_2858327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858408 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2858408 : Nat := 118140960795 + 2858408 * 2 ^ 59
def prefixEnd_2858408 : Nat := 4983230072969 + 3 ^ 40 * 2858408 * 2
def baseEnd_2858408 : Nat := 978491473771305132836285

theorem tailTrace_2858408 : CollatzResearch.WordTrace tailWord_2858408 prefixEnd_2858408 978491473771305132836285 := by
  unfold tailWord_2858408
  simp only [CollatzResearch.WordTrace]
  refine ⟨52127352314241734032867939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69503136418988978710490585 52127352314241734032867939)
  ·
    refine ⟨78191028471362601049301909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52127352314241734032867939 78191028471362601049301909)
    ·
      refine ⟨3665204459595121924186027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78191028471362601049301909 3665204459595121924186027)
      ·
        refine ⟨5497806689392682886279041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665204459595121924186027 5497806689392682886279041)
        ·
          refine ⟨4123355017044512164709281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5497806689392682886279041 4123355017044512164709281)
          ·
            refine ⟨3092516262783384123531961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123355017044512164709281 3092516262783384123531961)
            ·
              refine ⟨2319387197087538092648971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092516262783384123531961 2319387197087538092648971)
              ·
                refine ⟨3479080795631307138973457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319387197087538092648971 3479080795631307138973457)
                ·
                  refine ⟨2609310596723480354230093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479080795631307138973457 2609310596723480354230093)
                  ·
                    refine ⟨978491473771305132836285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609310596723480354230093 978491473771305132836285)
                    ·
                      rfl

theorem cell22_2858408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2858408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858408 prefixEnd_2858408 := by exact prefixLift 2858408
  have htrace : WordTrace (prefixWord ++ tailWord_2858408) baseStart_2858408 baseEnd_2858408 := by
    simpa [prefixWord, tailWord_2858408, baseEnd_2858408] using wordTrace_append hprefix tailTrace_2858408
  have hstable : (prefixWord ++ tailWord_2858408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858408).length < 2 ^ (prefixWord ++ tailWord_2858408).sum := by decide
  have hdescent : baseEnd_2858408 < baseStart_2858408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858430 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2858430 : Nat := 118140960795 + 2858430 * 2 ^ 59
def prefixEnd_2858430 : Nat := 4983230072969 + 3 ^ 40 * 2858430 * 2
def baseEnd_2858430 : Nat := 978499004820904408786217

theorem tailTrace_2858430 : CollatzResearch.WordTrace tailWord_2858430 prefixEnd_2858430 978499004820904408786217 := by
  unfold tailWord_2858430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031938379300470727879593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69503671356269177215357829 13031938379300470727879593)
  ·
    refine ⟨9773953784475353045909695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13031938379300470727879593 9773953784475353045909695)
    ·
      refine ⟨14660930676713029568864543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773953784475353045909695 14660930676713029568864543)
      ·
        refine ⟨21991396015069544353296815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14660930676713029568864543 21991396015069544353296815)
        ·
          refine ⟨32987094022604316529945223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21991396015069544353296815 32987094022604316529945223)
          ·
            refine ⟨49480641033906474794917835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32987094022604316529945223 49480641033906474794917835)
            ·
              refine ⟨74220961550859712192376753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49480641033906474794917835 74220961550859712192376753)
              ·
                refine ⟨55665721163144784144282565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74220961550859712192376753 55665721163144784144282565)
                ·
                  refine ⟨10437322718089647027052981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55665721163144784144282565 10437322718089647027052981)
                  ·
                    refine ⟨978499004820904408786217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10437322718089647027052981 978499004820904408786217)
                    ·
                      rfl

theorem cell22_2858430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2858430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858430 prefixEnd_2858430 := by exact prefixLift 2858430
  have htrace : WordTrace (prefixWord ++ tailWord_2858430) baseStart_2858430 baseEnd_2858430 := by
    simpa [prefixWord, tailWord_2858430, baseEnd_2858430] using wordTrace_append hprefix tailTrace_2858430
  have hstable : (prefixWord ++ tailWord_2858430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858430).length < 2 ^ (prefixWord ++ tailWord_2858430).sum := by decide
  have hdescent : baseEnd_2858430 < baseStart_2858430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858490 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_2858490 : Nat := 118140960795 + 2858490 * 2 ^ 59
def prefixEnd_2858490 : Nat := 4983230072969 + 3 ^ 40 * 2858490 * 2
def baseEnd_2858490 : Nat := 978519544047084252286033

theorem tailTrace_2858490 : CollatzResearch.WordTrace tailWord_2858490 prefixEnd_2858490 978519544047084252286033 := by
  unfold tailWord_2858490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26064423853546599017555231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69505130276124264046813949 26064423853546599017555231)
  ·
    refine ⟨39096635780319898526332847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26064423853546599017555231 39096635780319898526332847)
    ·
      refine ⟨58644953670479847789499271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39096635780319898526332847 58644953670479847789499271)
      ·
        refine ⟨87967430505719771684248907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58644953670479847789499271 87967430505719771684248907)
        ·
          refine ⟨131951145758579657526373361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87967430505719771684248907 131951145758579657526373361)
          ·
            refine ⟨98963359318934743144780021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131951145758579657526373361 98963359318934743144780021)
            ·
              refine ⟨9277814936150132169823127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98963359318934743144780021 9277814936150132169823127)
              ·
                refine ⟨13916722404225198254734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277814936150132169823127 13916722404225198254734691)
                ·
                  refine ⟨20875083606337797382102037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13916722404225198254734691 20875083606337797382102037)
                  ·
                    refine ⟨978519544047084252286033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20875083606337797382102037 978519544047084252286033)
                    ·
                      rfl

theorem cell22_2858490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_2858490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858490 prefixEnd_2858490 := by exact prefixLift 2858490
  have htrace : WordTrace (prefixWord ++ tailWord_2858490) baseStart_2858490 baseEnd_2858490 := by
    simpa [prefixWord, tailWord_2858490, baseEnd_2858490] using wordTrace_append hprefix tailTrace_2858490
  have hstable : (prefixWord ++ tailWord_2858490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858490).length < 2 ^ (prefixWord ++ tailWord_2858490).sum := by decide
  have hdescent : baseEnd_2858490 < baseStart_2858490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858629 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 4]
def baseStart_2858629 : Nat := 118140960795 + 2858629 * 2 ^ 59
def prefixEnd_2858629 : Nat := 4983230072969 + 3 ^ 40 * 2858629 * 2
def baseEnd_2858629 : Nat := 326189042195911407686869

theorem tailTrace_2858629 : CollatzResearch.WordTrace tailWord_2858629 prefixEnd_2858629 326189042195911407686869 := by
  unfold tailWord_2858629
  simp only [CollatzResearch.WordTrace]
  refine ⟨104262765160682822809530941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69508510107121881873020627 104262765160682822809530941)
  ·
    refine ⟨39098536935256058553574103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104262765160682822809530941 39098536935256058553574103)
    ·
      refine ⟨58647805402884087830361155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39098536935256058553574103 58647805402884087830361155)
      ·
        refine ⟨87971708104326131745541733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58647805402884087830361155 87971708104326131745541733)
        ·
          refine ⟨16494695269561149702289075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87971708104326131745541733 16494695269561149702289075)
          ·
            refine ⟨24742042904341724553433613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16494695269561149702289075 24742042904341724553433613)
            ·
              refine ⟨9278266089128146707537605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24742042904341724553433613 9278266089128146707537605)
              ·
                refine ⟨1739674891711527507663301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9278266089128146707537605 1739674891711527507663301)
                ·
                  refine ⟨326189042195911407686869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739674891711527507663301 326189042195911407686869)
                  ·
                    rfl

theorem cell22_2858629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_2858629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858629 prefixEnd_2858629 := by exact prefixLift 2858629
  have htrace : WordTrace (prefixWord ++ tailWord_2858629) baseStart_2858629 baseEnd_2858629 := by
    simpa [prefixWord, tailWord_2858629, baseEnd_2858629] using wordTrace_append hprefix tailTrace_2858629
  have hstable : (prefixWord ++ tailWord_2858629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858629).length < 2 ^ (prefixWord ++ tailWord_2858629).sum := by decide
  have hdescent : baseEnd_2858629 < baseStart_2858629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858678 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2858678 : Nat := 118140960795 + 2858678 * 2 ^ 59
def prefixEnd_2858678 : Nat := 4983230072969 + 3 ^ 40 * 2858678 * 2
def baseEnd_2858678 : Nat := 978583900289114428585457

theorem tailTrace_2858678 : CollatzResearch.WordTrace tailWord_2858678 prefixEnd_2858678 978583900289114428585457 := by
  unfold tailWord_2858678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6516534521094081511129043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69509701558336869452043125 6516534521094081511129043)
  ·
    refine ⟨9774801781641122266693565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6516534521094081511129043 9774801781641122266693565)
    ·
      refine ⟨3665550668115420850010087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9774801781641122266693565 3665550668115420850010087)
      ·
        refine ⟨5498326002173131275015131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665550668115420850010087 5498326002173131275015131)
        ·
          refine ⟨8247489003259696912522697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498326002173131275015131 8247489003259696912522697)
          ·
            refine ⟨6185616752444772684392023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8247489003259696912522697 6185616752444772684392023)
            ·
              refine ⟨9278425128667159026588035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185616752444772684392023 9278425128667159026588035)
              ·
                refine ⟨13917637693000738539882053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278425128667159026588035 13917637693000738539882053)
                ·
                  refine ⟨2609557067437638476227885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13917637693000738539882053 2609557067437638476227885)
                  ·
                    refine ⟨978583900289114428585457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609557067437638476227885 978583900289114428585457)
                    ·
                      rfl

theorem cell22_2858678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2858678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858678 prefixEnd_2858678 := by exact prefixLift 2858678
  have htrace : WordTrace (prefixWord ++ tailWord_2858678) baseStart_2858678 baseEnd_2858678 := by
    simpa [prefixWord, tailWord_2858678, baseEnd_2858678] using wordTrace_append hprefix tailTrace_2858678
  have hstable : (prefixWord ++ tailWord_2858678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858678).length < 2 ^ (prefixWord ++ tailWord_2858678).sum := by decide
  have hdescent : baseEnd_2858678 < baseStart_2858678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858706 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2858706 : Nat := 118140960795 + 2858706 * 2 ^ 59
def prefixEnd_2858706 : Nat := 4983230072969 + 3 ^ 40 * 2858706 * 2
def baseEnd_2858706 : Nat := 978593485261331688885371

theorem tailTrace_2858706 : CollatzResearch.WordTrace tailWord_2858706 prefixEnd_2858706 978593485261331688885371 := by
  unfold tailWord_2858706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26066393395350966240020993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69510382387602576640055981 26066393395350966240020993)
  ·
    refine ⟨19549795046513224680015745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26066393395350966240020993 19549795046513224680015745)
    ·
      refine ⟨14662346284884918510011809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19549795046513224680015745 14662346284884918510011809)
      ·
        refine ⟨10996759713663688882508857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14662346284884918510011809 10996759713663688882508857)
        ·
          refine ⟨8247569785247766661881643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10996759713663688882508857 8247569785247766661881643)
          ·
            refine ⟨12371354677871649992822465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247569785247766661881643 12371354677871649992822465)
            ·
              refine ⟨9278516008403737494616849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12371354677871649992822465 9278516008403737494616849)
              ·
                refine ⟨6958887006302803120962637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9278516008403737494616849 6958887006302803120962637)
                ·
                  refine ⟨2609582627363551170360989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6958887006302803120962637 2609582627363551170360989)
                  ·
                    refine ⟨978593485261331688885371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609582627363551170360989 978593485261331688885371)
                    ·
                      rfl

theorem cell22_2858706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2858706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858706 prefixEnd_2858706 := by exact prefixLift 2858706
  have htrace : WordTrace (prefixWord ++ tailWord_2858706) baseStart_2858706 baseEnd_2858706 := by
    simpa [prefixWord, tailWord_2858706, baseEnd_2858706] using wordTrace_append hprefix tailTrace_2858706
  have hstable : (prefixWord ++ tailWord_2858706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858706).length < 2 ^ (prefixWord ++ tailWord_2858706).sum := by decide
  have hdescent : baseEnd_2858706 < baseStart_2858706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858740 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2858740 : Nat := 118140960795 + 2858740 * 2 ^ 59
def prefixEnd_2858740 : Nat := 4983230072969 + 3 ^ 40 * 2858740 * 2
def baseEnd_2858740 : Nat := 978605124156166933535267

theorem tailTrace_2858740 : CollatzResearch.WordTrace tailWord_2858740 prefixEnd_2858740 978605124156166933535267 := by
  unfold tailWord_2858740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52133406831640344383410837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69511209108853792511214449 52133406831640344383410837)
  ·
    refine ⟨2443753445233141142972383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52133406831640344383410837 2443753445233141142972383)
    ·
      refine ⟨3665630167849711714458575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443753445233141142972383 3665630167849711714458575)
      ·
        refine ⟨5498445251774567571687863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665630167849711714458575 5498445251774567571687863)
        ·
          refine ⟨8247667877661851357531795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498445251774567571687863 8247667877661851357531795)
          ·
            refine ⟨12371501816492777036297693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247667877661851357531795 12371501816492777036297693)
            ·
              refine ⟨4639313181184791388611635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12371501816492777036297693 4639313181184791388611635)
              ·
                refine ⟨6958969771777187082917453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639313181184791388611635 6958969771777187082917453)
                ·
                  refine ⟨2609613664416445156094045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6958969771777187082917453 2609613664416445156094045)
                  ·
                    refine ⟨978605124156166933535267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609613664416445156094045 978605124156166933535267)
                    ·
                      rfl

theorem cell22_2858740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2858740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858740 prefixEnd_2858740 := by exact prefixLift 2858740
  have htrace : WordTrace (prefixWord ++ tailWord_2858740) baseStart_2858740 baseEnd_2858740 := by
    simpa [prefixWord, tailWord_2858740, baseEnd_2858740] using wordTrace_append hprefix tailTrace_2858740
  have hstable : (prefixWord ++ tailWord_2858740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858740).length < 2 ^ (prefixWord ++ tailWord_2858740).sum := by decide
  have hdescent : baseEnd_2858740 < baseStart_2858740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858747 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 6]
def baseStart_2858747 : Nat := 118140960795 + 2858747 * 2 ^ 59
def prefixEnd_2858747 : Nat := 4983230072969 + 3 ^ 40 * 2858747 * 2
def baseEnd_2858747 : Nat := 326202506799740416203415

theorem tailTrace_2858747 : CollatzResearch.WordTrace tailWord_2858747 prefixEnd_2858747 326202506799740416203415 := by
  unfold tailWord_2858747
  simp only [CollatzResearch.WordTrace]
  refine ⟨104267068974255328962326495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69511379316170219308217663 104267068974255328962326495)
  ·
    refine ⟨156400603461382993443489743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104267068974255328962326495 156400603461382993443489743)
    ·
      refine ⟨234600905192074490165234615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156400603461382993443489743 234600905192074490165234615)
      ·
        refine ⟨351901357788111735247851923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234600905192074490165234615 351901357788111735247851923)
        ·
          refine ⟨527852036682167602871777885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351901357788111735247851923 527852036682167602871777885)
          ·
            refine ⟨197944513755812851076916707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527852036682167602871777885 197944513755812851076916707)
            ·
              refine ⟨296916770633719276615375061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197944513755812851076916707 296916770633719276615375061)
              ·
                refine ⟨6958986811727795545672853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 296916770633719276615375061 6958986811727795545672853)
                ·
                  refine ⟨326202506799740416203415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6958986811727795545672853 326202506799740416203415)
                  ·
                    rfl

theorem cell22_2858747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_2858747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858747 prefixEnd_2858747 := by exact prefixLift 2858747
  have htrace : WordTrace (prefixWord ++ tailWord_2858747) baseStart_2858747 baseEnd_2858747 := by
    simpa [prefixWord, tailWord_2858747, baseEnd_2858747] using wordTrace_append hprefix tailTrace_2858747
  have hstable : (prefixWord ++ tailWord_2858747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858747).length < 2 ^ (prefixWord ++ tailWord_2858747).sum := by decide
  have hdescent : baseEnd_2858747 < baseStart_2858747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858766 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_2858766 : Nat := 118140960795 + 2858766 * 2 ^ 59
def prefixEnd_2858766 : Nat := 4983230072969 + 3 ^ 40 * 2858766 * 2
def baseEnd_2858766 : Nat := 978614024487511532385187

theorem tailTrace_2858766 : CollatzResearch.WordTrace tailWord_2858766 prefixEnd_2858766 978614024487511532385187 := by
  unfold tailWord_2858766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033470245148311900908519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69511841307457663471512101 13033470245148311900908519)
  ·
    refine ⟨19550205367722467851362779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13033470245148311900908519 19550205367722467851362779)
    ·
      refine ⟨29325308051583701777044169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19550205367722467851362779 29325308051583701777044169)
      ·
        refine ⟨21993981038687776332783127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29325308051583701777044169 21993981038687776332783127)
        ·
          refine ⟨32990971558031664499174691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21993981038687776332783127 32990971558031664499174691)
          ·
            refine ⟨49486457337047496748762037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32990971558031664499174691 49486457337047496748762037)
            ·
              refine ⟨4639355375348202820196441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49486457337047496748762037 4639355375348202820196441)
              ·
                refine ⟨3479516531511152115147331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639355375348202820196441 3479516531511152115147331)
                ·
                  refine ⟨5219274797266728172720997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479516531511152115147331 5219274797266728172720997)
                  ·
                    refine ⟨978614024487511532385187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219274797266728172720997 978614024487511532385187)
                    ·
                      rfl

theorem cell22_2858766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_2858766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858766 prefixEnd_2858766 := by exact prefixLift 2858766
  have htrace : WordTrace (prefixWord ++ tailWord_2858766) baseStart_2858766 baseEnd_2858766 := by
    simpa [prefixWord, tailWord_2858766, baseEnd_2858766] using wordTrace_append hprefix tailTrace_2858766
  have hstable : (prefixWord ++ tailWord_2858766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858766).length < 2 ^ (prefixWord ++ tailWord_2858766).sum := by decide
  have hdescent : baseEnd_2858766 < baseStart_2858766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858777 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_2858777 : Nat := 118140960795 + 2858777 * 2 ^ 59
def prefixEnd_2858777 : Nat := 4983230072969 + 3 ^ 40 * 2858777 * 2
def baseEnd_2858777 : Nat := 978617790012311170360153

theorem tailTrace_2858777 : CollatzResearch.WordTrace tailWord_2858777 prefixEnd_2858777 978617790012311170360153 := by
  unfold tailWord_2858777
  simp only [CollatzResearch.WordTrace]
  refine ⟨104268163164146644085918585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69512108776097762723945723 104268163164146644085918585)
  ·
    refine ⟨78201122373109983064438939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104268163164146644085918585 78201122373109983064438939)
    ·
      refine ⟨117301683559664974596658409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78201122373109983064438939 117301683559664974596658409)
      ·
        refine ⟨87976262669748730947493807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117301683559664974596658409 87976262669748730947493807)
        ·
          refine ⟨131964394004623096421240711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87976262669748730947493807 131964394004623096421240711)
          ·
            refine ⟨197946591006934644631861067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131964394004623096421240711 197946591006934644631861067)
            ·
              refine ⟨296919886510401966947791601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197946591006934644631861067 296919886510401966947791601)
              ·
                refine ⟨222689914882801475210843701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296919886510401966947791601 222689914882801475210843701)
                ·
                  refine ⟨20877179520262638301016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222689914882801475210843701 20877179520262638301016597)
                  ·
                    refine ⟨978617790012311170360153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20877179520262638301016597 978617790012311170360153)
                    ·
                      rfl

theorem cell22_2858777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_2858777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858777 prefixEnd_2858777 := by exact prefixLift 2858777
  have htrace : WordTrace (prefixWord ++ tailWord_2858777) baseStart_2858777 baseEnd_2858777 := by
    simpa [prefixWord, tailWord_2858777, baseEnd_2858777] using wordTrace_append hprefix tailTrace_2858777
  have hstable : (prefixWord ++ tailWord_2858777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858777).length < 2 ^ (prefixWord ++ tailWord_2858777).sum := by decide
  have hdescent : baseEnd_2858777 < baseStart_2858777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858796 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_2858796 : Nat := 118140960795 + 2858796 * 2 ^ 59
def prefixEnd_2858796 : Nat := 4983230072969 + 3 ^ 40 * 2858796 * 2
def baseEnd_2858796 : Nat := 978624294100601454135095

theorem tailTrace_2858796 : CollatzResearch.WordTrace tailWord_2858796 prefixEnd_2858796 978624294100601454135095 := by
  unfold tailWord_2858796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52134428075538905165430121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69512570767385206887240161 52134428075538905165430121)
  ·
    refine ⟨39100821056654178874072591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52134428075538905165430121 39100821056654178874072591)
    ·
      refine ⟨58651231584981268311108887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39100821056654178874072591 58651231584981268311108887)
      ·
        refine ⟨87976847377471902466663331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58651231584981268311108887 87976847377471902466663331)
        ·
          refine ⟨131965271066207853699994997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87976847377471902466663331 131965271066207853699994997)
          ·
            refine ⟨12371744162456986284374531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131965271066207853699994997 12371744162456986284374531)
            ·
              refine ⟨18557616243685479426561797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12371744162456986284374531 18557616243685479426561797)
              ·
                refine ⟨3479553045691027392480337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18557616243685479426561797 3479553045691027392480337)
                ·
                  refine ⟨2609664784268270544360253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479553045691027392480337 2609664784268270544360253)
                  ·
                    refine ⟨978624294100601454135095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609664784268270544360253 978624294100601454135095)
                    ·
                      rfl

theorem cell22_2858796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_2858796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858796 prefixEnd_2858796 := by exact prefixLift 2858796
  have htrace : WordTrace (prefixWord ++ tailWord_2858796) baseStart_2858796 baseEnd_2858796 := by
    simpa [prefixWord, tailWord_2858796, baseEnd_2858796] using wordTrace_append hprefix tailTrace_2858796
  have hstable : (prefixWord ++ tailWord_2858796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858796).length < 2 ^ (prefixWord ++ tailWord_2858796).sum := by decide
  have hdescent : baseEnd_2858796 < baseStart_2858796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858813 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_2858813 : Nat := 118140960795 + 2858813 * 2 ^ 59
def prefixEnd_2858813 : Nat := 4983230072969 + 3 ^ 40 * 2858813 * 2
def baseEnd_2858813 : Nat := 978630113548019076460043

theorem tailTrace_2858813 : CollatzResearch.WordTrace tailWord_2858813 prefixEnd_2858813 978630113548019076460043 := by
  unfold tailWord_2858813
  simp only [CollatzResearch.WordTrace]
  refine ⟨104269476192016222234229093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69512984128010814822819395 104269476192016222234229093)
  ·
    refine ⟨19550526786003041668917955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104269476192016222234229093 19550526786003041668917955)
    ·
      refine ⟨29325790179004562503376933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19550526786003041668917955 29325790179004562503376933)
      ·
        refine ⟨5498585658563355469383175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29325790179004562503376933 5498585658563355469383175)
        ·
          refine ⟨8247878487845033204074763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498585658563355469383175 8247878487845033204074763)
          ·
            refine ⟨12371817731767549806112145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247878487845033204074763 12371817731767549806112145)
            ·
              refine ⟨9278863298825662354584109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12371817731767549806112145 9278863298825662354584109)
              ·
                refine ⟨3479573737059623382969041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9278863298825662354584109 3479573737059623382969041)
                ·
                  refine ⟨2609680302794717537226781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479573737059623382969041 2609680302794717537226781)
                  ·
                    refine ⟨978630113548019076460043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609680302794717537226781 978630113548019076460043)
                    ·
                      rfl

theorem cell22_2858813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_2858813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858813 prefixEnd_2858813 := by exact prefixLift 2858813
  have htrace : WordTrace (prefixWord ++ tailWord_2858813) baseStart_2858813 baseEnd_2858813 := by
    simpa [prefixWord, tailWord_2858813, baseEnd_2858813] using wordTrace_append hprefix tailTrace_2858813
  have hstable : (prefixWord ++ tailWord_2858813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858813).length < 2 ^ (prefixWord ++ tailWord_2858813).sum := by decide
  have hdescent : baseEnd_2858813 < baseStart_2858813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858828 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_2858828 : Nat := 118140960795 + 2858828 * 2 ^ 59
def prefixEnd_2858828 : Nat := 4983230072969 + 3 ^ 40 * 2858828 * 2
def baseEnd_2858828 : Nat := 978635248354564037334997

theorem tailTrace_2858828 : CollatzResearch.WordTrace tailWord_2858828 prefixEnd_2858828 978635248354564037334997 := by
  unfold tailWord_2858828
  simp only [CollatzResearch.WordTrace]
  refine ⟨52135011643480939898012569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69513348857974586530683425 52135011643480939898012569)
  ·
    refine ⟨39101258732610704923509427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52135011643480939898012569 39101258732610704923509427)
    ·
      refine ⟨58651888098916057385264141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39101258732610704923509427 58651888098916057385264141)
      ·
        refine ⟨21994458037093521519474053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58651888098916057385264141 21994458037093521519474053)
        ·
          refine ⟨4123960881955035284901385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21994458037093521519474053 4123960881955035284901385)
          ·
            refine ⟨3092970661466276463676039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123960881955035284901385 3092970661466276463676039)
            ·
              refine ⟨4639455992199414695514059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092970661466276463676039 4639455992199414695514059)
              ·
                refine ⟨6959183988299122043271089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639455992199414695514059 6959183988299122043271089)
                ·
                  refine ⟨5219387991224341532453317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6959183988299122043271089 5219387991224341532453317)
                  ·
                    refine ⟨978635248354564037334997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219387991224341532453317 978635248354564037334997)
                    ·
                      rfl

theorem cell22_2858828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_2858828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858828 prefixEnd_2858828 := by exact prefixLift 2858828
  have htrace : WordTrace (prefixWord ++ tailWord_2858828) baseStart_2858828 baseEnd_2858828 := by
    simpa [prefixWord, tailWord_2858828, baseEnd_2858828] using wordTrace_append hprefix tailTrace_2858828
  have hstable : (prefixWord ++ tailWord_2858828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858828).length < 2 ^ (prefixWord ++ tailWord_2858828).sum := by decide
  have hdescent : baseEnd_2858828 < baseStart_2858828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858901 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2858901 : Nat := 118140960795 + 2858901 * 2 ^ 59
def prefixEnd_2858901 : Nat := 4983230072969 + 3 ^ 40 * 2858901 * 2
def baseEnd_2858901 : Nat := 978660237746416180259773

theorem tailTrace_2858901 : CollatzResearch.WordTrace tailWord_2858901 prefixEnd_2858901 978660237746416180259773 := by
  unfold tailWord_2858901
  simp only [CollatzResearch.WordTrace]
  refine ⟨104272685815697413263432557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69515123877131608842288371 104272685815697413263432557)
  ·
    refine ⟨39102257180886529973787209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104272685815697413263432557 39102257180886529973787209)
    ·
      refine ⟨29326692885664897480340407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39102257180886529973787209 29326692885664897480340407)
      ·
        refine ⟨43990039328497346220510611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29326692885664897480340407 43990039328497346220510611)
        ·
          refine ⟨65985058992746019330765917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43990039328497346220510611 65985058992746019330765917)
          ·
            refine ⟨24744397122279757249037219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65985058992746019330765917 24744397122279757249037219)
            ·
              refine ⟨37116595683419635873555829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24744397122279757249037219 37116595683419635873555829)
              ·
                refine ⟨3479680845320590863145859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37116595683419635873555829 3479680845320590863145859)
                ·
                  refine ⟨5219521267980886294718789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479680845320590863145859 5219521267980886294718789)
                  ·
                    refine ⟨978660237746416180259773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219521267980886294718789 978660237746416180259773)
                    ·
                      rfl

theorem cell22_2858901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2858901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858901 prefixEnd_2858901 := by exact prefixLift 2858901
  have htrace : WordTrace (prefixWord ++ tailWord_2858901) baseStart_2858901 baseEnd_2858901 := by
    simpa [prefixWord, tailWord_2858901, baseEnd_2858901] using wordTrace_append hprefix tailTrace_2858901
  have hstable : (prefixWord ++ tailWord_2858901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858901).length < 2 ^ (prefixWord ++ tailWord_2858901).sum := by decide
  have hdescent : baseEnd_2858901 < baseStart_2858901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858916 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_2858916 : Nat := 118140960795 + 2858916 * 2 ^ 59
def prefixEnd_2858916 : Nat := 4983230072969 + 3 ^ 40 * 2858916 * 2
def baseEnd_2858916 : Nat := 326221790850987047044909

theorem tailTrace_2858916 : CollatzResearch.WordTrace tailWord_2858916 prefixEnd_2858916 326221790850987047044909 := by
  unfold tailWord_2858916
  simp only [CollatzResearch.WordTrace]
  refine ⟨52136616455321535412614301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69515488607095380550152401 52136616455321535412614301)
  ·
    refine ⟨19551231170745575779730363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52136616455321535412614301 19551231170745575779730363)
    ·
      refine ⟨29326846756118363669595545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19551231170745575779730363 29326846756118363669595545)
      ·
        refine ⟨21995135067088772752196659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29326846756118363669595545 21995135067088772752196659)
        ·
          refine ⟨32992702600633159128294989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21995135067088772752196659 32992702600633159128294989)
          ·
            refine ⟨12372263475237434673110621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32992702600633159128294989 12372263475237434673110621)
            ·
              refine ⟨4639598803214038002416483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12372263475237434673110621 4639598803214038002416483)
              ·
                refine ⟨6959398204821057003624725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639598803214038002416483 6959398204821057003624725)
                ·
                  refine ⟨326221790850987047044909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6959398204821057003624725 326221790850987047044909)
                  ·
                    rfl

theorem cell22_2858916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_2858916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858916 prefixEnd_2858916 := by exact prefixLift 2858916
  have htrace : WordTrace (prefixWord ++ tailWord_2858916) baseStart_2858916 baseEnd_2858916 := by
    simpa [prefixWord, tailWord_2858916, baseEnd_2858916] using wordTrace_append hprefix tailTrace_2858916
  have hstable : (prefixWord ++ tailWord_2858916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858916).length < 2 ^ (prefixWord ++ tailWord_2858916).sum := by decide
  have hdescent : baseEnd_2858916 < baseStart_2858916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858944 : List Nat := [2, 1, 1, 2, 3, 2, 1, 10]
def baseStart_2858944 : Nat := 118140960795 + 2858944 * 2 ^ 59
def prefixEnd_2858944 : Nat := 4983230072969 + 3 ^ 40 * 2858944 * 2
def baseEnd_2858944 : Nat := 108741661947242044603849

theorem tailTrace_2858944 : CollatzResearch.WordTrace tailWord_2858944 prefixEnd_2858944 108741661947242044603849 := by
  unfold tailWord_2858944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52137127077270815803623943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69516169436361087738165257 52137127077270815803623943)
  ·
    refine ⟨78205690615906223705435915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52137127077270815803623943 78205690615906223705435915)
    ·
      refine ⟨117308535923859335558153873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78205690615906223705435915 117308535923859335558153873)
      ·
        refine ⟨87981401942894501668615405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117308535923859335558153873 87981401942894501668615405)
        ·
          refine ⟨32993025728585438125730777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87981401942894501668615405 32993025728585438125730777)
          ·
            refine ⟨24744769296439078594298083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32993025728585438125730777 24744769296439078594298083)
            ·
              refine ⟨37117153944658617891447125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24744769296439078594298083 37117153944658617891447125)
              ·
                refine ⟨108741661947242044603849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37117153944658617891447125 108741661947242044603849)
                ·
                  rfl

theorem cell22_2858944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_2858944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858944 prefixEnd_2858944 := by exact prefixLift 2858944
  have htrace : WordTrace (prefixWord ++ tailWord_2858944) baseStart_2858944 baseEnd_2858944 := by
    simpa [prefixWord, tailWord_2858944, baseEnd_2858944] using wordTrace_append hprefix tailTrace_2858944
  have hstable : (prefixWord ++ tailWord_2858944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858944).length < 2 ^ (prefixWord ++ tailWord_2858944).sum := by decide
  have hdescent : baseEnd_2858944 < baseStart_2858944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858965 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2858965 : Nat := 118140960795 + 2858965 * 2 ^ 59
def prefixEnd_2858965 : Nat := 4983230072969 + 3 ^ 40 * 2858965 * 2
def baseEnd_2858965 : Nat := 978682146254341346659577

theorem tailTrace_2858965 : CollatzResearch.WordTrace tailWord_2858965 prefixEnd_2858965 978682146254341346659577 := by
  unfold tailWord_2858965
  simp only [CollatzResearch.WordTrace]
  refine ⟨104275020087465552193762349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69516680058310368129174899 104275020087465552193762349)
  ·
    refine ⟨39103132532799582072660881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104275020087465552193762349 39103132532799582072660881)
    ·
      refine ⟨29327349399599686554495661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39103132532799582072660881 29327349399599686554495661)
      ·
        refine ⟨10997756024849882457935873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29327349399599686554495661 10997756024849882457935873)
        ·
          refine ⟨8248317018637411843451905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10997756024849882457935873 8248317018637411843451905)
          ·
            refine ⟨6186237763978058882588929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8248317018637411843451905 6186237763978058882588929)
            ·
              refine ⟨4639678322983544161941697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6186237763978058882588929 4639678322983544161941697)
              ·
                refine ⟨3479758742237658121456273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639678322983544161941697 3479758742237658121456273)
                ·
                  refine ⟨2609819056678243591092205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479758742237658121456273 2609819056678243591092205)
                  ·
                    refine ⟨978682146254341346659577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609819056678243591092205 978682146254341346659577)
                    ·
                      rfl

theorem cell22_2858965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2858965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858965 prefixEnd_2858965 := by exact prefixLift 2858965
  have htrace : WordTrace (prefixWord ++ tailWord_2858965) baseStart_2858965 baseEnd_2858965 := by
    simpa [prefixWord, tailWord_2858965, baseEnd_2858965] using wordTrace_append hprefix tailTrace_2858965
  have hstable : (prefixWord ++ tailWord_2858965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858965).length < 2 ^ (prefixWord ++ tailWord_2858965).sum := by decide
  have hdescent : baseEnd_2858965 < baseStart_2858965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858976 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_2858976 : Nat := 118140960795 + 2858976 * 2 ^ 59
def prefixEnd_2858976 : Nat := 4983230072969 + 3 ^ 40 * 2858976 * 2
def baseEnd_2858976 : Nat := 978685911779140984634543

theorem tailTrace_2858976 : CollatzResearch.WordTrace tailWord_2858976 prefixEnd_2858976 978685911779140984634543 := by
  unfold tailWord_2858976
  simp only [CollatzResearch.WordTrace]
  refine ⟨52137710645212850536206391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69516947526950467381608521 52137710645212850536206391)
  ·
    refine ⟨78206565967819275804309587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52137710645212850536206391 78206565967819275804309587)
    ·
      refine ⟨117309848951728913706464381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78206565967819275804309587 117309848951728913706464381)
      ·
        refine ⟨43991193356898342639924143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117309848951728913706464381 43991193356898342639924143)
        ·
          refine ⟨65986790035347513959886215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43991193356898342639924143 65986790035347513959886215)
          ·
            refine ⟨98980185053021270939829323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65986790035347513959886215 98980185053021270939829323)
            ·
              refine ⟨148470277579531906409743985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98980185053021270939829323 148470277579531906409743985)
              ·
                refine ⟨111352708184648929807307989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148470277579531906409743985 111352708184648929807307989)
                ·
                  refine ⟨2609829098077709292358781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 111352708184648929807307989 2609829098077709292358781)
                  ·
                    refine ⟨978685911779140984634543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609829098077709292358781 978685911779140984634543)
                    ·
                      rfl

theorem cell22_2858976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_2858976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2858976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2858976 prefixEnd_2858976 := by exact prefixLift 2858976
  have htrace : WordTrace (prefixWord ++ tailWord_2858976) baseStart_2858976 baseEnd_2858976 := by
    simpa [prefixWord, tailWord_2858976, baseEnd_2858976] using wordTrace_append hprefix tailTrace_2858976
  have hstable : (prefixWord ++ tailWord_2858976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858976).length < 2 ^ (prefixWord ++ tailWord_2858976).sum := by decide
  have hdescent : baseEnd_2858976 < baseStart_2858976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859066 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2859066 : Nat := 118140960795 + 2859066 * 2 ^ 59
def prefixEnd_2859066 : Nat := 4983230072969 + 3 ^ 40 * 2859066 * 2
def baseEnd_2859066 : Nat := 978716720618410749884267

theorem tailTrace_2859066 : CollatzResearch.WordTrace tailWord_2859066 prefixEnd_2859066 978716720618410749884267 := by
  unfold tailWord_2859066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069675965024911610797263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69519135906733097628792701 26069675965024911610797263)
  ·
    refine ⟨39104513947537367416195895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26069675965024911610797263 39104513947537367416195895)
    ·
      refine ⟨58656770921306051124293843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39104513947537367416195895 58656770921306051124293843)
      ·
        refine ⟨87985156381959076686440765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58656770921306051124293843 87985156381959076686440765)
        ·
          refine ⟨32994433643234653757415287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87985156381959076686440765 32994433643234653757415287)
          ·
            refine ⟨49491650464851980636122931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32994433643234653757415287 49491650464851980636122931)
            ·
              refine ⟨74237475697277970954184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49491650464851980636122931 74237475697277970954184397)
              ·
                refine ⟨27839053386479239107819149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74237475697277970954184397 27839053386479239107819149)
                ·
                  refine ⟨10439645019929714665432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27839053386479239107819149 10439645019929714665432181)
                  ·
                    refine ⟨978716720618410749884267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10439645019929714665432181 978716720618410749884267)
                    ·
                      rfl

theorem cell22_2859066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2859066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859066 prefixEnd_2859066 := by exact prefixLift 2859066
  have htrace : WordTrace (prefixWord ++ tailWord_2859066) baseStart_2859066 baseEnd_2859066 := by
    simpa [prefixWord, tailWord_2859066, baseEnd_2859066] using wordTrace_append hprefix tailTrace_2859066
  have hstable : (prefixWord ++ tailWord_2859066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859066).length < 2 ^ (prefixWord ++ tailWord_2859066).sum := by decide
  have hdescent : baseEnd_2859066 < baseStart_2859066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859096 : List Nat := [2, 1, 2, 2, 1, 4, 1, 9]
def baseStart_2859096 : Nat := 118140960795 + 2859096 * 2 ^ 59
def prefixEnd_2859096 : Nat := 4983230072969 + 3 ^ 40 * 2859096 * 2
def baseEnd_2859096 : Nat := 108747443359055630181575

theorem tailTrace_2859096 : CollatzResearch.WordTrace tailWord_2859096 prefixEnd_2859096 108747443359055630181575 := by
  unfold tailWord_2859096
  simp only [CollatzResearch.WordTrace]
  refine ⟨52139899024995480783390571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69519865366660641044520761 52139899024995480783390571)
  ·
    refine ⟨78209848537493221175085857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52139899024995480783390571 78209848537493221175085857)
    ·
      refine ⟨58657386403119915881314393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78209848537493221175085857 58657386403119915881314393)
      ·
        refine ⟨43993039802339936910985795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58657386403119915881314393 43993039802339936910985795)
        ·
          refine ⟨65989559703509905366478693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43993039802339936910985795 65989559703509905366478693)
          ·
            refine ⟨12373042444408107256214755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65989559703509905366478693 12373042444408107256214755)
            ·
              refine ⟨18559563666612160884322133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12373042444408107256214755 18559563666612160884322133)
              ·
                refine ⟨108747443359055630181575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18559563666612160884322133 108747443359055630181575)
                ·
                  rfl

theorem cell22_2859096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_2859096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859096 prefixEnd_2859096 := by exact prefixLift 2859096
  have htrace : WordTrace (prefixWord ++ tailWord_2859096) baseStart_2859096 baseEnd_2859096 := by
    simpa [prefixWord, tailWord_2859096, baseEnd_2859096] using wordTrace_append hprefix tailTrace_2859096
  have hstable : (prefixWord ++ tailWord_2859096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859096).length < 2 ^ (prefixWord ++ tailWord_2859096).sum := by decide
  have hdescent : baseEnd_2859096 < baseStart_2859096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859162 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_2859162 : Nat := 118140960795 + 2859162 * 2 ^ 59
def prefixEnd_2859162 : Nat := 4983230072969 + 3 ^ 40 * 2859162 * 2
def baseEnd_2859162 : Nat := 978749583380298499483973

theorem tailTrace_2859162 : CollatzResearch.WordTrace tailWord_2859162 prefixEnd_2859162 978749583380298499483973 := by
  unfold tailWord_2859162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070551316937963709670935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69521470178501236559122493 26070551316937963709670935)
  ·
    refine ⟨39105826975406945564506403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26070551316937963709670935 39105826975406945564506403)
    ·
      refine ⟨58658740463110418346759605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39105826975406945564506403 58658740463110418346759605)
      ·
        refine ⟨5499256918416601720008713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58658740463110418346759605 5499256918416601720008713)
        ·
          refine ⟨4124442688812451290006535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5499256918416601720008713 4124442688812451290006535)
          ·
            refine ⟨6186664033218676935009803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124442688812451290006535 6186664033218676935009803)
            ·
              refine ⟨9279996049828015402514705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186664033218676935009803 9279996049828015402514705)
              ·
                refine ⟨6959997037371011551886029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279996049828015402514705 6959997037371011551886029)
                ·
                  refine ⟨2609998889014129331957261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6959997037371011551886029 2609998889014129331957261)
                  ·
                    refine ⟨978749583380298499483973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609998889014129331957261 978749583380298499483973)
                    ·
                      rfl

theorem cell22_2859162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_2859162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859162 prefixEnd_2859162 := by exact prefixLift 2859162
  have htrace : WordTrace (prefixWord ++ tailWord_2859162) baseStart_2859162 baseEnd_2859162 := by
    simpa [prefixWord, tailWord_2859162, baseEnd_2859162] using wordTrace_append hprefix tailTrace_2859162
  have hstable : (prefixWord ++ tailWord_2859162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859162).length < 2 ^ (prefixWord ++ tailWord_2859162).sum := by decide
  have hdescent : baseEnd_2859162 < baseStart_2859162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859233 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2859233 : Nat := 118140960795 + 2859233 * 2 ^ 59
def prefixEnd_2859233 : Nat := 4983230072969 + 3 ^ 40 * 2859233 * 2
def baseEnd_2859233 : Nat := 978773888131277980958755

theorem tailTrace_2859233 : CollatzResearch.WordTrace tailWord_2859233 prefixEnd_2859233 978773888131277980958755 := by
  unfold tailWord_2859233
  simp only [CollatzResearch.WordTrace]
  refine ⟨104284794850494633964518353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69523196566996422643012235 104284794850494633964518353)
  ·
    refine ⟨78213596137870975473388765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104284794850494633964518353 78213596137870975473388765)
    ·
      refine ⟨29330098551701615802520787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78213596137870975473388765 29330098551701615802520787)
      ·
        refine ⟨43995147827552423703781181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29330098551701615802520787 43995147827552423703781181)
        ·
          refine ⟨16498180435332158888917943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43995147827552423703781181 16498180435332158888917943)
          ·
            refine ⟨24747270652998238333376915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16498180435332158888917943 24747270652998238333376915)
            ·
              refine ⟨37120905979497357500065373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24747270652998238333376915 37120905979497357500065373)
              ·
                refine ⟨13920339742311509062524515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37120905979497357500065373 13920339742311509062524515)
                ·
                  refine ⟨20880509613467263593786773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13920339742311509062524515 20880509613467263593786773)
                  ·
                    refine ⟨978773888131277980958755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20880509613467263593786773 978773888131277980958755)
                    ·
                      rfl

theorem cell22_2859233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2859233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859233 prefixEnd_2859233 := by exact prefixLift 2859233
  have htrace : WordTrace (prefixWord ++ tailWord_2859233) baseStart_2859233 baseEnd_2859233 := by
    simpa [prefixWord, tailWord_2859233, baseEnd_2859233] using wordTrace_append hprefix tailTrace_2859233
  have hstable : (prefixWord ++ tailWord_2859233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859233).length < 2 ^ (prefixWord ++ tailWord_2859233).sum := by decide
  have hdescent : baseEnd_2859233 < baseStart_2859233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859237 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 4]
def baseStart_2859237 : Nat := 118140960795 + 2859237 * 2 ^ 59
def prefixEnd_2859237 : Nat := 4983230072969 + 3 ^ 40 * 2859237 * 2
def baseEnd_2859237 : Nat := 326258419137674434619581

theorem tailTrace_2859237 : CollatzResearch.WordTrace tailWord_2859237 prefixEnd_2859237 326258419137674434619581 := by
  unfold tailWord_2859237
  simp only [CollatzResearch.WordTrace]
  refine ⟨104284940742480142647663965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69523293828320095098442643 104284940742480142647663965)
  ·
    refine ⟨39106852778430053492873987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104284940742480142647663965 39106852778430053492873987)
    ·
      refine ⟨58660279167645080239310981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39106852778430053492873987 58660279167645080239310981)
      ·
        refine ⟨10998802343933452544870809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58660279167645080239310981 10998802343933452544870809)
        ·
          refine ⟨8249101757950089408653107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10998802343933452544870809 8249101757950089408653107)
          ·
            refine ⟨12373652636925134112979661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8249101757950089408653107 12373652636925134112979661)
            ·
              refine ⟨4640119738846925292367373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12373652636925134112979661 4640119738846925292367373)
              ·
                refine ⟨1740044902067596984637765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640119738846925292367373 1740044902067596984637765)
                ·
                  refine ⟨326258419137674434619581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740044902067596984637765 326258419137674434619581)
                  ·
                    rfl

theorem cell22_2859237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_2859237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859237 prefixEnd_2859237 := by exact prefixLift 2859237
  have htrace : WordTrace (prefixWord ++ tailWord_2859237) baseStart_2859237 baseEnd_2859237 := by
    simpa [prefixWord, tailWord_2859237, baseEnd_2859237] using wordTrace_append hprefix tailTrace_2859237
  have hstable : (prefixWord ++ tailWord_2859237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859237).length < 2 ^ (prefixWord ++ tailWord_2859237).sum := by decide
  have hdescent : baseEnd_2859237 < baseStart_2859237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859250 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_2859250 : Nat := 118140960795 + 2859250 * 2 ^ 59
def prefixEnd_2859250 : Nat := 4983230072969 + 3 ^ 40 * 2859250 * 2
def baseEnd_2859250 : Nat := 978779707578695603283703

theorem tailTrace_2859250 : CollatzResearch.WordTrace tailWord_2859250 prefixEnd_2859250 978779707578695603283703 := by
  unfold tailWord_2859250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26071353722858261466971801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69523609927622030578591469 26071353722858261466971801)
  ·
    refine ⟨19553515292143696100228851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26071353722858261466971801 19553515292143696100228851)
    ·
      refine ⟨29330272938215544150343277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553515292143696100228851 29330272938215544150343277)
      ·
        refine ⟨10998852351830829056378729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29330272938215544150343277 10998852351830829056378729)
        ·
          refine ⟨8249139263873121792284047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10998852351830829056378729 8249139263873121792284047)
          ·
            refine ⟨12373708895809682688426071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8249139263873121792284047 12373708895809682688426071)
            ·
              refine ⟨18560563343714524032639107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12373708895809682688426071 18560563343714524032639107)
              ·
                refine ⟨27840845015571786048958661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18560563343714524032639107 27840845015571786048958661)
                ·
                  refine ⟨5220158440419709884179749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27840845015571786048958661 5220158440419709884179749)
                  ·
                    refine ⟨978779707578695603283703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220158440419709884179749 978779707578695603283703)
                    ·
                      rfl

theorem cell22_2859250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_2859250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859250 prefixEnd_2859250 := by exact prefixLift 2859250
  have htrace : WordTrace (prefixWord ++ tailWord_2859250) baseStart_2859250 baseEnd_2859250 := by
    simpa [prefixWord, tailWord_2859250, baseEnd_2859250] using wordTrace_append hprefix tailTrace_2859250
  have hstable : (prefixWord ++ tailWord_2859250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859250).length < 2 ^ (prefixWord ++ tailWord_2859250).sum := by decide
  have hdescent : baseEnd_2859250 < baseStart_2859250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859303 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2859303 : Nat := 118140960795 + 2859303 * 2 ^ 59
def prefixEnd_2859303 : Nat := 4983230072969 + 3 ^ 40 * 2859303 * 2
def baseEnd_2859303 : Nat := 978797850561821131708541

theorem tailTrace_2859303 : CollatzResearch.WordTrace tailWord_2859303 prefixEnd_2859303 978797850561821131708541 := by
  unfold tailWord_2859303
  simp only [CollatzResearch.WordTrace]
  refine ⟨104287347960241035919566563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69524898640160690613044375 104287347960241035919566563)
  ·
    refine ⟨156431021940361553879349845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104287347960241035919566563 156431021940361553879349845)
    ·
      refine ⟨1833176038363611959523631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 156431021940361553879349845 1833176038363611959523631)
      ·
        refine ⟨2749764057545417939285447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833176038363611959523631 2749764057545417939285447)
        ·
          refine ⟨4124646086318126908928171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749764057545417939285447 4124646086318126908928171)
          ·
            refine ⟨6186969129477190363392257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124646086318126908928171 6186969129477190363392257)
            ·
              refine ⟨4640226847107892772544193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6186969129477190363392257 4640226847107892772544193)
              ·
                refine ⟨3480170135330919579408145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640226847107892772544193 3480170135330919579408145)
                ·
                  refine ⟨2610127601498189684556109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480170135330919579408145 2610127601498189684556109)
                  ·
                    refine ⟨978797850561821131708541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610127601498189684556109 978797850561821131708541)
                    ·
                      rfl

theorem cell22_2859303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2859303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859303 prefixEnd_2859303 := by exact prefixLift 2859303
  have htrace : WordTrace (prefixWord ++ tailWord_2859303) baseStart_2859303 baseEnd_2859303 := by
    simpa [prefixWord, tailWord_2859303, baseEnd_2859303] using wordTrace_append hprefix tailTrace_2859303
  have hstable : (prefixWord ++ tailWord_2859303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859303).length < 2 ^ (prefixWord ++ tailWord_2859303).sum := by decide
  have hdescent : baseEnd_2859303 < baseStart_2859303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859340 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_2859340 : Nat := 118140960795 + 2859340 * 2 ^ 59
def prefixEnd_2859340 : Nat := 4983230072969 + 3 ^ 40 * 2859340 * 2
def baseEnd_2859340 : Nat := 978810516417965368533427

theorem tailTrace_2859340 : CollatzResearch.WordTrace tailWord_2859340 prefixEnd_2859340 978810516417965368533427 := by
  unfold tailWord_2859340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144348730553495619331737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69525798307404660825775649 52144348730553495619331737)
  ·
    refine ⟨39108261547915121714498803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52144348730553495619331737 39108261547915121714498803)
    ·
      refine ⟨58662392321872682571748205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39108261547915121714498803 58662392321872682571748205)
      ·
        refine ⟨21998397120702255964405577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58662392321872682571748205 21998397120702255964405577)
        ·
          refine ⟨16498797840526691973304183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21998397120702255964405577 16498797840526691973304183)
          ·
            refine ⟨24748196760790037959956275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16498797840526691973304183 24748196760790037959956275)
            ·
              refine ⟨37122295141185056939934413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24748196760790037959956275 37122295141185056939934413)
              ·
                refine ⟨13920860677944396352475405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37122295141185056939934413 13920860677944396352475405)
                ·
                  refine ⟨5220322754229148632178277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13920860677944396352475405 5220322754229148632178277)
                  ·
                    refine ⟨978810516417965368533427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220322754229148632178277 978810516417965368533427)
                    ·
                      rfl

theorem cell22_2859340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_2859340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859340 prefixEnd_2859340 := by exact prefixLift 2859340
  have htrace : WordTrace (prefixWord ++ tailWord_2859340) baseStart_2859340 baseEnd_2859340 := by
    simpa [prefixWord, tailWord_2859340, baseEnd_2859340] using wordTrace_append hprefix tailTrace_2859340
  have hstable : (prefixWord ++ tailWord_2859340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859340).length < 2 ^ (prefixWord ++ tailWord_2859340).sum := by decide
  have hdescent : baseEnd_2859340 < baseStart_2859340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859372 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_2859372 : Nat := 118140960795 + 2859372 * 2 ^ 59
def prefixEnd_2859372 : Nat := 4983230072969 + 3 ^ 40 * 2859372 * 2
def baseEnd_2859372 : Nat := 326273823557309317244443

theorem tailTrace_2859372 : CollatzResearch.WordTrace tailWord_2859372 prefixEnd_2859372 326273823557309317244443 := by
  unfold tailWord_2859372
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144932298495530351914185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69526576397994040469218913 52144932298495530351914185)
  ·
    refine ⟨39108699223871647763935639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52144932298495530351914185 39108699223871647763935639)
    ·
      refine ⟨58663048835807471645903459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39108699223871647763935639 58663048835807471645903459)
      ·
        refine ⟨87994573253711207468855189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58663048835807471645903459 87994573253711207468855189)
        ·
          refine ⟨4124745621267712850102587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87994573253711207468855189 4124745621267712850102587)
          ·
            refine ⟨6187118431901569275153881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124745621267712850102587 6187118431901569275153881)
            ·
              refine ⟨4640338823926176956365411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6187118431901569275153881 4640338823926176956365411)
              ·
                refine ⟨6960508235889265434548117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640338823926176956365411 6960508235889265434548117)
                ·
                  refine ⟨326273823557309317244443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6960508235889265434548117 326273823557309317244443)
                  ·
                    rfl

theorem cell22_2859372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_2859372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859372 prefixEnd_2859372 := by exact prefixLift 2859372
  have htrace : WordTrace (prefixWord ++ tailWord_2859372) baseStart_2859372 baseEnd_2859372 := by
    simpa [prefixWord, tailWord_2859372, baseEnd_2859372] using wordTrace_append hprefix tailTrace_2859372
  have hstable : (prefixWord ++ tailWord_2859372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859372).length < 2 ^ (prefixWord ++ tailWord_2859372).sum := by decide
  have hdescent : baseEnd_2859372 < baseStart_2859372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859387 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 1, 5]
def baseStart_2859387 : Nat := 118140960795 + 2859387 * 2 ^ 59
def prefixEnd_2859387 : Nat := 4983230072969 + 3 ^ 40 * 2859387 * 2
def baseEnd_2859387 : Nat := 978826605478472912608283

theorem tailTrace_2859387 : CollatzResearch.WordTrace tailWord_2859387 prefixEnd_2859387 978826605478472912608283 := by
  unfold tailWord_2859387
  simp only [CollatzResearch.WordTrace]
  refine ⟨104290411691936718265624415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69526941127957812177082943 104290411691936718265624415)
  ·
    refine ⟨156435617537905077398436623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104290411691936718265624415 156435617537905077398436623)
    ·
      refine ⟨234653426306857616097654935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156435617537905077398436623 234653426306857616097654935)
      ·
        refine ⟨351980139460286424146482403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234653426306857616097654935 351980139460286424146482403)
        ·
          refine ⟨527970209190429636219723605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351980139460286424146482403 527970209190429636219723605)
          ·
            refine ⟨3093575444475173649724943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 527970209190429636219723605 3093575444475173649724943)
            ·
              refine ⟨4640363166712760474587415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093575444475173649724943 4640363166712760474587415)
              ·
                refine ⟨6960544750069140711881123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640363166712760474587415 6960544750069140711881123)
                ·
                  refine ⟨10440817125103711067821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6960544750069140711881123 10440817125103711067821685)
                  ·
                    refine ⟨978826605478472912608283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10440817125103711067821685 978826605478472912608283)
                    ·
                      rfl

theorem cell22_2859387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5].length) (baseStart_2859387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859387 prefixEnd_2859387 := by exact prefixLift 2859387
  have htrace : WordTrace (prefixWord ++ tailWord_2859387) baseStart_2859387 baseEnd_2859387 := by
    simpa [prefixWord, tailWord_2859387, baseEnd_2859387] using wordTrace_append hprefix tailTrace_2859387
  have hstable : (prefixWord ++ tailWord_2859387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859387).length < 2 ^ (prefixWord ++ tailWord_2859387).sum := by decide
  have hdescent : baseEnd_2859387 < baseStart_2859387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859400 : List Nat := [2, 1, 3, 3, 1, 1, 3, 8]
def baseStart_2859400 : Nat := 118140960795 + 2859400 * 2 ^ 59
def prefixEnd_2859400 : Nat := 4983230072969 + 3 ^ 40 * 2859400 * 2
def baseEnd_2859400 : Nat := 108759006182682801337027

theorem tailTrace_2859400 : CollatzResearch.WordTrace tailWord_2859400 prefixEnd_2859400 108759006182682801337027 := by
  unfold tailWord_2859400
  simp only [CollatzResearch.WordTrace]
  refine ⟨52145442920444810742923827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69527257227259747657231769 52145442920444810742923827)
  ·
    refine ⟨78218164380667216114385741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52145442920444810742923827 78218164380667216114385741)
    ·
      refine ⟨29331811642750206042894653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78218164380667216114385741 29331811642750206042894653)
      ·
        refine ⟨10999429366031327266085495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29331811642750206042894653 10999429366031327266085495)
        ·
          refine ⟨16499144049046990899128243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999429366031327266085495 16499144049046990899128243)
          ·
            refine ⟨24748716073570486348692365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16499144049046990899128243 24748716073570486348692365)
            ·
              refine ⟨9280768527588932380759637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24748716073570486348692365 9280768527588932380759637)
              ·
                refine ⟨108759006182682801337027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9280768527588932380759637 108759006182682801337027)
                ·
                  rfl

theorem cell22_2859400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_2859400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859400 prefixEnd_2859400 := by exact prefixLift 2859400
  have htrace : WordTrace (prefixWord ++ tailWord_2859400) baseStart_2859400 baseEnd_2859400 := by
    simpa [prefixWord, tailWord_2859400, baseEnd_2859400] using wordTrace_append hprefix tailTrace_2859400
  have hstable : (prefixWord ++ tailWord_2859400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859400).length < 2 ^ (prefixWord ++ tailWord_2859400).sum := by decide
  have hdescent : baseEnd_2859400 < baseStart_2859400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859406 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_2859406 : Nat := 118140960795 + 2859406 * 2 ^ 59
def prefixEnd_2859406 : Nat := 4983230072969 + 3 ^ 40 * 2859406 * 2
def baseEnd_2859406 : Nat := 326277703188921065461075

theorem tailTrace_2859406 : CollatzResearch.WordTrace tailWord_2859406 prefixEnd_2859406 326277703188921065461075 := by
  unfold tailWord_2859406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036388084858485563820759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69527403119245256340377381 13036388084858485563820759)
  ·
    refine ⟨19554582127287728345731139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13036388084858485563820759 19554582127287728345731139)
    ·
      refine ⟨29331873190931592518596709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19554582127287728345731139 29331873190931592518596709)
      ·
        refine ⟨5499726223299673597236883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29331873190931592518596709 5499726223299673597236883)
        ·
          refine ⟨8249589334949510395855325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499726223299673597236883 8249589334949510395855325)
          ·
            refine ⟨3093596000606066398445747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8249589334949510395855325 3093596000606066398445747)
            ·
              refine ⟨4640394000909099597668621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093596000606066398445747 4640394000909099597668621)
              ·
                refine ⟨1740147750340912349125733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640394000909099597668621 1740147750340912349125733)
                ·
                  refine ⟨326277703188921065461075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740147750340912349125733 326277703188921065461075)
                  ·
                    rfl

theorem cell22_2859406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_2859406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859406 prefixEnd_2859406 := by exact prefixLift 2859406
  have htrace : WordTrace (prefixWord ++ tailWord_2859406) baseStart_2859406 baseEnd_2859406 := by
    simpa [prefixWord, tailWord_2859406, baseEnd_2859406] using wordTrace_append hprefix tailTrace_2859406
  have hstable : (prefixWord ++ tailWord_2859406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859406).length < 2 ^ (prefixWord ++ tailWord_2859406).sum := by decide
  have hdescent : baseEnd_2859406 < baseStart_2859406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859601 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_2859601 : Nat := 118140960795 + 2859601 * 2 ^ 59
def prefixEnd_2859601 : Nat := 4983230072969 + 3 ^ 40 * 2859601 * 2
def baseEnd_2859601 : Nat := 978899862051847687757627

theorem tailTrace_2859601 : CollatzResearch.WordTrace tailWord_2859601 prefixEnd_2859601 978899862051847687757627 := by
  unfold tailWord_2859601
  simp only [CollatzResearch.WordTrace]
  refine ⟨104298216913161432813914657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69532144608774288542609771 104298216913161432813914657)
  ·
    refine ⟨78223662684871074610435993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104298216913161432813914657 78223662684871074610435993)
    ·
      refine ⟨58667747013653305957826995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78223662684871074610435993 58667747013653305957826995)
      ·
        refine ⟨88001620520479958936740493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58667747013653305957826995 88001620520479958936740493)
        ·
          refine ⟨33000607695179984601277685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88001620520479958936740493 33000607695179984601277685)
          ·
            refine ⟨3093806971423123556369783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33000607695179984601277685 3093806971423123556369783)
            ·
              refine ⟨4640710457134685334554675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093806971423123556369783 4640710457134685334554675)
              ·
                refine ⟨6961065685702028001832013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640710457134685334554675 6961065685702028001832013)
                ·
                  refine ⟨2610399632138260500687005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6961065685702028001832013 2610399632138260500687005)
                  ·
                    refine ⟨978899862051847687757627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610399632138260500687005 978899862051847687757627)
                    ·
                      rfl

theorem cell22_2859601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_2859601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859601 prefixEnd_2859601 := by exact prefixLift 2859601
  have htrace : WordTrace (prefixWord ++ tailWord_2859601) baseStart_2859601 baseEnd_2859601 := by
    simpa [prefixWord, tailWord_2859601, baseEnd_2859601] using wordTrace_append hprefix tailTrace_2859601
  have hstable : (prefixWord ++ tailWord_2859601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859601).length < 2 ^ (prefixWord ++ tailWord_2859601).sum := by decide
  have hdescent : baseEnd_2859601 < baseStart_2859601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859644 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_2859644 : Nat := 118140960795 + 2859644 * 2 ^ 59
def prefixEnd_2859644 : Nat := 4983230072969 + 3 ^ 40 * 2859644 * 2
def baseEnd_2859644 : Nat := 978914581830609908932495

theorem tailTrace_2859644 : CollatzResearch.WordTrace tailWord_2859644 prefixEnd_2859644 978914581830609908932495 := by
  unfold tailWord_2859644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52149892626002825578864993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69533190168003767438486657 52149892626002825578864993)
  ·
    refine ⟨39112419469502119184148745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52149892626002825578864993 39112419469502119184148745)
    ·
      refine ⟨29334314602126589388111559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39112419469502119184148745 29334314602126589388111559)
      ·
        refine ⟨44001471903189884082167339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29334314602126589388111559 44001471903189884082167339)
        ·
          refine ⟨66002207854784826123251009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44001471903189884082167339 66002207854784826123251009)
          ·
            refine ⟨49501655891088619592438257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66002207854784826123251009 49501655891088619592438257)
            ·
              refine ⟨37126241918316464694328693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49501655891088619592438257 37126241918316464694328693)
              ·
                refine ⟨3480585179842168565093315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37126241918316464694328693 3480585179842168565093315)
                ·
                  refine ⟨5220877769763252847639973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480585179842168565093315 5220877769763252847639973)
                  ·
                    refine ⟨978914581830609908932495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220877769763252847639973 978914581830609908932495)
                    ·
                      rfl

theorem cell22_2859644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_2859644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859644 prefixEnd_2859644 := by exact prefixLift 2859644
  have htrace : WordTrace (prefixWord ++ tailWord_2859644) baseStart_2859644 baseEnd_2859644 := by
    simpa [prefixWord, tailWord_2859644, baseEnd_2859644] using wordTrace_append hprefix tailTrace_2859644
  have hstable : (prefixWord ++ tailWord_2859644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859644).length < 2 ^ (prefixWord ++ tailWord_2859644).sum := by decide
  have hdescent : baseEnd_2859644 < baseStart_2859644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859657 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_2859657 : Nat := 118140960795 + 2859657 * 2 ^ 59
def prefixEnd_2859657 : Nat := 4983230072969 + 3 ^ 40 * 2859657 * 2
def baseEnd_2859657 : Nat := 978919031996282208357455

theorem tailTrace_2859657 : CollatzResearch.WordTrace tailWord_2859657 prefixEnd_2859657 978919031996282208357455 := by
  unfold tailWord_2859657
  simp only [CollatzResearch.WordTrace]
  refine ⟨104300259400958554377953225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69533506267305702918635483 104300259400958554377953225)
  ·
    refine ⟨78225194550718915783464919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104300259400958554377953225 78225194550718915783464919)
    ·
      refine ⟨117337791826078373675197379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78225194550718915783464919 117337791826078373675197379)
      ·
        refine ⟨176006687739117560512796069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117337791826078373675197379 176006687739117560512796069)
        ·
          refine ⟨33001253951084542596149263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176006687739117560512796069 33001253951084542596149263)
          ·
            refine ⟨49501880926626813894223895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33001253951084542596149263 49501880926626813894223895)
            ·
              refine ⟨74252821389940220841335843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49501880926626813894223895 74252821389940220841335843)
              ·
                refine ⟨111379232084910331262003765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74252821389940220841335843 111379232084910331262003765)
                ·
                  refine ⟨10441803007960343555812853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111379232084910331262003765 10441803007960343555812853)
                  ·
                    refine ⟨978919031996282208357455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10441803007960343555812853 978919031996282208357455)
                    ·
                      rfl

theorem cell22_2859657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_2859657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859657 prefixEnd_2859657 := by exact prefixLift 2859657
  have htrace : WordTrace (prefixWord ++ tailWord_2859657) baseStart_2859657 baseEnd_2859657 := by
    simpa [prefixWord, tailWord_2859657, baseEnd_2859657] using wordTrace_append hprefix tailTrace_2859657
  have hstable : (prefixWord ++ tailWord_2859657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859657).length < 2 ^ (prefixWord ++ tailWord_2859657).sum := by decide
  have hdescent : baseEnd_2859657 < baseStart_2859657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859693 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2859693 : Nat := 118140960795 + 2859693 * 2 ^ 59
def prefixEnd_2859693 : Nat := 4983230072969 + 3 ^ 40 * 2859693 * 2
def baseEnd_2859693 : Nat := 326310451843996704819115

theorem tailTrace_2859693 : CollatzResearch.WordTrace tailWord_2859693 prefixEnd_2859693 326310451843996704819115 := by
  unfold tailWord_2859693
  simp only [CollatzResearch.WordTrace]
  refine ⟨104301572428828132526263733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69534381619218755017509155 104301572428828132526263733)
  ·
    refine ⟨9778272415202637424337225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104301572428828132526263733 9778272415202637424337225)
    ·
      refine ⟨7333704311401978068252919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9778272415202637424337225 7333704311401978068252919)
      ·
        refine ⟨11000556467102967102379379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7333704311401978068252919 11000556467102967102379379)
        ·
          refine ⟨16500834700654450653569069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000556467102967102379379 16500834700654450653569069)
          ·
            refine ⟨6187813012745418995088401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16500834700654450653569069 6187813012745418995088401)
            ·
              refine ⟨4640859759559064246316301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6187813012745418995088401 4640859759559064246316301)
              ·
                refine ⟨1740322409834649092368613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640859759559064246316301 1740322409834649092368613)
                ·
                  refine ⟨326310451843996704819115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740322409834649092368613 326310451843996704819115)
                  ·
                    rfl

theorem cell22_2859693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2859693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859693 prefixEnd_2859693 := by exact prefixLift 2859693
  have htrace : WordTrace (prefixWord ++ tailWord_2859693) baseStart_2859693 baseEnd_2859693 := by
    simpa [prefixWord, tailWord_2859693, baseEnd_2859693] using wordTrace_append hprefix tailTrace_2859693
  have hstable : (prefixWord ++ tailWord_2859693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859693).length < 2 ^ (prefixWord ++ tailWord_2859693).sum := by decide
  have hdescent : baseEnd_2859693 < baseStart_2859693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859725 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2859725 : Nat := 118140960795 + 2859725 * 2 ^ 59
def prefixEnd_2859725 : Nat := 4983230072969 + 3 ^ 40 * 2859725 * 2
def baseEnd_2859725 : Nat := 978942309785952697657247

theorem tailTrace_2859725 : CollatzResearch.WordTrace tailWord_2859725 prefixEnd_2859725 978942309785952697657247 := by
  unfold tailWord_2859725
  simp only [CollatzResearch.WordTrace]
  refine ⟨104302739564712201991428629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69535159709808134660952419 104302739564712201991428629)
  ·
    refine ⟨4889190917095884468348217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104302739564712201991428629 4889190917095884468348217)
    ·
      refine ⟨3666893187821913351261163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4889190917095884468348217 3666893187821913351261163)
      ·
        refine ⟨5500339781732870026891745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666893187821913351261163 5500339781732870026891745)
        ·
          refine ⟨4125254836299652520168809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5500339781732870026891745 4125254836299652520168809)
          ·
            refine ⟨3093941127224739390126607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125254836299652520168809 3093941127224739390126607)
            ·
              refine ⟨4640911690837109085189911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093941127224739390126607 4640911690837109085189911)
              ·
                refine ⟨6961367536255663627784867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640911690837109085189911 6961367536255663627784867)
                ·
                  refine ⟨10442051304383495441677301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961367536255663627784867 10442051304383495441677301)
                  ·
                    refine ⟨978942309785952697657247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10442051304383495441677301 978942309785952697657247)
                    ·
                      rfl

theorem cell22_2859725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2859725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859725 prefixEnd_2859725 := by exact prefixLift 2859725
  have htrace : WordTrace (prefixWord ++ tailWord_2859725) baseStart_2859725 baseEnd_2859725 := by
    simpa [prefixWord, tailWord_2859725, baseEnd_2859725] using wordTrace_append hprefix tailTrace_2859725
  have hstable : (prefixWord ++ tailWord_2859725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859725).length < 2 ^ (prefixWord ++ tailWord_2859725).sum := by decide
  have hdescent : baseEnd_2859725 < baseStart_2859725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859736 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_2859736 : Nat := 118140960795 + 2859736 * 2 ^ 59
def prefixEnd_2859736 : Nat := 4983230072969 + 3 ^ 40 * 2859736 * 2
def baseEnd_2859736 : Nat := 978946075310752335632213

theorem tailTrace_2859736 : CollatzResearch.WordTrace tailWord_2859736 prefixEnd_2859736 978946075310752335632213 := by
  unfold tailWord_2859736
  simp only [CollatzResearch.WordTrace]
  refine ⟨52151570383836175435039531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69535427178448233913386041 52151570383836175435039531)
  ·
    refine ⟨78227355575754263152559297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52151570383836175435039531 78227355575754263152559297)
    ·
      refine ⟨58670516681815697364419473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78227355575754263152559297 58670516681815697364419473)
      ·
        refine ⟨44002887511361773023314605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58670516681815697364419473 44002887511361773023314605)
        ·
          refine ⟨16501082816760664883742977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44002887511361773023314605 16501082816760664883742977)
          ·
            refine ⟨12375812112570498662807233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16501082816760664883742977 12375812112570498662807233)
            ·
              refine ⟨9281859084427873997105425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12375812112570498662807233 9281859084427873997105425)
              ·
                refine ⟨6961394313320905497829069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9281859084427873997105425 6961394313320905497829069)
                ·
                  refine ⟨2610522867495339561685901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6961394313320905497829069 2610522867495339561685901)
                  ·
                    refine ⟨978946075310752335632213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610522867495339561685901 978946075310752335632213)
                    ·
                      rfl

theorem cell22_2859736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_2859736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859736 prefixEnd_2859736 := by exact prefixLift 2859736
  have htrace : WordTrace (prefixWord ++ tailWord_2859736) baseStart_2859736 baseEnd_2859736 := by
    simpa [prefixWord, tailWord_2859736, baseEnd_2859736] using wordTrace_append hprefix tailTrace_2859736
  have hstable : (prefixWord ++ tailWord_2859736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859736).length < 2 ^ (prefixWord ++ tailWord_2859736).sum := by decide
  have hdescent : baseEnd_2859736 < baseStart_2859736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859749 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 7]
def baseStart_2859749 : Nat := 118140960795 + 2859749 * 2 ^ 59
def prefixEnd_2859749 : Nat := 4983230072969 + 3 ^ 40 * 2859749 * 2
def baseEnd_2859749 : Nat := 326316841825474878352391

theorem tailTrace_2859749 : CollatzResearch.WordTrace tailWord_2859749 prefixEnd_2859749 326316841825474878352391 := by
  unfold tailWord_2859749
  simp only [CollatzResearch.WordTrace]
  refine ⟨104303614916625254090302301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69535743277750169393534867 104303614916625254090302301)
  ·
    refine ⟨39113855593734470283863363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104303614916625254090302301 39113855593734470283863363)
    ·
      refine ⟨58670783390601705425795045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39113855593734470283863363 58670783390601705425795045)
      ·
        refine ⟨11000771885737819767336571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58670783390601705425795045 11000771885737819767336571)
        ·
          refine ⟨16501157828606729651004857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000771885737819767336571 16501157828606729651004857)
          ·
            refine ⟨12375868371455047238253643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16501157828606729651004857 12375868371455047238253643)
            ·
              refine ⟨18563802557182570857380465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12375868371455047238253643 18563802557182570857380465)
              ·
                refine ⟨13922851917886928143035349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18563802557182570857380465 13922851917886928143035349)
                ·
                  refine ⟨326316841825474878352391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13922851917886928143035349 326316841825474878352391)
                  ·
                    rfl

theorem cell22_2859749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_2859749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859749 prefixEnd_2859749 := by exact prefixLift 2859749
  have htrace : WordTrace (prefixWord ++ tailWord_2859749) baseStart_2859749 baseEnd_2859749 := by
    simpa [prefixWord, tailWord_2859749, baseEnd_2859749] using wordTrace_append hprefix tailTrace_2859749
  have hstable : (prefixWord ++ tailWord_2859749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859749).length < 2 ^ (prefixWord ++ tailWord_2859749).sum := by decide
  have hdescent : baseEnd_2859749 < baseStart_2859749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859753 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 1, 3]
def baseStart_2859753 : Nat := 118140960795 + 2859753 * 2 ^ 59
def prefixEnd_2859753 : Nat := 4983230072969 + 3 ^ 40 * 2859753 * 2
def baseEnd_2859753 : Nat := 978951894758169957957161

theorem tailTrace_2859753 : CollatzResearch.WordTrace tailWord_2859753 prefixEnd_2859753 978951894758169957957161 := by
  unfold tailWord_2859753
  simp only [CollatzResearch.WordTrace]
  refine ⟨104303760808610762773447913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69535840539073841848965275 104303760808610762773447913)
  ·
    refine ⟨78227820606458072080085935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104303760808610762773447913 78227820606458072080085935)
    ·
      refine ⟨117341730909687108120128903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78227820606458072080085935 117341730909687108120128903)
      ·
        refine ⟨176012596364530662180193355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117341730909687108120128903 176012596364530662180193355)
        ·
          refine ⟨264018894546795993270290033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176012596364530662180193355 264018894546795993270290033)
          ·
            refine ⟨198014170910096994952717525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264018894546795993270290033 198014170910096994952717525)
            ·
              refine ⟨4640957130705398319204317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198014170910096994952717525 4640957130705398319204317)
              ·
                refine ⟨1740358924014524369701619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640957130705398319204317 1740358924014524369701619)
                ·
                  refine ⟨2610538386021786554552429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740358924014524369701619 2610538386021786554552429)
                  ·
                    refine ⟨978951894758169957957161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610538386021786554552429 978951894758169957957161)
                    ·
                      rfl

theorem cell22_2859753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_2859753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859753 prefixEnd_2859753 := by exact prefixLift 2859753
  have htrace : WordTrace (prefixWord ++ tailWord_2859753) baseStart_2859753 baseEnd_2859753 := by
    simpa [prefixWord, tailWord_2859753, baseEnd_2859753] using wordTrace_append hprefix tailTrace_2859753
  have hstable : (prefixWord ++ tailWord_2859753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859753).length < 2 ^ (prefixWord ++ tailWord_2859753).sum := by decide
  have hdescent : baseEnd_2859753 < baseStart_2859753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859766 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2859766 : Nat := 118140960795 + 2859766 * 2 ^ 59
def prefixEnd_2859766 : Nat := 4983230072969 + 3 ^ 40 * 2859766 * 2
def baseEnd_2859766 : Nat := 326318781641280752460707

theorem tailTrace_2859766 : CollatzResearch.WordTrace tailWord_2859766 prefixEnd_2859766 326318781641280752460707 := by
  unfold tailWord_2859766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519014684847729124604447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69536156638375777329114101 6519014684847729124604447)
  ·
    refine ⟨9778522027271593686906671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519014684847729124604447 9778522027271593686906671)
    ·
      refine ⟨14667783040907390530360007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778522027271593686906671 14667783040907390530360007)
      ·
        refine ⟨22001674561361085795540011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14667783040907390530360007 22001674561361085795540011)
        ·
          refine ⟨33002511842041628693310017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22001674561361085795540011 33002511842041628693310017)
          ·
            refine ⟨24751883881531221519982513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33002511842041628693310017 24751883881531221519982513)
            ·
              refine ⟨18563912911148416139986885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24751883881531221519982513 18563912911148416139986885)
              ·
                refine ⟨3480733670840328026247541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18563912911148416139986885 3480733670840328026247541)
                ·
                  refine ⟨326318781641280752460707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480733670840328026247541 326318781641280752460707)
                  ·
                    rfl

theorem cell22_2859766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2859766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859766 prefixEnd_2859766 := by exact prefixLift 2859766
  have htrace : WordTrace (prefixWord ++ tailWord_2859766) baseStart_2859766 baseEnd_2859766 := by
    simpa [prefixWord, tailWord_2859766, baseEnd_2859766] using wordTrace_append hprefix tailTrace_2859766
  have hstable : (prefixWord ++ tailWord_2859766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859766).length < 2 ^ (prefixWord ++ tailWord_2859766).sum := by decide
  have hdescent : baseEnd_2859766 < baseStart_2859766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859779 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_2859779 : Nat := 118140960795 + 2859779 * 2 ^ 59
def prefixEnd_2859779 : Nat := 4983230072969 + 3 ^ 40 * 2859779 * 2
def baseEnd_2859779 : Nat := 978960795089514556807081

theorem tailTrace_2859779 : CollatzResearch.WordTrace tailWord_2859779 prefixEnd_2859779 978960795089514556807081 := by
  unfold tailWord_2859779
  simp only [CollatzResearch.WordTrace]
  refine ⟨104304709106516569213894391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69536472737677712809262927 104304709106516569213894391)
  ·
    refine ⟨156457063659774853820841587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104304709106516569213894391 156457063659774853820841587)
    ·
      refine ⟨234685595489662280731262381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156457063659774853820841587 234685595489662280731262381)
      ·
        refine ⟨88007098308623355274223393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234685595489662280731262381 88007098308623355274223393)
        ·
          refine ⟨66005323731467516455667545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88007098308623355274223393 66005323731467516455667545)
          ·
            refine ⟨49503992798600637341750659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66005323731467516455667545 49503992798600637341750659)
            ·
              refine ⟨74255989197900956012625989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49503992798600637341750659 74255989197900956012625989)
              ·
                refine ⟨13922997974606429252367373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74255989197900956012625989 13922997974606429252367373)
                ·
                  refine ⟨5221124240477410969637765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13922997974606429252367373 5221124240477410969637765)
                  ·
                    refine ⟨978960795089514556807081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221124240477410969637765 978960795089514556807081)
                    ·
                      rfl

theorem cell22_2859779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_2859779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859779 prefixEnd_2859779 := by exact prefixLift 2859779
  have htrace : WordTrace (prefixWord ++ tailWord_2859779) baseStart_2859779 baseEnd_2859779 := by
    simpa [prefixWord, tailWord_2859779, baseEnd_2859779] using wordTrace_append hprefix tailTrace_2859779
  have hstable : (prefixWord ++ tailWord_2859779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859779).length < 2 ^ (prefixWord ++ tailWord_2859779).sum := by decide
  have hdescent : baseEnd_2859779 < baseStart_2859779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859783 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 5]
def baseStart_2859783 : Nat := 118140960795 + 2859783 * 2 ^ 59
def prefixEnd_2859783 : Nat := 4983230072969 + 3 ^ 40 * 2859783 * 2
def baseEnd_2859783 : Nat := 326320721457086626569023

theorem tailTrace_2859783 : CollatzResearch.WordTrace tailWord_2859783 prefixEnd_2859783 326320721457086626569023 := by
  unfold tailWord_2859783
  simp only [CollatzResearch.WordTrace]
  refine ⟨104304854998502077897040003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69536569999001385264693335 104304854998502077897040003)
  ·
    refine ⟨156457282497753116845560005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104304854998502077897040003 156457282497753116845560005)
    ·
      refine ⟨29335740468328709408542501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156457282497753116845560005 29335740468328709408542501)
      ·
        refine ⟨5500451337811633014101719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29335740468328709408542501 5500451337811633014101719)
        ·
          refine ⟨8250677006717449521152579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500451337811633014101719 8250677006717449521152579)
          ·
            refine ⟨12376015510076174281728869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250677006717449521152579 12376015510076174281728869)
            ·
              refine ⟨2320502908139282677824163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12376015510076174281728869 2320502908139282677824163)
              ·
                refine ⟨3480754362208924016736245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320502908139282677824163 3480754362208924016736245)
                ·
                  refine ⟨326320721457086626569023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480754362208924016736245 326320721457086626569023)
                  ·
                    rfl

theorem cell22_2859783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 5].length) (baseStart_2859783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859783 prefixEnd_2859783 := by exact prefixLift 2859783
  have htrace : WordTrace (prefixWord ++ tailWord_2859783) baseStart_2859783 baseEnd_2859783 := by
    simpa [prefixWord, tailWord_2859783, baseEnd_2859783] using wordTrace_append hprefix tailTrace_2859783
  have hstable : (prefixWord ++ tailWord_2859783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859783).length < 2 ^ (prefixWord ++ tailWord_2859783).sum := by decide
  have hdescent : baseEnd_2859783 < baseStart_2859783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859811 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 4]
def baseStart_2859811 : Nat := 118140960795 + 2859811 * 2 ^ 59
def prefixEnd_2859811 : Nat := 4983230072969 + 3 ^ 40 * 2859811 * 2
def baseEnd_2859811 : Nat := 326323916447825713335661

theorem tailTrace_2859811 : CollatzResearch.WordTrace tailWord_2859811 prefixEnd_2859811 326323916447825713335661 := by
  unfold tailWord_2859811
  simp only [CollatzResearch.WordTrace]
  refine ⟨104305876242400638679059287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69537250828267092452706191 104305876242400638679059287)
  ·
    refine ⟨156458814363600958018588931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104305876242400638679059287 156458814363600958018588931)
    ·
      refine ⟨234688221545401437027883397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156458814363600958018588931 234688221545401437027883397)
      ·
        refine ⟨44004041539762769442728137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234688221545401437027883397 44004041539762769442728137)
        ·
          refine ⟨33003031154822077082046103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44004041539762769442728137 33003031154822077082046103)
          ·
            refine ⟨49504546732233115623069155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33003031154822077082046103 49504546732233115623069155)
            ·
              refine ⟨74256820098349673434603733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49504546732233115623069155 74256820098349673434603733)
              ·
                refine ⟨1740394221055070471123525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74256820098349673434603733 1740394221055070471123525)
                ·
                  refine ⟨326323916447825713335661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740394221055070471123525 326323916447825713335661)
                  ·
                    rfl

theorem cell22_2859811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 4].length) (baseStart_2859811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859811 prefixEnd_2859811 := by exact prefixLift 2859811
  have htrace : WordTrace (prefixWord ++ tailWord_2859811) baseStart_2859811 baseEnd_2859811 := by
    simpa [prefixWord, tailWord_2859811, baseEnd_2859811] using wordTrace_append hprefix tailTrace_2859811
  have hstable : (prefixWord ++ tailWord_2859811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859811).length < 2 ^ (prefixWord ++ tailWord_2859811).sum := by decide
  have hdescent : baseEnd_2859811 < baseStart_2859811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859813 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_2859813 : Nat := 118140960795 + 2859813 * 2 ^ 59
def prefixEnd_2859813 : Nat := 4983230072969 + 3 ^ 40 * 2859813 * 2
def baseEnd_2859813 : Nat := 978972433984349801456977

theorem tailTrace_2859813 : CollatzResearch.WordTrace tailWord_2859813 prefixEnd_2859813 978972433984349801456977 := by
  unfold tailWord_2859813
  simp only [CollatzResearch.WordTrace]
  refine ⟨104305949188393393020632093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69537299458928928680421395 104305949188393393020632093)
  ·
    refine ⟨39114730945647522382737035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104305949188393393020632093 39114730945647522382737035)
    ·
      refine ⟨58672096418471283574105553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39114730945647522382737035 58672096418471283574105553)
      ·
        refine ⟨44004072313853462680579165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58672096418471283574105553 44004072313853462680579165)
        ·
          refine ⟨16501527117695048505217187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44004072313853462680579165 16501527117695048505217187)
          ·
            refine ⟨24752290676542572757825781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16501527117695048505217187 24752290676542572757825781)
            ·
              refine ⟨2320527250925866196046167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24752290676542572757825781 2320527250925866196046167)
              ·
                refine ⟨3480790876388799294069251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320527250925866196046167 3480790876388799294069251)
                ·
                  refine ⟨5221186314583198941103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480790876388799294069251 5221186314583198941103877)
                  ·
                    refine ⟨978972433984349801456977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221186314583198941103877 978972433984349801456977)
                    ·
                      rfl

theorem cell22_2859813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_2859813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859813 prefixEnd_2859813 := by exact prefixLift 2859813
  have htrace : WordTrace (prefixWord ++ tailWord_2859813) baseStart_2859813 baseEnd_2859813 := by
    simpa [prefixWord, tailWord_2859813, baseEnd_2859813] using wordTrace_append hprefix tailTrace_2859813
  have hstable : (prefixWord ++ tailWord_2859813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859813).length < 2 ^ (prefixWord ++ tailWord_2859813).sum := by decide
  have hdescent : baseEnd_2859813 < baseStart_2859813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859821 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2859821 : Nat := 118140960795 + 2859821 * 2 ^ 59
def prefixEnd_2859821 : Nat := 4983230072969 + 3 ^ 40 * 2859821 * 2
def baseEnd_2859821 : Nat := 978975172547840447256953

theorem tailTrace_2859821 : CollatzResearch.WordTrace tailWord_2859821 prefixEnd_2859821 978975172547840447256953 := by
  unfold tailWord_2859821
  simp only [CollatzResearch.WordTrace]
  refine ⟨104306240972364410386923317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69537493981576273591282211 104306240972364410386923317)
  ·
    refine ⟨9778710091159163473774061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104306240972364410386923317 9778710091159163473774061)
    ·
      refine ⟨3667016284184686302665273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9778710091159163473774061 3667016284184686302665273)
      ·
        refine ⟨2750262213138514726998955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3667016284184686302665273 2750262213138514726998955)
        ·
          refine ⟨4125393319707772090498433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750262213138514726998955 4125393319707772090498433)
          ·
            refine ⟨3094044989780829067873825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125393319707772090498433 3094044989780829067873825)
            ·
              refine ⟨2320533742335621800905369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094044989780829067873825 2320533742335621800905369)
              ·
                refine ⟨1740400306751716350679027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320533742335621800905369 1740400306751716350679027)
                ·
                  refine ⟨2610600460127574526018541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740400306751716350679027 2610600460127574526018541)
                  ·
                    refine ⟨978975172547840447256953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610600460127574526018541 978975172547840447256953)
                    ·
                      rfl

theorem cell22_2859821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2859821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859821 prefixEnd_2859821 := by exact prefixLift 2859821
  have htrace : WordTrace (prefixWord ++ tailWord_2859821) baseStart_2859821 baseEnd_2859821 := by
    simpa [prefixWord, tailWord_2859821, baseEnd_2859821] using wordTrace_append hprefix tailTrace_2859821
  have hstable : (prefixWord ++ tailWord_2859821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859821).length < 2 ^ (prefixWord ++ tailWord_2859821).sum := by decide
  have hdescent : baseEnd_2859821 < baseStart_2859821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859871 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 5, 3]
def baseStart_2859871 : Nat := 118140960795 + 2859871 * 2 ^ 59
def prefixEnd_2859871 : Nat := 4983230072969 + 3 ^ 40 * 2859871 * 2
def baseEnd_2859871 : Nat := 978992288569656983506799

theorem tailTrace_2859871 : CollatzResearch.WordTrace tailWord_2859871 prefixEnd_2859871 978992288569656983506799 := by
  unfold tailWord_2859871
  simp only [CollatzResearch.WordTrace]
  refine ⟨104308064622183268926243467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69538709748122179284162311 104308064622183268926243467)
  ·
    refine ⟨156462096933274903389365201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104308064622183268926243467 156462096933274903389365201)
    ·
      refine ⟨117346572699956177542023901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156462096933274903389365201 117346572699956177542023901)
      ·
        refine ⟨44004964762483566578258963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117346572699956177542023901 44004964762483566578258963)
        ·
          refine ⟨66007447143725349867388445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44004964762483566578258963 66007447143725349867388445)
          ·
            refine ⟨24752792678897006200270667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66007447143725349867388445 24752792678897006200270667)
            ·
              refine ⟨37129189018345509300406001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24752792678897006200270667 37129189018345509300406001)
              ·
                refine ⟨27846891763759131975304501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37129189018345509300406001 27846891763759131975304501)
                ·
                  refine ⟨2610646102852418622684797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27846891763759131975304501 2610646102852418622684797)
                  ·
                    refine ⟨978992288569656983506799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610646102852418622684797 978992288569656983506799)
                    ·
                      rfl

theorem cell22_2859871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_2859871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859871 prefixEnd_2859871 := by exact prefixLift 2859871
  have htrace : WordTrace (prefixWord ++ tailWord_2859871) baseStart_2859871 baseEnd_2859871 := by
    simpa [prefixWord, tailWord_2859871, baseEnd_2859871] using wordTrace_append hprefix tailTrace_2859871
  have hstable : (prefixWord ++ tailWord_2859871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859871).length < 2 ^ (prefixWord ++ tailWord_2859871).sum := by decide
  have hdescent : baseEnd_2859871 < baseStart_2859871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859901 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 5]
def baseStart_2859901 : Nat := 118140960795 + 2859901 * 2 ^ 59
def prefixEnd_2859901 : Nat := 4983230072969 + 3 ^ 40 * 2859901 * 2
def baseEnd_2859901 : Nat := 326334186060915635085569

theorem tailTrace_2859901 : CollatzResearch.WordTrace tailWord_2859901 prefixEnd_2859901 326334186060915635085569 := by
  unfold tailWord_2859901
  simp only [CollatzResearch.WordTrace]
  refine ⟨104309158812074584049835557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69539439208049722699890371 104309158812074584049835557)
  ·
    refine ⟨19557967277263984509344167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104309158812074584049835557 19557967277263984509344167)
    ·
      refine ⟨29336950915895976764016251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19557967277263984509344167 29336950915895976764016251)
      ·
        refine ⟨44005426373843965146024377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29336950915895976764016251 44005426373843965146024377)
        ·
          refine ⟨33004069780382973859518283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44005426373843965146024377 33004069780382973859518283)
          ·
            refine ⟨49506104670574460789277425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33004069780382973859518283 49506104670574460789277425)
            ·
              refine ⟨37129578502930845591958069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49506104670574460789277425 37129578502930845591958069)
              ·
                refine ⟨3480897984649766774246069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37129578502930845591958069 3480897984649766774246069)
                ·
                  refine ⟨326334186060915635085569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480897984649766774246069 326334186060915635085569)
                  ·
                    rfl

theorem cell22_2859901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_2859901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859901 prefixEnd_2859901 := by exact prefixLift 2859901
  have htrace : WordTrace (prefixWord ++ tailWord_2859901) baseStart_2859901 baseEnd_2859901 := by
    simpa [prefixWord, tailWord_2859901, baseEnd_2859901] using wordTrace_append hprefix tailTrace_2859901
  have hstable : (prefixWord ++ tailWord_2859901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859901).length < 2 ^ (prefixWord ++ tailWord_2859901).sum := by decide
  have hdescent : baseEnd_2859901 < baseStart_2859901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859993 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_2859993 : Nat := 118140960795 + 2859993 * 2 ^ 59
def prefixEnd_2859993 : Nat := 4983230072969 + 3 ^ 40 * 2859993 * 2
def baseEnd_2859993 : Nat := 979034051662889331956425

theorem tailTrace_2859993 : CollatzResearch.WordTrace tailWord_2859993 prefixEnd_2859993 979034051662889331956425 := by
  unfold tailWord_2859993
  simp only [CollatzResearch.WordTrace]
  refine ⟨104312514327741283762184633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69541676218494189174789755 104312514327741283762184633)
  ·
    refine ⟨78234385745805962821638475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104312514327741283762184633 78234385745805962821638475)
    ·
      refine ⟨117351578618708944232457713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78234385745805962821638475 117351578618708944232457713)
      ·
        refine ⟨88013683964031708174343285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117351578618708944232457713 88013683964031708174343285)
        ·
          refine ⟨8251282871627972641344683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88013683964031708174343285 8251282871627972641344683)
          ·
            refine ⟨12376924307441958962017025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251282871627972641344683 12376924307441958962017025)
            ·
              refine ⟨9282693230581469221512769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12376924307441958962017025 9282693230581469221512769)
              ·
                refine ⟨6962019922936101916134577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9282693230581469221512769 6962019922936101916134577)
                ·
                  refine ⟨5221514942202076437100933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962019922936101916134577 5221514942202076437100933)
                  ·
                    refine ⟨979034051662889331956425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221514942202076437100933 979034051662889331956425)
                    ·
                      rfl

theorem cell22_2859993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_2859993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859993 prefixEnd_2859993 := by exact prefixLift 2859993
  have htrace : WordTrace (prefixWord ++ tailWord_2859993) baseStart_2859993 baseEnd_2859993 := by
    simpa [prefixWord, tailWord_2859993, baseEnd_2859993] using wordTrace_append hprefix tailTrace_2859993
  have hstable : (prefixWord ++ tailWord_2859993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859993).length < 2 ^ (prefixWord ++ tailWord_2859993).sum := by decide
  have hdescent : baseEnd_2859993 < baseStart_2859993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859997 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 4]
def baseStart_2859997 : Nat := 118140960795 + 2859997 * 2 ^ 59
def prefixEnd_2859997 : Nat := 4983230072969 + 3 ^ 40 * 2859997 * 2
def baseEnd_2859997 : Nat := 326345140314878218285471

theorem tailTrace_2859997 : CollatzResearch.WordTrace tailWord_2859997 prefixEnd_2859997 326345140314878218285471 := by
  unfold tailWord_2859997
  simp only [CollatzResearch.WordTrace]
  refine ⟨104312660219726792445330245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69541773479817861630220163 104312660219726792445330245)
  ·
    refine ⟨19558623791198773583499421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104312660219726792445330245 19558623791198773583499421)
    ·
      refine ⟨7334483921699540093812283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19558623791198773583499421 7334483921699540093812283)
      ·
        refine ⟨11001725882549310140718425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334483921699540093812283 11001725882549310140718425)
        ·
          refine ⟨8251294411911982605538819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11001725882549310140718425 8251294411911982605538819)
          ·
            refine ⟨12376941617867973908308229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251294411911982605538819 12376941617867973908308229)
            ·
              refine ⟨2320676553350245107807793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12376941617867973908308229 2320676553350245107807793)
              ·
                refine ⟨1740507415012683830855845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320676553350245107807793 1740507415012683830855845)
                ·
                  refine ⟨326345140314878218285471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740507415012683830855845 326345140314878218285471)
                  ·
                    rfl

theorem cell22_2859997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_2859997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2859997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2859997 prefixEnd_2859997 := by exact prefixLift 2859997
  have htrace : WordTrace (prefixWord ++ tailWord_2859997) baseStart_2859997 baseEnd_2859997 := by
    simpa [prefixWord, tailWord_2859997, baseEnd_2859997] using wordTrace_append hprefix tailTrace_2859997
  have hstable : (prefixWord ++ tailWord_2859997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859997).length < 2 ^ (prefixWord ++ tailWord_2859997).sum := by decide
  have hdescent : baseEnd_2859997 < baseStart_2859997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860053 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 7]
def baseStart_2860053 : Nat := 118140960795 + 2860053 * 2 ^ 59
def prefixEnd_2860053 : Nat := 4983230072969 + 3 ^ 40 * 2860053 * 2
def baseEnd_2860053 : Nat := 326351530296356391818747

theorem tailTrace_2860053 : CollatzResearch.WordTrace tailWord_2860053 prefixEnd_2860053 326351530296356391818747 := by
  unfold tailWord_2860053
  simp only [CollatzResearch.WordTrace]
  refine ⟨104314702707523914009368813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69543135138349276006245875 104314702707523914009368813)
  ·
    refine ⟨39118013515321467753513305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104314702707523914009368813 39118013515321467753513305)
    ·
      refine ⟨29338510136491100815134979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39118013515321467753513305 29338510136491100815134979)
      ·
        refine ⟨44007765204736651222702469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29338510136491100815134979 44007765204736651222702469)
        ·
          refine ⟨8251455975888122104256713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44007765204736651222702469 8251455975888122104256713)
          ·
            refine ⟨6188591981916091578192535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8251455975888122104256713 6188591981916091578192535)
            ·
              refine ⟨9282887972874137367288803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188591981916091578192535 9282887972874137367288803)
              ·
                refine ⟨13924331959311206050933205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282887972874137367288803 13924331959311206050933205)
                ·
                  refine ⟨326351530296356391818747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13924331959311206050933205 326351530296356391818747)
                  ·
                    rfl

theorem cell22_2860053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_2860053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860053 prefixEnd_2860053 := by exact prefixLift 2860053
  have htrace : WordTrace (prefixWord ++ tailWord_2860053) baseStart_2860053 baseEnd_2860053 := by
    simpa [prefixWord, tailWord_2860053, baseEnd_2860053] using wordTrace_append hprefix tailTrace_2860053
  have hstable : (prefixWord ++ tailWord_2860053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860053).length < 2 ^ (prefixWord ++ tailWord_2860053).sum := by decide
  have hdescent : baseEnd_2860053 < baseStart_2860053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860128 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_2860128 : Nat := 118140960795 + 2860128 * 2 ^ 59
def prefixEnd_2860128 : Nat := 4983230072969 + 3 ^ 40 * 2860128 * 2
def baseEnd_2860128 : Nat := 979080264921793979831011

theorem tailTrace_2860128 : CollatzResearch.WordTrace tailWord_2860128 prefixEnd_2860128 979080264921793979831011 := by
  unfold tailWord_2860128
  simp only [CollatzResearch.WordTrace]
  refine ⟨52158719091126100909174519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69544958788168134545566025 52158719091126100909174519)
  ·
    refine ⟨78238078636689151363761779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52158719091126100909174519 78238078636689151363761779)
    ·
      refine ⟨117357117955033727045642669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78238078636689151363761779 117357117955033727045642669)
      ·
        refine ⟨44008919233137647642116001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117357117955033727045642669 44008919233137647642116001)
        ·
          refine ⟨33006689424853235731587001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44008919233137647642116001 33006689424853235731587001)
          ·
            refine ⟨24755017068639926798690251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33006689424853235731587001 24755017068639926798690251)
            ·
              refine ⟨37132525602959890198035377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24755017068639926798690251 37132525602959890198035377)
              ·
                refine ⟨27849394202219917648526533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37132525602959890198035377 27849394202219917648526533)
                ·
                  refine ⟨5221761412916234559098725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27849394202219917648526533 5221761412916234559098725)
                  ·
                    refine ⟨979080264921793979831011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221761412916234559098725 979080264921793979831011)
                    ·
                      rfl

theorem cell22_2860128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_2860128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860128 prefixEnd_2860128 := by exact prefixLift 2860128
  have htrace : WordTrace (prefixWord ++ tailWord_2860128) baseStart_2860128 baseEnd_2860128 := by
    simpa [prefixWord, tailWord_2860128, baseEnd_2860128] using wordTrace_append hprefix tailTrace_2860128
  have hstable : (prefixWord ++ tailWord_2860128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860128).length < 2 ^ (prefixWord ++ tailWord_2860128).sum := by decide
  have hdescent : baseEnd_2860128 < baseStart_2860128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860209 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 1, 3]
def baseStart_2860209 : Nat := 118140960795 + 2860209 * 2 ^ 59
def prefixEnd_2860209 : Nat := 4983230072969 + 3 ^ 40 * 2860209 * 2
def baseEnd_2860209 : Nat := 979107992877136768555763

theorem tailTrace_2860209 : CollatzResearch.WordTrace tailWord_2860209 prefixEnd_2860209 979107992877136768555763 := by
  unfold tailWord_2860209
  simp only [CollatzResearch.WordTrace]
  refine ⟨104320392494958752652047681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69546928329972501768031787 104320392494958752652047681)
  ·
    refine ⟨78240294371219064489035761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104320392494958752652047681 78240294371219064489035761)
    ·
      refine ⟨58680220778414298366776821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78240294371219064489035761 58680220778414298366776821)
      ·
        refine ⟨5501270697976340471885327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58680220778414298366776821 5501270697976340471885327)
        ·
          refine ⟨8251906046964510707827991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501270697976340471885327 8251906046964510707827991)
          ·
            refine ⟨12377859070446766061741987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251906046964510707827991 12377859070446766061741987)
            ·
              refine ⟨18566788605670149092612981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12377859070446766061741987 18566788605670149092612981)
              ·
                refine ⟨1740636431781576477432467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18566788605670149092612981 1740636431781576477432467)
                ·
                  refine ⟨2610954647672364716148701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740636431781576477432467 2610954647672364716148701)
                  ·
                    refine ⟨979107992877136768555763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2610954647672364716148701 979107992877136768555763)
                    ·
                      rfl

theorem cell22_2860209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_2860209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860209 prefixEnd_2860209 := by exact prefixLift 2860209
  have htrace : WordTrace (prefixWord ++ tailWord_2860209) baseStart_2860209 baseEnd_2860209 := by
    simpa [prefixWord, tailWord_2860209, baseEnd_2860209] using wordTrace_append hprefix tailTrace_2860209
  have hstable : (prefixWord ++ tailWord_2860209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860209).length < 2 ^ (prefixWord ++ tailWord_2860209).sum := by decide
  have hdescent : baseEnd_2860209 < baseStart_2860209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860220 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_2860220 : Nat := 118140960795 + 2860220 * 2 ^ 59
def prefixEnd_2860220 : Nat := 4983230072969 + 3 ^ 40 * 2860220 * 2
def baseEnd_2860220 : Nat := 979111758401936406530729

theorem tailTrace_2860220 : CollatzResearch.WordTrace tailWord_2860220 prefixEnd_2860220 979111758401936406530729 := by
  unfold tailWord_2860220
  simp only [CollatzResearch.WordTrace]
  refine ⟨52160396848959450765349057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69547195798612601020465409 52160396848959450765349057)
  ·
    refine ⟨39120297636719588074011793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52160396848959450765349057 39120297636719588074011793)
    ·
      refine ⟨29340223227539691055508845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39120297636719588074011793 29340223227539691055508845)
      ·
        refine ⟨11002583710327384145815817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29340223227539691055508845 11002583710327384145815817)
        ·
          refine ⟨8251937782745538109361863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11002583710327384145815817 8251937782745538109361863)
          ·
            refine ⟨12377906674118307164042795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251937782745538109361863 12377906674118307164042795)
            ·
              refine ⟨18566860011177460746064193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12377906674118307164042795 18566860011177460746064193)
              ·
                refine ⟨13925145008383095559548145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18566860011177460746064193 13925145008383095559548145)
                ·
                  refine ⟨10443858756287321669661109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13925145008383095559548145 10443858756287321669661109)
                  ·
                    refine ⟨979111758401936406530729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10443858756287321669661109 979111758401936406530729)
                    ·
                      rfl

theorem cell22_2860220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_2860220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860220 prefixEnd_2860220 := by exact prefixLift 2860220
  have htrace : WordTrace (prefixWord ++ tailWord_2860220) baseStart_2860220 baseEnd_2860220 := by
    simpa [prefixWord, tailWord_2860220, baseEnd_2860220] using wordTrace_append hprefix tailTrace_2860220
  have hstable : (prefixWord ++ tailWord_2860220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860220).length < 2 ^ (prefixWord ++ tailWord_2860220).sum := by decide
  have hdescent : baseEnd_2860220 < baseStart_2860220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860222 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2860222 : Nat := 118140960795 + 2860222 * 2 ^ 59
def prefixEnd_2860222 : Nat := 4983230072969 + 3 ^ 40 * 2860222 * 2
def baseEnd_2860222 : Nat := 326370814347603022660241

theorem tailTrace_2860222 : CollatzResearch.WordTrace tailWord_2860222 prefixEnd_2860222 326370814347603022660241 := by
  unfold tailWord_2860222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040108330488956984033865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69547244429274437248180613 13040108330488956984033865)
  ·
    refine ⟨9780081247866717738025399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13040108330488956984033865 9780081247866717738025399)
    ·
      refine ⟨14670121871800076607038099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9780081247866717738025399 14670121871800076607038099)
      ·
        refine ⟨22005182807700114910557149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14670121871800076607038099 22005182807700114910557149)
        ·
          refine ⟨8251943552887543091458931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22005182807700114910557149 8251943552887543091458931)
          ·
            refine ⟨12377915329331314637188397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251943552887543091458931 12377915329331314637188397)
            ·
              refine ⟨4641718248499242988945649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12377915329331314637188397 4641718248499242988945649)
              ·
                refine ⟨3481288686374432241709237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641718248499242988945649 3481288686374432241709237)
                ·
                  refine ⟨326370814347603022660241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481288686374432241709237 326370814347603022660241)
                  ·
                    rfl

theorem cell22_2860222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2860222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860222 prefixEnd_2860222 := by exact prefixLift 2860222
  have htrace : WordTrace (prefixWord ++ tailWord_2860222) baseStart_2860222 baseEnd_2860222 := by
    simpa [prefixWord, tailWord_2860222, baseEnd_2860222] using wordTrace_append hprefix tailTrace_2860222
  have hstable : (prefixWord ++ tailWord_2860222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860222).length < 2 ^ (prefixWord ++ tailWord_2860222).sum := by decide
  have hdescent : baseEnd_2860222 < baseStart_2860222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860267 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 4]
def baseStart_2860267 : Nat := 118140960795 + 2860267 * 2 ^ 59
def prefixEnd_2860267 : Nat := 4983230072969 + 3 ^ 40 * 2860267 * 2
def baseEnd_2860267 : Nat := 326375949154147983535195

theorem tailTrace_2860267 : CollatzResearch.WordTrace tailWord_2860267 prefixEnd_2860267 326375949154147983535195 := by
  unfold tailWord_2860267
  simp only [CollatzResearch.WordTrace]
  refine ⟨104322507928748628557659055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69548338619165752371772703 104322507928748628557659055)
  ·
    refine ⟨156483761893122942836488583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104322507928748628557659055 156483761893122942836488583)
    ·
      refine ⟨234725642839684414254732875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156483761893122942836488583 234725642839684414254732875)
      ·
        refine ⟨352088464259526621382099313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234725642839684414254732875 352088464259526621382099313)
        ·
          refine ⟨264066348194644966036574485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352088464259526621382099313 264066348194644966036574485)
          ·
            refine ⟨12378110071623982782964429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 264066348194644966036574485 12378110071623982782964429)
            ·
              refine ⟨4641791276858993543611661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12378110071623982782964429 4641791276858993543611661)
              ·
                refine ⟨1740671728822122578854373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4641791276858993543611661 1740671728822122578854373)
                ·
                  refine ⟨326375949154147983535195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740671728822122578854373 326375949154147983535195)
                  ·
                    rfl

theorem cell22_2860267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 4].length) (baseStart_2860267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860267 prefixEnd_2860267 := by exact prefixLift 2860267
  have htrace : WordTrace (prefixWord ++ tailWord_2860267) baseStart_2860267 baseEnd_2860267 := by
    simpa [prefixWord, tailWord_2860267, baseEnd_2860267] using wordTrace_append hprefix tailTrace_2860267
  have hstable : (prefixWord ++ tailWord_2860267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860267).length < 2 ^ (prefixWord ++ tailWord_2860267).sum := by decide
  have hdescent : baseEnd_2860267 < baseStart_2860267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860282 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_2860282 : Nat := 118140960795 + 2860282 * 2 ^ 59
def prefixEnd_2860282 : Nat := 4983230072969 + 3 ^ 40 * 2860282 * 2
def baseEnd_2860282 : Nat := 979132982268988911480539

theorem tailTrace_2860282 : CollatzResearch.WordTrace tailWord_2860282 prefixEnd_2860282 979132982268988911480539 := by
  unfold tailWord_2860282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26080763755923571529863775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69548703349129524079636733 26080763755923571529863775)
  ·
    refine ⟨39121145633885357294795663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26080763755923571529863775 39121145633885357294795663)
    ·
      refine ⟨58681718450828035942193495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39121145633885357294795663 58681718450828035942193495)
      ·
        refine ⟨88022577676242053913290243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58681718450828035942193495 88022577676242053913290243)
        ·
          refine ⟨132033866514363080869935365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88022577676242053913290243 132033866514363080869935365)
          ·
            refine ⟨24756349971443077663112881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132033866514363080869935365 24756349971443077663112881)
            ·
              refine ⟨18567262478582308247334661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24756349971443077663112881 18567262478582308247334661)
              ·
                refine ⟨3481361714734182796375249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18567262478582308247334661 3481361714734182796375249)
                ·
                  refine ⟨2611021286050637097281437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3481361714734182796375249 2611021286050637097281437)
                  ·
                    refine ⟨979132982268988911480539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611021286050637097281437 979132982268988911480539)
                    ·
                      rfl

theorem cell22_2860282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_2860282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860282 prefixEnd_2860282 := by exact prefixLift 2860282
  have htrace : WordTrace (prefixWord ++ tailWord_2860282) baseStart_2860282 baseEnd_2860282 := by
    simpa [prefixWord, tailWord_2860282, baseEnd_2860282] using wordTrace_append hprefix tailTrace_2860282
  have hstable : (prefixWord ++ tailWord_2860282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860282).length < 2 ^ (prefixWord ++ tailWord_2860282).sum := by decide
  have hdescent : baseEnd_2860282 < baseStart_2860282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860284 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_2860284 : Nat := 118140960795 + 2860284 * 2 ^ 59
def prefixEnd_2860284 : Nat := 4983230072969 + 3 ^ 40 * 2860284 * 2
def baseEnd_2860284 : Nat := 326377888969953857643511

theorem tailTrace_2860284 : CollatzResearch.WordTrace tailWord_2860284 prefixEnd_2860284 326377888969953857643511 := by
  unfold tailWord_2860284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52161563984843520230513953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69548751979791360307351937 52161563984843520230513953)
  ·
    refine ⟨39121172988632640172885465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52161563984843520230513953 39121172988632640172885465)
    ·
      refine ⟨29340879741474480129664099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39121172988632640172885465 29340879741474480129664099)
      ·
        refine ⟨44011319612211720194496149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29340879741474480129664099 44011319612211720194496149)
        ·
          refine ⟨2063030606822424384117007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44011319612211720194496149 2063030606822424384117007)
          ·
            refine ⟨3094545910233636576175511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063030606822424384117007 3094545910233636576175511)
            ·
              refine ⟨4641818865350454864263267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094545910233636576175511 4641818865350454864263267)
              ·
                refine ⟨6962728298025682296394901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641818865350454864263267 6962728298025682296394901)
                ·
                  refine ⟨326377888969953857643511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6962728298025682296394901 326377888969953857643511)
                  ·
                    rfl

theorem cell22_2860284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_2860284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860284 prefixEnd_2860284 := by exact prefixLift 2860284
  have htrace : WordTrace (prefixWord ++ tailWord_2860284) baseStart_2860284 baseEnd_2860284 := by
    simpa [prefixWord, tailWord_2860284, baseEnd_2860284] using wordTrace_append hprefix tailTrace_2860284
  have hstable : (prefixWord ++ tailWord_2860284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860284).length < 2 ^ (prefixWord ++ tailWord_2860284).sum := by decide
  have hdescent : baseEnd_2860284 < baseStart_2860284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860299 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 2, 3]
def baseStart_2860299 : Nat := 118140960795 + 2860299 * 2 ^ 59
def prefixEnd_2860299 : Nat := 4983230072969 + 3 ^ 40 * 2860299 * 2
def baseEnd_2860299 : Nat := 979138801716406533805487

theorem tailTrace_2860299 : CollatzResearch.WordTrace tailWord_2860299 prefixEnd_2860299 979138801716406533805487 := by
  unfold tailWord_2860299
  simp only [CollatzResearch.WordTrace]
  refine ⟨104323675064632698022823951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69549116709755132015215967 104323675064632698022823951)
  ·
    refine ⟨156485512596949047034235927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104323675064632698022823951 156485512596949047034235927)
    ·
      refine ⟨234728268895423570551353891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156485512596949047034235927 234728268895423570551353891)
      ·
        refine ⟨352092403343135355827030837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234728268895423570551353891 352092403343135355827030837)
        ·
          refine ⟨33008662813418939608784141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352092403343135355827030837 33008662813418939608784141)
          ·
            refine ⟨12378248555032102353294053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33008662813418939608784141 12378248555032102353294053)
            ·
              refine ⟨2320921604068519191242635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12378248555032102353294053 2320921604068519191242635)
              ·
                refine ⟨3481382406102778786863953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320921604068519191242635 3481382406102778786863953)
                ·
                  refine ⟨2611036804577084090147965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3481382406102778786863953 2611036804577084090147965)
                  ·
                    refine ⟨979138801716406533805487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611036804577084090147965 979138801716406533805487)
                    ·
                      rfl

theorem cell22_2860299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 3].length) (baseStart_2860299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860299 prefixEnd_2860299 := by exact prefixLift 2860299
  have htrace : WordTrace (prefixWord ++ tailWord_2860299) baseStart_2860299 baseEnd_2860299 := by
    simpa [prefixWord, tailWord_2860299, baseEnd_2860299] using wordTrace_append hprefix tailTrace_2860299
  have hstable : (prefixWord ++ tailWord_2860299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860299).length < 2 ^ (prefixWord ++ tailWord_2860299).sum := by decide
  have hdescent : baseEnd_2860299 < baseStart_2860299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860391 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 5]
def baseStart_2860391 : Nat := 118140960795 + 2860391 * 2 ^ 59
def prefixEnd_2860391 : Nat := 4983230072969 + 3 ^ 40 * 2860391 * 2
def baseEnd_2860391 : Nat := 326390098398849653501735

theorem tailTrace_2860391 : CollatzResearch.WordTrace tailWord_2860391 prefixEnd_2860391 326390098398849653501735 := by
  unfold tailWord_2860391
  simp only [CollatzResearch.WordTrace]
  refine ⟨104327030580299397735173027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69551353720199598490115351 104327030580299397735173027)
  ·
    refine ⟨156490545870449096602759541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104327030580299397735173027 156490545870449096602759541)
    ·
      refine ⟨14670988675354602806508707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156490545870449096602759541 14670988675354602806508707)
      ·
        refine ⟨22006483013031904209763061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14670988675354602806508707 22006483013031904209763061)
        ·
          refine ⟨2063107782471741019665287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22006483013031904209763061 2063107782471741019665287)
          ·
            refine ⟨3094661673707611529497931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063107782471741019665287 3094661673707611529497931)
            ·
              refine ⟨4641992510561417294246897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094661673707611529497931 4641992510561417294246897)
              ·
                refine ⟨3481494382921062970685173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641992510561417294246897 3481494382921062970685173)
                ·
                  refine ⟨326390098398849653501735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481494382921062970685173 326390098398849653501735)
                  ·
                    rfl

theorem cell22_2860391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 5].length) (baseStart_2860391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860391 prefixEnd_2860391 := by exact prefixLift 2860391
  have htrace : WordTrace (prefixWord ++ tailWord_2860391) baseStart_2860391 baseEnd_2860391 := by
    simpa [prefixWord, tailWord_2860391, baseEnd_2860391] using wordTrace_append hprefix tailTrace_2860391
  have hstable : (prefixWord ++ tailWord_2860391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860391).length < 2 ^ (prefixWord ++ tailWord_2860391).sum := by decide
  have hdescent : baseEnd_2860391 < baseStart_2860391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860402 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_2860402 : Nat := 118140960795 + 2860402 * 2 ^ 59
def prefixEnd_2860402 : Nat := 4983230072969 + 3 ^ 40 * 2860402 * 2
def baseEnd_2860402 : Nat := 326391353573782866160057

theorem tailTrace_2860402 : CollatzResearch.WordTrace tailWord_2860402 prefixEnd_2860402 326391353573782866160057 := by
  unfold tailWord_2860402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26081857945814886653455865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69551621188839697742548973 26081857945814886653455865)
  ·
    refine ⟨19561393459361164990091899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26081857945814886653455865 19561393459361164990091899)
    ·
      refine ⟨29342090189041747485137849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19561393459361164990091899 29342090189041747485137849)
      ·
        refine ⟨22006567641781310613853387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29342090189041747485137849 22006567641781310613853387)
        ·
          refine ⟨33009851462671965920780081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22006567641781310613853387 33009851462671965920780081)
          ·
            refine ⟨24757388597003974440585061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33009851462671965920780081 24757388597003974440585061)
            ·
              refine ⟨4642010361938245207609699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24757388597003974440585061 4642010361938245207609699)
              ·
                refine ⟨6963015542907367811414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642010361938245207609699 6963015542907367811414549)
                ·
                  refine ⟨326391353573782866160057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6963015542907367811414549 326391353573782866160057)
                  ·
                    rfl

theorem cell22_2860402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_2860402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860402 prefixEnd_2860402 := by exact prefixLift 2860402
  have htrace : WordTrace (prefixWord ++ tailWord_2860402) baseStart_2860402 baseEnd_2860402 := by
    simpa [prefixWord, tailWord_2860402, baseEnd_2860402] using wordTrace_append hprefix tailTrace_2860402
  have hstable : (prefixWord ++ tailWord_2860402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860402).length < 2 ^ (prefixWord ++ tailWord_2860402).sum := by decide
  have hdescent : baseEnd_2860402 < baseStart_2860402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860436 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2860436 : Nat := 118140960795 + 2860436 * 2 ^ 59
def prefixEnd_2860436 : Nat := 4983230072969 + 3 ^ 40 * 2860436 * 2
def baseEnd_2860436 : Nat := 326395233205394614376689

theorem tailTrace_2860436 : CollatzResearch.WordTrace tailWord_2860436 prefixEnd_2860436 326395233205394614376689 := by
  unfold tailWord_2860436
  simp only [CollatzResearch.WordTrace]
  refine ⟨52164335932568185210280581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69552447910090913613707441 52164335932568185210280581)
  ·
    refine ⟨9780812987356534726927609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52164335932568185210280581 9780812987356534726927609)
    ·
      refine ⟨7335609740517401045195707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9780812987356534726927609 7335609740517401045195707)
      ·
        refine ⟨11003414610776101567793561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7335609740517401045195707 11003414610776101567793561)
        ·
          refine ⟨8252560958082076175845171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11003414610776101567793561 8252560958082076175845171)
          ·
            refine ⟨12378841437123114263767757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8252560958082076175845171 12378841437123114263767757)
            ·
              refine ⟨4642065538921167848912909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12378841437123114263767757 4642065538921167848912909)
              ·
                refine ⟨1740774577095437943342341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4642065538921167848912909 1740774577095437943342341)
                ·
                  refine ⟨326395233205394614376689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740774577095437943342341 326395233205394614376689)
                  ·
                    rfl

theorem cell22_2860436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2860436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860436 prefixEnd_2860436 := by exact prefixLift 2860436
  have htrace : WordTrace (prefixWord ++ tailWord_2860436) baseStart_2860436 baseEnd_2860436 := by
    simpa [prefixWord, tailWord_2860436, baseEnd_2860436] using wordTrace_append hprefix tailTrace_2860436
  have hstable : (prefixWord ++ tailWord_2860436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860436).length < 2 ^ (prefixWord ++ tailWord_2860436).sum := by decide
  have hdescent : baseEnd_2860436 < baseStart_2860436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860447 : List Nat := [1, 1, 2, 5, 1, 4, 8]
def baseStart_2860447 : Nat := 118140960795 + 2860447 * 2 ^ 59
def prefixEnd_2860447 : Nat := 4983230072969 + 3 ^ 40 * 2860447 * 2
def baseEnd_2860447 : Nat := 36266276486703091892779

theorem tailTrace_2860447 : CollatzResearch.WordTrace tailWord_2860447 prefixEnd_2860447 36266276486703091892779 := by
  unfold tailWord_2860447
  simp only [CollatzResearch.WordTrace]
  refine ⟨104329073068096519299211595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69552715378731012866141063 104329073068096519299211595)
  ·
    refine ⟨156493609602144778948817393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104329073068096519299211595 156493609602144778948817393)
    ·
      refine ⟨117370207201608584211613045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156493609602144778948817393 117370207201608584211613045)
      ·
        refine ⟨11003456925150804769838723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117370207201608584211613045 11003456925150804769838723)
        ·
          refine ⟨16505185387726207154758085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003456925150804769838723 16505185387726207154758085)
          ·
            refine ⟨3094722260198663841517141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16505185387726207154758085 3094722260198663841517141)
            ·
              refine ⟨36266276486703091892779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3094722260198663841517141 36266276486703091892779)
              ·
                rfl

theorem cell22_2860447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 8].length) (baseStart_2860447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860447 prefixEnd_2860447 := by exact prefixLift 2860447
  have htrace : WordTrace (prefixWord ++ tailWord_2860447) baseStart_2860447 baseEnd_2860447 := by
    simpa [prefixWord, tailWord_2860447, baseEnd_2860447] using wordTrace_append hprefix tailTrace_2860447
  have hstable : (prefixWord ++ tailWord_2860447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860447).length < 2 ^ (prefixWord ++ tailWord_2860447).sum := by decide
  have hdescent : baseEnd_2860447 < baseStart_2860447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860509 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2860509 : Nat := 118140960795 + 2860509 * 2 ^ 59
def prefixEnd_2860509 : Nat := 4983230072969 + 3 ^ 40 * 2860509 * 2
def baseEnd_2860509 : Nat := 326403563002678662018281

theorem tailTrace_2860509 : CollatzResearch.WordTrace tailWord_2860509 prefixEnd_2860509 326403563002678662018281 := by
  unfold tailWord_2860509
  simp only [CollatzResearch.WordTrace]
  refine ⟨104331334393871903887968581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69554222929247935925312387 104331334393871903887968581)
  ·
    refine ⟨19562125198850981978994109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104331334393871903887968581 19562125198850981978994109)
    ·
      refine ⟨7335796949569118242122791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19562125198850981978994109 7335796949569118242122791)
      ·
        refine ⟨11003695424353677363184187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7335796949569118242122791 11003695424353677363184187)
        ·
          refine ⟨16505543136530516044776281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003695424353677363184187 16505543136530516044776281)
          ·
            refine ⟨12379157352397887033582211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16505543136530516044776281 12379157352397887033582211)
            ·
              refine ⟨18568736028596830550373317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12379157352397887033582211 18568736028596830550373317)
              ·
                refine ⟨3481638005361905728194997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18568736028596830550373317 3481638005361905728194997)
                ·
                  refine ⟨326403563002678662018281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481638005361905728194997 326403563002678662018281)
                  ·
                    rfl

theorem cell22_2860509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2860509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860509 prefixEnd_2860509 := by exact prefixLift 2860509
  have htrace : WordTrace (prefixWord ++ tailWord_2860509) baseStart_2860509 baseEnd_2860509 := by
    simpa [prefixWord, tailWord_2860509, baseEnd_2860509] using wordTrace_append hprefix tailTrace_2860509
  have hstable : (prefixWord ++ tailWord_2860509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860509).length < 2 ^ (prefixWord ++ tailWord_2860509).sum := by decide
  have hdescent : baseEnd_2860509 < baseStart_2860509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860513 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 1, 3]
def baseStart_2860513 : Nat := 118140960795 + 2860513 * 2 ^ 59
def prefixEnd_2860513 : Nat := 4983230072969 + 3 ^ 40 * 2860513 * 2
def baseEnd_2860513 : Nat := 979212058289781308954831

theorem tailTrace_2860513 : CollatzResearch.WordTrace tailWord_2860513 prefixEnd_2860513 979212058289781308954831 := by
  unfold tailWord_2860513
  simp only [CollatzResearch.WordTrace]
  refine ⟨104331480285857412571114193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69554320190571608380742795 104331480285857412571114193)
  ·
    refine ⟨78248610214393059428335645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104331480285857412571114193 78248610214393059428335645)
    ·
      refine ⟨29343228830397397285625867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78248610214393059428335645 29343228830397397285625867)
      ·
        refine ⟨44014843245596095928438801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29343228830397397285625867 44014843245596095928438801)
        ·
          refine ⟨33011132434197071946329101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44014843245596095928438801 33011132434197071946329101)
          ·
            refine ⟨12379174662823901979873413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33011132434197071946329101 12379174662823901979873413)
            ·
              refine ⟨2321095249279481621226265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12379174662823901979873413 2321095249279481621226265)
              ·
                refine ⟨1740821436959611215919699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321095249279481621226265 1740821436959611215919699)
                ·
                  refine ⟨2611232155439416823879549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740821436959611215919699 2611232155439416823879549)
                  ·
                    refine ⟨979212058289781308954831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611232155439416823879549 979212058289781308954831)
                    ·
                      rfl

theorem cell22_2860513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_2860513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860513 prefixEnd_2860513 := by exact prefixLift 2860513
  have htrace : WordTrace (prefixWord ++ tailWord_2860513) baseStart_2860513 baseEnd_2860513 := by
    simpa [prefixWord, tailWord_2860513, baseEnd_2860513] using wordTrace_append hprefix tailTrace_2860513
  have hstable : (prefixWord ++ tailWord_2860513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860513).length < 2 ^ (prefixWord ++ tailWord_2860513).sum := by decide
  have hdescent : baseEnd_2860513 < baseStart_2860513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860556 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_2860556 : Nat := 118140960795 + 2860556 * 2 ^ 59
def prefixEnd_2860556 : Nat := 4983230072969 + 3 ^ 40 * 2860556 * 2
def baseEnd_2860556 : Nat := 979226778068543530129699

theorem tailTrace_2860556 : CollatzResearch.WordTrace tailWord_2860556 prefixEnd_2860556 979226778068543530129699 := by
  unfold tailWord_2860556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52166524312350815457464761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69555365749801087276619681 52166524312350815457464761)
  ·
    refine ⟨39124893234263111593098571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52166524312350815457464761 39124893234263111593098571)
    ·
      refine ⟨58687339851394667389647857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39124893234263111593098571 58687339851394667389647857)
      ·
        refine ⟨44015504888546000542235893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58687339851394667389647857 44015504888546000542235893)
        ·
          refine ⟨4126453583301187550834615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44015504888546000542235893 4126453583301187550834615)
          ·
            refine ⟨6189680374951781326251923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126453583301187550834615 6189680374951781326251923)
            ·
              refine ⟨9284520562427671989377885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6189680374951781326251923 9284520562427671989377885)
              ·
                refine ⟨3481695210910376996016707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9284520562427671989377885 3481695210910376996016707)
                ·
                  refine ⟨5222542816365565494025061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481695210910376996016707 5222542816365565494025061)
                  ·
                    refine ⟨979226778068543530129699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5222542816365565494025061 979226778068543530129699)
                    ·
                      rfl

theorem cell22_2860556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_2860556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860556 prefixEnd_2860556 := by exact prefixLift 2860556
  have htrace : WordTrace (prefixWord ++ tailWord_2860556) baseStart_2860556 baseEnd_2860556 := by
    simpa [prefixWord, tailWord_2860556, baseEnd_2860556] using wordTrace_append hprefix tailTrace_2860556
  have hstable : (prefixWord ++ tailWord_2860556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860556).length < 2 ^ (prefixWord ++ tailWord_2860556).sum := by decide
  have hdescent : baseEnd_2860556 < baseStart_2860556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860599 : List Nat := [1, 1, 3, 1, 2, 4, 4, 6]
def baseStart_2860599 : Nat := 118140960795 + 2860599 * 2 ^ 59
def prefixEnd_2860599 : Nat := 4983230072969 + 3 ^ 40 * 2860599 * 2
def baseEnd_2860599 : Nat := 108804610871922861256063

theorem tailTrace_2860599 : CollatzResearch.WordTrace tailWord_2860599 prefixEnd_2860599 108804610871922861256063 := by
  unfold tailWord_2860599
  simp only [CollatzResearch.WordTrace]
  refine ⟨104334616963545849258744851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69556411309030566172496567 104334616963545849258744851)
  ·
    refine ⟨156501925445318773888117277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104334616963545849258744851 156501925445318773888117277)
    ·
      refine ⟨58688222041994540208043979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156501925445318773888117277 58688222041994540208043979)
      ·
        refine ⟨88032333062991810312065969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58688222041994540208043979 88032333062991810312065969)
        ·
          refine ⟨66024249797243857734049477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88032333062991810312065969 66024249797243857734049477)
          ·
            refine ⟨12379546836983223325134277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66024249797243857734049477 12379546836983223325134277)
            ·
              refine ⟨2321165031934354373462677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12379546836983223325134277 2321165031934354373462677)
              ·
                refine ⟨108804610871922861256063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2321165031934354373462677 108804610871922861256063)
                ·
                  rfl

theorem cell22_2860599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 6].length) (baseStart_2860599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860599 prefixEnd_2860599 := by exact prefixLift 2860599
  have htrace : WordTrace (prefixWord ++ tailWord_2860599) baseStart_2860599 baseEnd_2860599 := by
    simpa [prefixWord, tailWord_2860599, baseEnd_2860599] using wordTrace_append hprefix tailTrace_2860599
  have hstable : (prefixWord ++ tailWord_2860599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860599).length < 2 ^ (prefixWord ++ tailWord_2860599).sum := by decide
  have hdescent : baseEnd_2860599 < baseStart_2860599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860605 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2860605 : Nat := 118140960795 + 2860605 * 2 ^ 59
def prefixEnd_2860605 : Nat := 4983230072969 + 3 ^ 40 * 2860605 * 2
def baseEnd_2860605 : Nat := 326414517256641245218183

theorem tailTrace_2860605 : CollatzResearch.WordTrace tailWord_2860605 prefixEnd_2860605 326414517256641245218183 := by
  unfold tailWord_2860605
  simp only [CollatzResearch.WordTrace]
  refine ⟨104334835801524112283463269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69556557201016074855642179 104334835801524112283463269)
  ·
    refine ⟨19562781712785771053149363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104334835801524112283463269 19562781712785771053149363)
    ·
      refine ⟨29344172569178656579724045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19562781712785771053149363 29344172569178656579724045)
      ·
        refine ⟨11004064713441996217396517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29344172569178656579724045 11004064713441996217396517)
        ·
          refine ⟨2063262133770374290761847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11004064713441996217396517 2063262133770374290761847)
          ·
            refine ⟨3094893200655561436142771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063262133770374290761847 3094893200655561436142771)
            ·
              refine ⟨4642339800983342154214157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094893200655561436142771 4642339800983342154214157)
              ·
                refine ⟨1740877425368753307830309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4642339800983342154214157 1740877425368753307830309)
                ·
                  refine ⟨326414517256641245218183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740877425368753307830309 326414517256641245218183)
                  ·
                    rfl

theorem cell22_2860605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2860605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860605 prefixEnd_2860605 := by exact prefixLift 2860605
  have htrace : WordTrace (prefixWord ++ tailWord_2860605) baseStart_2860605 baseEnd_2860605 := by
    simpa [prefixWord, tailWord_2860605, baseEnd_2860605] using wordTrace_append hprefix tailTrace_2860605
  have hstable : (prefixWord ++ tailWord_2860605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860605).length < 2 ^ (prefixWord ++ tailWord_2860605).sum := by decide
  have hdescent : baseEnd_2860605 < baseStart_2860605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860631 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 3, 3]
def baseStart_2860631 : Nat := 118140960795 + 2860631 * 2 ^ 59
def prefixEnd_2860631 : Nat := 4983230072969 + 3 ^ 40 * 2860631 * 2
def baseEnd_2860631 : Nat := 979252452101268334504469

theorem tailTrace_2860631 : CollatzResearch.WordTrace tailWord_2860631 prefixEnd_2860631 979252452101268334504469 := by
  unfold tailWord_2860631
  simp only [CollatzResearch.WordTrace]
  refine ⟨104335784099429918723909747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69557189399619945815939831 104335784099429918723909747)
  ·
    refine ⟨156503676149144878085864621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104335784099429918723909747 156503676149144878085864621)
    ·
      refine ⟨58688878555929329282199233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156503676149144878085864621 58688878555929329282199233)
      ·
        refine ⟨44016658916946996961649425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58688878555929329282199233 44016658916946996961649425)
        ·
          refine ⟨33012494187710247721237069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44016658916946996961649425 33012494187710247721237069)
          ·
            refine ⟨12379685320391342895463901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33012494187710247721237069 12379685320391342895463901)
            ·
              refine ⟨4642381995146753585798963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12379685320391342895463901 4642381995146753585798963)
              ·
                refine ⟨6963572992720130378698445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642381995146753585798963 6963572992720130378698445)
                ·
                  refine ⟨2611339872270048892011917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6963572992720130378698445 2611339872270048892011917)
                  ·
                    refine ⟨979252452101268334504469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611339872270048892011917 979252452101268334504469)
                    ·
                      rfl

theorem cell22_2860631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_2860631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860631 prefixEnd_2860631 := by exact prefixLift 2860631
  have htrace : WordTrace (prefixWord ++ tailWord_2860631) baseStart_2860631 baseEnd_2860631 := by
    simpa [prefixWord, tailWord_2860631, baseEnd_2860631] using wordTrace_append hprefix tailTrace_2860631
  have hstable : (prefixWord ++ tailWord_2860631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860631).length < 2 ^ (prefixWord ++ tailWord_2860631).sum := by decide
  have hdescent : baseEnd_2860631 < baseStart_2860631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860682 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_2860682 : Nat := 118140960795 + 2860682 * 2 ^ 59
def prefixEnd_2860682 : Nat := 4983230072969 + 3 ^ 40 * 2860682 * 2
def baseEnd_2860682 : Nat := 979269910443521201479313

theorem tailTrace_2860682 : CollatzResearch.WordTrace tailWord_2860682 prefixEnd_2860682 979269910443521201479313 := by
  unfold tailWord_2860682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26084411055561288608504075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69558429481496769622677533 26084411055561288608504075)
  ·
    refine ⟨39126616583341932912756113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26084411055561288608504075 39126616583341932912756113)
    ·
      refine ⟨29344962437506449684567085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39126616583341932912756113 29344962437506449684567085)
      ·
        refine ⟨11004360914064918631712657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29344962437506449684567085 11004360914064918631712657)
        ·
          refine ⟨8253270685548688973784493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11004360914064918631712657 8253270685548688973784493)
          ·
            refine ⟨3094976507080758365169185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8253270685548688973784493 3094976507080758365169185)
            ·
              refine ⟨2321232380310568773876889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094976507080758365169185 2321232380310568773876889)
              ·
                refine ⟨1740924285232926580407667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321232380310568773876889 1740924285232926580407667)
                ·
                  refine ⟨2611386427849389870611501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740924285232926580407667 2611386427849389870611501)
                  ·
                    refine ⟨979269910443521201479313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611386427849389870611501 979269910443521201479313)
                    ·
                      rfl

theorem cell22_2860682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_2860682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860682 prefixEnd_2860682 := by exact prefixLift 2860682
  have htrace : WordTrace (prefixWord ++ tailWord_2860682) baseStart_2860682 baseEnd_2860682 := by
    simpa [prefixWord, tailWord_2860682, baseEnd_2860682] using wordTrace_append hprefix tailTrace_2860682
  have hstable : (prefixWord ++ tailWord_2860682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860682).length < 2 ^ (prefixWord ++ tailWord_2860682).sum := by decide
  have hdescent : baseEnd_2860682 < baseStart_2860682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860719 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_2860719 : Nat := 118140960795 + 2860719 * 2 ^ 59
def prefixEnd_2860719 : Nat := 4983230072969 + 3 ^ 40 * 2860719 * 2
def baseEnd_2860719 : Nat := 979282576299665438304199

theorem tailTrace_2860719 : CollatzResearch.WordTrace tailWord_2860719 prefixEnd_2860719 979282576299665438304199 := by
  unfold tailWord_2860719
  simp only [CollatzResearch.WordTrace]
  refine ⟨104338993723111109753113211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69559329148740739835408807 104338993723111109753113211)
  ·
    refine ⟨156508490584666664629669817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104338993723111109753113211 156508490584666664629669817)
    ·
      refine ⟨117381367938499998472252363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156508490584666664629669817 117381367938499998472252363)
      ·
        refine ⟨176072051907749997708378545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117381367938499998472252363 176072051907749997708378545)
        ·
          refine ⟨132054038930812498281283909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176072051907749997708378545 132054038930812498281283909)
          ·
            refine ⟨24760132299527343427740733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132054038930812498281283909 24760132299527343427740733)
            ·
              refine ⟨9285049612322753785402775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24760132299527343427740733 9285049612322753785402775)
              ·
                refine ⟨13927574418484130678104163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9285049612322753785402775 13927574418484130678104163)
                ·
                  refine ⟨20891361627726196017156245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13927574418484130678104163 20891361627726196017156245)
                  ·
                    refine ⟨979282576299665438304199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20891361627726196017156245 979282576299665438304199)
                    ·
                      rfl

theorem cell22_2860719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_2860719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860719 prefixEnd_2860719 := by exact prefixLift 2860719
  have htrace : WordTrace (prefixWord ++ tailWord_2860719) baseStart_2860719 baseEnd_2860719 := by
    simpa [prefixWord, tailWord_2860719, baseEnd_2860719] using wordTrace_append hprefix tailTrace_2860719
  have hstable : (prefixWord ++ tailWord_2860719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860719).length < 2 ^ (prefixWord ++ tailWord_2860719).sum := by decide
  have hdescent : baseEnd_2860719 < baseStart_2860719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860779 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 7]
def baseStart_2860779 : Nat := 118140960795 + 2860779 * 2 ^ 59
def prefixEnd_2860779 : Nat := 4983230072969 + 3 ^ 40 * 2860779 * 2
def baseEnd_2860779 : Nat := 326434371841948427268005

theorem tailTrace_2860779 : CollatzResearch.WordTrace tailWord_2860779 prefixEnd_2860779 326434371841948427268005 := by
  unfold tailWord_2860779
  simp only [CollatzResearch.WordTrace]
  refine ⟨104341182102893740000297391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69560788068595826666864927 104341182102893740000297391)
  ·
    refine ⟨156511773154340610000446087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104341182102893740000297391 156511773154340610000446087)
    ·
      refine ⟨234767659731510915000669131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156511773154340610000446087 234767659731510915000669131)
      ·
        refine ⟨352151489597266372501003697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234767659731510915000669131 352151489597266372501003697)
        ·
          refine ⟨264113617197949779375752773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352151489597266372501003697 264113617197949779375752773)
          ·
            refine ⟨49521303224615583632953645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264113617197949779375752773 49521303224615583632953645)
            ·
              refine ⟨18570488709230843862357617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49521303224615583632953645 18570488709230843862357617)
              ·
                refine ⟨13927866531923132896768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18570488709230843862357617 13927866531923132896768213)
                ·
                  refine ⟨326434371841948427268005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13927866531923132896768213 326434371841948427268005)
                  ·
                    rfl

theorem cell22_2860779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_2860779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860779 prefixEnd_2860779 := by exact prefixLift 2860779
  have htrace : WordTrace (prefixWord ++ tailWord_2860779) baseStart_2860779 baseEnd_2860779 := by
    simpa [prefixWord, tailWord_2860779, baseEnd_2860779] using wordTrace_append hprefix tailTrace_2860779
  have hstable : (prefixWord ++ tailWord_2860779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860779).length < 2 ^ (prefixWord ++ tailWord_2860779).sum := by decide
  have hdescent : baseEnd_2860779 < baseStart_2860779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860796 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_2860796 : Nat := 118140960795 + 2860796 * 2 ^ 59
def prefixEnd_2860796 : Nat := 4983230072969 + 3 ^ 40 * 2860796 * 2
def baseEnd_2860796 : Nat := 326436311657754301376321

theorem tailTrace_2860796 : CollatzResearch.WordTrace tailWord_2860796 prefixEnd_2860796 326436311657754301376321 := by
  unfold tailWord_2860796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52170901071916075951833121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69561201429221434602444161 52170901071916075951833121)
  ·
    refine ⟨39128175803937056963874841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52170901071916075951833121 39128175803937056963874841)
    ·
      refine ⟨29346131852952792722906131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39128175803937056963874841 29346131852952792722906131)
      ·
        refine ⟨44019197779429189084359197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29346131852952792722906131 44019197779429189084359197)
        ·
          refine ⟨16507199167285945906634699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44019197779429189084359197 16507199167285945906634699)
          ·
            refine ⟨24760798750928918859952049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16507199167285945906634699 24760798750928918859952049)
            ·
              refine ⟨18570599063196689144964037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24760798750928918859952049 18570599063196689144964037)
              ·
                refine ⟨3481987324349379214680757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18570599063196689144964037 3481987324349379214680757)
                ·
                  refine ⟨326436311657754301376321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481987324349379214680757 326436311657754301376321)
                  ·
                    rfl

theorem cell22_2860796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_2860796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860796 prefixEnd_2860796 := by exact prefixLift 2860796
  have htrace : WordTrace (prefixWord ++ tailWord_2860796) baseStart_2860796 baseEnd_2860796 := by
    simpa [prefixWord, tailWord_2860796, baseEnd_2860796] using wordTrace_append hprefix tailTrace_2860796
  have hstable : (prefixWord ++ tailWord_2860796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860796).length < 2 ^ (prefixWord ++ tailWord_2860796).sum := by decide
  have hdescent : baseEnd_2860796 < baseStart_2860796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860809 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_2860809 : Nat := 118140960795 + 2860809 * 2 ^ 59
def prefixEnd_2860809 : Nat := 4983230072969 + 3 ^ 40 * 2860809 * 2
def baseEnd_2860809 : Nat := 979313385138935203553923

theorem tailTrace_2860809 : CollatzResearch.WordTrace tailWord_2860809 prefixEnd_2860809 979313385138935203553923 := by
  unfold tailWord_2860809
  simp only [CollatzResearch.WordTrace]
  refine ⟨104342276292785055123889481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69561517528523370082592987 104342276292785055123889481)
  ·
    refine ⟨78256707219588791342917111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104342276292785055123889481 78256707219588791342917111)
    ·
      refine ⟨117385060829383187014375667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78256707219588791342917111 117385060829383187014375667)
      ·
        refine ⟨176077591244074780521563501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117385060829383187014375667 176077591244074780521563501)
        ·
          refine ⟨66029096716528042695586313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176077591244074780521563501 66029096716528042695586313)
          ·
            refine ⟨49521822537396032021689735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66029096716528042695586313 49521822537396032021689735)
            ·
              refine ⟨74282733806094048032534603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49521822537396032021689735 74282733806094048032534603)
              ·
                refine ⟨111424100709141072048801905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74282733806094048032534603 111424100709141072048801905)
                ·
                  refine ⟨83568075531855804036601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111424100709141072048801905 83568075531855804036601429)
                  ·
                    refine ⟨979313385138935203553923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83568075531855804036601429 979313385138935203553923)
                    ·
                      rfl

theorem cell22_2860809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_2860809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860809 prefixEnd_2860809 := by exact prefixLift 2860809
  have htrace : WordTrace (prefixWord ++ tailWord_2860809) baseStart_2860809 baseEnd_2860809 := by
    simpa [prefixWord, tailWord_2860809, baseEnd_2860809] using wordTrace_append hprefix tailTrace_2860809
  have hstable : (prefixWord ++ tailWord_2860809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860809).length < 2 ^ (prefixWord ++ tailWord_2860809).sum := by decide
  have hdescent : baseEnd_2860809 < baseStart_2860809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860871 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2860871 : Nat := 118140960795 + 2860871 * 2 ^ 59
def prefixEnd_2860871 : Nat := 4983230072969 + 3 ^ 40 * 2860871 * 2
def baseEnd_2860871 : Nat := 979334609005987708503733

theorem tailTrace_2860871 : CollatzResearch.WordTrace tailWord_2860871 prefixEnd_2860871 979334609005987708503733 := by
  unfold tailWord_2860871
  simp only [CollatzResearch.WordTrace]
  refine ⟨104344537618560439712646467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69563025079040293141764311 104344537618560439712646467)
  ·
    refine ⟨156516806427840659568969701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104344537618560439712646467 156516806427840659568969701)
    ·
      refine ⟨29346901205220123669181819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156516806427840659568969701 29346901205220123669181819)
      ·
        refine ⟨44020351807830185503772729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29346901205220123669181819 44020351807830185503772729)
        ·
          refine ⟨33015263855872639127829547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44020351807830185503772729 33015263855872639127829547)
          ·
            refine ⟨49522895783808958691744321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33015263855872639127829547 49522895783808958691744321)
            ·
              refine ⟨37142171837856719018808241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49522895783808958691744321 37142171837856719018808241)
              ·
                refine ⟨27856628878392539264106181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37142171837856719018808241 27856628878392539264106181)
                ·
                  refine ⟨5223117914698601112019909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27856628878392539264106181 5223117914698601112019909)
                  ·
                    refine ⟨979334609005987708503733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223117914698601112019909 979334609005987708503733)
                    ·
                      rfl

theorem cell22_2860871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2860871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860871 prefixEnd_2860871 := by exact prefixLift 2860871
  have htrace : WordTrace (prefixWord ++ tailWord_2860871) baseStart_2860871 baseEnd_2860871 := by
    simpa [prefixWord, tailWord_2860871, baseEnd_2860871] using wordTrace_append hprefix tailTrace_2860871
  have hstable : (prefixWord ++ tailWord_2860871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860871).length < 2 ^ (prefixWord ++ tailWord_2860871).sum := by decide
  have hdescent : baseEnd_2860871 < baseStart_2860871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860873 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_2860873 : Nat := 118140960795 + 2860873 * 2 ^ 59
def prefixEnd_2860873 : Nat := 4983230072969 + 3 ^ 40 * 2860873 * 2
def baseEnd_2860873 : Nat := 979335293646860369953727

theorem tailTrace_2860873 : CollatzResearch.WordTrace tailWord_2860873 prefixEnd_2860873 979335293646860369953727 := by
  unfold tailWord_2860873
  simp only [CollatzResearch.WordTrace]
  refine ⟨104344610564553194054219273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69563073709702129369479515 104344610564553194054219273)
  ·
    refine ⟨78258457923414895540664455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104344610564553194054219273 78258457923414895540664455)
    ·
      refine ⟨117387686885122343310996683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78258457923414895540664455 117387686885122343310996683)
      ·
        refine ⟨176081530327683514966495025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117387686885122343310996683 176081530327683514966495025)
        ·
          refine ⟨132061147745762636224871269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176081530327683514966495025 132061147745762636224871269)
          ·
            refine ⟨24761465202330494292163363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132061147745762636224871269 24761465202330494292163363)
            ·
              refine ⟨37142197803495741438245045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24761465202330494292163363 37142197803495741438245045)
              ·
                refine ⟨3482081044077725759835473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37142197803495741438245045 3482081044077725759835473)
                ·
                  refine ⟨2611560783058294319876605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482081044077725759835473 2611560783058294319876605)
                  ·
                    refine ⟨979335293646860369953727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611560783058294319876605 979335293646860369953727)
                    ·
                      rfl

theorem cell22_2860873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_2860873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860873 prefixEnd_2860873 := by exact prefixLift 2860873
  have htrace : WordTrace (prefixWord ++ tailWord_2860873) baseStart_2860873 baseEnd_2860873 := by
    simpa [prefixWord, tailWord_2860873, baseEnd_2860873] using wordTrace_append hprefix tailTrace_2860873
  have hstable : (prefixWord ++ tailWord_2860873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860873).length < 2 ^ (prefixWord ++ tailWord_2860873).sum := by decide
  have hdescent : baseEnd_2860873 < baseStart_2860873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860892 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_2860892 : Nat := 118140960795 + 2860892 * 2 ^ 59
def prefixEnd_2860892 : Nat := 4983230072969 + 3 ^ 40 * 2860892 * 2
def baseEnd_2860892 : Nat := 326447265911716884576223

theorem tailTrace_2860892 : CollatzResearch.WordTrace tailWord_2860892 prefixEnd_2860892 326447265911716884576223 := by
  unfold tailWord_2860892
  simp only [CollatzResearch.WordTrace]
  refine ⟨52172651775742180149580465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69563535700989573532773953 52172651775742180149580465)
  ·
    refine ⟨39129488831806635112185349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52172651775742180149580465 39129488831806635112185349)
    ·
      refine ⟨7336779155963744083534753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39129488831806635112185349 7336779155963744083534753)
      ·
        refine ⟨5502584366972808062651065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7336779155963744083534753 5502584366972808062651065)
        ·
          refine ⟨4126938275229606046988299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5502584366972808062651065 4126938275229606046988299)
          ·
            refine ⟨6190407412844409070482449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126938275229606046988299 6190407412844409070482449)
            ·
              refine ⟨4642805559633306802861837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190407412844409070482449 4642805559633306802861837)
              ·
                refine ⟨1741052084862490051073189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4642805559633306802861837 1741052084862490051073189)
                ·
                  refine ⟨326447265911716884576223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741052084862490051073189 326447265911716884576223)
                  ·
                    rfl

theorem cell22_2860892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_2860892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860892 prefixEnd_2860892 := by exact prefixLift 2860892
  have htrace : WordTrace (prefixWord ++ tailWord_2860892) baseStart_2860892 baseEnd_2860892 := by
    simpa [prefixWord, tailWord_2860892, baseEnd_2860892] using wordTrace_append hprefix tailTrace_2860892
  have hstable : (prefixWord ++ tailWord_2860892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860892).length < 2 ^ (prefixWord ++ tailWord_2860892).sum := by decide
  have hdescent : baseEnd_2860892 < baseStart_2860892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860948 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2860948 : Nat := 118140960795 + 2860948 * 2 ^ 59
def prefixEnd_2860948 : Nat := 4983230072969 + 3 ^ 40 * 2860948 * 2
def baseEnd_2860948 : Nat := 326453655893195058109499

theorem tailTrace_2860948 : CollatzResearch.WordTrace tailWord_2860948 prefixEnd_2860948 326453655893195058109499 := by
  unfold tailWord_2860948
  simp only [CollatzResearch.WordTrace]
  refine ⟨52173673019640740931599749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69564897359520987908799665 52173673019640740931599749)
  ·
    refine ⟨9782563691182638924674953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52173673019640740931599749 9782563691182638924674953)
    ·
      refine ⟨7336922768386979193506215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9782563691182638924674953 7336922768386979193506215)
      ·
        refine ⟨11005384152580468790259323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7336922768386979193506215 11005384152580468790259323)
        ·
          refine ⟨16508076228870703185388985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005384152580468790259323 16508076228870703185388985)
          ·
            refine ⟨12381057171653027389041739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16508076228870703185388985 12381057171653027389041739)
            ·
              refine ⟨18571585757479541083562609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12381057171653027389041739 18571585757479541083562609)
              ·
                refine ⟨13928689318109655812671957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18571585757479541083562609 13928689318109655812671957)
                ·
                  refine ⟨326453655893195058109499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13928689318109655812671957 326453655893195058109499)
                  ·
                    rfl

theorem cell22_2860948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2860948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2860948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2860948 prefixEnd_2860948 := by exact prefixLift 2860948
  have htrace : WordTrace (prefixWord ++ tailWord_2860948) baseStart_2860948 baseEnd_2860948 := by
    simpa [prefixWord, tailWord_2860948, baseEnd_2860948] using wordTrace_append hprefix tailTrace_2860948
  have hstable : (prefixWord ++ tailWord_2860948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860948).length < 2 ^ (prefixWord ++ tailWord_2860948).sum := by decide
  have hdescent : baseEnd_2860948 < baseStart_2860948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861008 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_2861008 : Nat := 118140960795 + 2861008 * 2 ^ 59
def prefixEnd_2861008 : Nat := 4983230072969 + 3 ^ 40 * 2861008 * 2
def baseEnd_2861008 : Nat := 979381506905765017828313

theorem tailTrace_2861008 : CollatzResearch.WordTrace tailWord_2861008 prefixEnd_2861008 979381506905765017828313 := by
  unfold tailWord_2861008
  simp only [CollatzResearch.WordTrace]
  refine ⟨52174767209532056055191839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69566356279376074740255785 52174767209532056055191839)
  ·
    refine ⟨78262150814298084082787759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52174767209532056055191839 78262150814298084082787759)
    ·
      refine ⟨117393226221447126124181639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78262150814298084082787759 117393226221447126124181639)
      ·
        refine ⟨176089839332170689186272459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117393226221447126124181639 176089839332170689186272459)
        ·
          refine ⟨264134758998256033779408689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176089839332170689186272459 264134758998256033779408689)
          ·
            refine ⟨198101069248692025334556517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264134758998256033779408689 198101069248692025334556517)
            ·
              refine ⟨37143950484129754750229347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198101069248692025334556517 37143950484129754750229347)
              ·
                refine ⟨55715925726194632125344021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37143950484129754750229347 55715925726194632125344021)
                ·
                  refine ⟨2611684018415373380875501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55715925726194632125344021 2611684018415373380875501)
                  ·
                    refine ⟨979381506905765017828313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611684018415373380875501 979381506905765017828313)
                    ·
                      rfl

theorem cell22_2861008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_2861008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861008 prefixEnd_2861008 := by exact prefixLift 2861008
  have htrace : WordTrace (prefixWord ++ tailWord_2861008) baseStart_2861008 baseEnd_2861008 := by
    simpa [prefixWord, tailWord_2861008, baseEnd_2861008] using wordTrace_append hprefix tailTrace_2861008
  have hstable : (prefixWord ++ tailWord_2861008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861008).length < 2 ^ (prefixWord ++ tailWord_2861008).sum := by decide
  have hdescent : baseEnd_2861008 < baseStart_2861008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861012 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2861012 : Nat := 118140960795 + 2861012 * 2 ^ 59
def prefixEnd_2861012 : Nat := 4983230072969 + 3 ^ 40 * 2861012 * 2
def baseEnd_2861012 : Nat := 979382876187510340728301

theorem tailTrace_2861012 : CollatzResearch.WordTrace tailWord_2861012 prefixEnd_2861012 979382876187510340728301 := by
  unfold tailWord_2861012
  simp only [CollatzResearch.WordTrace]
  refine ⟨52174840155524810396764645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69566453540699747195686193 52174840155524810396764645)
  ·
    refine ⟨9782782529160901949393371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52174840155524810396764645 9782782529160901949393371)
    ·
      refine ⟨14674173793741352924090057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9782782529160901949393371 14674173793741352924090057)
      ·
        refine ⟨11005630345306014693067543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14674173793741352924090057 11005630345306014693067543)
        ·
          refine ⟨16508445517959022039601315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005630345306014693067543 16508445517959022039601315)
          ·
            refine ⟨24762668276938533059401973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16508445517959022039601315 24762668276938533059401973)
            ·
              refine ⟨2321500150962987474318935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24762668276938533059401973 2321500150962987474318935)
              ·
                refine ⟨3482250226444481211478403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321500150962987474318935 3482250226444481211478403)
                ·
                  refine ⟨5223375339666721817217605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482250226444481211478403 5223375339666721817217605)
                  ·
                    refine ⟨979382876187510340728301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223375339666721817217605 979382876187510340728301)
                    ·
                      rfl

theorem cell22_2861012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2861012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861012 prefixEnd_2861012 := by exact prefixLift 2861012
  have htrace : WordTrace (prefixWord ++ tailWord_2861012) baseStart_2861012 baseEnd_2861012 := by
    simpa [prefixWord, tailWord_2861012, baseEnd_2861012] using wordTrace_append hprefix tailTrace_2861012
  have hstable : (prefixWord ++ tailWord_2861012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861012).length < 2 ^ (prefixWord ++ tailWord_2861012).sum := by decide
  have hdescent : baseEnd_2861012 < baseStart_2861012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861020 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2861020 : Nat := 118140960795 + 2861020 * 2 ^ 59
def prefixEnd_2861020 : Nat := 4983230072969 + 3 ^ 40 * 2861020 * 2
def baseEnd_2861020 : Nat := 979385614751000986528277

theorem tailTrace_2861020 : CollatzResearch.WordTrace tailWord_2861020 prefixEnd_2861020 979385614751000986528277 := by
  unfold tailWord_2861020
  simp only [CollatzResearch.WordTrace]
  refine ⟨52174986047510319079910257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69566648063347092106547009 52174986047510319079910257)
  ·
    refine ⟨39131239535632739309932693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52174986047510319079910257 39131239535632739309932693)
    ·
      refine ⟨1834276853232784655153095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39131239535632739309932693 1834276853232784655153095)
      ·
        refine ⟨2751415279849176982729643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834276853232784655153095 2751415279849176982729643)
        ·
          refine ⟨4127122919773765474094465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751415279849176982729643 4127122919773765474094465)
          ·
            refine ⟨3095342189830324105570849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4127122919773765474094465 3095342189830324105570849)
            ·
              refine ⟨2321506642372743079178137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3095342189830324105570849 2321506642372743079178137)
              ·
                refine ⟨1741129981779557309383603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321506642372743079178137 1741129981779557309383603)
                ·
                  refine ⟨2611694972669335964075405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741129981779557309383603 2611694972669335964075405)
                  ·
                    refine ⟨979385614751000986528277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611694972669335964075405 979385614751000986528277)
                    ·
                      rfl

theorem cell22_2861020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2861020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861020 prefixEnd_2861020 := by exact prefixLift 2861020
  have htrace : WordTrace (prefixWord ++ tailWord_2861020) baseStart_2861020 baseEnd_2861020 := by
    simpa [prefixWord, tailWord_2861020, baseEnd_2861020] using wordTrace_append hprefix tailTrace_2861020
  have hstable : (prefixWord ++ tailWord_2861020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861020).length < 2 ^ (prefixWord ++ tailWord_2861020).sum := by decide
  have hdescent : baseEnd_2861020 < baseStart_2861020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861025 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2861025 : Nat := 118140960795 + 2861025 * 2 ^ 59
def prefixEnd_2861025 : Nat := 4983230072969 + 3 ^ 40 * 2861025 * 2
def baseEnd_2861025 : Nat := 979387326353182640153261

theorem tailTrace_2861025 : CollatzResearch.WordTrace tailWord_2861025 prefixEnd_2861025 979387326353182640153261 := by
  unfold tailWord_2861025
  simp only [CollatzResearch.WordTrace]
  refine ⟨104350154460002524013752529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69566769640001682675835019 104350154460002524013752529)
  ·
    refine ⟨78262615845001893010314397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104350154460002524013752529 78262615845001893010314397)
    ·
      refine ⟨29348480941875709878867899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78262615845001893010314397 29348480941875709878867899)
      ·
        refine ⟨44022721412813564818301849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29348480941875709878867899 44022721412813564818301849)
        ·
          refine ⟨33017041059610173613726387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44022721412813564818301849 33017041059610173613726387)
          ·
            refine ⟨49525561589415260420589581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33017041059610173613726387 49525561589415260420589581)
            ·
              refine ⟨18572085596030722657721093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49525561589415260420589581 18572085596030722657721093)
              ·
                refine ⟨3482266049255760498322705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18572085596030722657721093 3482266049255760498322705)
                ·
                  refine ⟨2611699536941820373742029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482266049255760498322705 2611699536941820373742029)
                  ·
                    refine ⟨979387326353182640153261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611699536941820373742029 979387326353182640153261)
                    ·
                      rfl

theorem cell22_2861025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2861025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861025 prefixEnd_2861025 := by exact prefixLift 2861025
  have htrace : WordTrace (prefixWord ++ tailWord_2861025) baseStart_2861025 baseEnd_2861025 := by
    simpa [prefixWord, tailWord_2861025, baseEnd_2861025] using wordTrace_append hprefix tailTrace_2861025
  have hstable : (prefixWord ++ tailWord_2861025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861025).length < 2 ^ (prefixWord ++ tailWord_2861025).sum := by decide
  have hdescent : baseEnd_2861025 < baseStart_2861025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861027 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 4]
def baseStart_2861027 : Nat := 118140960795 + 2861027 * 2 ^ 59
def prefixEnd_2861027 : Nat := 4983230072969 + 3 ^ 40 * 2861027 * 2
def baseEnd_2861027 : Nat := 326462670331351767201085

theorem tailTrace_2861027 : CollatzResearch.WordTrace tailWord_2861027 prefixEnd_2861027 326462670331351767201085 := by
  unfold tailWord_2861027
  simp only [CollatzResearch.WordTrace]
  refine ⟨104350227405995278355325335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69566818270663518903550223 104350227405995278355325335)
  ·
    refine ⟨156525341108992917532988003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104350227405995278355325335 156525341108992917532988003)
    ·
      refine ⟨234788011663489376299482005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156525341108992917532988003 234788011663489376299482005)
      ·
        refine ⟨11005688046726064514038219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234788011663489376299482005 11005688046726064514038219)
        ·
          refine ⟨16508532070089096771057329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005688046726064514038219 16508532070089096771057329)
          ·
            refine ⟨12381399052566822578292997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16508532070089096771057329 12381399052566822578292997)
            ·
              refine ⟨2321512322356279233429937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12381399052566822578292997 2321512322356279233429937)
              ·
                refine ⟨1741134241767209425072453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321512322356279233429937 1741134241767209425072453)
                ·
                  refine ⟨326462670331351767201085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741134241767209425072453 326462670331351767201085)
                  ·
                    rfl

theorem cell22_2861027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 4].length) (baseStart_2861027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861027 prefixEnd_2861027 := by exact prefixLift 2861027
  have htrace : WordTrace (prefixWord ++ tailWord_2861027) baseStart_2861027 baseEnd_2861027 := by
    simpa [prefixWord, tailWord_2861027, baseEnd_2861027] using wordTrace_append hprefix tailTrace_2861027
  have hstable : (prefixWord ++ tailWord_2861027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861027).length < 2 ^ (prefixWord ++ tailWord_2861027).sum := by decide
  have hdescent : baseEnd_2861027 < baseStart_2861027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861070 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_2861070 : Nat := 118140960795 + 2861070 * 2 ^ 59
def prefixEnd_2861070 : Nat := 4983230072969 + 3 ^ 40 * 2861070 * 2
def baseEnd_2861070 : Nat := 979402730772817522778123

theorem tailTrace_2861070 : CollatzResearch.WordTrace tailWord_2861070 prefixEnd_2861070 979402730772817522778123 := by
  unfold tailWord_2861070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043974468104937087392583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69567863829892997799427109 13043974468104937087392583)
  ·
    refine ⟨19565961702157405631088875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13043974468104937087392583 19565961702157405631088875)
    ·
      refine ⟨29348942553236108446633313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19565961702157405631088875 29348942553236108446633313)
      ·
        refine ⟨22011706914927081334974985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29348942553236108446633313 22011706914927081334974985)
        ·
          refine ⟨16508780186195311001231239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22011706914927081334974985 16508780186195311001231239)
          ·
            refine ⟨24763170279292966501846859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16508780186195311001231239 24763170279292966501846859)
            ·
              refine ⟨37144755418939449752770289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24763170279292966501846859 37144755418939449752770289)
              ·
                refine ⟨27858566564204587314577717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37144755418939449752770289 27858566564204587314577717)
                ·
                  refine ⟨2611740615394180060741661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27858566564204587314577717 2611740615394180060741661)
                  ·
                    refine ⟨979402730772817522778123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611740615394180060741661 979402730772817522778123)
                    ·
                      rfl

theorem cell22_2861070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_2861070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861070 prefixEnd_2861070 := by exact prefixLift 2861070
  have htrace : WordTrace (prefixWord ++ tailWord_2861070) baseStart_2861070 baseEnd_2861070 := by
    simpa [prefixWord, tailWord_2861070, baseEnd_2861070] using wordTrace_append hprefix tailTrace_2861070
  have hstable : (prefixWord ++ tailWord_2861070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861070).length < 2 ^ (prefixWord ++ tailWord_2861070).sum := by decide
  have hdescent : baseEnd_2861070 < baseStart_2861070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861083 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 5]
def baseStart_2861083 : Nat := 118140960795 + 2861083 * 2 ^ 59
def prefixEnd_2861083 : Nat := 4983230072969 + 3 ^ 40 * 2861083 * 2
def baseEnd_2861083 : Nat := 326469060312829940734361

theorem tailTrace_2861083 : CollatzResearch.WordTrace tailWord_2861083 prefixEnd_2861083 326469060312829940734361 := by
  unfold tailWord_2861083
  simp only [CollatzResearch.WordTrace]
  refine ⟨104352269893792399919363903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69568179929194933279575935 104352269893792399919363903)
  ·
    refine ⟨156528404840688599879045855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104352269893792399919363903 156528404840688599879045855)
    ·
      refine ⟨234792607261032899818568783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156528404840688599879045855 234792607261032899818568783)
      ·
        refine ⟨352188910891549349727853175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234792607261032899818568783 352188910891549349727853175)
        ·
          refine ⟨528283366337324024591779763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352188910891549349727853175 528283366337324024591779763)
          ·
            refine ⟨792425049505986036887669645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528283366337324024591779763 792425049505986036887669645)
            ·
              refine ⟨297159393564744763832876117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 792425049505986036887669645 297159393564744763832876117)
              ·
                refine ⟨3482336643336852701166517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 297159393564744763832876117 3482336643336852701166517)
                ·
                  refine ⟨326469060312829940734361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482336643336852701166517 326469060312829940734361)
                  ·
                    rfl

theorem cell22_2861083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 5].length) (baseStart_2861083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861083 prefixEnd_2861083 := by exact prefixLift 2861083
  have htrace : WordTrace (prefixWord ++ tailWord_2861083) baseStart_2861083 baseEnd_2861083 := by
    simpa [prefixWord, tailWord_2861083, baseEnd_2861083] using wordTrace_append hprefix tailTrace_2861083
  have hstable : (prefixWord ++ tailWord_2861083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861083).length < 2 ^ (prefixWord ++ tailWord_2861083).sum := by decide
  have hdescent : baseEnd_2861083 < baseStart_2861083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861087 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 1, 3]
def baseStart_2861087 : Nat := 118140960795 + 2861087 * 2 ^ 59
def prefixEnd_2861087 : Nat := 4983230072969 + 3 ^ 40 * 2861087 * 2
def baseEnd_2861087 : Nat := 979408550220235145103071

theorem tailTrace_2861087 : CollatzResearch.WordTrace tailWord_2861087 prefixEnd_2861087 979408550220235145103071 := by
  unfold tailWord_2861087
  simp only [CollatzResearch.WordTrace]
  refine ⟨104352415785777908602509515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69568277190518605735006343 104352415785777908602509515)
  ·
    refine ⟨156528623678666862903764273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104352415785777908602509515 156528623678666862903764273)
    ·
      refine ⟨117396467759000147177823205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156528623678666862903764273 117396467759000147177823205)
      ·
        refine ⟨22011837704812527595841851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117396467759000147177823205 22011837704812527595841851)
        ·
          refine ⟨33017756557218791393762777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22011837704812527595841851 33017756557218791393762777)
          ·
            refine ⟨24763317417914093545322083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33017756557218791393762777 24763317417914093545322083)
            ·
              refine ⟨37144976126871140317983125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24763317417914093545322083 37144976126871140317983125)
              ·
                refine ⟨1741170755947084702405459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37144976126871140317983125 1741170755947084702405459)
                ·
                  refine ⟨2611756133920627053608189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741170755947084702405459 2611756133920627053608189)
                  ·
                    refine ⟨979408550220235145103071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611756133920627053608189 979408550220235145103071)
                    ·
                      rfl

theorem cell22_2861087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_2861087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861087 prefixEnd_2861087 := by exact prefixLift 2861087
  have htrace : WordTrace (prefixWord ++ tailWord_2861087) baseStart_2861087 baseEnd_2861087 := by
    simpa [prefixWord, tailWord_2861087, baseEnd_2861087] using wordTrace_append hprefix tailTrace_2861087
  have hstable : (prefixWord ++ tailWord_2861087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861087).length < 2 ^ (prefixWord ++ tailWord_2861087).sum := by decide
  have hdescent : baseEnd_2861087 < baseStart_2861087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861121 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2861121 : Nat := 118140960795 + 2861121 * 2 ^ 59
def prefixEnd_2861121 : Nat := 4983230072969 + 3 ^ 40 * 2861121 * 2
def baseEnd_2861121 : Nat := 979420189115070389752967

theorem tailTrace_2861121 : CollatzResearch.WordTrace tailWord_2861121 prefixEnd_2861121 979420189115070389752967 := by
  unfold tailWord_2861121
  simp only [CollatzResearch.WordTrace]
  refine ⟨104353655867654732409247217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69569103911769821606164811 104353655867654732409247217)
  ·
    refine ⟨78265241900741049306935413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104353655867654732409247217 78265241900741049306935413)
    ·
      refine ⟨7337366428194473372525195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78265241900741049306935413 7337366428194473372525195)
      ·
        refine ⟨11006049642291710058787793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337366428194473372525195 11006049642291710058787793)
        ·
          refine ⟨8254537231718782544090845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006049642291710058787793 8254537231718782544090845)
          ·
            refine ⟨3095451461894543454034067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8254537231718782544090845 3095451461894543454034067)
            ·
              refine ⟨4643177192841815181051101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095451461894543454034067 4643177192841815181051101)
              ·
                refine ⟨1741191447315680692894163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4643177192841815181051101 1741191447315680692894163)
                ·
                  refine ⟨2611787170973521039341245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741191447315680692894163 2611787170973521039341245)
                  ·
                    refine ⟨979420189115070389752967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611787170973521039341245 979420189115070389752967)
                    ·
                      rfl

theorem cell22_2861121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2861121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861121 prefixEnd_2861121 := by exact prefixLift 2861121
  have htrace : WordTrace (prefixWord ++ tailWord_2861121) baseStart_2861121 baseEnd_2861121 := by
    simpa [prefixWord, tailWord_2861121, baseEnd_2861121] using wordTrace_append hprefix tailTrace_2861121
  have hstable : (prefixWord ++ tailWord_2861121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861121).length < 2 ^ (prefixWord ++ tailWord_2861121).sum := by decide
  have hdescent : baseEnd_2861121 < baseStart_2861121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861175 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_2861175 : Nat := 118140960795 + 2861175 * 2 ^ 59
def prefixEnd_2861175 : Nat := 4983230072969 + 3 ^ 40 * 2861175 * 2
def baseEnd_2861175 : Nat := 979438674418632248902801

theorem tailTrace_2861175 : CollatzResearch.WordTrace tailWord_2861175 prefixEnd_2861175 979438674418632248902801 := by
  unfold tailWord_2861175
  simp only [CollatzResearch.WordTrace]
  refine ⟨104355625409459099631712979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69570416939639399754475319 104355625409459099631712979)
  ·
    refine ⟨156533438114188649447569469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104355625409459099631712979 156533438114188649447569469)
    ·
      refine ⟨58700039292820743542838551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156533438114188649447569469 58700039292820743542838551)
      ·
        refine ⟨88050058939231115314257827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58700039292820743542838551 88050058939231115314257827)
        ·
          refine ⟨132075088408846672971386741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88050058939231115314257827 132075088408846672971386741)
          ·
            refine ⟨12382039538329375591067507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132075088408846672971386741 12382039538329375591067507)
            ·
              refine ⟨18573059307494063386601261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12382039538329375591067507 18573059307494063386601261)
              ·
                refine ⟨6964897240310273769975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18573059307494063386601261 6964897240310273769975473)
                ·
                  refine ⟨5223672930232705327481605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6964897240310273769975473 5223672930232705327481605)
                  ·
                    refine ⟨979438674418632248902801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223672930232705327481605 979438674418632248902801)
                    ·
                      rfl

theorem cell22_2861175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_2861175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861175 prefixEnd_2861175 := by exact prefixLift 2861175
  have htrace : WordTrace (prefixWord ++ tailWord_2861175) baseStart_2861175 baseEnd_2861175 := by
    simpa [prefixWord, tailWord_2861175, baseEnd_2861175] using wordTrace_append hprefix tailTrace_2861175
  have hstable : (prefixWord ++ tailWord_2861175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861175).length < 2 ^ (prefixWord ++ tailWord_2861175).sum := by decide
  have hdescent : baseEnd_2861175 < baseStart_2861175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861192 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2861192 : Nat := 118140960795 + 2861192 * 2 ^ 59
def prefixEnd_2861192 : Nat := 4983230072969 + 3 ^ 40 * 2861192 * 2
def baseEnd_2861192 : Nat := 979444493866049871227749

theorem tailTrace_2861192 : CollatzResearch.WordTrace tailWord_2861192 prefixEnd_2861192 979444493866049871227749 := by
  unfold tailWord_2861192
  simp only [CollatzResearch.WordTrace]
  refine ⟨52178122725198755767540915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69570830300265007690054553 52178122725198755767540915)
  ·
    refine ⟨78267184087798133651311373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52178122725198755767540915 78267184087798133651311373)
    ·
      refine ⟨29350194032924300119241765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78267184087798133651311373 29350194032924300119241765)
      ·
        refine ⟨5503161381173306272357831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29350194032924300119241765 5503161381173306272357831)
        ·
          refine ⟨8254742071759959408536747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503161381173306272357831 8254742071759959408536747)
          ·
            refine ⟨12382113107639939112805121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254742071759959408536747 12382113107639939112805121)
            ·
              refine ⟨9286584830729954334603841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382113107639939112805121 9286584830729954334603841)
              ·
                refine ⟨6964938623047465750952881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286584830729954334603841 6964938623047465750952881)
                ·
                  refine ⟨5223703967285599313214661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6964938623047465750952881 5223703967285599313214661)
                  ·
                    refine ⟨979444493866049871227749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223703967285599313214661 979444493866049871227749)
                    ·
                      rfl

theorem cell22_2861192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2861192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861192 prefixEnd_2861192 := by exact prefixLift 2861192
  have htrace : WordTrace (prefixWord ++ tailWord_2861192) baseStart_2861192 baseEnd_2861192 := by
    simpa [prefixWord, tailWord_2861192, baseEnd_2861192] using wordTrace_append hprefix tailTrace_2861192
  have hstable : (prefixWord ++ tailWord_2861192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861192).length < 2 ^ (prefixWord ++ tailWord_2861192).sum := by decide
  have hdescent : baseEnd_2861192 < baseStart_2861192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861194 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2861194 : Nat := 118140960795 + 2861194 * 2 ^ 59
def prefixEnd_2861194 : Nat := 4983230072969 + 3 ^ 40 * 2861194 * 2
def baseEnd_2861194 : Nat := 979445178506922532677743

theorem tailTrace_2861194 : CollatzResearch.WordTrace tailWord_2861194 prefixEnd_2861194 979445178506922532677743 := by
  unfold tailWord_2861194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089079599097566469163659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69570878930926843917769757 26089079599097566469163659)
  ·
    refine ⟨39133619398646349703745489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26089079599097566469163659 39133619398646349703745489)
    ·
      refine ⟨29350214548984762277809117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39133619398646349703745489 29350214548984762277809117)
      ·
        refine ⟨11006330455869285854178419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29350214548984762277809117 11006330455869285854178419)
        ·
          refine ⟨16509495683803928781267629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11006330455869285854178419 16509495683803928781267629)
          ·
            refine ⟨6191060881426473292975361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16509495683803928781267629 6191060881426473292975361)
            ·
              refine ⟨4643295661069854969731521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6191060881426473292975361 4643295661069854969731521)
              ·
                refine ⟨3482471745802391227298641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643295661069854969731521 3482471745802391227298641)
                ·
                  refine ⟨2611853809351793420473981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482471745802391227298641 2611853809351793420473981)
                  ·
                    refine ⟨979445178506922532677743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611853809351793420473981 979445178506922532677743)
                    ·
                      rfl

theorem cell22_2861194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2861194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861194 prefixEnd_2861194 := by exact prefixLift 2861194
  have htrace : WordTrace (prefixWord ++ tailWord_2861194) baseStart_2861194 baseEnd_2861194 := by
    simpa [prefixWord, tailWord_2861194, baseEnd_2861194] using wordTrace_append hprefix tailTrace_2861194
  have hstable : (prefixWord ++ tailWord_2861194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861194).length < 2 ^ (prefixWord ++ tailWord_2861194).sum := by decide
  have hdescent : baseEnd_2861194 < baseStart_2861194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861207 : List Nat := [1, 1, 3, 3, 4, 2, 1, 7]
def baseStart_2861207 : Nat := 118140960795 + 2861207 * 2 ^ 59
def prefixEnd_2861207 : Nat := 4983230072969 + 3 ^ 40 * 2861207 * 2
def baseEnd_2861207 : Nat := 108827736519177203566967

theorem tailTrace_2861207 : CollatzResearch.WordTrace tailWord_2861207 prefixEnd_2861207 108827736519177203566967 := by
  unfold tailWord_2861207
  simp only [CollatzResearch.WordTrace]
  refine ⟨104356792545343169096877875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69571195030228779397918583 104356792545343169096877875)
  ·
    refine ⟨156535188818014753645316813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104356792545343169096877875 156535188818014753645316813)
    ·
      refine ⟨58700695806755532616993805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156535188818014753645316813 58700695806755532616993805)
      ·
        refine ⟨22012760927533324731372677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58700695806755532616993805 22012760927533324731372677)
        ·
          refine ⟨4127392673912498387132377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22012760927533324731372677 4127392673912498387132377)
          ·
            refine ⟨3095544505434373790349283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4127392673912498387132377 3095544505434373790349283)
            ·
              refine ⟨4643316758151560685523925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095544505434373790349283 4643316758151560685523925)
              ·
                refine ⟨108827736519177203566967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4643316758151560685523925 108827736519177203566967)
                ·
                  rfl

theorem cell22_2861207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 7].length) (baseStart_2861207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861207 prefixEnd_2861207 := by exact prefixLift 2861207
  have htrace : WordTrace (prefixWord ++ tailWord_2861207) baseStart_2861207 baseEnd_2861207 := by
    simpa [prefixWord, tailWord_2861207, baseEnd_2861207] using wordTrace_append hprefix tailTrace_2861207
  have hstable : (prefixWord ++ tailWord_2861207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861207).length < 2 ^ (prefixWord ++ tailWord_2861207).sum := by decide
  have hdescent : baseEnd_2861207 < baseStart_2861207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861226 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2861226 : Nat := 118140960795 + 2861226 * 2 ^ 59
def prefixEnd_2861226 : Nat := 4983230072969 + 3 ^ 40 * 2861226 * 2
def baseEnd_2861226 : Nat := 979456132760885115877645

theorem tailTrace_2861226 : CollatzResearch.WordTrace tailWord_2861226 prefixEnd_2861226 979456132760885115877645 := by
  unfold tailWord_2861226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089371383068583835454883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69571657021516223561213021 26089371383068583835454883)
  ·
    refine ⟨39134057074602875753182325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26089371383068583835454883 39134057074602875753182325)
    ·
      refine ⟨3668817850744019601860843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39134057074602875753182325 3668817850744019601860843)
      ·
        refine ⟨5503226776116029402791265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3668817850744019601860843 5503226776116029402791265)
        ·
          refine ⟨4127420082087022052093449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5503226776116029402791265 4127420082087022052093449)
          ·
            refine ⟨3095565061565266539070087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4127420082087022052093449 3095565061565266539070087)
            ·
              refine ⟨4643347592347899808605131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095565061565266539070087 4643347592347899808605131)
              ·
                refine ⟨6965021388521849712907697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643347592347899808605131 6965021388521849712907697)
                ·
                  refine ⟨5223766041391387284680773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6965021388521849712907697 5223766041391387284680773)
                  ·
                    refine ⟨979456132760885115877645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223766041391387284680773 979456132760885115877645)
                    ·
                      rfl

theorem cell22_2861226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2861226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861226 prefixEnd_2861226 := by exact prefixLift 2861226
  have htrace : WordTrace (prefixWord ++ tailWord_2861226) baseStart_2861226 baseEnd_2861226 := by
    simpa [prefixWord, tailWord_2861226, baseEnd_2861226] using wordTrace_append hprefix tailTrace_2861226
  have hstable : (prefixWord ++ tailWord_2861226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861226).length < 2 ^ (prefixWord ++ tailWord_2861226).sum := by decide
  have hdescent : baseEnd_2861226 < baseStart_2861226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861239 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 1, 3]
def baseStart_2861239 : Nat := 118140960795 + 2861239 * 2 ^ 59
def prefixEnd_2861239 : Nat := 4983230072969 + 3 ^ 40 * 2861239 * 2
def baseEnd_2861239 : Nat := 979460582926557415302605

theorem tailTrace_2861239 : CollatzResearch.WordTrace tailWord_2861239 prefixEnd_2861239 979460582926557415302605 := by
  unfold tailWord_2861239
  simp only [CollatzResearch.WordTrace]
  refine ⟨104357959681227238562042771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69571973120818159041361847 104357959681227238562042771)
  ·
    refine ⟨156536939521840857843064157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104357959681227238562042771 156536939521840857843064157)
    ·
      refine ⟨58701352320690321691149059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156536939521840857843064157 58701352320690321691149059)
      ·
        refine ⟨88052028481035482536723589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58701352320690321691149059 88052028481035482536723589)
        ·
          refine ⟨16509755340194152975635673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88052028481035482536723589 16509755340194152975635673)
          ·
            refine ⟨12382316505145614731726755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16509755340194152975635673 12382316505145614731726755)
            ·
              refine ⟨18573474757718422097590133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12382316505145614731726755 18573474757718422097590133)
              ·
                refine ⟨1741263258536102071649075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18573474757718422097590133 1741263258536102071649075)
                ·
                  refine ⟨2611894887804153107473613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741263258536102071649075 2611894887804153107473613)
                  ·
                    refine ⟨979460582926557415302605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611894887804153107473613 979460582926557415302605)
                    ·
                      rfl

theorem cell22_2861239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_2861239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861239 prefixEnd_2861239 := by exact prefixLift 2861239
  have htrace : WordTrace (prefixWord ++ tailWord_2861239) baseStart_2861239 baseEnd_2861239 := by
    simpa [prefixWord, tailWord_2861239, baseEnd_2861239] using wordTrace_append hprefix tailTrace_2861239
  have hstable : (prefixWord ++ tailWord_2861239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861239).length < 2 ^ (prefixWord ++ tailWord_2861239).sum := by decide
  have hdescent : baseEnd_2861239 < baseStart_2861239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861252 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2861252 : Nat := 118140960795 + 2861252 * 2 ^ 59
def prefixEnd_2861252 : Nat := 4983230072969 + 3 ^ 40 * 2861252 * 2
def baseEnd_2861252 : Nat := 326488344364076571575855

theorem tailTrace_2861252 : CollatzResearch.WordTrace tailWord_2861252 prefixEnd_2861252 326488344364076571575855 := by
  unfold tailWord_2861252
  simp only [CollatzResearch.WordTrace]
  refine ⟨52179216915090070891133005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69572289220120094521510673 52179216915090070891133005)
  ·
    refine ⟨19567206343158776584174877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52179216915090070891133005 19567206343158776584174877)
    ·
      refine ⟨7337702378684541219065579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19567206343158776584174877 7337702378684541219065579)
      ·
        refine ⟨11006553568026811828598369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337702378684541219065579 11006553568026811828598369)
        ·
          refine ⟨8254915176020108871448777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006553568026811828598369 8254915176020108871448777)
          ·
            refine ⟨6191186382015081653586583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8254915176020108871448777 6191186382015081653586583)
            ·
              refine ⟨9286779573022622480379875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191186382015081653586583 9286779573022622480379875)
              ·
                refine ⟨13930169359533933720569813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9286779573022622480379875 13930169359533933720569813)
                ·
                  refine ⟨326488344364076571575855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13930169359533933720569813 326488344364076571575855)
                  ·
                    rfl

theorem cell22_2861252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2861252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861252 prefixEnd_2861252 := by exact prefixLift 2861252
  have htrace : WordTrace (prefixWord ++ tailWord_2861252) baseStart_2861252 baseEnd_2861252 := by
    simpa [prefixWord, tailWord_2861252, baseEnd_2861252] using wordTrace_append hprefix tailTrace_2861252
  have hstable : (prefixWord ++ tailWord_2861252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861252).length < 2 ^ (prefixWord ++ tailWord_2861252).sum := by decide
  have hdescent : baseEnd_2861252 < baseStart_2861252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861265 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2861265 : Nat := 118140960795 + 2861265 * 2 ^ 59
def prefixEnd_2861265 : Nat := 4983230072969 + 3 ^ 40 * 2861265 * 2
def baseEnd_2861265 : Nat := 979469483257902014152525

theorem tailTrace_2861265 : CollatzResearch.WordTrace tailWord_2861265 prefixEnd_2861265 979469483257902014152525 := by
  unfold tailWord_2861265
  simp only [CollatzResearch.WordTrace]
  refine ⟨104358907979133045002489249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69572605319422030001659499 104358907979133045002489249)
  ·
    refine ⟨78269180984349783751866937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104358907979133045002489249 78269180984349783751866937)
    ·
      refine ⟨58701885738262337813900203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78269180984349783751866937 58701885738262337813900203)
      ·
        refine ⟨88052828607393506720850305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58701885738262337813900203 88052828607393506720850305)
        ·
          refine ⟨66039621455545130040637729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88052828607393506720850305 66039621455545130040637729)
          ·
            refine ⟨49529716091658847530478297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66039621455545130040637729 49529716091658847530478297)
            ·
              refine ⟨37147287068744135647858723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49529716091658847530478297 37147287068744135647858723)
              ·
                refine ⟨55720930603116203471788085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37147287068744135647858723 55720930603116203471788085)
                ·
                  refine ⟨5223837244042144075480133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55720930603116203471788085 5223837244042144075480133)
                  ·
                    refine ⟨979469483257902014152525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223837244042144075480133 979469483257902014152525)
                    ·
                      rfl

theorem cell22_2861265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2861265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861265 prefixEnd_2861265 := by exact prefixLift 2861265
  have htrace : WordTrace (prefixWord ++ tailWord_2861265) baseStart_2861265 baseEnd_2861265 := by
    simpa [prefixWord, tailWord_2861265, baseEnd_2861265] using wordTrace_append hprefix tailTrace_2861265
  have hstable : (prefixWord ++ tailWord_2861265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861265).length < 2 ^ (prefixWord ++ tailWord_2861265).sum := by decide
  have hdescent : baseEnd_2861265 < baseStart_2861265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861280 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_2861280 : Nat := 118140960795 + 2861280 * 2 ^ 59
def prefixEnd_2861280 : Nat := 4983230072969 + 3 ^ 40 * 2861280 * 2
def baseEnd_2861280 : Nat := 326491539354815658342493

theorem tailTrace_2861280 : CollatzResearch.WordTrace tailWord_2861280 prefixEnd_2861280 326491539354815658342493 := by
  unfold tailWord_2861280
  simp only [CollatzResearch.WordTrace]
  refine ⟨52179727537039351282142647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69572970049385801709523529 52179727537039351282142647)
  ·
    refine ⟨78269591305559026923213971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52179727537039351282142647 78269591305559026923213971)
    ·
      refine ⟨117404386958338540384820957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78269591305559026923213971 117404386958338540384820957)
      ·
        refine ⟨44026645109376952644307859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117404386958338540384820957 44026645109376952644307859)
        ·
          refine ⟨66039967664065428966461789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44026645109376952644307859 66039967664065428966461789)
          ·
            refine ⟨24764987874024535862423171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66039967664065428966461789 24764987874024535862423171)
            ·
              refine ⟨37147481811036803793634757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24764987874024535862423171 37147481811036803793634757)
              ·
                refine ⟨6965152839569400711306517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37147481811036803793634757 6965152839569400711306517)
                ·
                  refine ⟨326491539354815658342493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6965152839569400711306517 326491539354815658342493)
                  ·
                    rfl

theorem cell22_2861280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_2861280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861280 prefixEnd_2861280 := by exact prefixLift 2861280
  have htrace : WordTrace (prefixWord ++ tailWord_2861280) baseStart_2861280 baseEnd_2861280 := by
    simpa [prefixWord, tailWord_2861280, baseEnd_2861280] using wordTrace_append hprefix tailTrace_2861280
  have hstable : (prefixWord ++ tailWord_2861280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861280).length < 2 ^ (prefixWord ++ tailWord_2861280).sum := by decide
  have hdescent : baseEnd_2861280 < baseStart_2861280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861312 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_2861312 : Nat := 118140960795 + 2861312 * 2 ^ 59
def prefixEnd_2861312 : Nat := 4983230072969 + 3 ^ 40 * 2861312 * 2
def baseEnd_2861312 : Nat := 979485572318409558227381

theorem tailTrace_2861312 : CollatzResearch.WordTrace tailWord_2861312 prefixEnd_2861312 979485572318409558227381 := by
  unfold tailWord_2861312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52180311104981386014725095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69573748139975181352966793 52180311104981386014725095)
  ·
    refine ⟨78270466657472079022087643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52180311104981386014725095 78270466657472079022087643)
    ·
      refine ⟨117405699986208118533131465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78270466657472079022087643 117405699986208118533131465)
      ·
        refine ⟨88054274989656088899848599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117405699986208118533131465 88054274989656088899848599)
        ·
          refine ⟨132081412484484133349772899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88054274989656088899848599 132081412484484133349772899)
          ·
            refine ⟨198122118726726200024659349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132081412484484133349772899 198122118726726200024659349)
            ·
              refine ⟨9286974315315290626155907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198122118726726200024659349 9286974315315290626155907)
              ·
                refine ⟨13930461472972935939233861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9286974315315290626155907 13930461472972935939233861)
                ·
                  refine ⟨2611961526182425488606349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13930461472972935939233861 2611961526182425488606349)
                  ·
                    refine ⟨979485572318409558227381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611961526182425488606349 979485572318409558227381)
                    ·
                      rfl

theorem cell22_2861312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_2861312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861312 prefixEnd_2861312 := by exact prefixLift 2861312
  have htrace : WordTrace (prefixWord ++ tailWord_2861312) baseStart_2861312 baseEnd_2861312 := by
    simpa [prefixWord, tailWord_2861312, baseEnd_2861312] using wordTrace_append hprefix tailTrace_2861312
  have hstable : (prefixWord ++ tailWord_2861312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861312).length < 2 ^ (prefixWord ++ tailWord_2861312).sum := by decide
  have hdescent : baseEnd_2861312 < baseStart_2861312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861314 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2861314 : Nat := 118140960795 + 2861314 * 2 ^ 59
def prefixEnd_2861314 : Nat := 4983230072969 + 3 ^ 40 * 2861314 * 2
def baseEnd_2861314 : Nat := 326495418986427406559125

theorem tailTrace_2861314 : CollatzResearch.WordTrace tailWord_2861314 prefixEnd_2861314 326495418986427406559125 := by
  unfold tailWord_2861314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26090173788988881592755749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69573796770637017580681997 26090173788988881592755749)
  ·
    refine ⟨4891907585435415298641703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26090173788988881592755749 4891907585435415298641703)
    ·
      refine ⟨7337861378153122947962555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891907585435415298641703 7337861378153122947962555)
      ·
        refine ⟨11006792067229684421943833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337861378153122947962555 11006792067229684421943833)
        ·
          refine ⟨8255094050422263316457875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006792067229684421943833 8255094050422263316457875)
          ·
            refine ⟨12382641075633394974686813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255094050422263316457875 12382641075633394974686813)
            ·
              refine ⟨4643490403362523115507555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12382641075633394974686813 4643490403362523115507555)
              ·
                refine ⟨6965235605043784673261333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643490403362523115507555 6965235605043784673261333)
                ·
                  refine ⟨326495418986427406559125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6965235605043784673261333 326495418986427406559125)
                  ·
                    rfl

theorem cell22_2861314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2861314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861314 prefixEnd_2861314 := by exact prefixLift 2861314
  have htrace : WordTrace (prefixWord ++ tailWord_2861314) baseStart_2861314 baseEnd_2861314 := by
    simpa [prefixWord, tailWord_2861314, baseEnd_2861314] using wordTrace_append hprefix tailTrace_2861314
  have hstable : (prefixWord ++ tailWord_2861314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861314).length < 2 ^ (prefixWord ++ tailWord_2861314).sum := by decide
  have hdescent : baseEnd_2861314 < baseStart_2861314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861329 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_2861329 : Nat := 118140960795 + 2861329 * 2 ^ 59
def prefixEnd_2861329 : Nat := 4983230072969 + 3 ^ 40 * 2861329 * 2
def baseEnd_2861329 : Nat := 979491391765827180552329

theorem tailTrace_2861329 : CollatzResearch.WordTrace tailWord_2861329 prefixEnd_2861329 979491391765827180552329 := by
  unfold tailWord_2861329
  simp only [CollatzResearch.WordTrace]
  refine ⟨104361242250901183932819041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69574161500600789288546027 104361242250901183932819041)
  ·
    refine ⟨78270931688175887949614281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104361242250901183932819041 78270931688175887949614281)
    ·
      refine ⟨58703198766131915962210711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78270931688175887949614281 58703198766131915962210711)
      ·
        refine ⟨88054798149197873943316067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58703198766131915962210711 88054798149197873943316067)
        ·
          refine ⟨132082197223796810914974101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88054798149197873943316067 132082197223796810914974101)
          ·
            refine ⟨6191352994865475511639411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132082197223796810914974101 6191352994865475511639411)
            ·
              refine ⟨9287029492298213267459117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191352994865475511639411 9287029492298213267459117)
              ·
                refine ⟨3482636059611829975297169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9287029492298213267459117 3482636059611829975297169)
                ·
                  refine ⟨2611977044708872481472877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482636059611829975297169 2611977044708872481472877)
                  ·
                    refine ⟨979491391765827180552329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2611977044708872481472877 979491391765827180552329)
                    ·
                      rfl

theorem cell22_2861329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_2861329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861329 prefixEnd_2861329 := by exact prefixLift 2861329
  have htrace : WordTrace (prefixWord ++ tailWord_2861329) baseStart_2861329 baseEnd_2861329 := by
    simpa [prefixWord, tailWord_2861329, baseEnd_2861329] using wordTrace_append hprefix tailTrace_2861329
  have hstable : (prefixWord ++ tailWord_2861329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861329).length < 2 ^ (prefixWord ++ tailWord_2861329).sum := by decide
  have hdescent : baseEnd_2861329 < baseStart_2861329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861344 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_2861344 : Nat := 118140960795 + 2861344 * 2 ^ 59
def prefixEnd_2861344 : Nat := 4983230072969 + 3 ^ 40 * 2861344 * 2
def baseEnd_2861344 : Nat := 979496526572372141427283

theorem tailTrace_2861344 : CollatzResearch.WordTrace tailWord_2861344 prefixEnd_2861344 979496526572372141427283 := by
  unfold tailWord_2861344
  simp only [CollatzResearch.WordTrace]
  refine ⟨52180894672923420747307543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69574526230564560996410057 52180894672923420747307543)
  ·
    refine ⟨78271342009385131120961315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52180894672923420747307543 78271342009385131120961315)
    ·
      refine ⟨117407013014077696681441973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78271342009385131120961315 117407013014077696681441973)
      ·
        refine ⟨11006907470069784063885185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117407013014077696681441973 11006907470069784063885185)
        ·
          refine ⟨8255180602552338047913889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006907470069784063885185 8255180602552338047913889)
          ·
            refine ⟨6191385451914253535935417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8255180602552338047913889 6191385451914253535935417)
            ·
              refine ⟨4643539088935690151951563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6191385451914253535935417 4643539088935690151951563)
              ·
                refine ⟨6965308633403535227927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643539088935690151951563 6965308633403535227927345)
                ·
                  refine ⟨5223981475052651420945509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6965308633403535227927345 5223981475052651420945509)
                  ·
                    refine ⟨979496526572372141427283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223981475052651420945509 979496526572372141427283)
                    ·
                      rfl

theorem cell22_2861344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_2861344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861344 prefixEnd_2861344 := by exact prefixLift 2861344
  have htrace : WordTrace (prefixWord ++ tailWord_2861344) baseStart_2861344 baseEnd_2861344 := by
    simpa [prefixWord, tailWord_2861344, baseEnd_2861344] using wordTrace_append hprefix tailTrace_2861344
  have hstable : (prefixWord ++ tailWord_2861344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861344).length < 2 ^ (prefixWord ++ tailWord_2861344).sum := by decide
  have hdescent : baseEnd_2861344 < baseStart_2861344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861408 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 1, 3]
def baseStart_2861408 : Nat := 118140960795 + 2861408 * 2 ^ 59
def prefixEnd_2861408 : Nat := 4983230072969 + 3 ^ 40 * 2861408 * 2
def baseEnd_2861408 : Nat := 979518435080297307827087

theorem tailTrace_2861408 : CollatzResearch.WordTrace tailWord_2861408 prefixEnd_2861408 979518435080297307827087 := by
  unfold tailWord_2861408
  simp only [CollatzResearch.WordTrace]
  refine ⟨52182061808807490212472439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69576082411743320283296585 52182061808807490212472439)
  ·
    refine ⟨78273092713211235318708659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52182061808807490212472439 78273092713211235318708659)
    ·
      refine ⟨117409639069816852978062989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78273092713211235318708659 117409639069816852978062989)
      ·
        refine ⟨44028614651181319866773621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117409639069816852978062989 44028614651181319866773621)
        ·
          refine ⟨4127682623548248737510027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44028614651181319866773621 4127682623548248737510027)
          ·
            refine ⟨6191523935322373106265041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127682623548248737510027 6191523935322373106265041)
            ·
              refine ⟨4643642951491779829698781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6191523935322373106265041 4643642951491779829698781)
              ·
                refine ⟨1741366106809417436137043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4643642951491779829698781 1741366106809417436137043)
                ·
                  refine ⟨2612049160214126154205565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741366106809417436137043 2612049160214126154205565)
                  ·
                    refine ⟨979518435080297307827087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612049160214126154205565 979518435080297307827087)
                    ·
                      rfl

theorem cell22_2861408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_2861408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861408 prefixEnd_2861408 := by exact prefixLift 2861408
  have htrace : WordTrace (prefixWord ++ tailWord_2861408) baseStart_2861408 baseEnd_2861408 := by
    simpa [prefixWord, tailWord_2861408, baseEnd_2861408] using wordTrace_append hprefix tailTrace_2861408
  have hstable : (prefixWord ++ tailWord_2861408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861408).length < 2 ^ (prefixWord ++ tailWord_2861408).sum := by decide
  have hdescent : baseEnd_2861408 < baseStart_2861408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861466 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_2861466 : Nat := 118140960795 + 2861466 * 2 ^ 59
def prefixEnd_2861466 : Nat := 4983230072969 + 3 ^ 40 * 2861466 * 2
def baseEnd_2861466 : Nat := 326512763221868163292303

theorem tailTrace_2861466 : CollatzResearch.WordTrace tailWord_2861466 prefixEnd_2861466 326512763221868163292303 := by
  unfold tailWord_2861466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26091559762851214082639063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69577492700936570887037501 26091559762851214082639063)
  ·
    refine ⟨39137339644276821123958595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26091559762851214082639063 39137339644276821123958595)
    ·
      refine ⟨58706009466415231685937893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39137339644276821123958595 58706009466415231685937893)
      ·
        refine ⟨11007376774952855941113355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58706009466415231685937893 11007376774952855941113355)
        ·
          refine ⟨16511065162429283911670033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007376774952855941113355 16511065162429283911670033)
          ·
            refine ⟨12383298871821962933752525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16511065162429283911670033 12383298871821962933752525)
            ·
              refine ⟨4643737076933236100157197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12383298871821962933752525 4643737076933236100157197)
              ·
                refine ⟨1741401403849963537558949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4643737076933236100157197 1741401403849963537558949)
                ·
                  refine ⟨326512763221868163292303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741401403849963537558949 326512763221868163292303)
                  ·
                    rfl

theorem cell22_2861466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_2861466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861466 prefixEnd_2861466 := by exact prefixLift 2861466
  have htrace : WordTrace (prefixWord ++ tailWord_2861466) baseStart_2861466 baseEnd_2861466 := by
    simpa [prefixWord, tailWord_2861466, baseEnd_2861466] using wordTrace_append hprefix tailTrace_2861466
  have hstable : (prefixWord ++ tailWord_2861466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861466).length < 2 ^ (prefixWord ++ tailWord_2861466).sum := by decide
  have hdescent : baseEnd_2861466 < baseStart_2861466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861479 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2861479 : Nat := 118140960795 + 2861479 * 2 ^ 59
def prefixEnd_2861479 : Nat := 4983230072969 + 3 ^ 40 * 2861479 * 2
def baseEnd_2861479 : Nat := 979542739831276789301869

theorem tailTrace_2861479 : CollatzResearch.WordTrace tailWord_2861479 prefixEnd_2861479 979542739831276789301869 := by
  unfold tailWord_2861479
  simp only [CollatzResearch.WordTrace]
  refine ⟨104366713200357759550779491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69577808800238506367186327 104366713200357759550779491)
  ·
    refine ⟨156550069800536639326169237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104366713200357759550779491 156550069800536639326169237)
    ·
      refine ⟨7338284521900154968414183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156550069800536639326169237 7338284521900154968414183)
      ·
        refine ⟨11007426782850232452621275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7338284521900154968414183 11007426782850232452621275)
        ·
          refine ⟨16511140174275348678931913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007426782850232452621275 16511140174275348678931913)
          ·
            refine ⟨12383355130706511509198935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16511140174275348678931913 12383355130706511509198935)
            ·
              refine ⟨18575032696059767263798403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12383355130706511509198935 18575032696059767263798403)
              ·
                refine ⟨27862549044089650895697605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18575032696059767263798403 27862549044089650895697605)
                ·
                  refine ⟨5224227945766809542943301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27862549044089650895697605 5224227945766809542943301)
                  ·
                    refine ⟨979542739831276789301869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5224227945766809542943301 979542739831276789301869)
                    ·
                      rfl

theorem cell22_2861479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2861479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861479 prefixEnd_2861479 := by exact prefixLift 2861479
  have htrace : WordTrace (prefixWord ++ tailWord_2861479) baseStart_2861479 baseEnd_2861479 := by
    simpa [prefixWord, tailWord_2861479, baseEnd_2861479] using wordTrace_append hprefix tailTrace_2861479
  have hstable : (prefixWord ++ tailWord_2861479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861479).length < 2 ^ (prefixWord ++ tailWord_2861479).sum := by decide
  have hdescent : baseEnd_2861479 < baseStart_2861479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861543 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2861543 : Nat := 118140960795 + 2861543 * 2 ^ 59
def prefixEnd_2861543 : Nat := 4983230072969 + 3 ^ 40 * 2861543 * 2
def baseEnd_2861543 : Nat := 979564648339201955701673

theorem tailTrace_2861543 : CollatzResearch.WordTrace tailWord_2861543 prefixEnd_2861543 979564648339201955701673 := by
  unfold tailWord_2861543
  simp only [CollatzResearch.WordTrace]
  refine ⟨104369047472125898481109283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69579364981417265654072855 104369047472125898481109283)
  ·
    refine ⟨156553571208188847721663925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104369047472125898481109283 156553571208188847721663925)
    ·
      refine ⟨14676897300767704473905993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156553571208188847721663925 14676897300767704473905993)
      ·
        refine ⟨11007672975575778355429495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14676897300767704473905993 11007672975575778355429495)
        ·
          refine ⟨16511509463363667533144243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007672975575778355429495 16511509463363667533144243)
          ·
            refine ⟨24767264195045501299716365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16511509463363667533144243 24767264195045501299716365)
            ·
              refine ⟨9287724073142062987393637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24767264195045501299716365 9287724073142062987393637)
              ·
                refine ⟨1741448263714136810136307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9287724073142062987393637 1741448263714136810136307)
                ·
                  refine ⟨2612172395571205215204461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741448263714136810136307 2612172395571205215204461)
                  ·
                    refine ⟨979564648339201955701673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612172395571205215204461 979564648339201955701673)
                    ·
                      rfl

theorem cell22_2861543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2861543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861543 prefixEnd_2861543 := by exact prefixLift 2861543
  have htrace : WordTrace (prefixWord ++ tailWord_2861543) baseStart_2861543 baseEnd_2861543 := by
    simpa [prefixWord, tailWord_2861543, baseEnd_2861543] using wordTrace_append hprefix tailTrace_2861543
  have hstable : (prefixWord ++ tailWord_2861543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861543).length < 2 ^ (prefixWord ++ tailWord_2861543).sum := by decide
  have hdescent : baseEnd_2861543 < baseStart_2861543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861601 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 4]
def baseStart_2861601 : Nat := 118140960795 + 2861601 * 2 ^ 59
def prefixEnd_2861601 : Nat := 4983230072969 + 3 ^ 40 * 2861601 * 2
def baseEnd_2861601 : Nat := 326528167641503045917165

theorem tailTrace_2861601 : CollatzResearch.WordTrace tailWord_2861601 prefixEnd_2861601 326528167641503045917165 := by
  unfold tailWord_2861601
  simp only [CollatzResearch.WordTrace]
  refine ⟨104371162905915774386720657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69580775270610516257813771 104371162905915774386720657)
  ·
    refine ⟨78278372179436830790040493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104371162905915774386720657 78278372179436830790040493)
    ·
      refine ⟨29354389567288811546265185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78278372179436830790040493 29354389567288811546265185)
      ·
        refine ⟨22015792175466608659698889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29354389567288811546265185 22015792175466608659698889)
        ·
          refine ⟨16511844131599956494774167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22015792175466608659698889 16511844131599956494774167)
          ·
            refine ⟨24767766197399934742161251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16511844131599956494774167 24767766197399934742161251)
            ·
              refine ⟨37151649296099902113241877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24767766197399934742161251 37151649296099902113241877)
              ·
                refine ⟨1741483560754682911558213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37151649296099902113241877 1741483560754682911558213)
                ·
                  refine ⟨326528167641503045917165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741483560754682911558213 326528167641503045917165)
                  ·
                    rfl

theorem cell22_2861601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_2861601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861601 prefixEnd_2861601 := by exact prefixLift 2861601
  have htrace : WordTrace (prefixWord ++ tailWord_2861601) baseStart_2861601 baseEnd_2861601 := by
    simpa [prefixWord, tailWord_2861601, baseEnd_2861601] using wordTrace_append hprefix tailTrace_2861601
  have hstable : (prefixWord ++ tailWord_2861601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861601).length < 2 ^ (prefixWord ++ tailWord_2861601).sum := by decide
  have hdescent : baseEnd_2861601 < baseStart_2861601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861616 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_2861616 : Nat := 118140960795 + 2861616 * 2 ^ 59
def prefixEnd_2861616 : Nat := 4983230072969 + 3 ^ 40 * 2861616 * 2
def baseEnd_2861616 : Nat := 979589637731054098626449

theorem tailTrace_2861616 : CollatzResearch.WordTrace tailWord_2861616 prefixEnd_2861616 979589637731054098626449 := by
  unfold tailWord_2861616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52185855000430715974258351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69581140000574287965677801 52185855000430715974258351)
  ·
    refine ⟨78278782500646073961387527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52185855000430715974258351 78278782500646073961387527)
    ·
      refine ⟨117418173750969110942081291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78278782500646073961387527 117418173750969110942081291)
      ·
        refine ⟨176127260626453666413121937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117418173750969110942081291 176127260626453666413121937)
        ·
          refine ⟨132095445469840249809841453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176127260626453666413121937 132095445469840249809841453)
          ·
            refine ⟨49535792051190093678690545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132095445469840249809841453 49535792051190093678690545)
            ·
              refine ⟨37151844038392570259017909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49535792051190093678690545 37151844038392570259017909)
              ·
                refine ⟨3482985378599303461782929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37151844038392570259017909 3482985378599303461782929)
                ·
                  refine ⟨2612239033949477596337197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482985378599303461782929 2612239033949477596337197)
                  ·
                    refine ⟨979589637731054098626449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612239033949477596337197 979589637731054098626449)
                    ·
                      rfl

theorem cell22_2861616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_2861616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861616 prefixEnd_2861616 := by exact prefixLift 2861616
  have htrace : WordTrace (prefixWord ++ tailWord_2861616) baseStart_2861616 baseEnd_2861616 := by
    simpa [prefixWord, tailWord_2861616, baseEnd_2861616] using wordTrace_append hprefix tailTrace_2861616
  have hstable : (prefixWord ++ tailWord_2861616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861616).length < 2 ^ (prefixWord ++ tailWord_2861616).sum := by decide
  have hdescent : baseEnd_2861616 < baseStart_2861616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861768 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_2861768 : Nat := 118140960795 + 2861768 * 2 ^ 59
def prefixEnd_2861768 : Nat := 4983230072969 + 3 ^ 40 * 2861768 * 2
def baseEnd_2861768 : Nat := 979641670437376368825983

theorem tailTrace_2861768 : CollatzResearch.WordTrace tailWord_2861768 prefixEnd_2861768 979641670437376368825983 := by
  unfold tailWord_2861768
  simp only [CollatzResearch.WordTrace]
  refine ⟨52188626948155380954024979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69584835930873841272033305 52188626948155380954024979)
  ·
    refine ⟨78282940422233071431037469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52188626948155380954024979 78282940422233071431037469)
    ·
      refine ⟨29356102658337401786639051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78282940422233071431037469 29356102658337401786639051)
      ·
        refine ⟨44034153987506102679958577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29356102658337401786639051 44034153987506102679958577)
        ·
          refine ⟨33025615490629577009968933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44034153987506102679958577 33025615490629577009968933)
          ·
            refine ⟨6192302904493045689369175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33025615490629577009968933 6192302904493045689369175)
            ·
              refine ⟨9288454356739568534053763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192302904493045689369175 9288454356739568534053763)
              ·
                refine ⟨13932681535109352801080645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288454356739568534053763 13932681535109352801080645)
                ·
                  refine ⟨2612377787833003650202621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13932681535109352801080645 2612377787833003650202621)
                  ·
                    refine ⟨979641670437376368825983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612377787833003650202621 979641670437376368825983)
                    ·
                      rfl

theorem cell22_2861768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_2861768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861768 prefixEnd_2861768 := by exact prefixLift 2861768
  have htrace : WordTrace (prefixWord ++ tailWord_2861768) baseStart_2861768 baseEnd_2861768 := by
    simpa [prefixWord, tailWord_2861768, baseEnd_2861768] using wordTrace_append hprefix tailTrace_2861768
  have hstable : (prefixWord ++ tailWord_2861768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861768).length < 2 ^ (prefixWord ++ tailWord_2861768).sum := by decide
  have hdescent : baseEnd_2861768 < baseStart_2861768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861785 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_2861785 : Nat := 118140960795 + 2861785 * 2 ^ 59
def prefixEnd_2861785 : Nat := 4983230072969 + 3 ^ 40 * 2861785 * 2
def baseEnd_2861785 : Nat := 979647489884793991150931

theorem tailTrace_2861785 : CollatzResearch.WordTrace tailWord_2861785 prefixEnd_2861785 979647489884793991150931 := by
  unfold tailWord_2861785
  simp only [CollatzResearch.WordTrace]
  refine ⟨104377873937249173811418809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69585249291499449207612539 104377873937249173811418809)
  ·
    refine ⟨78283405452936880358564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104377873937249173811418809 78283405452936880358564107)
    ·
      refine ⟨117425108179405320537846161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78283405452936880358564107 117425108179405320537846161)
      ·
        refine ⟨88068831134553990403384621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117425108179405320537846161 88068831134553990403384621)
        ·
          refine ⟨33025811675457746401269233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88068831134553990403384621 33025811675457746401269233)
          ·
            refine ⟨24769358756593309800951925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33025811675457746401269233 24769358756593309800951925)
            ·
              refine ⟨2322127383430622793839243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24769358756593309800951925 2322127383430622793839243)
              ·
                refine ⟨3483191075145934190758865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322127383430622793839243 3483191075145934190758865)
                ·
                  refine ⟨2612393306359450643069149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3483191075145934190758865 2612393306359450643069149)
                  ·
                    refine ⟨979647489884793991150931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612393306359450643069149 979647489884793991150931)
                    ·
                      rfl

theorem cell22_2861785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_2861785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861785 prefixEnd_2861785 := by exact prefixLift 2861785
  have htrace : WordTrace (prefixWord ++ tailWord_2861785) baseStart_2861785 baseEnd_2861785 := by
    simpa [prefixWord, tailWord_2861785, baseEnd_2861785] using wordTrace_append hprefix tailTrace_2861785
  have hstable : (prefixWord ++ tailWord_2861785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861785).length < 2 ^ (prefixWord ++ tailWord_2861785).sum := by decide
  have hdescent : baseEnd_2861785 < baseStart_2861785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861841 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2861841 : Nat := 118140960795 + 2861841 * 2 ^ 59
def prefixEnd_2861841 : Nat := 4983230072969 + 3 ^ 40 * 2861841 * 2
def baseEnd_2861841 : Nat := 979666659829228511750759

theorem tailTrace_2861841 : CollatzResearch.WordTrace tailWord_2861841 prefixEnd_2861841 979666659829228511750759 := by
  unfold tailWord_2861841
  simp only [CollatzResearch.WordTrace]
  refine ⟨104379916425046295375457377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69586610950030863583638251 104379916425046295375457377)
  ·
    refine ⟨78284937318784721531593033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104379916425046295375457377 78284937318784721531593033)
    ·
      refine ⟨58713702989088541148694775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78284937318784721531593033 58713702989088541148694775)
      ·
        refine ⟨88070554483632811723042163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58713702989088541148694775 88070554483632811723042163)
        ·
          refine ⟨132105831725449217584563245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88070554483632811723042163 132105831725449217584563245)
          ·
            refine ⟨49539686897043456594211217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132105831725449217584563245 49539686897043456594211217)
            ·
              refine ⟨37154765172782592445658413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49539686897043456594211217 37154765172782592445658413)
              ·
                refine ⟨13933036939793472167121905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37154765172782592445658413 13933036939793472167121905)
                ·
                  refine ⟨10449777704845104125341429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13933036939793472167121905 10449777704845104125341429)
                  ·
                    refine ⟨979666659829228511750759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10449777704845104125341429 979666659829228511750759)
                    ·
                      rfl

theorem cell22_2861841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2861841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861841 prefixEnd_2861841 := by exact prefixLift 2861841
  have htrace : WordTrace (prefixWord ++ tailWord_2861841) baseStart_2861841 baseEnd_2861841 := by
    simpa [prefixWord, tailWord_2861841, baseEnd_2861841] using wordTrace_append hprefix tailTrace_2861841
  have hstable : (prefixWord ++ tailWord_2861841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861841).length < 2 ^ (prefixWord ++ tailWord_2861841).sum := by decide
  have hdescent : baseEnd_2861841 < baseStart_2861841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861892 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2861892 : Nat := 118140960795 + 2861892 * 2 ^ 59
def prefixEnd_2861892 : Nat := 4983230072969 + 3 ^ 40 * 2861892 * 2
def baseEnd_2861892 : Nat := 979684118171481378725603

theorem tailTrace_2861892 : CollatzResearch.WordTrace tailWord_2861892 prefixEnd_2861892 979684118171481378725603 := by
  unfold tailWord_2861892
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190888273930765542781965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69587851031907687390375953 52190888273930765542781965)
  ·
    refine ⟨19571583102724037078543237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52190888273930765542781965 19571583102724037078543237)
    ·
      refine ⟨3669671831760756952226857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19571583102724037078543237 3669671831760756952226857)
      ·
        refine ⟨2752253873820567714170143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3669671831760756952226857 2752253873820567714170143)
        ·
          refine ⟨4128380810730851571255215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752253873820567714170143 4128380810730851571255215)
          ·
            refine ⟨6192571216096277356882823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128380810730851571255215 6192571216096277356882823)
            ·
              refine ⟨9288856824144416035324235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192571216096277356882823 9288856824144416035324235)
              ·
                refine ⟨13933285236216624052986353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288856824144416035324235 13933285236216624052986353)
                ·
                  refine ⟨10449963927162468039739765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13933285236216624052986353 10449963927162468039739765)
                  ·
                    refine ⟨979684118171481378725603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10449963927162468039739765 979684118171481378725603)
                    ·
                      rfl

theorem cell22_2861892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2861892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861892 prefixEnd_2861892 := by exact prefixLift 2861892
  have htrace : WordTrace (prefixWord ++ tailWord_2861892) baseStart_2861892 baseEnd_2861892 := by
    simpa [prefixWord, tailWord_2861892, baseEnd_2861892] using wordTrace_append hprefix tailTrace_2861892
  have hstable : (prefixWord ++ tailWord_2861892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861892).length < 2 ^ (prefixWord ++ tailWord_2861892).sum := by decide
  have hdescent : baseEnd_2861892 < baseStart_2861892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861937 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_2861937 : Nat := 118140960795 + 2861937 * 2 ^ 59
def prefixEnd_2861937 : Nat := 4983230072969 + 3 ^ 40 * 2861937 * 2
def baseEnd_2861937 : Nat := 979699522591116261350465

theorem tailTrace_2861937 : CollatzResearch.WordTrace tailWord_2861937 prefixEnd_2861937 979699522591116261350465 := by
  unfold tailWord_2861937
  simp only [CollatzResearch.WordTrace]
  refine ⟨104383417832698503770952065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69588945221799002513968043 104383417832698503770952065)
  ·
    refine ⟨78287563374523877828214049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104383417832698503770952065 78287563374523877828214049)
    ·
      refine ⟨58715672530892908371160537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78287563374523877828214049 58715672530892908371160537)
      ·
        refine ⟨44036754398169681278370403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58715672530892908371160537 44036754398169681278370403)
        ·
          refine ⟨66055131597254521917555605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44036754398169681278370403 66055131597254521917555605)
          ·
            refine ⟨3096334293621305714885419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66055131597254521917555605 3096334293621305714885419)
            ·
              refine ⟨4644501440431958572328129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096334293621305714885419 4644501440431958572328129)
              ·
                refine ⟨3483376080323968929246097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4644501440431958572328129 3483376080323968929246097)
                ·
                  refine ⟨2612532060242976696934573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3483376080323968929246097 2612532060242976696934573)
                  ·
                    refine ⟨979699522591116261350465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612532060242976696934573 979699522591116261350465)
                    ·
                      rfl

theorem cell22_2861937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_2861937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2861937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2861937 prefixEnd_2861937 := by exact prefixLift 2861937
  have htrace : WordTrace (prefixWord ++ tailWord_2861937) baseStart_2861937 baseEnd_2861937 := by
    simpa [prefixWord, tailWord_2861937, baseEnd_2861937] using wordTrace_append hprefix tailTrace_2861937
  have hstable : (prefixWord ++ tailWord_2861937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861937).length < 2 ^ (prefixWord ++ tailWord_2861937).sum := by decide
  have hdescent : baseEnd_2861937 < baseStart_2861937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862023 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 6]
def baseStart_2862023 : Nat := 118140960795 + 2862023 * 2 ^ 59
def prefixEnd_2862023 : Nat := 4983230072969 + 3 ^ 40 * 2862023 * 2
def baseEnd_2862023 : Nat := 326576320716213567900067

theorem tailTrace_2862023 : CollatzResearch.WordTrace tailWord_2862023 prefixEnd_2862023 326576320716213567900067 := by
  unfold tailWord_2862023
  simp only [CollatzResearch.WordTrace]
  refine ⟨104386554510386940458582723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69591036340257960305721815 104386554510386940458582723)
  ·
    refine ⟨156579831765580410687874085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104386554510386940458582723 156579831765580410687874085)
    ·
      refine ⟨29358718456046327003976391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156579831765580410687874085 29358718456046327003976391)
      ·
        refine ⟨44038077684069490505964587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29358718456046327003976391 44038077684069490505964587)
        ·
          refine ⟨66057116526104235758946881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44038077684069490505964587 66057116526104235758946881)
          ·
            refine ⟨49542837394578176819210161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66057116526104235758946881 49542837394578176819210161)
            ·
              refine ⟨37157128045933632614407621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49542837394578176819210161 37157128045933632614407621)
              ·
                refine ⟨6966961508612556115201429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37157128045933632614407621 6966961508612556115201429)
                ·
                  refine ⟨326576320716213567900067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6966961508612556115201429 326576320716213567900067)
                  ·
                    rfl

theorem cell22_2862023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_2862023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862023 prefixEnd_2862023 := by exact prefixLift 2862023
  have htrace : WordTrace (prefixWord ++ tailWord_2862023) baseStart_2862023 baseEnd_2862023 := by
    simpa [prefixWord, tailWord_2862023, baseEnd_2862023] using wordTrace_append hprefix tailTrace_2862023
  have hstable : (prefixWord ++ tailWord_2862023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862023).length < 2 ^ (prefixWord ++ tailWord_2862023).sum := by decide
  have hdescent : baseEnd_2862023 < baseStart_2862023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862085 : List Nat := [1, 3, 1, 1, 2, 3, 5, 6]
def baseStart_2862085 : Nat := 118140960795 + 2862085 * 2 ^ 59
def prefixEnd_2862085 : Nat := 4983230072969 + 3 ^ 40 * 2862085 * 2
def baseEnd_2862085 : Nat := 108861131779521467627779

theorem tailTrace_2862085 : CollatzResearch.WordTrace tailWord_2862085 prefixEnd_2862085 108861131779521467627779 := by
  unfold tailWord_2862085
  simp only [CollatzResearch.WordTrace]
  refine ⟨104388815836162325047339709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69592543890774883364893139 104388815836162325047339709)
  ·
    refine ⟨39145805938560871892752391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104388815836162325047339709 39145805938560871892752391)
    ·
      refine ⟨58718708907841307839128587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39145805938560871892752391 58718708907841307839128587)
      ·
        refine ⟨88078063361761961758692881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58718708907841307839128587 88078063361761961758692881)
        ·
          refine ⟨66058547521321471319019661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88078063361761961758692881 66058547521321471319019661)
          ·
            refine ⟨24771955320495551744632373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66058547521321471319019661 24771955320495551744632373)
            ·
              refine ⟨2322370811296457976059285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24771955320495551744632373 2322370811296457976059285)
              ·
                refine ⟨108861131779521467627779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2322370811296457976059285 108861131779521467627779)
                ·
                  rfl

theorem cell22_2862085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 6].length) (baseStart_2862085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862085 prefixEnd_2862085 := by exact prefixLift 2862085
  have htrace : WordTrace (prefixWord ++ tailWord_2862085) baseStart_2862085 baseEnd_2862085 := by
    simpa [prefixWord, tailWord_2862085, baseEnd_2862085] using wordTrace_append hprefix tailTrace_2862085
  have hstable : (prefixWord ++ tailWord_2862085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862085).length < 2 ^ (prefixWord ++ tailWord_2862085).sum := by decide
  have hdescent : baseEnd_2862085 < baseStart_2862085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862117 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_2862117 : Nat := 118140960795 + 2862117 * 2 ^ 59
def prefixEnd_2862117 : Nat := 4983230072969 + 3 ^ 40 * 2862117 * 2
def baseEnd_2862117 : Nat := 979761140269655791849913

theorem tailTrace_2862117 : CollatzResearch.WordTrace tailWord_2862117 prefixEnd_2862117 979761140269655791849913 := by
  unfold tailWord_2862117
  simp only [CollatzResearch.WordTrace]
  refine ⟨104389982972046394512504605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69593321981364263008336403 104389982972046394512504605)
  ·
    refine ⟨39146243614517397942189227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104389982972046394512504605 39146243614517397942189227)
    ·
      refine ⟨58719365421776096913283841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39146243614517397942189227 58719365421776096913283841)
      ·
        refine ⟨44039524066332072684962881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58719365421776096913283841 44039524066332072684962881)
        ·
          refine ⟨33029643049749054513722161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44039524066332072684962881 33029643049749054513722161)
          ·
            refine ⟨24772232287311790885291621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33029643049749054513722161 24772232287311790885291621)
            ·
              refine ⟨4644793553870960790992179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24772232287311790885291621 4644793553870960790992179)
              ·
                refine ⟨6967190330806441186488269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644793553870960790992179 6967190330806441186488269)
                ·
                  refine ⟨2612696374052415444933101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967190330806441186488269 2612696374052415444933101)
                  ·
                    refine ⟨979761140269655791849913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612696374052415444933101 979761140269655791849913)
                    ·
                      rfl

theorem cell22_2862117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_2862117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862117 prefixEnd_2862117 := by exact prefixLift 2862117
  have htrace : WordTrace (prefixWord ++ tailWord_2862117) baseStart_2862117 baseEnd_2862117 := by
    simpa [prefixWord, tailWord_2862117, baseEnd_2862117] using wordTrace_append hprefix tailTrace_2862117
  have hstable : (prefixWord ++ tailWord_2862117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862117).length < 2 ^ (prefixWord ++ tailWord_2862117).sum := by decide
  have hdescent : baseEnd_2862117 < baseStart_2862117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862134 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2862134 : Nat := 118140960795 + 2862134 * 2 ^ 59
def prefixEnd_2862134 : Nat := 4983230072969 + 3 ^ 40 * 2862134 * 2
def baseEnd_2862134 : Nat := 979766959717073414174861

theorem tailTrace_2862134 : CollatzResearch.WordTrace tailWord_2862134 prefixEnd_2862134 979766959717073414174861 := by
  unfold tailWord_2862134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524412688311550400992091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69593735341989870943915637 6524412688311550400992091)
  ·
    refine ⟨9786619032467325601488137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6524412688311550400992091 9786619032467325601488137)
    ·
      refine ⟨7339964274350494201116103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9786619032467325601488137 7339964274350494201116103)
      ·
        refine ⟨11009946411525741301674155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7339964274350494201116103 11009946411525741301674155)
        ·
          refine ⟨16514919617288611952511233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11009946411525741301674155 16514919617288611952511233)
          ·
            refine ⟨12386189712966458964383425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16514919617288611952511233 12386189712966458964383425)
            ·
              refine ⟨9289642284724844223287569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386189712966458964383425 9289642284724844223287569)
              ·
                refine ⟨6967231713543633167465677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9289642284724844223287569 6967231713543633167465677)
                ·
                  refine ⟨2612711892578862437799629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967231713543633167465677 2612711892578862437799629)
                  ·
                    refine ⟨979766959717073414174861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612711892578862437799629 979766959717073414174861)
                    ·
                      rfl

theorem cell22_2862134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2862134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862134 prefixEnd_2862134 := by exact prefixLift 2862134
  have htrace : WordTrace (prefixWord ++ tailWord_2862134) baseStart_2862134 baseEnd_2862134 := by
    simpa [prefixWord, tailWord_2862134, baseEnd_2862134] using wordTrace_append hprefix tailTrace_2862134
  have hstable : (prefixWord ++ tailWord_2862134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862134).length < 2 ^ (prefixWord ++ tailWord_2862134).sum := by decide
  have hdescent : baseEnd_2862134 < baseStart_2862134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862151 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2862151 : Nat := 118140960795 + 2862151 * 2 ^ 59
def prefixEnd_2862151 : Nat := 4983230072969 + 3 ^ 40 * 2862151 * 2
def baseEnd_2862151 : Nat := 979772779164491036499809

theorem tailTrace_2862151 : CollatzResearch.WordTrace tailWord_2862151 prefixEnd_2862151 979772779164491036499809 := by
  unfold tailWord_2862151
  simp only [CollatzResearch.WordTrace]
  refine ⟨104391223053923218319242307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69594148702615478879494871 104391223053923218319242307)
  ·
    refine ⟨156586834580884827478863461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104391223053923218319242307 156586834580884827478863461)
    ·
      refine ⟨29360031483915905152286899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156586834580884827478863461 29360031483915905152286899)
      ·
        refine ⟨44040047225873857728430349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29360031483915905152286899 44040047225873857728430349)
        ·
          refine ⟨16515017709702696648161381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44040047225873857728430349 16515017709702696648161381)
          ·
            refine ⟨3096565820569255621530259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16515017709702696648161381 3096565820569255621530259)
            ·
              refine ⟨4644848730853883432295389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096565820569255621530259 4644848730853883432295389)
              ·
                refine ⟨1741818274070206287110771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4644848730853883432295389 1741818274070206287110771)
                ·
                  refine ⟨2612727411105309430666157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741818274070206287110771 2612727411105309430666157)
                  ·
                    refine ⟨979772779164491036499809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612727411105309430666157 979772779164491036499809)
                    ·
                      rfl

theorem cell22_2862151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2862151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862151 prefixEnd_2862151 := by exact prefixLift 2862151
  have htrace : WordTrace (prefixWord ++ tailWord_2862151) baseStart_2862151 baseEnd_2862151 := by
    simpa [prefixWord, tailWord_2862151, baseEnd_2862151] using wordTrace_append hprefix tailTrace_2862151
  have hstable : (prefixWord ++ tailWord_2862151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862151).length < 2 ^ (prefixWord ++ tailWord_2862151).sum := by decide
  have hdescent : baseEnd_2862151 < baseStart_2862151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862226 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_2862226 : Nat := 118140960795 + 2862226 * 2 ^ 59
def prefixEnd_2862226 : Nat := 4983230072969 + 3 ^ 40 * 2862226 * 2
def baseEnd_2862226 : Nat := 326599484399071946958193

theorem tailTrace_2862226 : CollatzResearch.WordTrace tailWord_2862226 prefixEnd_2862226 326599484399071946958193 := by
  unfold tailWord_2862226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098489632162876532055633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69595972352434337418815021 26098489632162876532055633)
  ·
    refine ⟨19573867224122157399041725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26098489632162876532055633 19573867224122157399041725)
    ·
      refine ⟨7340200209045809024640647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19573867224122157399041725 7340200209045809024640647)
      ·
        refine ⟨11010300313568713536960971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340200209045809024640647 11010300313568713536960971)
        ·
          refine ⟨16515450470353070305441457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010300313568713536960971 16515450470353070305441457)
          ·
            refine ⟨12386587852764802729081093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16515450470353070305441457 12386587852764802729081093)
            ·
              refine ⟨2322485222393400511702705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12386587852764802729081093 2322485222393400511702705)
              ·
                refine ⟨1741863916795050383777029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322485222393400511702705 1741863916795050383777029)
                ·
                  refine ⟨326599484399071946958193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741863916795050383777029 326599484399071946958193)
                  ·
                    rfl

theorem cell22_2862226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_2862226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862226 prefixEnd_2862226 := by exact prefixLift 2862226
  have htrace : WordTrace (prefixWord ++ tailWord_2862226) baseStart_2862226 baseEnd_2862226 := by
    simpa [prefixWord, tailWord_2862226, baseEnd_2862226] using wordTrace_append hprefix tailTrace_2862226
  have hstable : (prefixWord ++ tailWord_2862226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862226).length < 2 ^ (prefixWord ++ tailWord_2862226).sum := by decide
  have hdescent : baseEnd_2862226 < baseStart_2862226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862262 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2862262 : Nat := 118140960795 + 2862262 * 2 ^ 59
def prefixEnd_2862262 : Nat := 4983230072969 + 3 ^ 40 * 2862262 * 2
def baseEnd_2862262 : Nat := 979810776732923746974469

theorem tailTrace_2862262 : CollatzResearch.WordTrace tailWord_2862262 prefixEnd_2862262 979810776732923746974469 := by
  unfold tailWord_2862262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524704472282567767283315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69596847704347389517688693 6524704472282567767283315)
  ·
    refine ⟨9787056708423851650924973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6524704472282567767283315 9787056708423851650924973)
    ·
      refine ⟨3670146265658944369096865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9787056708423851650924973 3670146265658944369096865)
      ·
        refine ⟨2752609699244208276822649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3670146265658944369096865 2752609699244208276822649)
        ·
          refine ⟨2064457274433156207616987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2752609699244208276822649 2064457274433156207616987)
          ·
            refine ⟨3096685911649734311425481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064457274433156207616987 3096685911649734311425481)
            ·
              refine ⟨2322514433737300733569111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3096685911649734311425481 2322514433737300733569111)
              ·
                refine ⟨3483771650605951100353667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322514433737300733569111 3483771650605951100353667)
                ·
                  refine ⟨5225657475908926650530501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483771650605951100353667 5225657475908926650530501)
                  ·
                    refine ⟨979810776732923746974469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225657475908926650530501 979810776732923746974469)
                    ·
                      rfl

theorem cell22_2862262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2862262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862262 prefixEnd_2862262 := by exact prefixLift 2862262
  have htrace : WordTrace (prefixWord ++ tailWord_2862262) baseStart_2862262 baseEnd_2862262 := by
    simpa [prefixWord, tailWord_2862262, baseEnd_2862262] using wordTrace_append hprefix tailTrace_2862262
  have hstable : (prefixWord ++ tailWord_2862262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862262).length < 2 ^ (prefixWord ++ tailWord_2862262).sum := by decide
  have hdescent : baseEnd_2862262 < baseStart_2862262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862282 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_2862282 : Nat := 118140960795 + 2862282 * 2 ^ 59
def prefixEnd_2862282 : Nat := 4983230072969 + 3 ^ 40 * 2862282 * 2
def baseEnd_2862282 : Nat := 326605874380550120491469

theorem tailTrace_2862282 : CollatzResearch.WordTrace tailWord_2862282 prefixEnd_2862282 326605874380550120491469 := by
  unfold tailWord_2862282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26099000254112156923065275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69597334010965751794840733 26099000254112156923065275)
  ·
    refine ⟨39148500381168235384597913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26099000254112156923065275 39148500381168235384597913)
    ·
      refine ⟨29361375285876176538448435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39148500381168235384597913 29361375285876176538448435)
      ·
        refine ⟨44042062928814264807672653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29361375285876176538448435 44042062928814264807672653)
        ·
          refine ⟨16515773598305349302877245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44042062928814264807672653 16515773598305349302877245)
          ·
            refine ⟨6193415099364505988578967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16515773598305349302877245 6193415099364505988578967)
            ·
              refine ⟨9290122649046758982868451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193415099364505988578967 9290122649046758982868451)
              ·
                refine ⟨13935183973570138474302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9290122649046758982868451 13935183973570138474302677)
                ·
                  refine ⟨326605874380550120491469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13935183973570138474302677 326605874380550120491469)
                  ·
                    rfl

theorem cell22_2862282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_2862282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862282 prefixEnd_2862282 := by exact prefixLift 2862282
  have htrace : WordTrace (prefixWord ++ tailWord_2862282) baseStart_2862282 baseEnd_2862282 := by
    simpa [prefixWord, tailWord_2862282, baseEnd_2862282] using wordTrace_append hprefix tailTrace_2862282
  have hstable : (prefixWord ++ tailWord_2862282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862282).length < 2 ^ (prefixWord ++ tailWord_2862282).sum := by decide
  have hdescent : baseEnd_2862282 < baseStart_2862282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862286 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_2862286 : Nat := 118140960795 + 2862286 * 2 ^ 59
def prefixEnd_2862286 : Nat := 4983230072969 + 3 ^ 40 * 2862286 * 2
def baseEnd_2862286 : Nat := 979818992423395684374395

theorem tailTrace_2862286 : CollatzResearch.WordTrace tailWord_2862286 prefixEnd_2862286 979818992423395684374395 := by
  unfold tailWord_2862286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049518363554267046925839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69597431272289424250271141 13049518363554267046925839)
  ·
    refine ⟨19574277545331400570388759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13049518363554267046925839 19574277545331400570388759)
    ·
      refine ⟨29361416317997100855583139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19574277545331400570388759 29361416317997100855583139)
      ·
        refine ⟨44042124476995651283374709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29361416317997100855583139 44042124476995651283374709)
        ·
          refine ⟨4128949169718342307816379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44042124476995651283374709 4128949169718342307816379)
          ·
            refine ⟨6193423754577513461724569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128949169718342307816379 6193423754577513461724569)
            ·
              refine ⟨4645067815933135096293427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193423754577513461724569 4645067815933135096293427)
              ·
                refine ⟨6967601723899702644440141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645067815933135096293427 6967601723899702644440141)
                ·
                  refine ⟨2612850646462388491665053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967601723899702644440141 2612850646462388491665053)
                  ·
                    refine ⟨979818992423395684374395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612850646462388491665053 979818992423395684374395)
                    ·
                      rfl

theorem cell22_2862286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_2862286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862286 prefixEnd_2862286 := by exact prefixLift 2862286
  have htrace : WordTrace (prefixWord ++ tailWord_2862286) baseStart_2862286 baseEnd_2862286 := by
    simpa [prefixWord, tailWord_2862286, baseEnd_2862286] using wordTrace_append hprefix tailTrace_2862286
  have hstable : (prefixWord ++ tailWord_2862286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862286).length < 2 ^ (prefixWord ++ tailWord_2862286).sum := by decide
  have hdescent : baseEnd_2862286 < baseStart_2862286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862357 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2862357 : Nat := 118140960795 + 2862357 * 2 ^ 59
def prefixEnd_2862357 : Nat := 4983230072969 + 3 ^ 40 * 2862357 * 2
def baseEnd_2862357 : Nat := 979843297174375165849177

theorem tailTrace_2862357 : CollatzResearch.WordTrace tailWord_2862357 prefixEnd_2862357 979843297174375165849177 := by
  unfold tailWord_2862357
  simp only [CollatzResearch.WordTrace]
  refine ⟨104398736491176915501241325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69599157660784610334160883 104398736491176915501241325)
  ·
    refine ⟨39149526184191343312965497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104398736491176915501241325 39149526184191343312965497)
    ·
      refine ⟨29362144638143507484724123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39149526184191343312965497 29362144638143507484724123)
      ·
        refine ⟨44043216957215261227086185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29362144638143507484724123 44043216957215261227086185)
        ·
          refine ⟨33032412717911445920314639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44043216957215261227086185 33032412717911445920314639)
          ·
            refine ⟨49548619076867168880471959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33032412717911445920314639 49548619076867168880471959)
            ·
              refine ⟨74322928615300753320707939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49548619076867168880471959 74322928615300753320707939)
              ·
                refine ⟨111484392922951129981061909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74322928615300753320707939 111484392922951129981061909)
                ·
                  refine ⟨5225830918263334217862277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111484392922951129981061909 5225830918263334217862277)
                  ·
                    refine ⟨979843297174375165849177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225830918263334217862277 979843297174375165849177)
                    ·
                      rfl

theorem cell22_2862357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2862357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862357 prefixEnd_2862357 := by exact prefixLift 2862357
  have htrace : WordTrace (prefixWord ++ tailWord_2862357) baseStart_2862357 baseEnd_2862357 := by
    simpa [prefixWord, tailWord_2862357, baseEnd_2862357] using wordTrace_append hprefix tailTrace_2862357
  have hstable : (prefixWord ++ tailWord_2862357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862357).length < 2 ^ (prefixWord ++ tailWord_2862357).sum := by decide
  have hdescent : baseEnd_2862357 < baseStart_2862357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862372 : List Nat := [2, 3, 1, 3, 1, 1, 1, 10]
def baseStart_2862372 : Nat := 118140960795 + 2862372 * 2 ^ 59
def prefixEnd_2862372 : Nat := 4983230072969 + 3 ^ 40 * 2862372 * 2
def baseEnd_2862372 : Nat := 108872047997880014080459

theorem tailTrace_2862372 : CollatzResearch.WordTrace tailWord_2862372 prefixEnd_2862372 108872047997880014080459 := by
  unfold tailWord_2862372
  simp only [CollatzResearch.WordTrace]
  refine ⟨52199641793061286531518685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69599522390748382042024913 52199641793061286531518685)
  ·
    refine ⟨19574865672397982449319507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52199641793061286531518685 19574865672397982449319507)
    ·
      refine ⟨29362298508596973673979261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19574865672397982449319507 29362298508596973673979261)
      ·
        refine ⟨11010861940723865127742223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29362298508596973673979261 11010861940723865127742223)
        ·
          refine ⟨16516292911085797691613335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010861940723865127742223 16516292911085797691613335)
          ·
            refine ⟨24774439366628696537420003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16516292911085797691613335 24774439366628696537420003)
            ·
              refine ⟨37161659049943044806130005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24774439366628696537420003 37161659049943044806130005)
              ·
                refine ⟨108872047997880014080459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37161659049943044806130005 108872047997880014080459)
                ·
                  rfl

theorem cell22_2862372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_2862372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862372 prefixEnd_2862372 := by exact prefixLift 2862372
  have htrace : WordTrace (prefixWord ++ tailWord_2862372) baseStart_2862372 baseEnd_2862372 := by
    simpa [prefixWord, tailWord_2862372, baseEnd_2862372] using wordTrace_append hprefix tailTrace_2862372
  have hstable : (prefixWord ++ tailWord_2862372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862372).length < 2 ^ (prefixWord ++ tailWord_2862372).sum := by decide
  have hdescent : baseEnd_2862372 < baseStart_2862372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862393 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_2862393 : Nat := 118140960795 + 2862393 * 2 ^ 59
def prefixEnd_2862393 : Nat := 4983230072969 + 3 ^ 40 * 2862393 * 2
def baseEnd_2862393 : Nat := 979855620710083071949067

theorem tailTrace_2862393 : CollatzResearch.WordTrace tailWord_2862393 prefixEnd_2862393 979855620710083071949067 := by
  unfold tailWord_2862393
  simp only [CollatzResearch.WordTrace]
  refine ⟨104400049519046493649551833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69600033012697662433034555 104400049519046493649551833)
  ·
    refine ⟨78300037139284870237163875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104400049519046493649551833 78300037139284870237163875)
    ·
      refine ⟨117450055708927305355745813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78300037139284870237163875 117450055708927305355745813)
      ·
        refine ⟨5505471361355967438550585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117450055708927305355745813 5505471361355967438550585)
        ·
          refine ⟨4129103521016975578912939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5505471361355967438550585 4129103521016975578912939)
          ·
            refine ⟨6193655281525463368369409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129103521016975578912939 6193655281525463368369409)
            ·
              refine ⟨4645241461144097526277057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193655281525463368369409 4645241461144097526277057)
              ·
                refine ⟨3483931095858073144707793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645241461144097526277057 3483931095858073144707793)
                ·
                  refine ⟨2612948321893554858530845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3483931095858073144707793 2612948321893554858530845)
                  ·
                    refine ⟨979855620710083071949067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612948321893554858530845 979855620710083071949067)
                    ·
                      rfl

theorem cell22_2862393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_2862393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862393 prefixEnd_2862393 := by exact prefixLift 2862393
  have htrace : WordTrace (prefixWord ++ tailWord_2862393) baseStart_2862393 baseEnd_2862393 := by
    simpa [prefixWord, tailWord_2862393, baseEnd_2862393] using wordTrace_append hprefix tailTrace_2862393
  have hstable : (prefixWord ++ tailWord_2862393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862393).length < 2 ^ (prefixWord ++ tailWord_2862393).sum := by decide
  have hdescent : baseEnd_2862393 < baseStart_2862393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862421 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2862421 : Nat := 118140960795 + 2862421 * 2 ^ 59
def prefixEnd_2862421 : Nat := 4983230072969 + 3 ^ 40 * 2862421 * 2
def baseEnd_2862421 : Nat := 979865205682300332248981

theorem tailTrace_2862421 : CollatzResearch.WordTrace tailWord_2862421 prefixEnd_2862421 979865205682300332248981 := by
  unfold tailWord_2862421
  simp only [CollatzResearch.WordTrace]
  refine ⟨104401070762945054431571117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69600713841963369621047411 104401070762945054431571117)
  ·
    refine ⟨39150401536104395411839169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104401070762945054431571117 39150401536104395411839169)
    ·
      refine ⟨29362801152078296558879377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39150401536104395411839169 29362801152078296558879377)
      ·
        refine ⟨22022100864058722419159533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29362801152078296558879377 22022100864058722419159533)
        ·
          refine ⟨8258287824022020907184825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22022100864058722419159533 8258287824022020907184825)
          ·
            refine ⟨6193715868016515680388619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8258287824022020907184825 6193715868016515680388619)
            ·
              refine ⟨9290573802024773520582929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193715868016515680388619 9290573802024773520582929)
              ·
                refine ⟨6967930351518580140437197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9290573802024773520582929 6967930351518580140437197)
                ·
                  refine ⟨2612973881819467552663949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967930351518580140437197 2612973881819467552663949)
                  ·
                    refine ⟨979865205682300332248981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2612973881819467552663949 979865205682300332248981)
                    ·
                      rfl

theorem cell22_2862421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2862421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862421 prefixEnd_2862421 := by exact prefixLift 2862421
  have htrace : WordTrace (prefixWord ++ tailWord_2862421) baseStart_2862421 baseEnd_2862421 := by
    simpa [prefixWord, tailWord_2862421, baseEnd_2862421] using wordTrace_append hprefix tailTrace_2862421
  have hstable : (prefixWord ++ tailWord_2862421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862421).length < 2 ^ (prefixWord ++ tailWord_2862421).sum := by decide
  have hdescent : baseEnd_2862421 < baseStart_2862421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862434 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2862434 : Nat := 118140960795 + 2862434 * 2 ^ 59
def prefixEnd_2862434 : Nat := 4983230072969 + 3 ^ 40 * 2862434 * 2
def baseEnd_2862434 : Nat := 326623218615990877224647

theorem tailTrace_2862434 : CollatzResearch.WordTrace tailWord_2862434 prefixEnd_2862434 326623218615990877224647 := by
  unfold tailWord_2862434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100386227974489412948589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69601029941265305101196237 26100386227974489412948589)
  ·
    refine ⟨9787644835490433529855721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26100386227974489412948589 9787644835490433529855721)
    ·
      refine ⟨7340733626617825147391791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9787644835490433529855721 7340733626617825147391791)
      ·
        refine ⟨11011100439926737721087687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340733626617825147391791 11011100439926737721087687)
        ·
          refine ⟨16516650659890106581631531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011100439926737721087687 16516650659890106581631531)
          ·
            refine ⟨24774975989835159872447297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16516650659890106581631531 24774975989835159872447297)
            ·
              refine ⟨18581231992376369904335473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24774975989835159872447297 18581231992376369904335473)
              ·
                refine ⟨13935923994282277428251605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18581231992376369904335473 13935923994282277428251605)
                ·
                  refine ⟨326623218615990877224647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13935923994282277428251605 326623218615990877224647)
                  ·
                    rfl

theorem cell22_2862434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2862434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862434 prefixEnd_2862434 := by exact prefixLift 2862434
  have htrace : WordTrace (prefixWord ++ tailWord_2862434) baseStart_2862434 baseEnd_2862434 := by
    simpa [prefixWord, tailWord_2862434, baseEnd_2862434] using wordTrace_append hprefix tailTrace_2862434
  have hstable : (prefixWord ++ tailWord_2862434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862434).length < 2 ^ (prefixWord ++ tailWord_2862434).sum := by decide
  have hdescent : baseEnd_2862434 < baseStart_2862434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862513 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 4]
def baseStart_2862513 : Nat := 118140960795 + 2862513 * 2 ^ 59
def prefixEnd_2862513 : Nat := 4983230072969 + 3 ^ 40 * 2862513 * 2
def baseEnd_2862513 : Nat := 326632233054147586316233

theorem tailTrace_2862513 : CollatzResearch.WordTrace tailWord_2862513 prefixEnd_2862513 326632233054147586316233 := by
  unfold tailWord_2862513
  simp only [CollatzResearch.WordTrace]
  refine ⟨104404426278611754143920193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69602950852407836095946795 104404426278611754143920193)
  ·
    refine ⟨78303319708958815607940145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104404426278611754143920193 78303319708958815607940145)
    ·
      refine ⟨58727489781719111705955109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78303319708958815607940145 58727489781719111705955109)
      ·
        refine ⟨11011404334072333444866583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58727489781719111705955109 11011404334072333444866583)
        ·
          refine ⟨16517106501108500167299875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011404334072333444866583 16517106501108500167299875)
          ·
            refine ⟨24775659751662750250949813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16517106501108500167299875 24775659751662750250949813)
            ·
              refine ⟨2322718101718382836026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24775659751662750250949813 2322718101718382836026545)
              ·
                refine ⟨1742038576288787127019909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322718101718382836026545 1742038576288787127019909)
                ·
                  refine ⟨326632233054147586316233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742038576288787127019909 326632233054147586316233)
                  ·
                    rfl

theorem cell22_2862513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_2862513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862513 prefixEnd_2862513 := by exact prefixLift 2862513
  have htrace : WordTrace (prefixWord ++ tailWord_2862513) baseStart_2862513 baseEnd_2862513 := by
    simpa [prefixWord, tailWord_2862513, baseEnd_2862513] using wordTrace_append hprefix tailTrace_2862513
  have hstable : (prefixWord ++ tailWord_2862513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862513).length < 2 ^ (prefixWord ++ tailWord_2862513).sum := by decide
  have hdescent : baseEnd_2862513 < baseStart_2862513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862528 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_2862528 : Nat := 118140960795 + 2862528 * 2 ^ 59
def prefixEnd_2862528 : Nat := 4983230072969 + 3 ^ 40 * 2862528 * 2
def baseEnd_2862528 : Nat := 979901833968987719823653

theorem tailTrace_2862528 : CollatzResearch.WordTrace tailWord_2862528 prefixEnd_2862528 979901833968987719823653 := by
  unfold tailWord_2862528
  simp only [CollatzResearch.WordTrace]
  refine ⟨52202486686778705852858119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69603315582371607803810825 52202486686778705852858119)
  ·
    refine ⟨78303730030168058779287179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52202486686778705852858119 78303730030168058779287179)
    ·
      refine ⟨117455595045252088168930769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78303730030168058779287179 117455595045252088168930769)
      ·
        refine ⟨88091696283939066126698077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117455595045252088168930769 88091696283939066126698077)
        ·
          refine ⟨33034386106477149797511779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88091696283939066126698077 33034386106477149797511779)
          ·
            refine ⟨49551579159715724696267669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33034386106477149797511779 49551579159715724696267669)
            ·
              refine ⟨2322730273111674595137547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49551579159715724696267669 2322730273111674595137547)
              ·
                refine ⟨3484095409667511892706321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322730273111674595137547 3484095409667511892706321)
                ·
                  refine ⟨2613071557250633919529741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484095409667511892706321 2613071557250633919529741)
                  ·
                    refine ⟨979901833968987719823653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613071557250633919529741 979901833968987719823653)
                    ·
                      rfl

theorem cell22_2862528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_2862528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862528 prefixEnd_2862528 := by exact prefixLift 2862528
  have htrace : WordTrace (prefixWord ++ tailWord_2862528) baseStart_2862528 baseEnd_2862528 := by
    simpa [prefixWord, tailWord_2862528, baseEnd_2862528] using wordTrace_append hprefix tailTrace_2862528
  have hstable : (prefixWord ++ tailWord_2862528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862528).length < 2 ^ (prefixWord ++ tailWord_2862528).sum := by decide
  have hdescent : baseEnd_2862528 < baseStart_2862528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862584 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_2862584 : Nat := 118140960795 + 2862584 * 2 ^ 59
def prefixEnd_2862584 : Nat := 4983230072969 + 3 ^ 40 * 2862584 * 2
def baseEnd_2862584 : Nat := 979921003913422240423481

theorem tailTrace_2862584 : CollatzResearch.WordTrace tailWord_2862584 prefixEnd_2862584 979921003913422240423481 := by
  unfold tailWord_2862584
  simp only [CollatzResearch.WordTrace]
  refine ⟨52203507930677266634877403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69604677240903022179836537 52203507930677266634877403)
  ·
    refine ⟨78305261896015899952316105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52203507930677266634877403 78305261896015899952316105)
    ·
      refine ⟨58728946422011924964237079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78305261896015899952316105 58728946422011924964237079)
      ·
        refine ⟨88093419633017887446355619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58728946422011924964237079 88093419633017887446355619)
        ·
          refine ⟨132140129449526831169533429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88093419633017887446355619 132140129449526831169533429)
          ·
            refine ⟨12388137135893140422143759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132140129449526831169533429 12388137135893140422143759)
            ·
              refine ⟨18582205703839710633215639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12388137135893140422143759 18582205703839710633215639)
              ·
                refine ⟨27873308555759565949823459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18582205703839710633215639 27873308555759565949823459)
                ·
                  refine ⟨41809962833639348924735189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27873308555759565949823459 41809962833639348924735189)
                  ·
                    refine ⟨979921003913422240423481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41809962833639348924735189 979921003913422240423481)
                    ·
                      rfl

theorem cell22_2862584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_2862584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862584 prefixEnd_2862584 := by exact prefixLift 2862584
  have htrace : WordTrace (prefixWord ++ tailWord_2862584) baseStart_2862584 baseEnd_2862584 := by
    simpa [prefixWord, tailWord_2862584, baseEnd_2862584] using wordTrace_append hprefix tailTrace_2862584
  have hstable : (prefixWord ++ tailWord_2862584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862584).length < 2 ^ (prefixWord ++ tailWord_2862584).sum := by decide
  have hdescent : baseEnd_2862584 < baseStart_2862584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862661 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2862661 : Nat := 118140960795 + 2862661 * 2 ^ 59
def prefixEnd_2862661 : Nat := 4983230072969 + 3 ^ 40 * 2862661 * 2
def baseEnd_2862661 : Nat := 979947362587019706248245

theorem tailTrace_2862661 : CollatzResearch.WordTrace tailWord_2862661 prefixEnd_2862661 979947362587019706248245 := by
  unfold tailWord_2862661
  simp only [CollatzResearch.WordTrace]
  refine ⟨104409824282075575420307837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69606549521383716946871891 104409824282075575420307837)
  ·
    refine ⟨39153684105778340782615439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104409824282075575420307837 39153684105778340782615439)
    ·
      refine ⟨58730526158667511173923159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39153684105778340782615439 58730526158667511173923159)
      ·
        refine ⟨88095789238001266760884739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58730526158667511173923159 88095789238001266760884739)
        ·
          refine ⟨132143683857001900141327109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88095789238001266760884739 132143683857001900141327109)
          ·
            refine ⟨24776940723187856276498833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132143683857001900141327109 24776940723187856276498833)
            ·
              refine ⟨18582705542390892207374125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24776940723187856276498833 18582705542390892207374125)
              ·
                refine ⟨6968514578396584577765297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18582705542390892207374125 6968514578396584577765297)
                ·
                  refine ⟨5226385933797438433323973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6968514578396584577765297 5226385933797438433323973)
                  ·
                    refine ⟨979947362587019706248245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5226385933797438433323973 979947362587019706248245)
                    ·
                      rfl

theorem cell22_2862661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2862661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862661 prefixEnd_2862661 := by exact prefixLift 2862661
  have htrace : WordTrace (prefixWord ++ tailWord_2862661) baseStart_2862661 baseEnd_2862661 := by
    simpa [prefixWord, tailWord_2862661, baseEnd_2862661] using wordTrace_append hprefix tailTrace_2862661
  have hstable : (prefixWord ++ tailWord_2862661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862661).length < 2 ^ (prefixWord ++ tailWord_2862661).sum := by decide
  have hdescent : baseEnd_2862661 < baseStart_2862661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862725 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_2862725 : Nat := 118140960795 + 2862725 * 2 ^ 59
def prefixEnd_2862725 : Nat := 4983230072969 + 3 ^ 40 * 2862725 * 2
def baseEnd_2862725 : Nat := 979969271094944872648049

theorem tailTrace_2862725 : CollatzResearch.WordTrace tailWord_2862725 prefixEnd_2862725 979969271094944872648049 := by
  unfold tailWord_2862725
  simp only [CollatzResearch.WordTrace]
  refine ⟨104412158553843714350637629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69608105702562476233758419 104412158553843714350637629)
  ·
    refine ⟨39154559457691392881489111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104412158553843714350637629 39154559457691392881489111)
    ·
      refine ⟨58731839186537089322233667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39154559457691392881489111 58731839186537089322233667)
      ·
        refine ⟨88097758779805633983350501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58731839186537089322233667 88097758779805633983350501)
        ·
          refine ⟨16518329771213556371878219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88097758779805633983350501 16518329771213556371878219)
          ·
            refine ⟨24777494656820334557817329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16518329771213556371878219 24777494656820334557817329)
            ·
              refine ⟨18583120992615250918362997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24777494656820334557817329 18583120992615250918362997)
              ·
                refine ⟨1742167593057679773596531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18583120992615250918362997 1742167593057679773596531)
                ·
                  refine ⟨2613251389586519660394797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742167593057679773596531 2613251389586519660394797)
                  ·
                    refine ⟨979969271094944872648049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613251389586519660394797 979969271094944872648049)
                    ·
                      rfl

theorem cell22_2862725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_2862725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862725 prefixEnd_2862725 := by exact prefixLift 2862725
  have htrace : WordTrace (prefixWord ++ tailWord_2862725) baseStart_2862725 baseEnd_2862725 := by
    simpa [prefixWord, tailWord_2862725, baseEnd_2862725] using wordTrace_append hprefix tailTrace_2862725
  have hstable : (prefixWord ++ tailWord_2862725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862725).length < 2 ^ (prefixWord ++ tailWord_2862725).sum := by decide
  have hdescent : baseEnd_2862725 < baseStart_2862725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862753 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2862753 : Nat := 118140960795 + 2862753 * 2 ^ 59
def prefixEnd_2862753 : Nat := 4983230072969 + 3 ^ 40 * 2862753 * 2
def baseEnd_2862753 : Nat := 979978856067162132947963

theorem tailTrace_2862753 : CollatzResearch.WordTrace tailWord_2862753 prefixEnd_2862753 979978856067162132947963 := by
  unfold tailWord_2862753
  simp only [CollatzResearch.WordTrace]
  refine ⟨104413179797742275132656913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69608786531828183421771275 104413179797742275132656913)
  ·
    refine ⟨78309884848306706349492685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104413179797742275132656913 78309884848306706349492685)
    ·
      refine ⟨29366206818115014881059757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78309884848306706349492685 29366206818115014881059757)
      ·
        refine ⟨11012327556793130580397409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29366206818115014881059757 11012327556793130580397409)
        ·
          refine ⟨8259245667594847935298057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11012327556793130580397409 8259245667594847935298057)
          ·
            refine ⟨6194434250696135951473543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259245667594847935298057 6194434250696135951473543)
            ·
              refine ⟨9291651376044203927210315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194434250696135951473543 9291651376044203927210315)
              ·
                refine ⟨13937477064066305890815473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9291651376044203927210315 13937477064066305890815473)
                ·
                  refine ⟨10453107798049729418111605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13937477064066305890815473 10453107798049729418111605)
                  ·
                    refine ⟨979978856067162132947963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10453107798049729418111605 979978856067162132947963)
                    ·
                      rfl

theorem cell22_2862753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2862753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862753 prefixEnd_2862753 := by exact prefixLift 2862753
  have htrace : WordTrace (prefixWord ++ tailWord_2862753) baseStart_2862753 baseEnd_2862753 := by
    simpa [prefixWord, tailWord_2862753, baseEnd_2862753] using wordTrace_append hprefix tailTrace_2862753
  have hstable : (prefixWord ++ tailWord_2862753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862753).length < 2 ^ (prefixWord ++ tailWord_2862753).sum := by decide
  have hdescent : baseEnd_2862753 < baseStart_2862753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862828 : List Nat := [2, 2, 1, 1, 2, 2, 6, 6]
def baseStart_2862828 : Nat := 118140960795 + 2862828 * 2 ^ 59
def prefixEnd_2862828 : Nat := 4983230072969 + 3 ^ 40 * 2862828 * 2
def baseEnd_2862828 : Nat := 108889392233320770813637

theorem tailTrace_2862828 : CollatzResearch.WordTrace tailWord_2862828 prefixEnd_2862828 108889392233320770813637 := by
  unfold tailWord_2862828
  simp only [CollatzResearch.WordTrace]
  refine ⟨52207957636235281470818569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69610610181647041961091425 52207957636235281470818569)
  ·
    refine ⟨39155968227176461103113927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52207957636235281470818569 39155968227176461103113927)
    ·
      refine ⟨58733952340764691654670891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39155968227176461103113927 58733952340764691654670891)
      ·
        refine ⟨88100928511147037482006337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58733952340764691654670891 88100928511147037482006337)
        ·
          refine ⟨66075696383360278111504753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88100928511147037482006337 66075696383360278111504753)
          ·
            refine ⟨49556772287520208583628565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66075696383360278111504753 49556772287520208583628565)
            ·
              refine ⟨2322973700977509777357589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49556772287520208583628565 2322973700977509777357589)
              ·
                refine ⟨108889392233320770813637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2322973700977509777357589 108889392233320770813637)
                ·
                  rfl

theorem cell22_2862828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_2862828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862828 prefixEnd_2862828 := by exact prefixLift 2862828
  have htrace : WordTrace (prefixWord ++ tailWord_2862828) baseStart_2862828 baseEnd_2862828 := by
    simpa [prefixWord, tailWord_2862828, baseEnd_2862828] using wordTrace_append hprefix tailTrace_2862828
  have hstable : (prefixWord ++ tailWord_2862828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862828).length < 2 ^ (prefixWord ++ tailWord_2862828).sum := by decide
  have hdescent : baseEnd_2862828 < baseStart_2862828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862841 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_2862841 : Nat := 118140960795 + 2862841 * 2 ^ 59
def prefixEnd_2862841 : Nat := 4983230072969 + 3 ^ 40 * 2862841 * 2
def baseEnd_2862841 : Nat := 980008980265559236747693

theorem tailTrace_2862841 : CollatzResearch.WordTrace tailWord_2862841 prefixEnd_2862841 980008980265559236747693 := by
  unfold tailWord_2862841
  simp only [CollatzResearch.WordTrace]
  refine ⟨104416389421423466161860377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69610926280948977441240251 104416389421423466161860377)
  ·
    refine ⟨78312292066067599621395283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104416389421423466161860377 78312292066067599621395283)
    ·
      refine ⟨117468438099101399432092925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78312292066067599621395283 117468438099101399432092925)
      ·
        refine ⟨44050664287163024787034847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117468438099101399432092925 44050664287163024787034847)
        ·
          refine ⟨66075996430744537180552271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44050664287163024787034847 66075996430744537180552271)
          ·
            refine ⟨99113994646116805770828407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66075996430744537180552271 99113994646116805770828407)
            ·
              refine ⟨148670991969175208656242611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99113994646116805770828407 148670991969175208656242611)
              ·
                refine ⟨223006487953762812984363917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148670991969175208656242611 223006487953762812984363917)
                ·
                  refine ⟨83627432982661054869136469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223006487953762812984363917 83627432982661054869136469)
                  ·
                    refine ⟨980008980265559236747693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83627432982661054869136469 980008980265559236747693)
                    ·
                      rfl

theorem cell22_2862841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_2862841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862841 prefixEnd_2862841 := by exact prefixLift 2862841
  have htrace : WordTrace (prefixWord ++ tailWord_2862841) baseStart_2862841 baseEnd_2862841 := by
    simpa [prefixWord, tailWord_2862841, baseEnd_2862841] using wordTrace_append hprefix tailTrace_2862841
  have hstable : (prefixWord ++ tailWord_2862841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862841).length < 2 ^ (prefixWord ++ tailWord_2862841).sum := by decide
  have hdescent : baseEnd_2862841 < baseStart_2862841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862860 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_2862860 : Nat := 118140960795 + 2862860 * 2 ^ 59
def prefixEnd_2862860 : Nat := 4983230072969 + 3 ^ 40 * 2862860 * 2
def baseEnd_2862860 : Nat := 980015484353849520522635

theorem tailTrace_2862860 : CollatzResearch.WordTrace tailWord_2862860 prefixEnd_2862860 980015484353849520522635 := by
  unfold tailWord_2862860
  simp only [CollatzResearch.WordTrace]
  refine ⟨52208541204177316203401017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69611388272236421604534689 52208541204177316203401017)
  ·
    refine ⟨39156405903132987152550763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52208541204177316203401017 39156405903132987152550763)
    ·
      refine ⟨58734608854699480728826145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39156405903132987152550763 58734608854699480728826145)
      ·
        refine ⟨44050956641024610546619609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58734608854699480728826145 44050956641024610546619609)
        ·
          refine ⟨33038217480768457909964707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44050956641024610546619609 33038217480768457909964707)
          ·
            refine ⟨49557326221152686864947061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33038217480768457909964707 49557326221152686864947061)
            ·
              refine ⟨4645999333233064393588787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49557326221152686864947061 4645999333233064393588787)
              ·
                refine ⟨6968998999849596590383181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645999333233064393588787 6968998999849596590383181)
                ·
                  refine ⟨2613374624943598721393693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6968998999849596590383181 2613374624943598721393693)
                  ·
                    refine ⟨980015484353849520522635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613374624943598721393693 980015484353849520522635)
                    ·
                      rfl

theorem cell22_2862860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_2862860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862860 prefixEnd_2862860 := by exact prefixLift 2862860
  have htrace : WordTrace (prefixWord ++ tailWord_2862860) baseStart_2862860 baseEnd_2862860 := by
    simpa [prefixWord, tailWord_2862860, baseEnd_2862860] using wordTrace_append hprefix tailTrace_2862860
  have hstable : (prefixWord ++ tailWord_2862860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862860).length < 2 ^ (prefixWord ++ tailWord_2862860).sum := by decide
  have hdescent : baseEnd_2862860 < baseStart_2862860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862866 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2862866 : Nat := 118140960795 + 2862866 * 2 ^ 59
def prefixEnd_2862866 : Nat := 4983230072969 + 3 ^ 40 * 2862866 * 2
def baseEnd_2862866 : Nat := 980017538276467504872617

theorem tailTrace_2862866 : CollatzResearch.WordTrace tailWord_2862866 prefixEnd_2862866 980017538276467504872617 := by
  unfold tailWord_2862866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26104325311583223857880113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69611534164221930287680301 26104325311583223857880113)
  ·
    refine ⟨19578243983687417893410085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26104325311583223857880113 19578243983687417893410085)
    ·
      refine ⟨3670920746941390855014391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19578243983687417893410085 3670920746941390855014391)
      ·
        refine ⟨5506381120412086282521587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670920746941390855014391 5506381120412086282521587)
        ·
          refine ⟨8259571680618129423782381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506381120412086282521587 8259571680618129423782381)
          ·
            refine ⟨3097339380231798533918393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8259571680618129423782381 3097339380231798533918393)
            ·
              refine ⟨2323004535173848900438795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097339380231798533918393 2323004535173848900438795)
              ·
                refine ⟨3484506802760773350658193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323004535173848900438795 3484506802760773350658193)
                ·
                  refine ⟨2613380102070580012993645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484506802760773350658193 2613380102070580012993645)
                  ·
                    refine ⟨980017538276467504872617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613380102070580012993645 980017538276467504872617)
                    ·
                      rfl

theorem cell22_2862866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2862866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862866 prefixEnd_2862866 := by exact prefixLift 2862866
  have htrace : WordTrace (prefixWord ++ tailWord_2862866) baseStart_2862866 baseEnd_2862866 := by
    simpa [prefixWord, tailWord_2862866, baseEnd_2862866] using wordTrace_append hprefix tailTrace_2862866
  have hstable : (prefixWord ++ tailWord_2862866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862866).length < 2 ^ (prefixWord ++ tailWord_2862866).sum := by decide
  have hdescent : baseEnd_2862866 < baseStart_2862866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862911 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 1, 3]
def baseStart_2862911 : Nat := 118140960795 + 2862911 * 2 ^ 59
def prefixEnd_2862911 : Nat := 4983230072969 + 3 ^ 40 * 2862911 * 2
def baseEnd_2862911 : Nat := 980032942696102387497479

theorem tailTrace_2862911 : CollatzResearch.WordTrace tailWord_2862911 prefixEnd_2862911 980032942696102387497479 := by
  unfold tailWord_2862911
  simp only [CollatzResearch.WordTrace]
  refine ⟨104418942531169868116908587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69612628354113245411272391 104418942531169868116908587)
  ·
    refine ⟨156628413796754802175362881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104418942531169868116908587 156628413796754802175362881)
    ·
      refine ⟨117471310347566101631522161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156628413796754802175362881 117471310347566101631522161)
      ·
        refine ⟨88103482760674576223641621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117471310347566101631522161 88103482760674576223641621)
        ·
          refine ⟨4129850754406620760483201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88103482760674576223641621 4129850754406620760483201)
          ·
            refine ⟨3097388065804965570362401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4129850754406620760483201 3097388065804965570362401)
            ·
              refine ⟨2323041049353724177771801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097388065804965570362401 2323041049353724177771801)
              ·
                refine ⟨1742280787015293133328851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323041049353724177771801 1742280787015293133328851)
                ·
                  refine ⟨2613421180522939699993277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742280787015293133328851 2613421180522939699993277)
                  ·
                    refine ⟨980032942696102387497479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613421180522939699993277 980032942696102387497479)
                    ·
                      rfl

theorem cell22_2862911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_2862911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862911 prefixEnd_2862911 := by exact prefixLift 2862911
  have htrace : WordTrace (prefixWord ++ tailWord_2862911) baseStart_2862911 baseEnd_2862911 := by
    simpa [prefixWord, tailWord_2862911, baseEnd_2862911] using wordTrace_append hprefix tailTrace_2862911
  have hstable : (prefixWord ++ tailWord_2862911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862911).length < 2 ^ (prefixWord ++ tailWord_2862911).sum := by decide
  have hdescent : baseEnd_2862911 < baseStart_2862911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862935 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 6]
def baseStart_2862935 : Nat := 118140960795 + 2862935 * 2 ^ 59
def prefixEnd_2862935 : Nat := 4983230072969 + 3 ^ 40 * 2862935 * 2
def baseEnd_2862935 : Nat := 326680386128858108299135

theorem tailTrace_2862935 : CollatzResearch.WordTrace tailWord_2862935 prefixEnd_2862935 326680386128858108299135 := by
  unfold tailWord_2862935
  simp only [CollatzResearch.WordTrace]
  refine ⟨104419817883082920215782259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69613211922055280143854839 104419817883082920215782259)
  ·
    refine ⟨156629726824624380323673389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104419817883082920215782259 156629726824624380323673389)
    ·
      refine ⟨58736147559234142621377521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156629726824624380323673389 58736147559234142621377521)
      ·
        refine ⟨44052110669425606966033141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58736147559234142621377521 44052110669425606966033141)
        ·
          refine ⟨4129885375258650653065607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44052110669425606966033141 4129885375258650653065607)
          ·
            refine ⟨6194828062887975979598411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129885375258650653065607 6194828062887975979598411)
            ·
              refine ⟨9292242094331963969397617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194828062887975979598411 9292242094331963969397617)
              ·
                refine ⟨6969181570748972977048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9292242094331963969397617 6969181570748972977048213)
                ·
                  refine ⟨326680386128858108299135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6969181570748972977048213 326680386128858108299135)
                  ·
                    rfl

theorem cell22_2862935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 6].length) (baseStart_2862935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862935 prefixEnd_2862935 := by exact prefixLift 2862935
  have htrace : WordTrace (prefixWord ++ tailWord_2862935) baseStart_2862935 baseEnd_2862935 := by
    simpa [prefixWord, tailWord_2862935, baseEnd_2862935] using wordTrace_append hprefix tailTrace_2862935
  have hstable : (prefixWord ++ tailWord_2862935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862935).length < 2 ^ (prefixWord ++ tailWord_2862935).sum := by decide
  have hdescent : baseEnd_2862935 < baseStart_2862935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862952 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_2862952 : Nat := 118140960795 + 2862952 * 2 ^ 59
def prefixEnd_2862952 : Nat := 4983230072969 + 3 ^ 40 * 2862952 * 2
def baseEnd_2862952 : Nat := 326682325944663982407451

theorem tailTrace_2862952 : CollatzResearch.WordTrace tailWord_2862952 prefixEnd_2862952 326682325944663982407451 := by
  unfold tailWord_2862952
  simp only [CollatzResearch.WordTrace]
  refine ⟨52210218962010666059575555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69613625282680888079434073 52210218962010666059575555)
  ·
    refine ⟨78315328443015999089363333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52210218962010666059575555 78315328443015999089363333)
    ·
      refine ⟨14684124083065499829255625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78315328443015999089363333 14684124083065499829255625)
      ·
        refine ⟨11013093062299124871941719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14684124083065499829255625 11013093062299124871941719)
        ·
          refine ⟨16519639593448687307912579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11013093062299124871941719 16519639593448687307912579)
          ·
            refine ⟨24779459390173030961868869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16519639593448687307912579 24779459390173030961868869)
            ·
              refine ⟨4646148635657443305350413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24779459390173030961868869 4646148635657443305350413)
              ·
                refine ⟨1742305738371541239506405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4646148635657443305350413 1742305738371541239506405)
                ·
                  refine ⟨326682325944663982407451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742305738371541239506405 326682325944663982407451)
                  ·
                    rfl

theorem cell22_2862952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_2862952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862952 prefixEnd_2862952 := by exact prefixLift 2862952
  have htrace : WordTrace (prefixWord ++ tailWord_2862952) baseStart_2862952 baseEnd_2862952 := by
    simpa [prefixWord, tailWord_2862952, baseEnd_2862952] using wordTrace_append hprefix tailTrace_2862952
  have hstable : (prefixWord ++ tailWord_2862952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862952).length < 2 ^ (prefixWord ++ tailWord_2862952).sum := by decide
  have hdescent : baseEnd_2862952 < baseStart_2862952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862954 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2862954 : Nat := 118140960795 + 2862954 * 2 ^ 59
def prefixEnd_2862954 : Nat := 4983230072969 + 3 ^ 40 * 2862954 * 2
def baseEnd_2862954 : Nat := 980047662474864608672347

theorem tailTrace_2862954 : CollatzResearch.WordTrace tailWord_2862954 prefixEnd_2862954 980047662474864608672347 := by
  unfold tailWord_2862954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26105127717503521615180979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69613673913342724307149277 26105127717503521615180979)
  ·
    refine ⟨39157691576255282422771469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26105127717503521615180979 39157691576255282422771469)
    ·
      refine ⟨14684134341095730908539301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39157691576255282422771469 14684134341095730908539301)
      ·
        refine ⟨2753275188955449545351119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14684134341095730908539301 2753275188955449545351119)
        ·
          refine ⟨4129912783433174318026679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753275188955449545351119 4129912783433174318026679)
          ·
            refine ⟨6194869175149761477040019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129912783433174318026679 6194869175149761477040019)
            ·
              refine ⟨9292303762724642215560029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194869175149761477040019 9292303762724642215560029)
              ·
                refine ⟨3484613911021740830835011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9292303762724642215560029 3484613911021740830835011)
                ·
                  refine ⟨5226920866532611246252517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484613911021740830835011 5226920866532611246252517)
                  ·
                    refine ⟨980047662474864608672347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5226920866532611246252517 980047662474864608672347)
                    ·
                      rfl

theorem cell22_2862954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2862954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862954 prefixEnd_2862954 := by exact prefixLift 2862954
  have htrace : WordTrace (prefixWord ++ tailWord_2862954) baseStart_2862954 baseEnd_2862954 := by
    simpa [prefixWord, tailWord_2862954, baseEnd_2862954] using wordTrace_append hprefix tailTrace_2862954
  have hstable : (prefixWord ++ tailWord_2862954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862954).length < 2 ^ (prefixWord ++ tailWord_2862954).sum := by decide
  have hdescent : baseEnd_2862954 < baseStart_2862954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862965 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2862965 : Nat := 118140960795 + 2862965 * 2 ^ 59
def prefixEnd_2862965 : Nat := 4983230072969 + 3 ^ 40 * 2862965 * 2
def baseEnd_2862965 : Nat := 980051427999664246647313

theorem tailTrace_2862965 : CollatzResearch.WordTrace tailWord_2862965 prefixEnd_2862965 980051427999664246647313 := by
  unfold tailWord_2862965
  simp only [CollatzResearch.WordTrace]
  refine ⟨104420912072974235339374349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69613941381982823559582899 104420912072974235339374349)
  ·
    refine ⟨39157842027365338252265381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104420912072974235339374349 39157842027365338252265381)
    ·
      refine ⟨7342095380131000922299759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39157842027365338252265381 7342095380131000922299759)
      ·
        refine ⟨11013143070196501383449639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342095380131000922299759 11013143070196501383449639)
        ·
          refine ⟨16519714605294752075174459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11013143070196501383449639 16519714605294752075174459)
          ·
            refine ⟨24779571907942128112761689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16519714605294752075174459 24779571907942128112761689)
            ·
              refine ⟨18584678930956596084571267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24779571907942128112761689 18584678930956596084571267)
              ·
                refine ⟨27877018396434894126856901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18584678930956596084571267 27877018396434894126856901)
                ·
                  refine ⟨5226940949331542648785669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27877018396434894126856901 5226940949331542648785669)
                  ·
                    refine ⟨980051427999664246647313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5226940949331542648785669 980051427999664246647313)
                    ·
                      rfl

theorem cell22_2862965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2862965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862965 prefixEnd_2862965 := by exact prefixLift 2862965
  have htrace : WordTrace (prefixWord ++ tailWord_2862965) baseStart_2862965 baseEnd_2862965 := by
    simpa [prefixWord, tailWord_2862965, baseEnd_2862965] using wordTrace_append hprefix tailTrace_2862965
  have hstable : (prefixWord ++ tailWord_2862965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862965).length < 2 ^ (prefixWord ++ tailWord_2862965).sum := by decide
  have hdescent : baseEnd_2862965 < baseStart_2862965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862984 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_2862984 : Nat := 118140960795 + 2862984 * 2 ^ 59
def prefixEnd_2862984 : Nat := 4983230072969 + 3 ^ 40 * 2862984 * 2
def baseEnd_2862984 : Nat := 980057932087954530422255

theorem tailTrace_2862984 : CollatzResearch.WordTrace tailWord_2862984 prefixEnd_2862984 980057932087954530422255 := by
  unfold tailWord_2862984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52210802529952700792158003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69614403373270267722877337 52210802529952700792158003)
  ·
    refine ⟨78316203794929051188237005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52210802529952700792158003 78316203794929051188237005)
    ·
      refine ⟨29368576423098394195588877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78316203794929051188237005 29368576423098394195588877)
      ·
        refine ⟨11013216158661897823345829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29368576423098394195588877 11013216158661897823345829)
        ·
          refine ⟨2064978029749105841877343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11013216158661897823345829 2064978029749105841877343)
          ·
            refine ⟨3097467044623658762816015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064978029749105841877343 3097467044623658762816015)
            ·
              refine ⟨4646200566935488144224023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097467044623658762816015 4646200566935488144224023)
              ·
                refine ⟨6969300850403232216336035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646200566935488144224023 6969300850403232216336035)
                ·
                  refine ⟨10453951275604848324504053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969300850403232216336035 10453951275604848324504053)
                  ·
                    refine ⟨980057932087954530422255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10453951275604848324504053 980057932087954530422255)
                    ·
                      rfl

theorem cell22_2862984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_2862984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862984 prefixEnd_2862984 := by exact prefixLift 2862984
  have htrace : WordTrace (prefixWord ++ tailWord_2862984) baseStart_2862984 baseEnd_2862984 := by
    simpa [prefixWord, tailWord_2862984, baseEnd_2862984] using wordTrace_append hprefix tailTrace_2862984
  have hstable : (prefixWord ++ tailWord_2862984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862984).length < 2 ^ (prefixWord ++ tailWord_2862984).sum := by decide
  have hdescent : baseEnd_2862984 < baseStart_2862984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862993 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2862993 : Nat := 118140960795 + 2862993 * 2 ^ 59
def prefixEnd_2862993 : Nat := 4983230072969 + 3 ^ 40 * 2862993 * 2
def baseEnd_2862993 : Nat := 980061012971881506947227

theorem tailTrace_2862993 : CollatzResearch.WordTrace tailWord_2862993 prefixEnd_2862993 980061012971881506947227 := by
  unfold tailWord_2862993
  simp only [CollatzResearch.WordTrace]
  refine ⟨104421933316872796121393633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69614622211248530747595755 104421933316872796121393633)
  ·
    refine ⟨78316449987654597091045225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104421933316872796121393633 78316449987654597091045225)
    ·
      refine ⟨58737337490740947818283919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78316449987654597091045225 58737337490740947818283919)
      ·
        refine ⟨88106006236111421727425879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58737337490740947818283919 88106006236111421727425879)
        ·
          refine ⟨132159009354167132591138819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88106006236111421727425879 132159009354167132591138819)
          ·
            refine ⟨198238514031250698886708229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132159009354167132591138819 198238514031250698886708229)
            ·
              refine ⟨37169721380859506041257793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198238514031250698886708229 37169721380859506041257793)
              ·
                refine ⟨27877291035644629530943345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37169721380859506041257793 27877291035644629530943345)
                ·
                  refine ⟨20907968276733472148207509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27877291035644629530943345 20907968276733472148207509)
                  ·
                    refine ⟨980061012971881506947227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20907968276733472148207509 980061012971881506947227)
                    ·
                      rfl

theorem cell22_2862993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2862993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2862993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2862993 prefixEnd_2862993 := by exact prefixLift 2862993
  have htrace : WordTrace (prefixWord ++ tailWord_2862993) baseStart_2862993 baseEnd_2862993 := by
    simpa [prefixWord, tailWord_2862993, baseEnd_2862993] using wordTrace_append hprefix tailTrace_2862993
  have hstable : (prefixWord ++ tailWord_2862993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862993).length < 2 ^ (prefixWord ++ tailWord_2862993).sum := by decide
  have hdescent : baseEnd_2862993 < baseStart_2862993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863025 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 7]
def baseStart_2863025 : Nat := 118140960795 + 2863025 * 2 ^ 59
def prefixEnd_2863025 : Nat := 4983230072969 + 3 ^ 40 * 2863025 * 2
def baseEnd_2863025 : Nat := 326690655741948030049043

theorem tailTrace_2863025 : CollatzResearch.WordTrace tailWord_2863025 prefixEnd_2863025 326690655741948030049043 := by
  unfold tailWord_2863025
  simp only [CollatzResearch.WordTrace]
  refine ⟨104423100452756865586558529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69615400301837910391039019 104423100452756865586558529)
  ·
    refine ⟨78317325339567649189918897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104423100452756865586558529 78317325339567649189918897)
    ·
      refine ⟨58737994004675736892439173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78317325339567649189918897 58737994004675736892439173)
      ·
        refine ⟨11013373875876700667332345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58737994004675736892439173 11013373875876700667332345)
        ·
          refine ⟨8260030406907525500499259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11013373875876700667332345 8260030406907525500499259)
          ·
            refine ⟨12390045610361288250748889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260030406907525500499259 12390045610361288250748889)
            ·
              refine ⟨9292534207770966188061667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12390045610361288250748889 9292534207770966188061667)
              ·
                refine ⟨13938801311656449282092501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9292534207770966188061667 13938801311656449282092501)
                ·
                  refine ⟨326690655741948030049043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13938801311656449282092501 326690655741948030049043)
                  ·
                    rfl

theorem cell22_2863025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_2863025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863025 prefixEnd_2863025 := by exact prefixLift 2863025
  have htrace : WordTrace (prefixWord ++ tailWord_2863025) baseStart_2863025 baseEnd_2863025 := by
    simpa [prefixWord, tailWord_2863025, baseEnd_2863025] using wordTrace_append hprefix tailTrace_2863025
  have hstable : (prefixWord ++ tailWord_2863025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863025).length < 2 ^ (prefixWord ++ tailWord_2863025).sum := by decide
  have hdescent : baseEnd_2863025 < baseStart_2863025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863029 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2863029 : Nat := 118140960795 + 2863029 * 2 ^ 59
def prefixEnd_2863029 : Nat := 4983230072969 + 3 ^ 40 * 2863029 * 2
def baseEnd_2863029 : Nat := 980073336507589413047117

theorem tailTrace_2863029 : CollatzResearch.WordTrace tailWord_2863029 prefixEnd_2863029 980073336507589413047117 := by
  unfold tailWord_2863029
  simp only [CollatzResearch.WordTrace]
  refine ⟨104423246344742374269704141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69615497563161582846469427 104423246344742374269704141)
  ·
    refine ⟨39158717379278390351139053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104423246344742374269704141 39158717379278390351139053)
    ·
      refine ⟨14684519017229396381677145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39158717379278390351139053 14684519017229396381677145)
      ·
        refine ⟨11013389262922047286257859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14684519017229396381677145 11013389262922047286257859)
        ·
          refine ⟨16520083894383070929386789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11013389262922047286257859 16520083894383070929386789)
          ·
            refine ⟨3097515730196825799260023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16520083894383070929386789 3097515730196825799260023)
            ·
              refine ⟨4646273595295238698890035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097515730196825799260023 4646273595295238698890035)
              ·
                refine ⟨6969410392942858048335053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646273595295238698890035 6969410392942858048335053)
                ·
                  refine ⟨2613528897353571768125645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6969410392942858048335053 2613528897353571768125645)
                  ·
                    refine ⟨980073336507589413047117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613528897353571768125645 980073336507589413047117)
                    ·
                      rfl

theorem cell22_2863029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2863029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863029 prefixEnd_2863029 := by exact prefixLift 2863029
  have htrace : WordTrace (prefixWord ++ tailWord_2863029) baseStart_2863029 baseEnd_2863029 := by
    simpa [prefixWord, tailWord_2863029, baseEnd_2863029] using wordTrace_append hprefix tailTrace_2863029
  have hstable : (prefixWord ++ tailWord_2863029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863029).length < 2 ^ (prefixWord ++ tailWord_2863029).sum := by decide
  have hdescent : baseEnd_2863029 < baseStart_2863029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863055 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_2863055 : Nat := 118140960795 + 2863055 * 2 ^ 59
def prefixEnd_2863055 : Nat := 4983230072969 + 3 ^ 40 * 2863055 * 2
def baseEnd_2863055 : Nat := 980082236838934011897037

theorem tailTrace_2863055 : CollatzResearch.WordTrace tailWord_2863055 prefixEnd_2863055 980082236838934011897037 := by
  unfold tailWord_2863055
  simp only [CollatzResearch.WordTrace]
  refine ⟨104424194642648180710150619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69616129761765453806767079 104424194642648180710150619)
  ·
    refine ⟨156636291963972271065225929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104424194642648180710150619 156636291963972271065225929)
    ·
      refine ⟨117477218972979203298919447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156636291963972271065225929 117477218972979203298919447)
      ·
        refine ⟨176215828459468804948379171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117477218972979203298919447 176215828459468804948379171)
        ·
          refine ⟨264323742689203207422568757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176215828459468804948379171 264323742689203207422568757)
          ·
            refine ⟨24780350877112800695865821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264323742689203207422568757 24780350877112800695865821)
            ·
              refine ⟨9292631578917300260949683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24780350877112800695865821 9292631578917300260949683)
              ·
                refine ⟨13938947368375950391424525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9292631578917300260949683 13938947368375950391424525)
                ·
                  refine ⟨5227105263140981396784197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13938947368375950391424525 5227105263140981396784197)
                  ·
                    refine ⟨980082236838934011897037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227105263140981396784197 980082236838934011897037)
                    ·
                      rfl

theorem cell22_2863055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_2863055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863055 prefixEnd_2863055 := by exact prefixLift 2863055
  have htrace : WordTrace (prefixWord ++ tailWord_2863055) baseStart_2863055 baseEnd_2863055 := by
    simpa [prefixWord, tailWord_2863055, baseEnd_2863055] using wordTrace_append hprefix tailTrace_2863055
  have hstable : (prefixWord ++ tailWord_2863055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863055).length < 2 ^ (prefixWord ++ tailWord_2863055).sum := by decide
  have hdescent : baseEnd_2863055 < baseStart_2863055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863087 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 4]
def baseStart_2863087 : Nat := 118140960795 + 2863087 * 2 ^ 59
def prefixEnd_2863087 : Nat := 4983230072969 + 3 ^ 40 * 2863087 * 2
def baseEnd_2863087 : Nat := 326697730364298865032313

theorem tailTrace_2863087 : CollatzResearch.WordTrace tailWord_2863087 prefixEnd_2863087 326697730364298865032313 := by
  unfold tailWord_2863087
  simp only [CollatzResearch.WordTrace]
  refine ⟨104425361778532250175315515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69616907852354833450210343 104425361778532250175315515)
  ·
    refine ⟨156638042667798375262973273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104425361778532250175315515 156638042667798375262973273)
    ·
      refine ⟨117478532000848781447229955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156638042667798375262973273 117478532000848781447229955)
      ·
        refine ⟨176217798001273172170844933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117478532000848781447229955 176217798001273172170844933)
        ·
          refine ⟨33040837125238719782033425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176217798001273172170844933 33040837125238719782033425)
          ·
            refine ⟨24780627843929039836525069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33040837125238719782033425 24780627843929039836525069)
            ·
              refine ⟨9292735441473389938696901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24780627843929039836525069 9292735441473389938696901)
              ·
                refine ⟨1742387895276260613505669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9292735441473389938696901 1742387895276260613505669)
                ·
                  refine ⟨326697730364298865032313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742387895276260613505669 326697730364298865032313)
                  ·
                    rfl

theorem cell22_2863087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 4].length) (baseStart_2863087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863087 prefixEnd_2863087 := by exact prefixLift 2863087
  have htrace : WordTrace (prefixWord ++ tailWord_2863087) baseStart_2863087 baseEnd_2863087 := by
    simpa [prefixWord, tailWord_2863087, baseEnd_2863087] using wordTrace_append hprefix tailTrace_2863087
  have hstable : (prefixWord ++ tailWord_2863087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863087).length < 2 ^ (prefixWord ++ tailWord_2863087).sum := by decide
  have hdescent : baseEnd_2863087 < baseStart_2863087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863100 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_2863100 : Nat := 118140960795 + 2863100 * 2 ^ 59
def prefixEnd_2863100 : Nat := 4983230072969 + 3 ^ 40 * 2863100 * 2
def baseEnd_2863100 : Nat := 980097641258568894521899

theorem tailTrace_2863100 : CollatzResearch.WordTrace tailWord_2863100 prefixEnd_2863100 980097641258568894521899 := by
  unfold tailWord_2863100
  simp only [CollatzResearch.WordTrace]
  refine ⟨52212917963742576697769377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69617223951656768930359169 52212917963742576697769377)
  ·
    refine ⟨39159688472806932523327033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52212917963742576697769377 39159688472806932523327033)
    ·
      refine ⟨29369766354605199392495275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39159688472806932523327033 29369766354605199392495275)
      ·
        refine ⟨44054649531907799088742913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29369766354605199392495275 44054649531907799088742913)
        ·
          refine ⟨33040987148930849316557185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44054649531907799088742913 33040987148930849316557185)
          ·
            refine ⟨24780740361698136987417889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33040987148930849316557185 24780740361698136987417889)
            ·
              refine ⟨18585555271273602740563417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24780740361698136987417889 18585555271273602740563417)
              ·
                refine ⟨13939166453455202055422563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18585555271273602740563417 13939166453455202055422563)
                ·
                  refine ⟨20908749680182803083133845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13939166453455202055422563 20908749680182803083133845)
                  ·
                    refine ⟨980097641258568894521899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20908749680182803083133845 980097641258568894521899)
                    ·
                      rfl

theorem cell22_2863100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_2863100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863100 prefixEnd_2863100 := by exact prefixLift 2863100
  have htrace : WordTrace (prefixWord ++ tailWord_2863100) baseStart_2863100 baseEnd_2863100 := by
    simpa [prefixWord, tailWord_2863100, baseEnd_2863100] using wordTrace_append hprefix tailTrace_2863100
  have hstable : (prefixWord ++ tailWord_2863100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863100).length < 2 ^ (prefixWord ++ tailWord_2863100).sum := by decide
  have hdescent : baseEnd_2863100 < baseStart_2863100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863166 : List Nat := [4, 2, 1, 3, 2, 2, 2, 6]
def baseStart_2863166 : Nat := 118140960795 + 2863166 * 2 ^ 59
def prefixEnd_2863166 : Nat := 4983230072969 + 3 ^ 40 * 2863166 * 2
def baseEnd_2863166 : Nat := 108902248267485191374633

theorem tailTrace_2863166 : CollatzResearch.WordTrace tailWord_2863166 prefixEnd_2863166 108902248267485191374633 := by
  unfold tailWord_2863166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13053530393155755833430169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69618828763497364444960901 13053530393155755833430169)
  ·
    refine ⟨9790147794866816875072627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13053530393155755833430169 9790147794866816875072627)
    ·
      refine ⟨14685221692300225312608941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9790147794866816875072627 14685221692300225312608941)
      ·
        refine ⟨5506958134612584492228353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14685221692300225312608941 5506958134612584492228353)
        ·
          refine ⟨4130218600959438369171265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5506958134612584492228353 4130218600959438369171265)
          ·
            refine ⟨3097663950719578776878449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130218600959438369171265 3097663950719578776878449)
            ·
              refine ⟨2323247963039684082658837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097663950719578776878449 2323247963039684082658837)
              ·
                refine ⟨108902248267485191374633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2323247963039684082658837 108902248267485191374633)
                ·
                  rfl

theorem cell22_2863166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_2863166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863166 prefixEnd_2863166 := by exact prefixLift 2863166
  have htrace : WordTrace (prefixWord ++ tailWord_2863166) baseStart_2863166 baseEnd_2863166 := by
    simpa [prefixWord, tailWord_2863166, baseEnd_2863166] using wordTrace_append hprefix tailTrace_2863166
  have hstable : (prefixWord ++ tailWord_2863166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863166).length < 2 ^ (prefixWord ++ tailWord_2863166).sum := by decide
  have hdescent : baseEnd_2863166 < baseStart_2863166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863207 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2863207 : Nat := 118140960795 + 2863207 * 2 ^ 59
def prefixEnd_2863207 : Nat := 4983230072969 + 3 ^ 40 * 2863207 * 2
def baseEnd_2863207 : Nat := 980134269545256282096571

theorem tailTrace_2863207 : CollatzResearch.WordTrace tailWord_2863207 prefixEnd_2863207 980134269545256282096571 := by
  unfold tailWord_2863207
  simp only [CollatzResearch.WordTrace]
  refine ⟨104429738538097510669683875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69619825692065007113122583 104429738538097510669683875)
  ·
    refine ⟨156644607807146266004525813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104429738538097510669683875 156644607807146266004525813)
    ·
      refine ⟨14685431981919962437924295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156644607807146266004525813 14685431981919962437924295)
      ·
        refine ⟨22028147972879943656886443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14685431981919962437924295 22028147972879943656886443)
        ·
          refine ⟨33042221959319915485329665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22028147972879943656886443 33042221959319915485329665)
          ·
            refine ⟨24781666469489936613997249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33042221959319915485329665 24781666469489936613997249)
            ·
              refine ⟨18586249852117452460497937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24781666469489936613997249 18586249852117452460497937)
              ·
                refine ⟨13939687389088089345373453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18586249852117452460497937 13939687389088089345373453)
                ·
                  refine ⟨5227382770908033504515045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13939687389088089345373453 5227382770908033504515045)
                  ·
                    refine ⟨980134269545256282096571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227382770908033504515045 980134269545256282096571)
                    ·
                      rfl

theorem cell22_2863207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2863207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863207 prefixEnd_2863207 := by exact prefixLift 2863207
  have htrace : WordTrace (prefixWord ++ tailWord_2863207) baseStart_2863207 baseEnd_2863207 := by
    simpa [prefixWord, tailWord_2863207, baseEnd_2863207] using wordTrace_append hprefix tailTrace_2863207
  have hstable : (prefixWord ++ tailWord_2863207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863207).length < 2 ^ (prefixWord ++ tailWord_2863207).sum := by decide
  have hdescent : baseEnd_2863207 < baseStart_2863207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863237 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2863237 : Nat := 118140960795 + 2863237 * 2 ^ 59
def prefixEnd_2863237 : Nat := 4983230072969 + 3 ^ 40 * 2863237 * 2
def baseEnd_2863237 : Nat := 980144539158346203846479

theorem tailTrace_2863237 : CollatzResearch.WordTrace tailWord_2863237 prefixEnd_2863237 980144539158346203846479 := by
  unfold tailWord_2863237
  simp only [CollatzResearch.WordTrace]
  refine ⟨104430832727988825793275965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69620555151992550528850643 104430832727988825793275965)
  ·
    refine ⟨39161562272995809672478487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104430832727988825793275965 39161562272995809672478487)
    ·
      refine ⟨58742343409493714508717731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39161562272995809672478487 58742343409493714508717731)
      ·
        refine ⟨88113515114240571763076597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58742343409493714508717731 88113515114240571763076597)
        ·
          refine ⟨8260642041960053602788431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88113515114240571763076597 8260642041960053602788431)
          ·
            refine ⟨12390963062940080404182647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260642041960053602788431 12390963062940080404182647)
            ·
              refine ⟨18586444594410120606273971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12390963062940080404182647 18586444594410120606273971)
              ·
                refine ⟨27879666891615180909410957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18586444594410120606273971 27879666891615180909410957)
                ·
                  refine ⟨10454875084355692841029109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27879666891615180909410957 10454875084355692841029109)
                  ·
                    refine ⟨980144539158346203846479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454875084355692841029109 980144539158346203846479)
                    ·
                      rfl

theorem cell22_2863237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2863237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863237 prefixEnd_2863237 := by exact prefixLift 2863237
  have htrace : WordTrace (prefixWord ++ tailWord_2863237) baseStart_2863237 baseEnd_2863237 := by
    simpa [prefixWord, tailWord_2863237, baseEnd_2863237] using wordTrace_append hprefix tailTrace_2863237
  have hstable : (prefixWord ++ tailWord_2863237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863237).length < 2 ^ (prefixWord ++ tailWord_2863237).sum := by decide
  have hdescent : baseEnd_2863237 < baseStart_2863237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863256 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_2863256 : Nat := 118140960795 + 2863256 * 2 ^ 59
def prefixEnd_2863256 : Nat := 4983230072969 + 3 ^ 40 * 2863256 * 2
def baseEnd_2863256 : Nat := 326717014415545495873807

theorem tailTrace_2863256 : CollatzResearch.WordTrace tailWord_2863256 prefixEnd_2863256 326717014415545495873807 := by
  unfold tailWord_2863256
  simp only [CollatzResearch.WordTrace]
  refine ⟨52215762857459996019108811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69621017143279994692145081 52215762857459996019108811)
  ·
    refine ⟨78323644286189994028663217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52215762857459996019108811 78323644286189994028663217)
    ·
      refine ⟨58742733214642495521497413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78323644286189994028663217 58742733214642495521497413)
      ·
        refine ⟨11014262477745467910280765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58742733214642495521497413 11014262477745467910280765)
        ·
          refine ⟨4130348429154550466355287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11014262477745467910280765 4130348429154550466355287)
          ·
            refine ⟨6195522643731825699532931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130348429154550466355287 6195522643731825699532931)
            ·
              refine ⟨9293283965597738549299397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195522643731825699532931 9293283965597738549299397)
              ·
                refine ⟨1742490743549575977993637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9293283965597738549299397 1742490743549575977993637)
                ·
                  refine ⟨326717014415545495873807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742490743549575977993637 326717014415545495873807)
                  ·
                    rfl

theorem cell22_2863256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_2863256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863256 prefixEnd_2863256 := by exact prefixLift 2863256
  have htrace : WordTrace (prefixWord ++ tailWord_2863256) baseStart_2863256 baseEnd_2863256 := by
    simpa [prefixWord, tailWord_2863256, baseEnd_2863256] using wordTrace_append hprefix tailTrace_2863256
  have hstable : (prefixWord ++ tailWord_2863256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863256).length < 2 ^ (prefixWord ++ tailWord_2863256).sum := by decide
  have hdescent : baseEnd_2863256 < baseStart_2863256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863271 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2863271 : Nat := 118140960795 + 2863271 * 2 ^ 59
def prefixEnd_2863271 : Nat := 4983230072969 + 3 ^ 40 * 2863271 * 2
def baseEnd_2863271 : Nat := 980156178053181448496375

theorem tailTrace_2863271 : CollatzResearch.WordTrace tailWord_2863271 prefixEnd_2863271 980156178053181448496375 := by
  unfold tailWord_2863271
  simp only [CollatzResearch.WordTrace]
  refine ⟨104432072809865649600013667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69621381873243766400009111 104432072809865649600013667)
  ·
    refine ⟨156648109214798474400020501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104432072809865649600013667 156648109214798474400020501)
    ·
      refine ⟨7342880119443678487500961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156648109214798474400020501 7342880119443678487500961)
      ·
        refine ⟨5507160089582758865625721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7342880119443678487500961 5507160089582758865625721)
        ·
          refine ⟨4130370067187069149219291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507160089582758865625721 4130370067187069149219291)
          ·
            refine ⟨6195555100780603723828937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130370067187069149219291 6195555100780603723828937)
            ·
              refine ⟨4646666325585452792871703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6195555100780603723828937 4646666325585452792871703)
              ·
                refine ⟨6969999488378179189307555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646666325585452792871703 6969999488378179189307555)
                ·
                  refine ⟨10454999232567268783961333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969999488378179189307555 10454999232567268783961333)
                  ·
                    refine ⟨980156178053181448496375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454999232567268783961333 980156178053181448496375)
                    ·
                      rfl

theorem cell22_2863271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2863271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863271 prefixEnd_2863271 := by exact prefixLift 2863271
  have htrace : WordTrace (prefixWord ++ tailWord_2863271) baseStart_2863271 baseEnd_2863271 := by
    simpa [prefixWord, tailWord_2863271, baseEnd_2863271] using wordTrace_append hprefix tailTrace_2863271
  have hstable : (prefixWord ++ tailWord_2863271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863271).length < 2 ^ (prefixWord ++ tailWord_2863271).sum := by decide
  have hdescent : baseEnd_2863271 < baseStart_2863271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863357 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 8]
def baseStart_2863357 : Nat := 118140960795 + 2863357 * 2 ^ 59
def prefixEnd_2863357 : Nat := 4983230072969 + 3 ^ 40 * 2863357 * 2
def baseEnd_2863357 : Nat := 326728539203568630282037

theorem tailTrace_2863357 : CollatzResearch.WordTrace tailWord_2863357 prefixEnd_2863357 326728539203568630282037 := by
  unfold tailWord_2863357
  simp only [CollatzResearch.WordTrace]
  refine ⟨104435209487554086287644325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69623472991702724191762883 104435209487554086287644325)
  ·
    refine ⟨19581601778916391178933311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104435209487554086287644325 19581601778916391178933311)
    ·
      refine ⟨29372402668374586768399967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19581601778916391178933311 29372402668374586768399967)
      ·
        refine ⟨44058604002561880152599951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29372402668374586768399967 44058604002561880152599951)
        ·
          refine ⟨66087906003842820228899927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44058604002561880152599951 66087906003842820228899927)
          ·
            refine ⟨99131859005764230343349891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66087906003842820228899927 99131859005764230343349891)
            ·
              refine ⟨148697788508646345515024837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99131859005764230343349891 148697788508646345515024837)
              ·
                refine ⟨27880835345371189784067157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148697788508646345515024837 27880835345371189784067157)
                ·
                  refine ⟨326728539203568630282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27880835345371189784067157 326728539203568630282037)
                  ·
                    rfl

theorem cell22_2863357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_2863357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863357 prefixEnd_2863357 := by exact prefixLift 2863357
  have htrace : WordTrace (prefixWord ++ tailWord_2863357) baseStart_2863357 baseEnd_2863357 := by
    simpa [prefixWord, tailWord_2863357, baseEnd_2863357] using wordTrace_append hprefix tailTrace_2863357
  have hstable : (prefixWord ++ tailWord_2863357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863357).length < 2 ^ (prefixWord ++ tailWord_2863357).sum := by decide
  have hdescent : baseEnd_2863357 < baseStart_2863357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863359 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 1, 4]
def baseStart_2863359 : Nat := 118140960795 + 2863359 * 2 ^ 59
def prefixEnd_2863359 : Nat := 4983230072969 + 3 ^ 40 * 2863359 * 2
def baseEnd_2863359 : Nat := 980186302251578552296105

theorem tailTrace_2863359 : CollatzResearch.WordTrace tailWord_2863359 prefixEnd_2863359 980186302251578552296105 := by
  unfold tailWord_2863359
  simp only [CollatzResearch.WordTrace]
  refine ⟨104435282433546840629217131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69623521622364560419478087 104435282433546840629217131)
  ·
    refine ⟨156652923650320260943825697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104435282433546840629217131 156652923650320260943825697)
    ·
      refine ⟨117489692737740195707869273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156652923650320260943825697 117489692737740195707869273)
      ·
        refine ⟨88117269553305146780901955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117489692737740195707869273 88117269553305146780901955)
        ·
          refine ⟨132175904329957720171352933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88117269553305146780901955 132175904329957720171352933)
          ·
            refine ⟨24782982061867072532128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132175904329957720171352933 24782982061867072532128675)
            ·
              refine ⟨37174473092800608798193013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24782982061867072532128675 37174473092800608798193013)
              ·
                refine ⟨3485106852450057074830595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37174473092800608798193013 3485106852450057074830595)
                ·
                  refine ⟨5227660278675085612245893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485106852450057074830595 5227660278675085612245893)
                  ·
                    refine ⟨980186302251578552296105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227660278675085612245893 980186302251578552296105)
                    ·
                      rfl

theorem cell22_2863359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_2863359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863359 prefixEnd_2863359 := by exact prefixLift 2863359
  have htrace : WordTrace (prefixWord ++ tailWord_2863359) baseStart_2863359 baseEnd_2863359 := by
    simpa [prefixWord, tailWord_2863359, baseEnd_2863359] using wordTrace_append hprefix tailTrace_2863359
  have hstable : (prefixWord ++ tailWord_2863359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863359).length < 2 ^ (prefixWord ++ tailWord_2863359).sum := by decide
  have hdescent : baseEnd_2863359 < baseStart_2863359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863367 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 1, 3]
def baseStart_2863367 : Nat := 118140960795 + 2863367 * 2 ^ 59
def prefixEnd_2863367 : Nat := 4983230072969 + 3 ^ 40 * 2863367 * 2
def baseEnd_2863367 : Nat := 980189040815069198096081

theorem tailTrace_2863367 : CollatzResearch.WordTrace tailWord_2863367 prefixEnd_2863367 980189040815069198096081 := by
  unfold tailWord_2863367
  simp only [CollatzResearch.WordTrace]
  refine ⟨104435574217517857995508355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69623716145011905330338903 104435574217517857995508355)
  ·
    refine ⟨156653361326276786993262533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104435574217517857995508355 156653361326276786993262533)
    ·
      refine ⟨29372505248676897561236725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156653361326276786993262533 29372505248676897561236725)
      ·
        refine ⟨2753672367063459146365943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29372505248676897561236725 2753672367063459146365943)
        ·
          refine ⟨4130508550595188719548915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753672367063459146365943 4130508550595188719548915)
          ·
            refine ⟨6195762825892783079323373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130508550595188719548915 6195762825892783079323373)
            ·
              refine ⟨2323411059709793654746265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6195762825892783079323373 2323411059709793654746265)
              ·
                refine ⟨1742558294782345241059699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323411059709793654746265 1742558294782345241059699)
                ·
                  refine ⟨2613837442173517861589549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742558294782345241059699 2613837442173517861589549)
                  ·
                    refine ⟨980189040815069198096081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613837442173517861589549 980189040815069198096081)
                    ·
                      rfl

theorem cell22_2863367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_2863367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863367 prefixEnd_2863367 := by exact prefixLift 2863367
  have htrace : WordTrace (prefixWord ++ tailWord_2863367) baseStart_2863367 baseEnd_2863367 := by
    simpa [prefixWord, tailWord_2863367, baseEnd_2863367] using wordTrace_append hprefix tailTrace_2863367
  have hstable : (prefixWord ++ tailWord_2863367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863367).length < 2 ^ (prefixWord ++ tailWord_2863367).sum := by decide
  have hdescent : baseEnd_2863367 < baseStart_2863367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863387 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_2863387 : Nat := 118140960795 + 2863387 * 2 ^ 59
def prefixEnd_2863387 : Nat := 4983230072969 + 3 ^ 40 * 2863387 * 2
def baseEnd_2863387 : Nat := 980195887223795812596019

theorem tailTrace_2863387 : CollatzResearch.WordTrace tailWord_2863387 prefixEnd_2863387 980195887223795812596019 := by
  unfold tailWord_2863387
  simp only [CollatzResearch.WordTrace]
  refine ⟨104436303677445401411236415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69624202451630267607490943 104436303677445401411236415)
  ·
    refine ⟨156654455516168102116854623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104436303677445401411236415 156654455516168102116854623)
    ·
      refine ⟨234981683274252153175281935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156654455516168102116854623 234981683274252153175281935)
      ·
        refine ⟨352472524911378229762922903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234981683274252153175281935 352472524911378229762922903)
        ·
          refine ⟨528708787367067344644384355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352472524911378229762922903 528708787367067344644384355)
          ·
            refine ⟨793063181050601016966576533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528708787367067344644384355 793063181050601016966576533)
            ·
              refine ⟨37174836611746922670308275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 793063181050601016966576533 37174836611746922670308275)
              ·
                refine ⟨55762254917620384005462413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37174836611746922670308275 55762254917620384005462413)
                ·
                  refine ⟨20910845594107644002048405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55762254917620384005462413 20910845594107644002048405)
                  ·
                    refine ⟨980195887223795812596019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20910845594107644002048405 980195887223795812596019)
                    ·
                      rfl

theorem cell22_2863387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_2863387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863387 prefixEnd_2863387 := by exact prefixLift 2863387
  have htrace : WordTrace (prefixWord ++ tailWord_2863387) baseStart_2863387 baseEnd_2863387 := by
    simpa [prefixWord, tailWord_2863387, baseEnd_2863387] using wordTrace_append hprefix tailTrace_2863387
  have hstable : (prefixWord ++ tailWord_2863387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863387).length < 2 ^ (prefixWord ++ tailWord_2863387).sum := by decide
  have hdescent : baseEnd_2863387 < baseStart_2863387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863404 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2863404 : Nat := 118140960795 + 2863404 * 2 ^ 59
def prefixEnd_2863404 : Nat := 4983230072969 + 3 ^ 40 * 2863404 * 2
def baseEnd_2863404 : Nat := 980201706671213434920967

theorem tailTrace_2863404 : CollatzResearch.WordTrace tailWord_2863404 prefixEnd_2863404 980201706671213434920967 := by
  unfold tailWord_2863404
  simp only [CollatzResearch.WordTrace]
  refine ⟨52218461859191906657302633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69624615812255875543070177 52218461859191906657302633)
  ·
    refine ⟨39163846394393929992976975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52218461859191906657302633 39163846394393929992976975)
    ·
      refine ⟨58745769591590894989465463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39163846394393929992976975 58745769591590894989465463)
      ·
        refine ⟨88118654387386342484198195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58745769591590894989465463 88118654387386342484198195)
        ·
          refine ⟨132177981581079513726297293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88118654387386342484198195 132177981581079513726297293)
          ·
            refine ⟨49566743092904817647361485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132177981581079513726297293 49566743092904817647361485)
            ·
              refine ⟨18587528659839306617760557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49566743092904817647361485 18587528659839306617760557)
              ·
                refine ⟨6970323247439739981660209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18587528659839306617760557 6970323247439739981660209)
                ·
                  refine ⟨5227742435579804986245157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6970323247439739981660209 5227742435579804986245157)
                  ·
                    refine ⟨980201706671213434920967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227742435579804986245157 980201706671213434920967)
                    ·
                      rfl

theorem cell22_2863404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2863404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863404 prefixEnd_2863404 := by exact prefixLift 2863404
  have htrace : WordTrace (prefixWord ++ tailWord_2863404) baseStart_2863404 baseEnd_2863404 := by
    simpa [prefixWord, tailWord_2863404, baseEnd_2863404] using wordTrace_append hprefix tailTrace_2863404
  have hstable : (prefixWord ++ tailWord_2863404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863404).length < 2 ^ (prefixWord ++ tailWord_2863404).sum := by decide
  have hdescent : baseEnd_2863404 < baseStart_2863404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863511 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 1, 4]
def baseStart_2863511 : Nat := 118140960795 + 2863511 * 2 ^ 59
def prefixEnd_2863511 : Nat := 4983230072969 + 3 ^ 40 * 2863511 * 2
def baseEnd_2863511 : Nat := 980238334957900822495639

theorem tailTrace_2863511 : CollatzResearch.WordTrace tailWord_2863511 prefixEnd_2863511 980238334957900822495639 := by
  unfold tailWord_2863511
  simp only [CollatzResearch.WordTrace]
  refine ⟨104440826328996170588750387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69627217552664113725833591 104440826328996170588750387)
  ·
    refine ⟨156661239493494255883125581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104440826328996170588750387 156661239493494255883125581)
    ·
      refine ⟨58747964810060345956172093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156661239493494255883125581 58747964810060345956172093)
      ·
        refine ⟨22030486803772629733564535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58747964810060345956172093 22030486803772629733564535)
        ·
          refine ⟨33045730205658944600346803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22030486803772629733564535 33045730205658944600346803)
          ·
            refine ⟨49568595308488416900520205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33045730205658944600346803 49568595308488416900520205)
            ·
              refine ⟨18588223240683156337695077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49568595308488416900520205 18588223240683156337695077)
              ·
                refine ⟨3485291857628091813317827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18588223240683156337695077 3485291857628091813317827)
                ·
                  refine ⟨5227937786442137719976741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485291857628091813317827 5227937786442137719976741)
                  ·
                    refine ⟨980238334957900822495639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227937786442137719976741 980238334957900822495639)
                    ·
                      rfl

theorem cell22_2863511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_2863511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863511 prefixEnd_2863511 := by exact prefixLift 2863511
  have htrace : WordTrace (prefixWord ++ tailWord_2863511) baseStart_2863511 baseEnd_2863511 := by
    simpa [prefixWord, tailWord_2863511, baseEnd_2863511] using wordTrace_append hprefix tailTrace_2863511
  have hstable : (prefixWord ++ tailWord_2863511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863511).length < 2 ^ (prefixWord ++ tailWord_2863511).sum := by decide
  have hdescent : baseEnd_2863511 < baseStart_2863511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863569 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2863569 : Nat := 118140960795 + 2863569 * 2 ^ 59
def prefixEnd_2863569 : Nat := 4983230072969 + 3 ^ 40 * 2863569 * 2
def baseEnd_2863569 : Nat := 980258189543208004545461

theorem tailTrace_2863569 : CollatzResearch.WordTrace tailWord_2863569 prefixEnd_2863569 980258189543208004545461 := by
  unfold tailWord_2863569
  simp only [CollatzResearch.WordTrace]
  refine ⟨104442941762786046494361761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69628627841857364329574507 104442941762786046494361761)
  ·
    refine ⟨78332206322089534870771321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104442941762786046494361761 78332206322089534870771321)
    ·
      refine ⟨58749154741567151153078491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78332206322089534870771321 58749154741567151153078491)
      ·
        refine ⟨88123732112350726729617737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58749154741567151153078491 88123732112350726729617737)
        ·
          refine ⟨66092799084263045047213303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88123732112350726729617737 66092799084263045047213303)
          ·
            refine ⟨99139198626394567570819955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66092799084263045047213303 99139198626394567570819955)
            ·
              refine ⟨148708797939591851356229933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99139198626394567570819955 148708797939591851356229933)
              ·
                refine ⟨55765799227346944258586225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148708797939591851356229933 55765799227346944258586225)
                ·
                  refine ⟨41824349420510208193939669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55765799227346944258586225 41824349420510208193939669)
                  ·
                    refine ⟨980258189543208004545461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41824349420510208193939669 980258189543208004545461)
                    ·
                      rfl

theorem cell22_2863569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2863569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863569 prefixEnd_2863569 := by exact prefixLift 2863569
  have htrace : WordTrace (prefixWord ++ tailWord_2863569) baseStart_2863569 baseEnd_2863569 := by
    simpa [prefixWord, tailWord_2863569, baseEnd_2863569] using wordTrace_append hprefix tailTrace_2863569
  have hstable : (prefixWord ++ tailWord_2863569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863569).length < 2 ^ (prefixWord ++ tailWord_2863569).sum := by decide
  have hdescent : baseEnd_2863569 < baseStart_2863569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863573 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2863573 : Nat := 118140960795 + 2863573 * 2 ^ 59
def prefixEnd_2863573 : Nat := 4983230072969 + 3 ^ 40 * 2863573 * 2
def baseEnd_2863573 : Nat := 980259558824953327445449

theorem tailTrace_2863573 : CollatzResearch.WordTrace tailWord_2863573 prefixEnd_2863573 980259558824953327445449 := by
  unfold tailWord_2863573
  simp only [CollatzResearch.WordTrace]
  refine ⟨104443087654771555177507373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69628725103181036785004915 104443087654771555177507373)
  ·
    refine ⟨39166157870539333191565265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104443087654771555177507373 39166157870539333191565265)
    ·
      refine ⟨29374618402904499893673949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39166157870539333191565265 29374618402904499893673949)
      ·
        refine ⟨11015481901089187460127731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29374618402904499893673949 11015481901089187460127731)
        ·
          refine ⟨16523222851633781190191597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11015481901089187460127731 16523222851633781190191597)
          ·
            refine ⟨6196208569362667946321849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16523222851633781190191597 6196208569362667946321849)
            ·
              refine ⟨4647156427022000959741387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196208569362667946321849 4647156427022000959741387)
              ·
                refine ⟨6970734640533001439612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647156427022000959741387 6970734640533001439612081)
                ·
                  refine ⟨5228050980399751079709061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6970734640533001439612081 5228050980399751079709061)
                  ·
                    refine ⟨980259558824953327445449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228050980399751079709061 980259558824953327445449)
                    ·
                      rfl

theorem cell22_2863573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2863573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863573 prefixEnd_2863573 := by exact prefixLift 2863573
  have htrace : WordTrace (prefixWord ++ tailWord_2863573) baseStart_2863573 baseEnd_2863573 := by
    simpa [prefixWord, tailWord_2863573, baseEnd_2863573] using wordTrace_append hprefix tailTrace_2863573
  have hstable : (prefixWord ++ tailWord_2863573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863573).length < 2 ^ (prefixWord ++ tailWord_2863573).sum := by decide
  have hdescent : baseEnd_2863573 < baseStart_2863573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863605 : List Nat := [1, 3, 5, 1, 2, 2, 1, 7]
def baseStart_2863605 : Nat := 118140960795 + 2863605 * 2 ^ 59
def prefixEnd_2863605 : Nat := 4983230072969 + 3 ^ 40 * 2863605 * 2
def baseEnd_2863605 : Nat := 108918945897657323405039

theorem tailTrace_2863605 : CollatzResearch.WordTrace tailWord_2863605 prefixEnd_2863605 108918945897657323405039 := by
  unfold tailWord_2863605
  simp only [CollatzResearch.WordTrace]
  refine ⟨104444254790655624642672269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69629503193770416428448179 104444254790655624642672269)
  ·
    refine ⟨39166595546495859241002101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104444254790655624642672269 39166595546495859241002101)
    ·
      refine ⟨3671868332483986803843947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39166595546495859241002101 3671868332483986803843947)
      ·
        refine ⟨5507802498725980205765921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671868332483986803843947 5507802498725980205765921)
        ·
          refine ⟨4130851874044485154324441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507802498725980205765921 4130851874044485154324441)
          ·
            refine ⟨3098138905533363865743331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130851874044485154324441 3098138905533363865743331)
            ·
              refine ⟨4647208358300045798614997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098138905533363865743331 4647208358300045798614997)
              ·
                refine ⟨108918945897657323405039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4647208358300045798614997 108918945897657323405039)
                ·
                  rfl

theorem cell22_2863605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 7].length) (baseStart_2863605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863605 prefixEnd_2863605 := by exact prefixLift 2863605
  have htrace : WordTrace (prefixWord ++ tailWord_2863605) baseStart_2863605 baseEnd_2863605 := by
    simpa [prefixWord, tailWord_2863605, baseEnd_2863605] using wordTrace_append hprefix tailTrace_2863605
  have hstable : (prefixWord ++ tailWord_2863605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863605).length < 2 ^ (prefixWord ++ tailWord_2863605).sum := by decide
  have hdescent : baseEnd_2863605 < baseStart_2863605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863620 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2863620 : Nat := 118140960795 + 2863620 * 2 ^ 59
def prefixEnd_2863620 : Nat := 4983230072969 + 3 ^ 40 * 2863620 * 2
def baseEnd_2863620 : Nat := 980275647885460871520305

theorem tailTrace_2863620 : CollatzResearch.WordTrace tailWord_2863620 prefixEnd_2863620 980275647885460871520305 := by
  unfold tailWord_2863620
  simp only [CollatzResearch.WordTrace]
  refine ⟨52222400942800641102234157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69629867923734188136312209 52222400942800641102234157)
  ·
    refine ⟨19583400353550240413337809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52222400942800641102234157 19583400353550240413337809)
    ·
      refine ⟨14687550265162680310003357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19583400353550240413337809 14687550265162680310003357)
      ·
        refine ⟨5507831349436005116251259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14687550265162680310003357 5507831349436005116251259)
        ·
          refine ⟨8261747024154007674376889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5507831349436005116251259 8261747024154007674376889)
          ·
            refine ⟨6196310268115505755782667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8261747024154007674376889 6196310268115505755782667)
            ·
              refine ⟨9294465402173258633674001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196310268115505755782667 9294465402173258633674001)
              ·
                refine ⟨6970849051629943975255501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9294465402173258633674001 6970849051629943975255501)
                ·
                  refine ⟨2614068394361228990720813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6970849051629943975255501 2614068394361228990720813)
                  ·
                    refine ⟨980275647885460871520305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2614068394361228990720813 980275647885460871520305)
                    ·
                      rfl

theorem cell22_2863620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2863620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863620 prefixEnd_2863620 := by exact prefixLift 2863620
  have htrace : WordTrace (prefixWord ++ tailWord_2863620) baseStart_2863620 baseEnd_2863620 := by
    simpa [prefixWord, tailWord_2863620, baseEnd_2863620] using wordTrace_append hprefix tailTrace_2863620
  have hstable : (prefixWord ++ tailWord_2863620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863620).length < 2 ^ (prefixWord ++ tailWord_2863620).sum := by decide
  have hdescent : baseEnd_2863620 < baseStart_2863620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863691 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_2863691 : Nat := 118140960795 + 2863691 * 2 ^ 59
def prefixEnd_2863691 : Nat := 4983230072969 + 3 ^ 40 * 2863691 * 2
def baseEnd_2863691 : Nat := 980299952636440352995087

theorem tailTrace_2863691 : CollatzResearch.WordTrace tailWord_2863691 prefixEnd_2863691 980299952636440352995087 := by
  unfold tailWord_2863691
  simp only [CollatzResearch.WordTrace]
  refine ⟨104447391468344061330302927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69631594312229374220201951 104447391468344061330302927)
  ·
    refine ⟨156671087202516091995454391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104447391468344061330302927 156671087202516091995454391)
    ·
      refine ⟨235006630803774137993181587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156671087202516091995454391 235006630803774137993181587)
      ·
        refine ⟨352509946205661206989772381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235006630803774137993181587 352509946205661206989772381)
        ·
          refine ⟨132191229827122952621164643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352509946205661206989772381 132191229827122952621164643)
          ·
            refine ⟨198286844740684428931746965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132191229827122952621164643 198286844740684428931746965)
            ·
              refine ⟨9294695847219582606175639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198286844740684428931746965 9294695847219582606175639)
              ·
                refine ⟨13942043770829373909263459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9294695847219582606175639 13942043770829373909263459)
                ·
                  refine ⟨20913065656244060863895189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13942043770829373909263459 20913065656244060863895189)
                  ·
                    refine ⟨980299952636440352995087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20913065656244060863895189 980299952636440352995087)
                    ·
                      rfl

theorem cell22_2863691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_2863691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863691 prefixEnd_2863691 := by exact prefixLift 2863691
  have htrace : WordTrace (prefixWord ++ tailWord_2863691) baseStart_2863691 baseEnd_2863691 := by
    simpa [prefixWord, tailWord_2863691, baseEnd_2863691] using wordTrace_append hprefix tailTrace_2863691
  have hstable : (prefixWord ++ tailWord_2863691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863691).length < 2 ^ (prefixWord ++ tailWord_2863691).sum := by decide
  have hdescent : baseEnd_2863691 < baseStart_2863691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863736 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_2863736 : Nat := 118140960795 + 2863736 * 2 ^ 59
def prefixEnd_2863736 : Nat := 4983230072969 + 3 ^ 40 * 2863736 * 2
def baseEnd_2863736 : Nat := 980315357056075235619949

theorem tailTrace_2863736 : CollatzResearch.WordTrace tailWord_2863736 prefixEnd_2863736 980315357056075235619949 := by
  unfold tailWord_2863736
  simp only [CollatzResearch.WordTrace]
  refine ⟨52224516376590517007845531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69632688502120689343794041 52224516376590517007845531)
  ·
    refine ⟨78336774564885775511768297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52224516376590517007845531 78336774564885775511768297)
    ·
      refine ⟨58752580923664331633826223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78336774564885775511768297 58752580923664331633826223)
      ·
        refine ⟨88128871385496497450739335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58752580923664331633826223 88128871385496497450739335)
        ·
          refine ⟨132193307078244746176109003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88128871385496497450739335 132193307078244746176109003)
          ·
            refine ⟨198289960617367119264163505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132193307078244746176109003 198289960617367119264163505)
            ·
              refine ⟨148717470463025339448122629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198289960617367119264163505 148717470463025339448122629)
              ·
                refine ⟨27884525711817251146522993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148717470463025339448122629 27884525711817251146522993)
                ·
                  refine ⟨20913394283862938359892245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27884525711817251146522993 20913394283862938359892245)
                  ·
                    refine ⟨980315357056075235619949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20913394283862938359892245 980315357056075235619949)
                    ·
                      rfl

theorem cell22_2863736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_2863736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863736 prefixEnd_2863736 := by exact prefixLift 2863736
  have htrace : WordTrace (prefixWord ++ tailWord_2863736) baseStart_2863736 baseEnd_2863736 := by
    simpa [prefixWord, tailWord_2863736, baseEnd_2863736] using wordTrace_append hprefix tailTrace_2863736
  have hstable : (prefixWord ++ tailWord_2863736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863736).length < 2 ^ (prefixWord ++ tailWord_2863736).sum := by decide
  have hdescent : baseEnd_2863736 < baseStart_2863736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863845 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_2863845 : Nat := 118140960795 + 2863845 * 2 ^ 59
def prefixEnd_2863845 : Nat := 4983230072969 + 3 ^ 40 * 2863845 * 2
def baseEnd_2863845 : Nat := 980352669983635284644615

theorem tailTrace_2863845 : CollatzResearch.WordTrace tailWord_2863845 prefixEnd_2863845 980352669983635284644615 := by
  unfold tailWord_2863845
  simp only [CollatzResearch.WordTrace]
  refine ⟨104453008309786145631408989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69635338873190763754272659 104453008309786145631408989)
  ·
    refine ⟨39169878116169804611778371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104453008309786145631408989 39169878116169804611778371)
    ·
      refine ⟨58754817174254706917667557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39169878116169804611778371 58754817174254706917667557)
      ·
        refine ⟨11016528220172757547062667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58754817174254706917667557 11016528220172757547062667)
        ·
          refine ⟨16524792330259136320594001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016528220172757547062667 16524792330259136320594001)
          ·
            refine ⟨12393594247694352240445501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16524792330259136320594001 12393594247694352240445501)
            ·
              refine ⟨4647597842885382090167063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12393594247694352240445501 4647597842885382090167063)
              ·
                refine ⟨6971396764328073135250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647597842885382090167063 6971396764328073135250595)
                ·
                  refine ⟨10457095146492109702875893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971396764328073135250595 10457095146492109702875893)
                  ·
                    refine ⟨980352669983635284644615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10457095146492109702875893 980352669983635284644615)
                    ·
                      rfl

theorem cell22_2863845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_2863845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863845 prefixEnd_2863845 := by exact prefixLift 2863845
  have htrace : WordTrace (prefixWord ++ tailWord_2863845) baseStart_2863845 baseEnd_2863845 := by
    simpa [prefixWord, tailWord_2863845, baseEnd_2863845] using wordTrace_append hprefix tailTrace_2863845
  have hstable : (prefixWord ++ tailWord_2863845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863845).length < 2 ^ (prefixWord ++ tailWord_2863845).sum := by decide
  have hdescent : baseEnd_2863845 < baseStart_2863845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863980 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2863980 : Nat := 118140960795 + 2863980 * 2 ^ 59
def prefixEnd_2863980 : Nat := 4983230072969 + 3 ^ 40 * 2863980 * 2
def baseEnd_2863980 : Nat := 980398883242539932519201

theorem tailTrace_2863980 : CollatzResearch.WordTrace tailWord_2863980 prefixEnd_2863980 980398883242539932519201 := by
  unfold tailWord_2863980
  simp only [CollatzResearch.WordTrace]
  refine ⟨52228966082148531843786697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69638621442864709125048929 52228966082148531843786697)
  ·
    refine ⟨39171724561611398882840023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52228966082148531843786697 39171724561611398882840023)
    ·
      refine ⟨58757586842417098324260035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39171724561611398882840023 58757586842417098324260035)
      ·
        refine ⟨88136380263625647486390053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58757586842417098324260035 88136380263625647486390053)
        ·
          refine ⟨16525571299429808903698135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88136380263625647486390053 16525571299429808903698135)
          ·
            refine ⟨24788356949144713355547203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16525571299429808903698135 24788356949144713355547203)
            ·
              refine ⟨37182535423717070033320805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24788356949144713355547203 37182535423717070033320805)
              ·
                refine ⟨6971725391946950631247651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37182535423717070033320805 6971725391946950631247651)
                ·
                  refine ⟨10457588087920425946871477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971725391946950631247651 10457588087920425946871477)
                  ·
                    refine ⟨980398883242539932519201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10457588087920425946871477 980398883242539932519201)
                    ·
                      rfl

theorem cell22_2863980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2863980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863980 prefixEnd_2863980 := by exact prefixLift 2863980
  have htrace : WordTrace (prefixWord ++ tailWord_2863980) baseStart_2863980 baseEnd_2863980 := by
    simpa [prefixWord, tailWord_2863980, baseEnd_2863980] using wordTrace_append hprefix tailTrace_2863980
  have hstable : (prefixWord ++ tailWord_2863980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863980).length < 2 ^ (prefixWord ++ tailWord_2863980).sum := by decide
  have hdescent : baseEnd_2863980 < baseStart_2863980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863995 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_2863995 : Nat := 118140960795 + 2863995 * 2 ^ 59
def prefixEnd_2863995 : Nat := 4983230072969 + 3 ^ 40 * 2863995 * 2
def baseEnd_2863995 : Nat := 980404018049084893394155

theorem tailTrace_2863995 : CollatzResearch.WordTrace tailWord_2863995 prefixEnd_2863995 980404018049084893394155 := by
  unfold tailWord_2863995
  simp only [CollatzResearch.WordTrace]
  refine ⟨104458479259242721249369439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69638986172828480832912959 104458479259242721249369439)
  ·
    refine ⟨156687718888864081874054159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104458479259242721249369439 156687718888864081874054159)
    ·
      refine ⟨235031578333296122811081239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156687718888864081874054159 235031578333296122811081239)
      ·
        refine ⟨352547367499944184216621859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235031578333296122811081239 352547367499944184216621859)
        ·
          refine ⟨528821051249916276324932789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352547367499944184216621859 528821051249916276324932789)
          ·
            refine ⟨49576973554679650905462449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 528821051249916276324932789 49576973554679650905462449)
            ·
              refine ⟨37182730166009738179096837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49576973554679650905462449 37182730166009738179096837)
              ·
                refine ⟨6971761906126825908580657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37182730166009738179096837 6971761906126825908580657)
                ·
                  refine ⟨5228821429595119431435493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971761906126825908580657 5228821429595119431435493)
                  ·
                    refine ⟨980404018049084893394155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228821429595119431435493 980404018049084893394155)
                    ·
                      rfl

theorem cell22_2863995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_2863995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2863995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2863995 prefixEnd_2863995 := by exact prefixLift 2863995
  have htrace : WordTrace (prefixWord ++ tailWord_2863995) baseStart_2863995 baseEnd_2863995 := by
    simpa [prefixWord, tailWord_2863995, baseEnd_2863995] using wordTrace_append hprefix tailTrace_2863995
  have hstable : (prefixWord ++ tailWord_2863995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863995).length < 2 ^ (prefixWord ++ tailWord_2863995).sum := by decide
  have hdescent : baseEnd_2863995 < baseStart_2863995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864055 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 7]
def baseStart_2864055 : Nat := 118140960795 + 2864055 * 2 ^ 59
def prefixEnd_2864055 : Nat := 4983230072969 + 3 ^ 40 * 2864055 * 2
def baseEnd_2864055 : Nat := 326808185758421578964657

theorem tailTrace_2864055 : CollatzResearch.WordTrace tailWord_2864055 prefixEnd_2864055 326808185758421578964657 := by
  unfold tailWord_2864055
  simp only [CollatzResearch.WordTrace]
  refine ⟨104460667639025351496553619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69640445092683567664369079 104460667639025351496553619)
  ·
    refine ⟨156691001458538027244830429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104460667639025351496553619 156691001458538027244830429)
    ·
      refine ⟨58759125546951760216811411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156691001458538027244830429 58759125546951760216811411)
      ·
        refine ⟨88138688320427640325217117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58759125546951760216811411 88138688320427640325217117)
        ·
          refine ⟨33052008120160365121956419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88138688320427640325217117 33052008120160365121956419)
          ·
            refine ⟨49578012180240547682934629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33052008120160365121956419 49578012180240547682934629)
            ·
              refine ⟨9295877283795102690550243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49578012180240547682934629 9295877283795102690550243)
              ·
                refine ⟨13943815925692654035825365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9295877283795102690550243 13943815925692654035825365)
                ·
                  refine ⟨326808185758421578964657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13943815925692654035825365 326808185758421578964657)
                  ·
                    rfl

theorem cell22_2864055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_2864055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864055 prefixEnd_2864055 := by exact prefixLift 2864055
  have htrace : WordTrace (prefixWord ++ tailWord_2864055) baseStart_2864055 baseEnd_2864055 := by
    simpa [prefixWord, tailWord_2864055, baseEnd_2864055] using wordTrace_append hprefix tailTrace_2864055
  have hstable : (prefixWord ++ tailWord_2864055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864055).length < 2 ^ (prefixWord ++ tailWord_2864055).sum := by decide
  have hdescent : baseEnd_2864055 < baseStart_2864055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864100 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_2864100 : Nat := 118140960795 + 2864100 * 2 ^ 59
def prefixEnd_2864100 : Nat := 4983230072969 + 3 ^ 40 * 2864100 * 2
def baseEnd_2864100 : Nat := 326813320564966539839611

theorem tailTrace_2864100 : CollatzResearch.WordTrace tailWord_2864100 prefixEnd_2864100 326813320564966539839611 := by
  unfold tailWord_2864100
  simp only [CollatzResearch.WordTrace]
  refine ⟨52231154461931162090970877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69641539282574882787961169 52231154461931162090970877)
  ·
    refine ⟨19586682923224185784114079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52231154461931162090970877 19586682923224185784114079)
    ·
      refine ⟨29380024384836278676171119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19586682923224185784114079 29380024384836278676171119)
      ·
        refine ⟨44070036577254418014256679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29380024384836278676171119 44070036577254418014256679)
        ·
          refine ⟨66105054865881627021385019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44070036577254418014256679 66105054865881627021385019)
          ·
            refine ⟨99157582298822440532077529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66105054865881627021385019 99157582298822440532077529)
            ·
              refine ⟨74368186724116830399058147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99157582298822440532077529 74368186724116830399058147)
              ·
                refine ⟨111552280086175245598587221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74368186724116830399058147 111552280086175245598587221)
                ·
                  refine ⟨326813320564966539839611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111552280086175245598587221 326813320564966539839611)
                  ·
                    rfl

theorem cell22_2864100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_2864100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864100 prefixEnd_2864100 := by exact prefixLift 2864100
  have htrace : WordTrace (prefixWord ++ tailWord_2864100) baseStart_2864100 baseEnd_2864100 := by
    simpa [prefixWord, tailWord_2864100, baseEnd_2864100] using wordTrace_append hprefix tailTrace_2864100
  have hstable : (prefixWord ++ tailWord_2864100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864100).length < 2 ^ (prefixWord ++ tailWord_2864100).sum := by decide
  have hdescent : baseEnd_2864100 < baseStart_2864100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864110 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2864110 : Nat := 118140960795 + 2864110 * 2 ^ 59
def prefixEnd_2864110 : Nat := 4983230072969 + 3 ^ 40 * 2864110 * 2
def baseEnd_2864110 : Nat := 980443384899262926768803

theorem tailTrace_2864110 : CollatzResearch.WordTrace tailWord_2864110 prefixEnd_2864110 980443384899262926768803 := by
  unfold tailWord_2864110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057834206728261986225723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69641782435884063926537189 13057834206728261986225723)
  ·
    refine ⟨19586751310092392979338585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13057834206728261986225723 19586751310092392979338585)
    ·
      refine ⟨14690063482569294734503939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19586751310092392979338585 14690063482569294734503939)
      ·
        refine ⟨22035095223853942101755909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14690063482569294734503939 22035095223853942101755909)
        ·
          refine ⟨4131580354472614144079233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22035095223853942101755909 4131580354472614144079233)
          ·
            refine ⟨3098685265854460608059425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131580354472614144079233 3098685265854460608059425)
            ·
              refine ⟨2324013949390845456044569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098685265854460608059425 2324013949390845456044569)
              ·
                refine ⟨1743010462043134092033427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324013949390845456044569 1743010462043134092033427)
                ·
                  refine ⟨2614515693064701138050141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743010462043134092033427 2614515693064701138050141)
                  ·
                    refine ⟨980443384899262926768803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2614515693064701138050141 980443384899262926768803)
                    ·
                      rfl

theorem cell22_2864110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2864110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864110 prefixEnd_2864110 := by exact prefixLift 2864110
  have htrace : WordTrace (prefixWord ++ tailWord_2864110) baseStart_2864110 baseEnd_2864110 := by
    simpa [prefixWord, tailWord_2864110, baseEnd_2864110] using wordTrace_append hprefix tailTrace_2864110
  have hstable : (prefixWord ++ tailWord_2864110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864110).length < 2 ^ (prefixWord ++ tailWord_2864110).sum := by decide
  have hdescent : baseEnd_2864110 < baseStart_2864110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864145 : List Nat := [1, 2, 2, 1, 1, 2, 1, 12]
def baseStart_2864145 : Nat := 118140960795 + 2864145 * 2 ^ 59
def prefixEnd_2864145 : Nat := 4983230072969 + 3 ^ 40 * 2864145 * 2
def baseEnd_2864145 : Nat := 108939485123837166904855

theorem tailTrace_2864145 : CollatzResearch.WordTrace tailWord_2864145 prefixEnd_2864145 108939485123837166904855 := by
  unfold tailWord_2864145
  simp only [CollatzResearch.WordTrace]
  refine ⟨104463950208699296867329889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69642633472466197911553259 104463950208699296867329889)
  ·
    refine ⟨78347962656524472650497417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104463950208699296867329889 78347962656524472650497417)
    ·
      refine ⟨58760971992393354487873063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78347962656524472650497417 58760971992393354487873063)
      ·
        refine ⟨88141457988590031731809595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58760971992393354487873063 88141457988590031731809595)
        ·
          refine ⟨132212186982885047597714393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88141457988590031731809595 132212186982885047597714393)
          ·
            refine ⟨99159140237163785698285795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132212186982885047597714393 99159140237163785698285795)
            ·
              refine ⟨148738710355745678547428693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99159140237163785698285795 148738710355745678547428693)
              ·
                refine ⟨108939485123837166904855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 148738710355745678547428693 108939485123837166904855)
                ·
                  rfl

theorem cell22_2864145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 12].length) (baseStart_2864145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864145 prefixEnd_2864145 := by exact prefixLift 2864145
  have htrace : WordTrace (prefixWord ++ tailWord_2864145) baseStart_2864145 baseEnd_2864145 := by
    simpa [prefixWord, tailWord_2864145, baseEnd_2864145] using wordTrace_append hprefix tailTrace_2864145
  have hstable : (prefixWord ++ tailWord_2864145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864145).length < 2 ^ (prefixWord ++ tailWord_2864145).sum := by decide
  have hdescent : baseEnd_2864145 < baseStart_2864145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864151 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 4]
def baseStart_2864151 : Nat := 118140960795 + 2864151 * 2 ^ 59
def prefixEnd_2864151 : Nat := 4983230072969 + 3 ^ 40 * 2864151 * 2
def baseEnd_2864151 : Nat := 326819140012384162164559

theorem tailTrace_2864151 : CollatzResearch.WordTrace tailWord_2864151 prefixEnd_2864151 326819140012384162164559 := by
  unfold tailWord_2864151
  simp only [CollatzResearch.WordTrace]
  refine ⟨104464169046677559892048307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69642779364451706594698871 104464169046677559892048307)
  ·
    refine ⟨156696253570016339838072461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104464169046677559892048307 156696253570016339838072461)
    ·
      refine ⟨58761095088756127439277173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156696253570016339838072461 58761095088756127439277173)
      ·
        refine ⟨5508852664570886947432235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58761095088756127439277173 5508852664570886947432235)
        ·
          refine ⟨8263278996856330421148353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508852664570886947432235 8263278996856330421148353)
          ·
            refine ⟨6197459247642247815861265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8263278996856330421148353 6197459247642247815861265)
            ·
              refine ⟨4648094435731685861895949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197459247642247815861265 4648094435731685861895949)
              ·
                refine ⟨1743035413399382198210981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4648094435731685861895949 1743035413399382198210981)
                ·
                  refine ⟨326819140012384162164559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743035413399382198210981 326819140012384162164559)
                  ·
                    rfl

theorem cell22_2864151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 4].length) (baseStart_2864151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864151 prefixEnd_2864151 := by exact prefixLift 2864151
  have htrace : WordTrace (prefixWord ++ tailWord_2864151) baseStart_2864151 baseEnd_2864151 := by
    simpa [prefixWord, tailWord_2864151, baseEnd_2864151] using wordTrace_append hprefix tailTrace_2864151
  have hstable : (prefixWord ++ tailWord_2864151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864151).length < 2 ^ (prefixWord ++ tailWord_2864151).sum := by decide
  have hdescent : baseEnd_2864151 < baseStart_2864151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864162 : List Nat := [3, 3, 1, 1, 1, 4, 9]
def baseStart_2864162 : Nat := 118140960795 + 2864162 * 2 ^ 59
def prefixEnd_2864162 : Nat := 4983230072969 + 3 ^ 40 * 2864162 * 2
def baseEnd_2864162 : Nat := 36313377243035263869209

theorem tailTrace_2864162 : CollatzResearch.WordTrace tailWord_2864162 prefixEnd_2864162 36313377243035263869209 := by
  unfold tailWord_2864162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26116142562409427192674685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69643046833091805847132493 26116142562409427192674685)
  ·
    refine ⟨9793553460903535197253007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26116142562409427192674685 9793553460903535197253007)
    ·
      refine ⟨14690330191355302795879511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9793553460903535197253007 14690330191355302795879511)
      ·
        refine ⟨22035495287032954193819267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14690330191355302795879511 22035495287032954193819267)
        ·
          refine ⟨33053242930549431290728901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22035495287032954193819267 33053242930549431290728901)
          ·
            refine ⟨6197483049478018367011669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33053242930549431290728901 6197483049478018367011669)
            ·
              refine ⟨36313377243035263869209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6197483049478018367011669 36313377243035263869209)
              ·
                rfl

theorem cell22_2864162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 9].length) (baseStart_2864162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864162 prefixEnd_2864162 := by exact prefixLift 2864162
  have htrace : WordTrace (prefixWord ++ tailWord_2864162) baseStart_2864162 baseEnd_2864162 := by
    simpa [prefixWord, tailWord_2864162, baseEnd_2864162] using wordTrace_append hprefix tailTrace_2864162
  have hstable : (prefixWord ++ tailWord_2864162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864162).length < 2 ^ (prefixWord ++ tailWord_2864162).sum := by decide
  have hdescent : baseEnd_2864162 < baseStart_2864162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864252 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_2864252 : Nat := 118140960795 + 2864252 * 2 ^ 59
def prefixEnd_2864252 : Nat := 4983230072969 + 3 ^ 40 * 2864252 * 2
def baseEnd_2864252 : Nat := 326830664800407296572789

theorem tailTrace_2864252 : CollatzResearch.WordTrace tailWord_2864252 prefixEnd_2864252 326830664800407296572789 := by
  unfold tailWord_2864252
  simp only [CollatzResearch.WordTrace]
  refine ⟨52233926409655827070737505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69645235212874436094316673 52233926409655827070737505)
  ·
    refine ⟨39175444807241870303053129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52233926409655827070737505 39175444807241870303053129)
    ·
      refine ⟨29381583605431402727289847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39175444807241870303053129 29381583605431402727289847)
      ·
        refine ⟨44072375408147104090934771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29381583605431402727289847 44072375408147104090934771)
        ·
          refine ⟨66108563112220656136402157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44072375408147104090934771 66108563112220656136402157)
          ·
            refine ⟨24790711167082746051150809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66108563112220656136402157 24790711167082746051150809)
            ·
              refine ⟨18593033375312059538363107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24790711167082746051150809 18593033375312059538363107)
              ·
                refine ⟨27889550062968089307544661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18593033375312059538363107 27889550062968089307544661)
                ·
                  refine ⟨326830664800407296572789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27889550062968089307544661 326830664800407296572789)
                  ·
                    rfl

theorem cell22_2864252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_2864252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864252 prefixEnd_2864252 := by exact prefixLift 2864252
  have htrace : WordTrace (prefixWord ++ tailWord_2864252) baseStart_2864252 baseEnd_2864252 := by
    simpa [prefixWord, tailWord_2864252, baseEnd_2864252] using wordTrace_append hprefix tailTrace_2864252
  have hstable : (prefixWord ++ tailWord_2864252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864252).length < 2 ^ (prefixWord ++ tailWord_2864252).sum := by decide
  have hdescent : baseEnd_2864252 < baseStart_2864252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864312 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_2864312 : Nat := 118140960795 + 2864312 * 2 ^ 59
def prefixEnd_2864312 : Nat := 4983230072969 + 3 ^ 40 * 2864312 * 2
def baseEnd_2864312 : Nat := 980512533627401733218183

theorem tailTrace_2864312 : CollatzResearch.WordTrace tailWord_2864312 prefixEnd_2864312 980512533627401733218183 := by
  unfold tailWord_2864312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52235020599547142194329595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69646694132729522925772793 52235020599547142194329595)
  ·
    refine ⟨78352530899320713291494393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52235020599547142194329595 78352530899320713291494393)
    ·
      refine ⟨58764398174490534968620795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78352530899320713291494393 58764398174490534968620795)
      ·
        refine ⟨88146597261735802452931193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58764398174490534968620795 88146597261735802452931193)
        ·
          refine ⟨66109947946301851839698395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88146597261735802452931193 66109947946301851839698395)
          ·
            refine ⟨99164921919452777759547593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66109947946301851839698395 99164921919452777759547593)
            ·
              refine ⟨74373691439589583319660695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99164921919452777759547593 74373691439589583319660695)
              ·
                refine ⟨111560537159384374979491043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74373691439589583319660695 111560537159384374979491043)
                ·
                  refine ⟨167340805739076562469236565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111560537159384374979491043 167340805739076562469236565)
                  ·
                    refine ⟨980512533627401733218183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167340805739076562469236565 980512533627401733218183)
                    ·
                      rfl

theorem cell22_2864312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_2864312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864312 prefixEnd_2864312 := by exact prefixLift 2864312
  have htrace : WordTrace (prefixWord ++ tailWord_2864312) baseStart_2864312 baseEnd_2864312 := by
    simpa [prefixWord, tailWord_2864312, baseEnd_2864312] using wordTrace_append hprefix tailTrace_2864312
  have hstable : (prefixWord ++ tailWord_2864312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864312).length < 2 ^ (prefixWord ++ tailWord_2864312).sum := by decide
  have hdescent : baseEnd_2864312 < baseStart_2864312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864316 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2864316 : Nat := 118140960795 + 2864316 * 2 ^ 59
def prefixEnd_2864316 : Nat := 4983230072969 + 3 ^ 40 * 2864316 * 2
def baseEnd_2864316 : Nat := 980513902909147056118171

theorem tailTrace_2864316 : CollatzResearch.WordTrace tailWord_2864316 prefixEnd_2864316 980513902909147056118171 := by
  unfold tailWord_2864316
  simp only [CollatzResearch.WordTrace]
  refine ⟨52235093545539896535902401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69646791394053195381203201 52235093545539896535902401)
  ·
    refine ⟨39176320159154922401926801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52235093545539896535902401 39176320159154922401926801)
    ·
      refine ⟨29382240119366191801445101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39176320159154922401926801 29382240119366191801445101)
      ·
        refine ⟨11018340044762321925541913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29382240119366191801445101 11018340044762321925541913)
        ·
          refine ⟨8263755033571741444156435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11018340044762321925541913 8263755033571741444156435)
          ·
            refine ⟨12395632550357612166234653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263755033571741444156435 12395632550357612166234653)
            ·
              refine ⟨4648362206384104562337995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12395632550357612166234653 4648362206384104562337995)
              ·
                refine ⟨6972543309576156843506993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648362206384104562337995 6972543309576156843506993)
                ·
                  refine ⟨5229407482182117632630245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972543309576156843506993 5229407482182117632630245)
                  ·
                    refine ⟨980513902909147056118171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5229407482182117632630245 980513902909147056118171)
                    ·
                      rfl

theorem cell22_2864316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2864316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864316 prefixEnd_2864316 := by exact prefixLift 2864316
  have htrace : WordTrace (prefixWord ++ tailWord_2864316) baseStart_2864316 baseEnd_2864316 := by
    simpa [prefixWord, tailWord_2864316, baseEnd_2864316] using wordTrace_append hprefix tailTrace_2864316
  have hstable : (prefixWord ++ tailWord_2864316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864316).length < 2 ^ (prefixWord ++ tailWord_2864316).sum := by decide
  have hdescent : baseEnd_2864316 < baseStart_2864316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864455 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 4]
def baseStart_2864455 : Nat := 118140960795 + 2864455 * 2 ^ 59
def prefixEnd_2864455 : Nat := 4983230072969 + 3 ^ 40 * 2864455 * 2
def baseEnd_2864455 : Nat := 326853828483265675630915

theorem tailTrace_2864455 : CollatzResearch.WordTrace tailWord_2864455 prefixEnd_2864455 326853828483265675630915 := by
  unfold tailWord_2864455
  simp only [CollatzResearch.WordTrace]
  refine ⟨104475256837576219811114819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69650171225050813207409879 104475256837576219811114819)
  ·
    refine ⟨156712885256364329716672229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104475256837576219811114819 156712885256364329716672229)
    ·
      refine ⟨29383665985568311821876043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156712885256364329716672229 29383665985568311821876043)
      ·
        refine ⟨44075498978352467732814065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29383665985568311821876043 44075498978352467732814065)
        ·
          refine ⟨33056624233764350799610549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44075498978352467732814065 33056624233764350799610549)
          ·
            refine ⟨3099058521915407887463489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33056624233764350799610549 3099058521915407887463489)
            ·
              refine ⟨2324293891436555915597617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099058521915407887463489 2324293891436555915597617)
              ·
                refine ⟨1743220418577416936698213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324293891436555915597617 1743220418577416936698213)
                ·
                  refine ⟨326853828483265675630915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743220418577416936698213 326853828483265675630915)
                  ·
                    rfl

theorem cell22_2864455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 4].length) (baseStart_2864455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864455 prefixEnd_2864455 := by exact prefixLift 2864455
  have htrace : WordTrace (prefixWord ++ tailWord_2864455) baseStart_2864455 baseEnd_2864455 := by
    simpa [prefixWord, tailWord_2864455, baseEnd_2864455] using wordTrace_append hprefix tailTrace_2864455
  have hstable : (prefixWord ++ tailWord_2864455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864455).length < 2 ^ (prefixWord ++ tailWord_2864455).sum := by decide
  have hdescent : baseEnd_2864455 < baseStart_2864455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864479 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_2864479 : Nat := 118140960795 + 2864479 * 2 ^ 59
def prefixEnd_2864479 : Nat := 4983230072969 + 3 ^ 40 * 2864479 * 2
def baseEnd_2864479 : Nat := 980569701140268964292671

theorem tailTrace_2864479 : CollatzResearch.WordTrace tailWord_2864479 prefixEnd_2864479 980569701140268964292671 := by
  unfold tailWord_2864479
  simp only [CollatzResearch.WordTrace]
  refine ⟨104476132189489271909988491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69650754792992847939992327 104476132189489271909988491)
  ·
    refine ⟨156714198284233907864982737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104476132189489271909988491 156714198284233907864982737)
    ·
      refine ⟨117535648713175430898737053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156714198284233907864982737 117535648713175430898737053)
      ·
        refine ⟨44075868267440786587026395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117535648713175430898737053 44075868267440786587026395)
        ·
          refine ⟨66113802401161179880539593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44075868267440786587026395 66113802401161179880539593)
          ·
            refine ⟨49585351800870884910404695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66113802401161179880539593 49585351800870884910404695)
            ·
              refine ⟨74378027701306327365607043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49585351800870884910404695 74378027701306327365607043)
              ·
                refine ⟨111567041551959491048410565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74378027701306327365607043 111567041551959491048410565)
                ·
                  refine ⟨20918820290992404571576981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111567041551959491048410565 20918820290992404571576981)
                  ·
                    refine ⟨980569701140268964292671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20918820290992404571576981 980569701140268964292671)
                    ·
                      rfl

theorem cell22_2864479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_2864479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864479 prefixEnd_2864479 := by exact prefixLift 2864479
  have htrace : WordTrace (prefixWord ++ tailWord_2864479) baseStart_2864479 baseEnd_2864479 := by
    simpa [prefixWord, tailWord_2864479, baseEnd_2864479] using wordTrace_append hprefix tailTrace_2864479
  have hstable : (prefixWord ++ tailWord_2864479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864479).length < 2 ^ (prefixWord ++ tailWord_2864479).sum := by decide
  have hdescent : baseEnd_2864479 < baseStart_2864479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864515 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 1, 3]
def baseStart_2864515 : Nat := 118140960795 + 2864515 * 2 ^ 59
def prefixEnd_2864515 : Nat := 4983230072969 + 3 ^ 40 * 2864515 * 2
def baseEnd_2864515 : Nat := 980582024675976870392561

theorem tailTrace_2864515 : CollatzResearch.WordTrace tailWord_2864515 prefixEnd_2864515 980582024675976870392561 := by
  unfold tailWord_2864515
  simp only [CollatzResearch.WordTrace]
  refine ⟨104477445217358850058298999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69651630144905900038865999 104477445217358850058298999)
  ·
    refine ⟨156716167826038275087448499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104477445217358850058298999 156716167826038275087448499)
    ·
      refine ⟨235074251739057412631172749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156716167826038275087448499 235074251739057412631172749)
      ·
        refine ⟨88152844402146529736689781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235074251739057412631172749 88152844402146529736689781)
        ·
          refine ⟨8264329162701237162814667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88152844402146529736689781 8264329162701237162814667)
          ·
            refine ⟨12396493744051855744222001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264329162701237162814667 12396493744051855744222001)
            ·
              refine ⟨9297370308038891808166501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12396493744051855744222001 9297370308038891808166501)
              ·
                refine ⟨1743256932757292214031219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9297370308038891808166501 1743256932757292214031219)
                ·
                  refine ⟨2614885399135938321046829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743256932757292214031219 2614885399135938321046829)
                  ·
                    refine ⟨980582024675976870392561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2614885399135938321046829 980582024675976870392561)
                    ·
                      rfl

theorem cell22_2864515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 3].length) (baseStart_2864515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864515 prefixEnd_2864515 := by exact prefixLift 2864515
  have htrace : WordTrace (prefixWord ++ tailWord_2864515) baseStart_2864515 baseEnd_2864515 := by
    simpa [prefixWord, tailWord_2864515, baseEnd_2864515] using wordTrace_append hprefix tailTrace_2864515
  have hstable : (prefixWord ++ tailWord_2864515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864515).length < 2 ^ (prefixWord ++ tailWord_2864515).sum := by decide
  have hdescent : baseEnd_2864515 < baseStart_2864515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864601 : List Nat := [1, 2, 1, 2, 4, 2, 2, 8]
def baseStart_2864601 : Nat := 118140960795 + 2864601 * 2 ^ 59
def prefixEnd_2864601 : Nat := 4983230072969 + 3 ^ 40 * 2864601 * 2
def baseEnd_2864601 : Nat := 108956829359277923638033

theorem tailTrace_2864601 : CollatzResearch.WordTrace tailWord_2864601 prefixEnd_2864601 108956829359277923638033 := by
  unfold tailWord_2864601
  simp only [CollatzResearch.WordTrace]
  refine ⟨104480581895047286745929657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69653721263364857830619771 104480581895047286745929657)
  ·
    refine ⟨78360436421285465059447243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104480581895047286745929657 78360436421285465059447243)
    ·
      refine ⟨117540654631928197589170865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78360436421285465059447243 117540654631928197589170865)
      ·
        refine ⟨88155490973946148191878149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117540654631928197589170865 88155490973946148191878149)
        ·
          refine ⟨16529154557614902785977153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88155490973946148191878149 16529154557614902785977153)
          ·
            refine ⟨12396865918211177089482865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16529154557614902785977153 12396865918211177089482865)
            ·
              refine ⟨9297649438658382817112149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12396865918211177089482865 9297649438658382817112149)
              ·
                refine ⟨108956829359277923638033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9297649438658382817112149 108956829359277923638033)
                ·
                  rfl

theorem cell22_2864601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 8].length) (baseStart_2864601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864601 prefixEnd_2864601 := by exact prefixLift 2864601
  have htrace : WordTrace (prefixWord ++ tailWord_2864601) baseStart_2864601 baseEnd_2864601 := by
    simpa [prefixWord, tailWord_2864601, baseEnd_2864601] using wordTrace_append hprefix tailTrace_2864601
  have hstable : (prefixWord ++ tailWord_2864601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864601).length < 2 ^ (prefixWord ++ tailWord_2864601).sum := by decide
  have hdescent : baseEnd_2864601 < baseStart_2864601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864618 : List Nat := [3, 1, 3, 1, 5, 9]
def baseStart_2864618 : Nat := 118140960795 + 2864618 * 2 ^ 59
def prefixEnd_2864618 : Nat := 4983230072969 + 3 ^ 40 * 2864618 * 2
def baseEnd_2864618 : Nat := 12106386218282949815645

theorem tailTrace_2864618 : CollatzResearch.WordTrace tailWord_2864618 prefixEnd_2864618 12106386218282949815645 := by
  unfold tailWord_2864618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26120300483996424662324627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69654134623990465766199005 26120300483996424662324627)
  ·
    refine ⟨39180450725994636993486941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26120300483996424662324627 39180450725994636993486941)
    ·
      refine ⟨14692669022247988872557603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39180450725994636993486941 14692669022247988872557603)
      ·
        refine ⟨22039003533371983308836405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14692669022247988872557603 22039003533371983308836405)
        ·
          refine ⟨2066156581253623435203413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22039003533371983308836405 2066156581253623435203413)
          ·
            refine ⟨12106386218282949815645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2066156581253623435203413 12106386218282949815645)
            ·
              rfl

theorem cell22_2864618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 9].length) (baseStart_2864618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864618 prefixEnd_2864618 := by exact prefixLift 2864618
  have htrace : WordTrace (prefixWord ++ tailWord_2864618) baseStart_2864618 baseEnd_2864618 := by
    simpa [prefixWord, tailWord_2864618, baseEnd_2864618] using wordTrace_append hprefix tailTrace_2864618
  have hstable : (prefixWord ++ tailWord_2864618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864618).length < 2 ^ (prefixWord ++ tailWord_2864618).sum := by decide
  have hdescent : baseEnd_2864618 < baseStart_2864618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864633 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_2864633 : Nat := 118140960795 + 2864633 * 2 ^ 59
def prefixEnd_2864633 : Nat := 4983230072969 + 3 ^ 40 * 2864633 * 2
def baseEnd_2864633 : Nat := 980622418487463895942199

theorem tailTrace_2864633 : CollatzResearch.WordTrace tailWord_2864633 prefixEnd_2864633 980622418487463895942199 := by
  unfold tailWord_2864633
  simp only [CollatzResearch.WordTrace]
  refine ⟨104481749030931356211094553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69654499353954237474063035 104481749030931356211094553)
  ·
    refine ⟨78361311773198517158320915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104481749030931356211094553 78361311773198517158320915)
    ·
      refine ⟨117541967659797775737481373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78361311773198517158320915 117541967659797775737481373)
      ·
        refine ⟨44078237872424165901555515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117541967659797775737481373 44078237872424165901555515)
        ·
          refine ⟨66117356808636248852333273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44078237872424165901555515 66117356808636248852333273)
          ·
            refine ⟨49588017606477186639249955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66117356808636248852333273 49588017606477186639249955)
            ·
              refine ⟨74382026409715779958874933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49588017606477186639249955 74382026409715779958874933)
              ·
                refine ⟨6973314975910854371144525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74382026409715779958874933 6973314975910854371144525)
                ·
                  refine ⟨2614993115966570389179197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6973314975910854371144525 2614993115966570389179197)
                  ·
                    refine ⟨980622418487463895942199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2614993115966570389179197 980622418487463895942199)
                    ·
                      rfl

theorem cell22_2864633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_2864633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864633 prefixEnd_2864633 := by exact prefixLift 2864633
  have htrace : WordTrace (prefixWord ++ tailWord_2864633) baseStart_2864633 baseEnd_2864633 := by
    simpa [prefixWord, tailWord_2864633, baseEnd_2864633] using wordTrace_append hprefix tailTrace_2864633
  have hstable : (prefixWord ++ tailWord_2864633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864633).length < 2 ^ (prefixWord ++ tailWord_2864633).sum := by decide
  have hdescent : baseEnd_2864633 < baseStart_2864633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864650 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2864650 : Nat := 118140960795 + 2864650 * 2 ^ 59
def prefixEnd_2864650 : Nat := 4983230072969 + 3 ^ 40 * 2864650 * 2
def baseEnd_2864650 : Nat := 980628237934881518267147

theorem tailTrace_2864650 : CollatzResearch.WordTrace tailWord_2864650 prefixEnd_2864650 980628237934881518267147 := by
  unfold tailWord_2864650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26120592267967442028615851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69654912714579845409642269 26120592267967442028615851)
  ·
    refine ⟨39180888401951163042923777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26120592267967442028615851 39180888401951163042923777)
    ·
      refine ⟨29385666301463372282192833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39180888401951163042923777 29385666301463372282192833)
      ·
        refine ⟨22039249726097529211644625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29385666301463372282192833 22039249726097529211644625)
        ·
          refine ⟨16529437294573146908733469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22039249726097529211644625 16529437294573146908733469)
          ·
            refine ⟨6198538985464930090775051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16529437294573146908733469 6198538985464930090775051)
            ·
              refine ⟨9297808478197395136162577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198538985464930090775051 9297808478197395136162577)
              ·
                refine ⟨6973356358648046352121933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297808478197395136162577 6973356358648046352121933)
                ·
                  refine ⟨2615008634493017382045725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6973356358648046352121933 2615008634493017382045725)
                  ·
                    refine ⟨980628237934881518267147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615008634493017382045725 980628237934881518267147)
                    ·
                      rfl

theorem cell22_2864650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2864650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864650 prefixEnd_2864650 := by exact prefixLift 2864650
  have htrace : WordTrace (prefixWord ++ tailWord_2864650) baseStart_2864650 baseEnd_2864650 := by
    simpa [prefixWord, tailWord_2864650, baseEnd_2864650] using wordTrace_append hprefix tailTrace_2864650
  have hstable : (prefixWord ++ tailWord_2864650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864650).length < 2 ^ (prefixWord ++ tailWord_2864650).sum := by decide
  have hdescent : baseEnd_2864650 < baseStart_2864650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864680 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_2864680 : Nat := 118140960795 + 2864680 * 2 ^ 59
def prefixEnd_2864680 : Nat := 4983230072969 + 3 ^ 40 * 2864680 * 2
def baseEnd_2864680 : Nat := 326879502515990480005685

theorem tailTrace_2864680 : CollatzResearch.WordTrace tailWord_2864680 prefixEnd_2864680 326879502515990480005685 := by
  unfold tailWord_2864680
  simp only [CollatzResearch.WordTrace]
  refine ⟨52241731630880541619027747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69655642174507388825370329 52241731630880541619027747)
  ·
    refine ⟨78362597446320812428541621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52241731630880541619027747 78362597446320812428541621)
    ·
      refine ⟨7346493510592576165175777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78362597446320812428541621 7346493510592576165175777)
      ·
        refine ⟨5509870132944432123881833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7346493510592576165175777 5509870132944432123881833)
        ·
          refine ⟨4132402599708324092911375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5509870132944432123881833 4132402599708324092911375)
          ·
            refine ⟨6198603899562486139367063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132402599708324092911375 6198603899562486139367063)
            ·
              refine ⟨9297905849343729209050595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198603899562486139367063 9297905849343729209050595)
              ·
                refine ⟨13946858774015593813575893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9297905849343729209050595 13946858774015593813575893)
                ·
                  refine ⟨326879502515990480005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13946858774015593813575893 326879502515990480005685)
                  ·
                    rfl

theorem cell22_2864680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_2864680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864680 prefixEnd_2864680 := by exact prefixLift 2864680
  have htrace : WordTrace (prefixWord ++ tailWord_2864680) baseStart_2864680 baseEnd_2864680 := by
    simpa [prefixWord, tailWord_2864680, baseEnd_2864680] using wordTrace_append hprefix tailTrace_2864680
  have hstable : (prefixWord ++ tailWord_2864680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864680).length < 2 ^ (prefixWord ++ tailWord_2864680).sum := by decide
  have hdescent : baseEnd_2864680 < baseStart_2864680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864740 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_2864740 : Nat := 118140960795 + 2864740 * 2 ^ 59
def prefixEnd_2864740 : Nat := 4983230072969 + 3 ^ 40 * 2864740 * 2
def baseEnd_2864740 : Nat := 980659046774151283516871

theorem tailTrace_2864740 : CollatzResearch.WordTrace tailWord_2864740 prefixEnd_2864740 980659046774151283516871 := by
  unfold tailWord_2864740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52242825820771856742619837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69657101094362475656826449 52242825820771856742619837)
  ·
    refine ⟨19591059682789446278482439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52242825820771856742619837 19591059682789446278482439)
    ·
      refine ⟨29386589524184169417723659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19591059682789446278482439 29386589524184169417723659)
      ·
        refine ⟨44079884286276254126585489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29386589524184169417723659 44079884286276254126585489)
        ·
          refine ⟨33059913214707190594939117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44079884286276254126585489 33059913214707190594939117)
          ·
            refine ⟨12397467455515196473102169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33059913214707190594939117 12397467455515196473102169)
            ·
              refine ⟨9298100591636397354826627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12397467455515196473102169 9298100591636397354826627)
              ·
                refine ⟨13947150887454596032239941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298100591636397354826627 13947150887454596032239941)
                ·
                  refine ⟨2615090791397736756044989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13947150887454596032239941 2615090791397736756044989)
                  ·
                    refine ⟨980659046774151283516871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615090791397736756044989 980659046774151283516871)
                    ·
                      rfl

theorem cell22_2864740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_2864740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864740 prefixEnd_2864740 := by exact prefixLift 2864740
  have htrace : WordTrace (prefixWord ++ tailWord_2864740) baseStart_2864740 baseEnd_2864740 := by
    simpa [prefixWord, tailWord_2864740, baseEnd_2864740] using wordTrace_append hprefix tailTrace_2864740
  have hstable : (prefixWord ++ tailWord_2864740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864740).length < 2 ^ (prefixWord ++ tailWord_2864740).sum := by decide
  have hdescent : baseEnd_2864740 < baseStart_2864740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864772 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2864772 : Nat := 118140960795 + 2864772 * 2 ^ 59
def prefixEnd_2864772 : Nat := 4983230072969 + 3 ^ 40 * 2864772 * 2
def baseEnd_2864772 : Nat := 980670001028113866716773

theorem tailTrace_2864772 : CollatzResearch.WordTrace tailWord_2864772 prefixEnd_2864772 980670001028113866716773 := by
  unfold tailWord_2864772
  simp only [CollatzResearch.WordTrace]
  refine ⟨52243409388713891475202285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69657879184951855300269713 52243409388713891475202285)
  ·
    refine ⟨19591278520767709303200857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52243409388713891475202285 19591278520767709303200857)
    ·
      refine ⟨14693458890575781977400643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19591278520767709303200857 14693458890575781977400643)
      ·
        refine ⟨22040188335863672966100965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14693458890575781977400643 22040188335863672966100965)
        ·
          refine ⟨4132535312974438681143931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22040188335863672966100965 4132535312974438681143931)
          ·
            refine ⟨6198802969461658021715897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132535312974438681143931 6198802969461658021715897)
            ·
              refine ⟨4649102227096243516286923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6198802969461658021715897 4649102227096243516286923)
              ·
                refine ⟨6973653340644365274430385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649102227096243516286923 6973653340644365274430385)
                ·
                  refine ⟨5230240005483273955822789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973653340644365274430385 5230240005483273955822789)
                  ·
                    refine ⟨980670001028113866716773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230240005483273955822789 980670001028113866716773)
                    ·
                      rfl

theorem cell22_2864772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2864772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864772 prefixEnd_2864772 := by exact prefixLift 2864772
  have htrace : WordTrace (prefixWord ++ tailWord_2864772) baseStart_2864772 baseEnd_2864772 := by
    simpa [prefixWord, tailWord_2864772, baseEnd_2864772] using wordTrace_append hprefix tailTrace_2864772
  have hstable : (prefixWord ++ tailWord_2864772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864772).length < 2 ^ (prefixWord ++ tailWord_2864772).sum := by decide
  have hdescent : baseEnd_2864772 < baseStart_2864772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864875 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 1, 5]
def baseStart_2864875 : Nat := 118140960795 + 2864875 * 2 ^ 59
def prefixEnd_2864875 : Nat := 4983230072969 + 3 ^ 40 * 2864875 * 2
def baseEnd_2864875 : Nat := 980705260033055931391457

theorem tailTrace_2864875 : CollatzResearch.WordTrace tailWord_2864875 prefixEnd_2864875 980705260033055931391457 := by
  unfold tailWord_2864875
  simp only [CollatzResearch.WordTrace]
  refine ⟨104490575496054631541404079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69660383664036421027602719 104490575496054631541404079)
  ·
    refine ⟨156735863244081947312106119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104490575496054631541404079 156735863244081947312106119)
    ·
      refine ⟨235103794866122920968159179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156735863244081947312106119 235103794866122920968159179)
      ·
        refine ⟨352655692299184381452238769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235103794866122920968159179 352655692299184381452238769)
        ·
          refine ⟨264491769224388286089179077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352655692299184381452238769 264491769224388286089179077)
          ·
            refine ⟨49592206729572803641721077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264491769224388286089179077 49592206729572803641721077)
            ·
              refine ⟨4649269380897450341411351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49592206729572803641721077 4649269380897450341411351)
              ·
                refine ⟨6973904071346175512117027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649269380897450341411351 6973904071346175512117027)
                ·
                  refine ⟨10460856107019263268175541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973904071346175512117027 10460856107019263268175541)
                  ·
                    refine ⟨980705260033055931391457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10460856107019263268175541 980705260033055931391457)
                    ·
                      rfl

theorem cell22_2864875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_2864875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864875 prefixEnd_2864875 := by exact prefixLift 2864875
  have htrace : WordTrace (prefixWord ++ tailWord_2864875) baseStart_2864875 baseEnd_2864875 := by
    simpa [prefixWord, tailWord_2864875, baseEnd_2864875] using wordTrace_append hprefix tailTrace_2864875
  have hstable : (prefixWord ++ tailWord_2864875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864875).length < 2 ^ (prefixWord ++ tailWord_2864875).sum := by decide
  have hdescent : baseEnd_2864875 < baseStart_2864875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864890 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_2864890 : Nat := 118140960795 + 2864890 * 2 ^ 59
def prefixEnd_2864890 : Nat := 4983230072969 + 3 ^ 40 * 2864890 * 2
def baseEnd_2864890 : Nat := 980710394839600892266411

theorem tailTrace_2864890 : CollatzResearch.WordTrace tailWord_2864890 prefixEnd_2864890 980710394839600892266411 := by
  unfold tailWord_2864890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122780647750072275800031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69660748394000192735466749 26122780647750072275800031)
  ·
    refine ⟨39184170971625108413700047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26122780647750072275800031 39184170971625108413700047)
    ·
      refine ⟨58776256457437662620550071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39184170971625108413700047 58776256457437662620550071)
      ·
        refine ⟨88164384686156493930825107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58776256457437662620550071 88164384686156493930825107)
        ·
          refine ⟨132246577029234740896237661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88164384686156493930825107 132246577029234740896237661)
          ·
            refine ⟨49592466385963027836089123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132246577029234740896237661 49592466385963027836089123)
            ·
              refine ⟨74388699578944541754133685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49592466385963027836089123 74388699578944541754133685)
              ·
                refine ⟨6973940585526050789450033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74388699578944541754133685 6973940585526050789450033)
                ·
                  refine ⟨5230455439144538092087525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973940585526050789450033 5230455439144538092087525)
                  ·
                    refine ⟨980710394839600892266411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230455439144538092087525 980710394839600892266411)
                    ·
                      rfl

theorem cell22_2864890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_2864890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864890 prefixEnd_2864890 := by exact prefixLift 2864890
  have htrace : WordTrace (prefixWord ++ tailWord_2864890) baseStart_2864890 baseEnd_2864890 := by
    simpa [prefixWord, tailWord_2864890, baseEnd_2864890] using wordTrace_append hprefix tailTrace_2864890
  have hstable : (prefixWord ++ tailWord_2864890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864890).length < 2 ^ (prefixWord ++ tailWord_2864890).sum := by decide
  have hdescent : baseEnd_2864890 < baseStart_2864890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864965 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2864965 : Nat := 118140960795 + 2864965 * 2 ^ 59
def prefixEnd_2864965 : Nat := 4983230072969 + 3 ^ 40 * 2864965 * 2
def baseEnd_2864965 : Nat := 980736068872325696641181

theorem tailTrace_2864965 : CollatzResearch.WordTrace tailWord_2864965 prefixEnd_2864965 980736068872325696641181 := by
  unfold tailWord_2864965
  simp only [CollatzResearch.WordTrace]
  refine ⟨104493858065728576912180349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69662572043819051274786899 104493858065728576912180349)
  ·
    refine ⟨39185196774648216342067631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104493858065728576912180349 39185196774648216342067631)
    ·
      refine ⟨58777795161972324513101447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39185196774648216342067631 58777795161972324513101447)
      ·
        refine ⟨88166692742958486769652171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58777795161972324513101447 88166692742958486769652171)
        ·
          refine ⟨132250039114437730154478257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88166692742958486769652171 132250039114437730154478257)
          ·
            refine ⟨99187529335828297615858693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132250039114437730154478257 99187529335828297615858693)
            ·
              refine ⟨18597661750467805802973505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99187529335828297615858693 18597661750467805802973505)
              ·
                refine ⟨13948246312850854352230129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18597661750467805802973505 13948246312850854352230129)
                ·
                  refine ⟨10461184734638140764172597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13948246312850854352230129 10461184734638140764172597)
                  ·
                    refine ⟨980736068872325696641181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10461184734638140764172597 980736068872325696641181)
                    ·
                      rfl

theorem cell22_2864965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2864965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864965 prefixEnd_2864965 := by exact prefixLift 2864965
  have htrace : WordTrace (prefixWord ++ tailWord_2864965) baseStart_2864965 baseEnd_2864965 := by
    simpa [prefixWord, tailWord_2864965, baseEnd_2864965] using wordTrace_append hprefix tailTrace_2864965
  have hstable : (prefixWord ++ tailWord_2864965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864965).length < 2 ^ (prefixWord ++ tailWord_2864965).sum := by decide
  have hdescent : baseEnd_2864965 < baseStart_2864965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864997 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_2864997 : Nat := 118140960795 + 2864997 * 2 ^ 59
def prefixEnd_2864997 : Nat := 4983230072969 + 3 ^ 40 * 2864997 * 2
def baseEnd_2864997 : Nat := 980747023126288279841083

theorem tailTrace_2864997 : CollatzResearch.WordTrace tailWord_2864997 prefixEnd_2864997 980747023126288279841083 := by
  unfold tailWord_2864997
  simp only [CollatzResearch.WordTrace]
  refine ⟨104495025201612646377345245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69663350134408430918230163 104495025201612646377345245)
  ·
    refine ⟨39185634450604742391504467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104495025201612646377345245 39185634450604742391504467)
    ·
      refine ⟨58778451675907113587256701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39185634450604742391504467 58778451675907113587256701)
      ·
        refine ⟨22041919378465167595221263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58778451675907113587256701 22041919378465167595221263)
        ·
          refine ⟨33062879067697751392831895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041919378465167595221263 33062879067697751392831895)
          ·
            refine ⟨49594318601546627089247843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33062879067697751392831895 49594318601546627089247843)
            ·
              refine ⟨74391477902319940633871765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49594318601546627089247843 74391477902319940633871765)
              ·
                refine ⟨3487100526671247217212739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74391477902319940633871765 3487100526671247217212739)
                ·
                  refine ⟨5230650790006870825819109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487100526671247217212739 5230650790006870825819109)
                  ·
                    refine ⟨980747023126288279841083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230650790006870825819109 980747023126288279841083)
                    ·
                      rfl

theorem cell22_2864997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_2864997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2864997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2864997 prefixEnd_2864997 := by exact prefixLift 2864997
  have htrace : WordTrace (prefixWord ++ tailWord_2864997) baseStart_2864997 baseEnd_2864997 := by
    simpa [prefixWord, tailWord_2864997, baseEnd_2864997] using wordTrace_append hprefix tailTrace_2864997
  have hstable : (prefixWord ++ tailWord_2864997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864997).length < 2 ^ (prefixWord ++ tailWord_2864997).sum := by decide
  have hdescent : baseEnd_2864997 < baseStart_2864997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865044 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2865044 : Nat := 118140960795 + 2865044 * 2 ^ 59
def prefixEnd_2865044 : Nat := 4983230072969 + 3 ^ 40 * 2865044 * 2
def baseEnd_2865044 : Nat := 980763112186795823915939

theorem tailTrace_2865044 : CollatzResearch.WordTrace tailWord_2865044 prefixEnd_2865044 980763112186795823915939 := by
  unfold tailWord_2865044
  simp only [CollatzResearch.WordTrace]
  refine ⟨52248369716221186702153093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69664492954961582269537457 52248369716221186702153093)
  ·
    refine ⟨9796569321791472506653705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52248369716221186702153093 9796569321791472506653705)
    ·
      refine ⟨7347426991343604379990279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796569321791472506653705 7347426991343604379990279)
      ·
        refine ⟨11021140487015406569985419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347426991343604379990279 11021140487015406569985419)
        ·
          refine ⟨16531710730523109854978129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11021140487015406569985419 16531710730523109854978129)
          ·
            refine ⟨12398783047892332391233597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16531710730523109854978129 12398783047892332391233597)
            ·
              refine ⟨4649543642959624646712599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12398783047892332391233597 4649543642959624646712599)
              ·
                refine ⟨6974315464439436970068899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649543642959624646712599 6974315464439436970068899)
                ·
                  refine ⟨10461473196659155455103349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974315464439436970068899 10461473196659155455103349)
                  ·
                    refine ⟨980763112186795823915939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10461473196659155455103349 980763112186795823915939)
                    ·
                      rfl

theorem cell22_2865044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2865044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865044 prefixEnd_2865044 := by exact prefixLift 2865044
  have htrace : WordTrace (prefixWord ++ tailWord_2865044) baseStart_2865044 baseEnd_2865044 := by
    simpa [prefixWord, tailWord_2865044, baseEnd_2865044] using wordTrace_append hprefix tailTrace_2865044
  have hstable : (prefixWord ++ tailWord_2865044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865044).length < 2 ^ (prefixWord ++ tailWord_2865044).sum := by decide
  have hdescent : baseEnd_2865044 < baseStart_2865044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865181 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 4]
def baseStart_2865181 : Nat := 118140960795 + 2865181 * 2 ^ 59
def prefixEnd_2865181 : Nat := 4983230072969 + 3 ^ 40 * 2865181 * 2
def baseEnd_2865181 : Nat := 326936670028857711080173

theorem tailTrace_2865181 : CollatzResearch.WordTrace tailWord_2865181 prefixEnd_2865181 326936670028857711080173 := by
  unfold tailWord_2865181
  simp only [CollatzResearch.WordTrace]
  refine ⟨104501736232946045802043397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69667824155297363868028931 104501736232946045802043397)
  ·
    refine ⟨19594075543677383587883137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104501736232946045802043397 19594075543677383587883137)
    ·
      refine ⟨14695556657758037690912353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19594075543677383587883137 14695556657758037690912353)
      ·
        refine ⟨11021667493318528268184265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14695556657758037690912353 11021667493318528268184265)
        ·
          refine ⟨8266250619988896201138199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11021667493318528268184265 8266250619988896201138199)
          ·
            refine ⟨12399375929983344301707299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266250619988896201138199 12399375929983344301707299)
            ·
              refine ⟨18599063894975016452560949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12399375929983344301707299 18599063894975016452560949)
              ·
                refine ⟨1743662240153907792427589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18599063894975016452560949 1743662240153907792427589)
                ·
                  refine ⟨326936670028857711080173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743662240153907792427589 326936670028857711080173)
                  ·
                    rfl

theorem cell22_2865181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_2865181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865181 prefixEnd_2865181 := by exact prefixLift 2865181
  have htrace : WordTrace (prefixWord ++ tailWord_2865181) baseStart_2865181 baseEnd_2865181 := by
    simpa [prefixWord, tailWord_2865181, baseEnd_2865181] using wordTrace_append hprefix tailTrace_2865181
  have hstable : (prefixWord ++ tailWord_2865181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865181).length < 2 ^ (prefixWord ++ tailWord_2865181).sum := by decide
  have hdescent : baseEnd_2865181 < baseStart_2865181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865213 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2865213 : Nat := 118140960795 + 2865213 * 2 ^ 59
def prefixEnd_2865213 : Nat := 4983230072969 + 3 ^ 40 * 2865213 * 2
def baseEnd_2865213 : Nat := 980820964340535716440421

theorem tailTrace_2865213 : CollatzResearch.WordTrace tailWord_2865213 prefixEnd_2865213 980820964340535716440421 := by
  unfold tailWord_2865213
  simp only [CollatzResearch.WordTrace]
  refine ⟨104502903368830115267208293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69668602245886743511472195 104502903368830115267208293)
  ·
    refine ⟨19594294381655646612601555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104502903368830115267208293 19594294381655646612601555)
    ·
      refine ⟨29391441572483469918902333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19594294381655646612601555 29391441572483469918902333)
      ·
        refine ⟨11021790589681301219588375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29391441572483469918902333 11021790589681301219588375)
        ·
          refine ⟨16532685884521951829382563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11021790589681301219588375 16532685884521951829382563)
          ·
            refine ⟨24799028826782927744073845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16532685884521951829382563 24799028826782927744073845)
            ·
              refine ⟨2324908952510899476006923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24799028826782927744073845 2324908952510899476006923)
              ·
                refine ⟨3487363428766349214010385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324908952510899476006923 3487363428766349214010385)
                ·
                  refine ⟨2615522571574761910507789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487363428766349214010385 2615522571574761910507789)
                  ·
                    refine ⟨980820964340535716440421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615522571574761910507789 980820964340535716440421)
                    ·
                      rfl

theorem cell22_2865213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2865213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865213 prefixEnd_2865213 := by exact prefixLift 2865213
  have htrace : WordTrace (prefixWord ++ tailWord_2865213) baseStart_2865213 baseEnd_2865213 := by
    simpa [prefixWord, tailWord_2865213, baseEnd_2865213] using wordTrace_append hprefix tailTrace_2865213
  have hstable : (prefixWord ++ tailWord_2865213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865213).length < 2 ^ (prefixWord ++ tailWord_2865213).sum := by decide
  have hdescent : baseEnd_2865213 < baseStart_2865213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865224 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_2865224 : Nat := 118140960795 + 2865224 * 2 ^ 59
def prefixEnd_2865224 : Nat := 4983230072969 + 3 ^ 40 * 2865224 * 2
def baseEnd_2865224 : Nat := 980824729865335354415387

theorem tailTrace_2865224 : CollatzResearch.WordTrace tailWord_2865224 prefixEnd_2865224 980824729865335354415387 := by
  unfold tailWord_2865224
  simp only [CollatzResearch.WordTrace]
  refine ⟨52251652285895132072929363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69668869714526842763905817 52251652285895132072929363)
  ·
    refine ⟨78377478428842698109394045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52251652285895132072929363 78377478428842698109394045)
    ·
      refine ⟨29391554410816011791022767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78377478428842698109394045 29391554410816011791022767)
      ·
        refine ⟨44087331616224017686534151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29391554410816011791022767 44087331616224017686534151)
        ·
          refine ⟨66130997424336026529801227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44087331616224017686534151 66130997424336026529801227)
          ·
            refine ⟨99196496136504039794701841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66130997424336026529801227 99196496136504039794701841)
            ·
              refine ⟨74397372102378029846026381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99196496136504039794701841 74397372102378029846026381)
              ·
                refine ⟨27899014538391761192259893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74397372102378029846026381 27899014538391761192259893)
                ·
                  refine ⟨2615532612974227611774365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27899014538391761192259893 2615532612974227611774365)
                  ·
                    refine ⟨980824729865335354415387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615532612974227611774365 980824729865335354415387)
                    ·
                      rfl

theorem cell22_2865224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_2865224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865224 prefixEnd_2865224 := by exact prefixLift 2865224
  have htrace : WordTrace (prefixWord ++ tailWord_2865224) baseStart_2865224 baseEnd_2865224 := by
    simpa [prefixWord, tailWord_2865224, baseEnd_2865224] using wordTrace_append hprefix tailTrace_2865224
  have hstable : (prefixWord ++ tailWord_2865224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865224).length < 2 ^ (prefixWord ++ tailWord_2865224).sum := by decide
  have hdescent : baseEnd_2865224 < baseStart_2865224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865271 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 5]
def baseStart_2865271 : Nat := 118140960795 + 2865271 * 2 ^ 59
def prefixEnd_2865271 : Nat := 4983230072969 + 3 ^ 40 * 2865271 * 2
def baseEnd_2865271 : Nat := 326946939641947632830081

theorem tailTrace_2865271 : CollatzResearch.WordTrace tailWord_2865271 prefixEnd_2865271 326946939641947632830081 := by
  unfold tailWord_2865271
  simp only [CollatzResearch.WordTrace]
  refine ⟨104505018802619991172819667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69670012535079994115213111 104505018802619991172819667)
  ·
    refine ⟨156757528203929986759229501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104505018802619991172819667 156757528203929986759229501)
    ·
      refine ⟨58784073076473745034711063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156757528203929986759229501 58784073076473745034711063)
      ·
        refine ⟨88176109614710617552066595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58784073076473745034711063 88176109614710617552066595)
        ·
          refine ⟨132264164422065926328099893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88176109614710617552066595 132264164422065926328099893)
          ·
            refine ⟨12399765414568680593259365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132264164422065926328099893 12399765414568680593259365)
            ·
              refine ⟨2324956015231627611236131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12399765414568680593259365 2324956015231627611236131)
              ·
                refine ⟨3487434022847441416854197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324956015231627611236131 3487434022847441416854197)
                ·
                  refine ⟨326946939641947632830081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3487434022847441416854197 326946939641947632830081)
                  ·
                    rfl

theorem cell22_2865271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 5].length) (baseStart_2865271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865271 prefixEnd_2865271 := by exact prefixLift 2865271
  have htrace : WordTrace (prefixWord ++ tailWord_2865271) baseStart_2865271 baseEnd_2865271 := by
    simpa [prefixWord, tailWord_2865271, baseEnd_2865271] using wordTrace_append hprefix tailTrace_2865271
  have hstable : (prefixWord ++ tailWord_2865271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865271).length < 2 ^ (prefixWord ++ tailWord_2865271).sum := by decide
  have hdescent : baseEnd_2865271 < baseStart_2865271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865333 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 6]
def baseStart_2865333 : Nat := 118140960795 + 2865333 * 2 ^ 59
def prefixEnd_2865333 : Nat := 4983230072969 + 3 ^ 40 * 2865333 * 2
def baseEnd_2865333 : Nat := 326954014264298467813351

theorem tailTrace_2865333 : CollatzResearch.WordTrace tailWord_2865333 prefixEnd_2865333 326954014264298467813351 := by
  unfold tailWord_2865333
  simp only [CollatzResearch.WordTrace]
  refine ⟨104507280128395375761576653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69671520085596917174384435 104507280128395375761576653)
  ·
    refine ⟨39190230048148265910591245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104507280128395375761576653 39190230048148265910591245)
    ·
      refine ⟨14696336268055599716471717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39190230048148265910591245 14696336268055599716471717)
      ·
        refine ⟨2755563050260424946838447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14696336268055599716471717 2755563050260424946838447)
        ·
          refine ⟨4133344575390637420257671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755563050260424946838447 4133344575390637420257671)
          ·
            refine ⟨6200016863085956130386507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133344575390637420257671 6200016863085956130386507)
            ·
              refine ⟨9300025294628934195579761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200016863085956130386507 9300025294628934195579761)
              ·
                refine ⟨6975018970971700646684821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9300025294628934195579761 6975018970971700646684821)
                ·
                  refine ⟨326954014264298467813351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6975018970971700646684821 326954014264298467813351)
                  ·
                    rfl

theorem cell22_2865333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_2865333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865333 prefixEnd_2865333 := by exact prefixLift 2865333
  have htrace : WordTrace (prefixWord ++ tailWord_2865333) baseStart_2865333 baseEnd_2865333 := by
    simpa [prefixWord, tailWord_2865333, baseEnd_2865333] using wordTrace_append hprefix tailTrace_2865333
  have hstable : (prefixWord ++ tailWord_2865333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865333).length < 2 ^ (prefixWord ++ tailWord_2865333).sum := by decide
  have hdescent : baseEnd_2865333 < baseStart_2865333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865406 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2865406 : Nat := 118140960795 + 2865406 * 2 ^ 59
def prefixEnd_2865406 : Nat := 4983230072969 + 3 ^ 40 * 2865406 * 2
def baseEnd_2865406 : Nat := 326962344061582515454943

theorem tailTrace_2865406 : CollatzResearch.WordTrace tailWord_2865406 prefixEnd_2865406 326962344061582515454943 := by
  unfold tailWord_2865406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13063742832141363653623009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69673295104753939485989381 13063742832141363653623009)
  ·
    refine ⟨9797807124106022740217257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13063742832141363653623009 9797807124106022740217257)
    ·
      refine ⟨7348355343079517055162943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9797807124106022740217257 7348355343079517055162943)
      ·
        refine ⟨11022533014619275582744415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348355343079517055162943 11022533014619275582744415)
        ·
          refine ⟨16533799521928913374116623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11022533014619275582744415 16533799521928913374116623)
          ·
            refine ⟨24800699282893370061174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16533799521928913374116623 24800699282893370061174935)
            ·
              refine ⟨37201048924340055091762403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24800699282893370061174935 37201048924340055091762403)
              ·
                refine ⟨55801573386510082637643605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37201048924340055091762403 55801573386510082637643605)
                ·
                  refine ⟨326962344061582515454943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55801573386510082637643605 326962344061582515454943)
                  ·
                    rfl

theorem cell22_2865406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2865406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865406 prefixEnd_2865406 := by exact prefixLift 2865406
  have htrace : WordTrace (prefixWord ++ tailWord_2865406) baseStart_2865406 baseEnd_2865406 := by
    simpa [prefixWord, tailWord_2865406, baseEnd_2865406] using wordTrace_append hprefix tailTrace_2865406
  have hstable : (prefixWord ++ tailWord_2865406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865406).length < 2 ^ (prefixWord ++ tailWord_2865406).sum := by decide
  have hdescent : baseEnd_2865406 < baseStart_2865406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865436 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2865436 : Nat := 118140960795 + 2865436 * 2 ^ 59
def prefixEnd_2865436 : Nat := 4983230072969 + 3 ^ 40 * 2865436 * 2
def baseEnd_2865436 : Nat := 980897301797837468114737

theorem tailTrace_2865436 : CollatzResearch.WordTrace tailWord_2865436 prefixEnd_2865436 980897301797837468114737 := by
  unfold tailWord_2865436
  simp only [CollatzResearch.WordTrace]
  refine ⟨52255518423511112176288081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69674024564681482901717441 52255518423511112176288081)
  ·
    refine ⟨39191638817633334132216061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52255518423511112176288081 39191638817633334132216061)
    ·
      refine ⟨14696864556612500299581023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39191638817633334132216061 14696864556612500299581023)
      ·
        refine ⟨22045296834918750449371535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14696864556612500299581023 22045296834918750449371535)
        ·
          refine ⟨33067945252378125674057303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22045296834918750449371535 33067945252378125674057303)
          ·
            refine ⟨49601917878567188511085955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33067945252378125674057303 49601917878567188511085955)
            ·
              refine ⟨74402876817850782766628933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49601917878567188511085955 74402876817850782766628933)
              ·
                refine ⟨13950539403347021768742925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74402876817850782766628933 13950539403347021768742925)
                ·
                  refine ⟨5231452276255133163278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13950539403347021768742925 5231452276255133163278597)
                  ·
                    refine ⟨980897301797837468114737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5231452276255133163278597 980897301797837468114737)
                    ·
                      rfl

theorem cell22_2865436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2865436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865436 prefixEnd_2865436 := by exact prefixLift 2865436
  have htrace : WordTrace (prefixWord ++ tailWord_2865436) baseStart_2865436 baseEnd_2865436 := by
    simpa [prefixWord, tailWord_2865436, baseEnd_2865436] using wordTrace_append hprefix tailTrace_2865436
  have hstable : (prefixWord ++ tailWord_2865436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865436).length < 2 ^ (prefixWord ++ tailWord_2865436).sum := by decide
  have hdescent : baseEnd_2865436 < baseStart_2865436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865440 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_2865440 : Nat := 118140960795 + 2865440 * 2 ^ 59
def prefixEnd_2865440 : Nat := 4983230072969 + 3 ^ 40 * 2865440 * 2
def baseEnd_2865440 : Nat := 326966223693194263671575

theorem tailTrace_2865440 : CollatzResearch.WordTrace tailWord_2865440 prefixEnd_2865440 326966223693194263671575 := by
  unfold tailWord_2865440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52255591369503866517860887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69674121826005155357147849 52255591369503866517860887)
  ·
    refine ⟨78383387054255799776791331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52255591369503866517860887 78383387054255799776791331)
    ·
      refine ⟨117575080581383699665186997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78383387054255799776791331 117575080581383699665186997)
      ·
        refine ⟨11022663804504721843611281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117575080581383699665186997 11022663804504721843611281)
        ·
          refine ⟨8266997853378541382708461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11022663804504721843611281 8266997853378541382708461)
          ·
            refine ⟨3100124195016953018515673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8266997853378541382708461 3100124195016953018515673)
            ·
              refine ⟨2325093146262714763886755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3100124195016953018515673 2325093146262714763886755)
              ·
                refine ⟨3487639719394072145830133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325093146262714763886755 3487639719394072145830133)
                ·
                  refine ⟨326966223693194263671575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3487639719394072145830133 326966223693194263671575)
                  ·
                    rfl

theorem cell22_2865440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_2865440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865440 prefixEnd_2865440 := by exact prefixLift 2865440
  have htrace : WordTrace (prefixWord ++ tailWord_2865440) baseStart_2865440 baseEnd_2865440 := by
    simpa [prefixWord, tailWord_2865440, baseEnd_2865440] using wordTrace_append hprefix tailTrace_2865440
  have hstable : (prefixWord ++ tailWord_2865440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865440).length < 2 ^ (prefixWord ++ tailWord_2865440).sum := by decide
  have hdescent : baseEnd_2865440 < baseStart_2865440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865449 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_2865449 : Nat := 118140960795 + 2865449 * 2 ^ 59
def prefixEnd_2865449 : Nat := 4983230072969 + 3 ^ 40 * 2865449 * 2
def baseEnd_2865449 : Nat := 980901751963509767539697

theorem tailTrace_2865449 : CollatzResearch.WordTrace tailWord_2865449 prefixEnd_2865449 980901751963509767539697 := by
  unfold tailWord_2865449
  simp only [CollatzResearch.WordTrace]
  refine ⟨104511510995975127572799401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69674340663983418381866267 104511510995975127572799401)
  ·
    refine ⟨78383633246981345679599551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104511510995975127572799401 78383633246981345679599551)
    ·
      refine ⟨117575449870472018519399327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78383633246981345679599551 117575449870472018519399327)
      ·
        refine ⟨176363174805708027779098991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117575449870472018519399327 176363174805708027779098991)
        ·
          refine ⟨264544762208562041668648487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176363174805708027779098991 264544762208562041668648487)
          ·
            refine ⟨396817143312843062502972731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264544762208562041668648487 396817143312843062502972731)
            ·
              refine ⟨595225714969264593754459097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396817143312843062502972731 595225714969264593754459097)
              ·
                refine ⟨446419286226948445315844323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595225714969264593754459097 446419286226948445315844323)
                ·
                  refine ⟨669628929340422667973766485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446419286226948445315844323 669628929340422667973766485)
                  ·
                    refine ⟨980901751963509767539697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 669628929340422667973766485 980901751963509767539697)
                    ·
                      rfl

theorem cell22_2865449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_2865449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865449 prefixEnd_2865449 := by exact prefixLift 2865449
  have htrace : WordTrace (prefixWord ++ tailWord_2865449) baseStart_2865449 baseEnd_2865449 := by
    simpa [prefixWord, tailWord_2865449, baseEnd_2865449] using wordTrace_append hprefix tailTrace_2865449
  have hstable : (prefixWord ++ tailWord_2865449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865449).length < 2 ^ (prefixWord ++ tailWord_2865449).sum := by decide
  have hdescent : baseEnd_2865449 < baseStart_2865449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865466 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2865466 : Nat := 118140960795 + 2865466 * 2 ^ 59
def prefixEnd_2865466 : Nat := 4983230072969 + 3 ^ 40 * 2865466 * 2
def baseEnd_2865466 : Nat := 980907571410927389864645

theorem tailTrace_2865466 : CollatzResearch.WordTrace tailWord_2865466 prefixEnd_2865466 980907571410927389864645 := by
  unfold tailWord_2865466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26128032759228384869042063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69674754024609026317445501 26128032759228384869042063)
  ·
    refine ⟨39192049138842577303563095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26128032759228384869042063 39192049138842577303563095)
    ·
      refine ⟨58788073708263865955344643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39192049138842577303563095 58788073708263865955344643)
      ·
        refine ⟨88182110562395798933016965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58788073708263865955344643 88182110562395798933016965)
        ·
          refine ⟨16534145730449212299940681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88182110562395798933016965 16534145730449212299940681)
          ·
            refine ⟨12400609297836909224955511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16534145730449212299940681 12400609297836909224955511)
            ·
              refine ⟨18600913946755363837433267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12400609297836909224955511 18600913946755363837433267)
              ·
                refine ⟨27901370920133045756149901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18600913946755363837433267 27901370920133045756149901)
                ·
                  refine ⟨10463014095049892158556213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27901370920133045756149901 10463014095049892158556213)
                  ·
                    refine ⟨980907571410927389864645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10463014095049892158556213 980907571410927389864645)
                    ·
                      rfl

theorem cell22_2865466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2865466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865466 prefixEnd_2865466 := by exact prefixLift 2865466
  have htrace : WordTrace (prefixWord ++ tailWord_2865466) baseStart_2865466 baseEnd_2865466 := by
    simpa [prefixWord, tailWord_2865466, baseEnd_2865466] using wordTrace_append hprefix tailTrace_2865466
  have hstable : (prefixWord ++ tailWord_2865466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865466).length < 2 ^ (prefixWord ++ tailWord_2865466).sum := by decide
  have hdescent : baseEnd_2865466 < baseStart_2865466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865468 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_2865468 : Nat := 118140960795 + 2865468 * 2 ^ 59
def prefixEnd_2865468 : Nat := 4983230072969 + 3 ^ 40 * 2865468 * 2
def baseEnd_2865468 : Nat := 326969418683933350438213

theorem tailTrace_2865468 : CollatzResearch.WordTrace tailWord_2865468 prefixEnd_2865468 326969418683933350438213 := by
  unfold tailWord_2865468
  simp only [CollatzResearch.WordTrace]
  refine ⟨52256101991453146908870529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69674802655270862545160705 52256101991453146908870529)
  ·
    refine ⟨39192076493589860181652897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52256101991453146908870529 39192076493589860181652897)
    ·
      refine ⟨29394057370192395136239673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39192076493589860181652897 29394057370192395136239673)
      ·
        refine ⟨22045543027644296352179755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29394057370192395136239673 22045543027644296352179755)
        ·
          refine ⟨33068314541466444528269633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22045543027644296352179755 33068314541466444528269633)
          ·
            refine ⟨24801235906099833396202225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33068314541466444528269633 24801235906099833396202225)
            ·
              refine ⟨18600926929574875047151669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24801235906099833396202225 18600926929574875047151669)
              ·
                refine ⟨1743836899647644535670469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18600926929574875047151669 1743836899647644535670469)
                ·
                  refine ⟨326969418683933350438213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743836899647644535670469 326969418683933350438213)
                  ·
                    rfl

theorem cell22_2865468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_2865468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865468 prefixEnd_2865468 := by exact prefixLift 2865468
  have htrace : WordTrace (prefixWord ++ tailWord_2865468) baseStart_2865468 baseEnd_2865468 := by
    simpa [prefixWord, tailWord_2865468, baseEnd_2865468] using wordTrace_append hprefix tailTrace_2865468
  have hstable : (prefixWord ++ tailWord_2865468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865468).length < 2 ^ (prefixWord ++ tailWord_2865468).sum := by decide
  have hdescent : baseEnd_2865468 < baseStart_2865468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865545 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_2865545 : Nat := 118140960795 + 2865545 * 2 ^ 59
def prefixEnd_2865545 : Nat := 4983230072969 + 3 ^ 40 * 2865545 * 2
def baseEnd_2865545 : Nat := 980934614725397517139403

theorem tailTrace_2865545 : CollatzResearch.WordTrace tailWord_2865545 prefixEnd_2865545 980934614725397517139403 := by
  unfold tailWord_2865545
  simp only [CollatzResearch.WordTrace]
  refine ⟨104515012403627335968294089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69676674935751557312196059 104515012403627335968294089)
  ·
    refine ⟨78386259302720501976220567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104515012403627335968294089 78386259302720501976220567)
    ·
      refine ⟨117579388954080752964330851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78386259302720501976220567 117579388954080752964330851)
      ·
        refine ⟨176369083431121129446496277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117579388954080752964330851 176369083431121129446496277)
        ·
          refine ⟨8267300785833802942804513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176369083431121129446496277 8267300785833802942804513)
          ·
            refine ⟨6200475589375352207103385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8267300785833802942804513 6200475589375352207103385)
            ·
              refine ⟨4650356692031514155327539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200475589375352207103385 4650356692031514155327539)
              ·
                refine ⟨6975535038047271232991309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650356692031514155327539 6975535038047271232991309)
                ·
                  refine ⟨2615825639267726712371741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6975535038047271232991309 2615825639267726712371741)
                  ·
                    refine ⟨980934614725397517139403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615825639267726712371741 980934614725397517139403)
                    ·
                      rfl

theorem cell22_2865545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_2865545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865545 prefixEnd_2865545 := by exact prefixLift 2865545
  have htrace : WordTrace (prefixWord ++ tailWord_2865545) baseStart_2865545 baseEnd_2865545 := by
    simpa [prefixWord, tailWord_2865545, baseEnd_2865545] using wordTrace_append hprefix tailTrace_2865545
  have hstable : (prefixWord ++ tailWord_2865545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865545).length < 2 ^ (prefixWord ++ tailWord_2865545).sum := by decide
  have hdescent : baseEnd_2865545 < baseStart_2865545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865635 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 1, 5]
def baseStart_2865635 : Nat := 118140960795 + 2865635 * 2 ^ 59
def prefixEnd_2865635 : Nat := 4983230072969 + 3 ^ 40 * 2865635 * 2
def baseEnd_2865635 : Nat := 980965423564667282389127

theorem tailTrace_2865635 : CollatzResearch.WordTrace tailWord_2865635 prefixEnd_2865635 980965423564667282389127 := by
  unfold tailWord_2865635
  simp only [CollatzResearch.WordTrace]
  refine ⟨104518294973301281339070359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69678863315534187559380239 104518294973301281339070359)
  ·
    refine ⟨156777442459951922008605539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104518294973301281339070359 156777442459951922008605539)
    ·
      refine ⟨235166163689927883012908309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156777442459951922008605539 235166163689927883012908309)
      ·
        refine ⟨11023413922965369516230077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235166163689927883012908309 11023413922965369516230077)
        ·
          refine ⟨4133780221112013568586279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11023413922965369516230077 4133780221112013568586279)
          ·
            refine ⟨6200670331668020352879419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133780221112013568586279 6200670331668020352879419)
            ·
              refine ⟨9301005497502030529319129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200670331668020352879419 9301005497502030529319129)
              ·
                refine ⟨6975754123126522896989347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9301005497502030529319129 6975754123126522896989347)
                ·
                  refine ⟨10463631184689784345484021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6975754123126522896989347 10463631184689784345484021)
                  ·
                    refine ⟨980965423564667282389127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10463631184689784345484021 980965423564667282389127)
                    ·
                      rfl

theorem cell22_2865635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_2865635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865635 prefixEnd_2865635 := by exact prefixLift 2865635
  have htrace : WordTrace (prefixWord ++ tailWord_2865635) baseStart_2865635 baseEnd_2865635 := by
    simpa [prefixWord, tailWord_2865635, baseEnd_2865635] using wordTrace_append hprefix tailTrace_2865635
  have hstable : (prefixWord ++ tailWord_2865635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865635).length < 2 ^ (prefixWord ++ tailWord_2865635).sum := by decide
  have hdescent : baseEnd_2865635 < baseStart_2865635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865665 : List Nat := [1, 2, 4, 1, 3, 3, 1, 7]
def baseStart_2865665 : Nat := 118140960795 + 2865665 * 2 ^ 59
def prefixEnd_2865665 : Nat := 4983230072969 + 3 ^ 40 * 2865665 * 2
def baseEnd_2865665 : Nat := 108997299241973022682115

theorem tailTrace_2865665 : CollatzResearch.WordTrace tailWord_2865665 prefixEnd_2865665 108997299241973022682115 := by
  unfold tailWord_2865665
  simp only [CollatzResearch.WordTrace]
  refine ⟨104519389163192596462662449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69679592775461730975108299 104519389163192596462662449)
  ·
    refine ⟨78389541872394447346996837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104519389163192596462662449 78389541872394447346996837)
    ·
      refine ⟨14698039101073958877561907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78389541872394447346996837 14698039101073958877561907)
      ·
        refine ⟨22047058651610938316342861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14698039101073958877561907 22047058651610938316342861)
        ·
          refine ⟨8267646994354101868628573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22047058651610938316342861 8267646994354101868628573)
          ·
            refine ⟨3100367622882788200735715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8267646994354101868628573 3100367622882788200735715)
            ·
              refine ⟨4650551434324182301103573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100367622882788200735715 4650551434324182301103573)
              ·
                refine ⟨108997299241973022682115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4650551434324182301103573 108997299241973022682115)
                ·
                  rfl

theorem cell22_2865665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 7].length) (baseStart_2865665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865665 prefixEnd_2865665 := by exact prefixLift 2865665
  have htrace : WordTrace (prefixWord ++ tailWord_2865665) baseStart_2865665 baseEnd_2865665 := by
    simpa [prefixWord, tailWord_2865665, baseEnd_2865665] using wordTrace_append hprefix tailTrace_2865665
  have hstable : (prefixWord ++ tailWord_2865665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865665).length < 2 ^ (prefixWord ++ tailWord_2865665).sum := by decide
  have hdescent : baseEnd_2865665 < baseStart_2865665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865684 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2865684 : Nat := 118140960795 + 2865684 * 2 ^ 59
def prefixEnd_2865684 : Nat := 4983230072969 + 3 ^ 40 * 2865684 * 2
def baseEnd_2865684 : Nat := 980982197266047487913977

theorem tailTrace_2865684 : CollatzResearch.WordTrace tailWord_2865684 prefixEnd_2865684 980982197266047487913977 := by
  unfold tailWord_2865684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52260041075061881353802053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69680054766749175138402737 52260041075061881353802053)
  ·
    refine ⟨9798757701574102753837885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52260041075061881353802053 9798757701574102753837885)
    ·
      refine ⟨3674534138090288532689207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9798757701574102753837885 3674534138090288532689207)
      ·
        refine ⟨5511801207135432799033811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3674534138090288532689207 5511801207135432799033811)
        ·
          refine ⟨8267701810703149198550717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5511801207135432799033811 8267701810703149198550717)
          ·
            refine ⟨3100388179013680949456519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8267701810703149198550717 3100388179013680949456519)
            ·
              refine ⟨4650582268520521424184779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100388179013680949456519 4650582268520521424184779)
              ·
                refine ⟨6975873402780782136277169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650582268520521424184779 6975873402780782136277169)
                ·
                  refine ⟨5231905052085586602207877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6975873402780782136277169 5231905052085586602207877)
                  ·
                    refine ⟨980982197266047487913977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5231905052085586602207877 980982197266047487913977)
                    ·
                      rfl

theorem cell22_2865684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2865684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865684 prefixEnd_2865684 := by exact prefixLift 2865684
  have htrace : WordTrace (prefixWord ++ tailWord_2865684) baseStart_2865684 baseEnd_2865684 := by
    simpa [prefixWord, tailWord_2865684, baseEnd_2865684] using wordTrace_append hprefix tailTrace_2865684
  have hstable : (prefixWord ++ tailWord_2865684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865684).length < 2 ^ (prefixWord ++ tailWord_2865684).sum := by decide
  have hdescent : baseEnd_2865684 < baseStart_2865684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865703 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2865703 : Nat := 118140960795 + 2865703 * 2 ^ 59
def prefixEnd_2865703 : Nat := 4983230072969 + 3 ^ 40 * 2865703 * 2
def baseEnd_2865703 : Nat := 980988701354337771688919

theorem tailTrace_2865703 : CollatzResearch.WordTrace tailWord_2865703 prefixEnd_2865703 980988701354337771688919 := by
  unfold tailWord_2865703
  simp only [CollatzResearch.WordTrace]
  refine ⟨104520775137054928952545763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69680516758036619301697175 104520775137054928952545763)
  ·
    refine ⟨156781162705582393428818645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104520775137054928952545763 156781162705582393428818645)
    ·
      refine ⟨3674558500912087345987937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 156781162705582393428818645 3674558500912087345987937)
      ·
        refine ⟨2755918875684065509490953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3674558500912087345987937 2755918875684065509490953)
        ·
          refine ⟨2066939156763049132118215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755918875684065509490953 2066939156763049132118215)
          ·
            refine ⟨3100408735144573698177323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066939156763049132118215 3100408735144573698177323)
            ·
              refine ⟨4650613102716860547265985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100408735144573698177323 4650613102716860547265985)
              ·
                refine ⟨3487959827037645410449489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650613102716860547265985 3487959827037645410449489)
                ·
                  refine ⟨2615969870278234057837117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487959827037645410449489 2615969870278234057837117)
                  ·
                    refine ⟨980988701354337771688919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615969870278234057837117 980988701354337771688919)
                    ·
                      rfl

theorem cell22_2865703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2865703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865703 prefixEnd_2865703 := by exact prefixLift 2865703
  have htrace : WordTrace (prefixWord ++ tailWord_2865703) baseStart_2865703 baseEnd_2865703 := by
    simpa [prefixWord, tailWord_2865703, baseEnd_2865703] using wordTrace_append hprefix tailTrace_2865703
  have hstable : (prefixWord ++ tailWord_2865703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865703).length < 2 ^ (prefixWord ++ tailWord_2865703).sum := by decide
  have hdescent : baseEnd_2865703 < baseStart_2865703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865725 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2865725 : Nat := 118140960795 + 2865725 * 2 ^ 59
def prefixEnd_2865725 : Nat := 4983230072969 + 3 ^ 40 * 2865725 * 2
def baseEnd_2865725 : Nat := 980996232403937047638851

theorem tailTrace_2865725 : CollatzResearch.WordTrace tailWord_2865725 prefixEnd_2865725 980996232403937047638851 := by
  unfold tailWord_2865725
  simp only [CollatzResearch.WordTrace]
  refine ⟨104521577542975226709846629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69681051695316817806564419 104521577542975226709846629)
  ·
    refine ⟨19597795789307855008096243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104521577542975226709846629 19597795789307855008096243)
    ·
      refine ⟨29396693683961782512144365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597795789307855008096243 29396693683961782512144365)
      ·
        refine ⟨11023760131485668442054137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29396693683961782512144365 11023760131485668442054137)
        ·
          refine ⟨8267820098614251331540603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11023760131485668442054137 8267820098614251331540603)
          ·
            refine ⟨12401730147921376997310905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8267820098614251331540603 12401730147921376997310905)
            ·
              refine ⟨9301297610941032747983179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12401730147921376997310905 9301297610941032747983179)
              ·
                refine ⟨13951946416411549121974769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9301297610941032747983179 13951946416411549121974769)
                ·
                  refine ⟨10463959812308661841481077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13951946416411549121974769 10463959812308661841481077)
                  ·
                    refine ⟨980996232403937047638851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10463959812308661841481077 980996232403937047638851)
                    ·
                      rfl

theorem cell22_2865725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2865725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865725 prefixEnd_2865725 := by exact prefixLift 2865725
  have htrace : WordTrace (prefixWord ++ tailWord_2865725) baseStart_2865725 baseEnd_2865725 := by
    simpa [prefixWord, tailWord_2865725, baseEnd_2865725] using wordTrace_append hprefix tailTrace_2865725
  have hstable : (prefixWord ++ tailWord_2865725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865725).length < 2 ^ (prefixWord ++ tailWord_2865725).sum := by decide
  have hdescent : baseEnd_2865725 < baseStart_2865725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865783 : List Nat := [1, 1, 3, 1, 1, 3, 3, 9]
def baseStart_2865783 : Nat := 118140960795 + 2865783 * 2 ^ 59
def prefixEnd_2865783 : Nat := 4983230072969 + 3 ^ 40 * 2865783 * 2
def baseEnd_2865783 : Nat := 109001787443249358854297

theorem tailTrace_2865783 : CollatzResearch.WordTrace tailWord_2865783 prefixEnd_2865783 109001787443249358854297 := by
  unfold tailWord_2865783
  simp only [CollatzResearch.WordTrace]
  refine ⟨104523692976765102615458003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69682461984510068410305335 104523692976765102615458003)
  ·
    refine ⟨156785539465147653923187005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104523692976765102615458003 156785539465147653923187005)
    ·
      refine ⟨58794577299430370221195127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156785539465147653923187005 58794577299430370221195127)
      ·
        refine ⟨88191865949145555331792691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58794577299430370221195127 88191865949145555331792691)
        ·
          refine ⟨132287798923718332997689037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88191865949145555331792691 132287798923718332997689037)
          ·
            refine ⟨49607924596394374874133389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132287798923718332997689037 49607924596394374874133389)
            ·
              refine ⟨18602971723647890577800021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49607924596394374874133389 18602971723647890577800021)
              ·
                refine ⟨109001787443249358854297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18602971723647890577800021 109001787443249358854297)
                ·
                  rfl

theorem cell22_2865783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 9].length) (baseStart_2865783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865783 prefixEnd_2865783 := by exact prefixLift 2865783
  have htrace : WordTrace (prefixWord ++ tailWord_2865783) baseStart_2865783 baseEnd_2865783 := by
    simpa [prefixWord, tailWord_2865783, baseEnd_2865783] using wordTrace_append hprefix tailTrace_2865783
  have hstable : (prefixWord ++ tailWord_2865783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865783).length < 2 ^ (prefixWord ++ tailWord_2865783).sum := by decide
  have hdescent : baseEnd_2865783 < baseStart_2865783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865866 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_2865866 : Nat := 118140960795 + 2865866 * 2 ^ 59
def prefixEnd_2865866 : Nat := 4983230072969 + 3 ^ 40 * 2865866 * 2
def baseEnd_2865866 : Nat := 981044499585459679863419

theorem tailTrace_2865866 : CollatzResearch.WordTrace tailWord_2865866 prefixEnd_2865866 981044499585459679863419 := by
  unfold tailWord_2865866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26131680058866101947682363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69684480156976271860486301 26131680058866101947682363)
  ·
    refine ⟨39197520088299152921523545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26131680058866101947682363 39197520088299152921523545)
    ·
      refine ⟨29398140066224364691142659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39197520088299152921523545 29398140066224364691142659)
      ·
        refine ⟨44097210099336547036713989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29398140066224364691142659 44097210099336547036713989)
        ·
          refine ⟨8268226893625602569383873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44097210099336547036713989 8268226893625602569383873)
          ·
            refine ⟨6201170170219201927037905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8268226893625602569383873 6201170170219201927037905)
            ·
              refine ⟨4650877627664401445278429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201170170219201927037905 4650877627664401445278429)
              ·
                refine ⟨1744079110374150541979411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4650877627664401445278429 1744079110374150541979411)
                ·
                  refine ⟨2616118665561225812969117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744079110374150541979411 2616118665561225812969117)
                  ·
                    refine ⟨981044499585459679863419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616118665561225812969117 981044499585459679863419)
                    ·
                      rfl

theorem cell22_2865866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_2865866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865866 prefixEnd_2865866 := by exact prefixLift 2865866
  have htrace : WordTrace (prefixWord ++ tailWord_2865866) baseStart_2865866 baseEnd_2865866 := by
    simpa [prefixWord, tailWord_2865866, baseEnd_2865866] using wordTrace_append hprefix tailTrace_2865866
  have hstable : (prefixWord ++ tailWord_2865866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865866).length < 2 ^ (prefixWord ++ tailWord_2865866).sum := by decide
  have hdescent : baseEnd_2865866 < baseStart_2865866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865952 : List Nat := [2, 1, 1, 5, 1, 3, 2, 7]
def baseStart_2865952 : Nat := 118140960795 + 2865952 * 2 ^ 59
def prefixEnd_2865952 : Nat := 4983230072969 + 3 ^ 40 * 2865952 * 2
def baseEnd_2865952 : Nat := 109008215460331569134795

theorem tailTrace_2865952 : CollatzResearch.WordTrace tailWord_2865952 prefixEnd_2865952 109008215460331569134795 := by
  unfold tailWord_2865952
  simp only [CollatzResearch.WordTrace]
  refine ⟨52264928456576422239180055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69686571275435229652240073 52264928456576422239180055)
  ·
    refine ⟨78397392684864633358770083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52264928456576422239180055 78397392684864633358770083)
    ·
      refine ⟨117596089027296950038155125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78397392684864633358770083 117596089027296950038155125)
      ·
        refine ⟨11024633346309089066077043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117596089027296950038155125 11024633346309089066077043)
        ·
          refine ⟨16536950019463633599115565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11024633346309089066077043 16536950019463633599115565)
          ·
            refine ⟨6201356257298862599668337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16536950019463633599115565 6201356257298862599668337)
            ·
              refine ⟨4651017192974146949751253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201356257298862599668337 4651017192974146949751253)
              ·
                refine ⟨109008215460331569134795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4651017192974146949751253 109008215460331569134795)
                ·
                  rfl

theorem cell22_2865952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_2865952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865952 prefixEnd_2865952 := by exact prefixLift 2865952
  have htrace : WordTrace (prefixWord ++ tailWord_2865952) baseStart_2865952 baseEnd_2865952 := by
    simpa [prefixWord, tailWord_2865952, baseEnd_2865952] using wordTrace_append hprefix tailTrace_2865952
  have hstable : (prefixWord ++ tailWord_2865952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865952).length < 2 ^ (prefixWord ++ tailWord_2865952).sum := by decide
  have hdescent : baseEnd_2865952 < baseStart_2865952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
