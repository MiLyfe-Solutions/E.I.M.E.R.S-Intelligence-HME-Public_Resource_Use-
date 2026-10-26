import V185TrunkScan22Chunk342

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3060606 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3060606 : Nat := 118140960795 + 3060606 * 2 ^ 59
def prefixEnd_3060606 : Nat := 4983230072969 + 3 ^ 40 * 3060606 * 2
def baseEnd_3060606 : Nat := 1047707981356505065766357

theorem tailTrace_3060606 : CollatzResearch.WordTrace tailWord_3060606 prefixEnd_3060606 1047707981356505065766357 := by
  unfold tailWord_3060606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13953683943744330841856209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74419647699969764489899781 13953683943744330841856209)
  ·
    refine ⟨10465262957808248131392157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13953683943744330841856209 10465262957808248131392157)
    ·
      refine ⟨3924473609178093049272059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10465262957808248131392157 3924473609178093049272059)
      ·
        refine ⟨5886710413767139573908089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924473609178093049272059 5886710413767139573908089)
        ·
          refine ⟨4415032810325354680431067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5886710413767139573908089 4415032810325354680431067)
          ·
            refine ⟨6622549215488032020646601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415032810325354680431067 6622549215488032020646601)
            ·
              refine ⟨4966911911616024015484951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6622549215488032020646601 4966911911616024015484951)
              ·
                refine ⟨7450367867424036023227427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966911911616024015484951 7450367867424036023227427)
                ·
                  refine ⟨11175551801136054034841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450367867424036023227427 11175551801136054034841141)
                  ·
                    refine ⟨1047707981356505065766357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11175551801136054034841141 1047707981356505065766357)
                    ·
                      rfl

theorem cell22_3060606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3060606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060606 prefixEnd_3060606 := by exact prefixLift 3060606
  have htrace : WordTrace (prefixWord ++ tailWord_3060606) baseStart_3060606 baseEnd_3060606 := by
    simpa [prefixWord, tailWord_3060606, baseEnd_3060606] using wordTrace_append hprefix tailTrace_3060606
  have hstable : (prefixWord ++ tailWord_3060606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060606).length < 2 ^ (prefixWord ++ tailWord_3060606).sum := by decide
  have hdescent : baseEnd_3060606 < baseStart_3060606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060617 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_3060617 : Nat := 118140960795 + 3060617 * 2 ^ 59
def prefixEnd_3060617 : Nat := 4983230072969 + 3 ^ 40 * 3060617 * 2
def baseEnd_3060617 : Nat := 1047711746881304703741323

theorem tailTrace_3060617 : CollatzResearch.WordTrace tailWord_3060617 prefixEnd_3060617 1047711746881304703741323 := by
  unfold tailWord_3060617
  simp only [CollatzResearch.WordTrace]
  refine ⟨111629872752914795613500105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74419915168609863742333403 111629872752914795613500105)
  ·
    refine ⟨83722404564686096710125079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111629872752914795613500105 83722404564686096710125079)
    ·
      refine ⟨125583606847029145065187619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83722404564686096710125079 125583606847029145065187619)
      ·
        refine ⟨188375410270543717597781429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125583606847029145065187619 188375410270543717597781429)
        ·
          refine ⟨17660194712863473524792009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188375410270543717597781429 17660194712863473524792009)
          ·
            refine ⟨13245146034647605143594007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17660194712863473524792009 13245146034647605143594007)
            ·
              refine ⟨19867719051971407715391011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13245146034647605143594007 19867719051971407715391011)
              ·
                refine ⟨29801578577957111573086517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19867719051971407715391011 29801578577957111573086517)
                ·
                  refine ⟨2793897991683479209976861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29801578577957111573086517 2793897991683479209976861)
                  ·
                    refine ⟨1047711746881304703741323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2793897991683479209976861 1047711746881304703741323)
                    ·
                      rfl

theorem cell22_3060617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_3060617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060617 prefixEnd_3060617 := by exact prefixLift 3060617
  have htrace : WordTrace (prefixWord ++ tailWord_3060617) baseStart_3060617 baseEnd_3060617 := by
    simpa [prefixWord, tailWord_3060617, baseEnd_3060617] using wordTrace_append hprefix tailTrace_3060617
  have hstable : (prefixWord ++ tailWord_3060617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060617).length < 2 ^ (prefixWord ++ tailWord_3060617).sum := by decide
  have hdescent : baseEnd_3060617 < baseStart_3060617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060664 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_3060664 : Nat := 118140960795 + 3060664 * 2 ^ 59
def prefixEnd_3060664 : Nat := 4983230072969 + 3 ^ 40 * 3060664 * 2
def baseEnd_3060664 : Nat := 349242611980604082605393

theorem tailTrace_3060664 : CollatzResearch.WordTrace tailWord_3060664 prefixEnd_3060664 349242611980604082605393 := by
  unfold tailWord_3060664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55815793491872261320230523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74421057989163015093640697 55815793491872261320230523)
  ·
    refine ⟨83723690237808391980345785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55815793491872261320230523 83723690237808391980345785)
    ·
      refine ⟨62792767678356293985259339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83723690237808391980345785 62792767678356293985259339)
      ·
        refine ⟨94189151517534440977889009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62792767678356293985259339 94189151517534440977889009)
        ·
          refine ⟨70641863638150830733416757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94189151517534440977889009 70641863638150830733416757)
          ·
            refine ⟨6622674716076640381257821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70641863638150830733416757 6622674716076640381257821)
            ·
              refine ⟨2483503018528740142971683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6622674716076640381257821 2483503018528740142971683)
              ·
                refine ⟨3725254527793110214457525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483503018528740142971683 3725254527793110214457525)
                ·
                  refine ⟨349242611980604082605393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3725254527793110214457525 349242611980604082605393)
                  ·
                    rfl

theorem cell22_3060664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_3060664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060664 prefixEnd_3060664 := by exact prefixLift 3060664
  have htrace : WordTrace (prefixWord ++ tailWord_3060664) baseStart_3060664 baseEnd_3060664 := by
    simpa [prefixWord, tailWord_3060664, baseEnd_3060664] using wordTrace_append hprefix tailTrace_3060664
  have hstable : (prefixWord ++ tailWord_3060664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060664).length < 2 ^ (prefixWord ++ tailWord_3060664).sum := by decide
  have hdescent : baseEnd_3060664 < baseStart_3060664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060737 : List Nat := [1, 2, 4, 1, 2, 2, 2, 8]
def baseStart_3060737 : Nat := 118140960795 + 3060737 * 2 ^ 59
def prefixEnd_3060737 : Nat := 4983230072969 + 3 ^ 40 * 3060737 * 2
def baseEnd_3060737 : Nat := 116416980592629376748995

theorem tailTrace_3060737 : CollatzResearch.WordTrace tailWord_3060737 prefixEnd_3060737 116416980592629376748995 := by
  unfold tailWord_3060737
  simp only [CollatzResearch.WordTrace]
  refine ⟨111634249512480056107868465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74422833008320037405245643 111634249512480056107868465)
  ·
    refine ⟨83725687134360042080901349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111634249512480056107868465 83725687134360042080901349)
    ·
      refine ⟨15698566337692507890169003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83725687134360042080901349 15698566337692507890169003)
      ·
        refine ⟨23547849506538761835253505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15698566337692507890169003 23547849506538761835253505)
        ·
          refine ⟨17660887129904071376440129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23547849506538761835253505 17660887129904071376440129)
          ·
            refine ⟨13245665347428053532330097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17660887129904071376440129 13245665347428053532330097)
            ·
              refine ⟨9934249010571040149247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13245665347428053532330097 9934249010571040149247573)
              ·
                refine ⟨116416980592629376748995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9934249010571040149247573 116416980592629376748995)
                ·
                  rfl

theorem cell22_3060737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 8].length) (baseStart_3060737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060737 prefixEnd_3060737 := by exact prefixLift 3060737
  have htrace : WordTrace (prefixWord ++ tailWord_3060737) baseStart_3060737 baseEnd_3060737 := by
    simpa [prefixWord, tailWord_3060737, baseEnd_3060737] using wordTrace_append hprefix tailTrace_3060737
  have hstable : (prefixWord ++ tailWord_3060737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060737).length < 2 ^ (prefixWord ++ tailWord_3060737).sum := by decide
  have hdescent : baseEnd_3060737 < baseStart_3060737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060767 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_3060767 : Nat := 118140960795 + 3060767 * 2 ^ 59
def prefixEnd_3060767 : Nat := 4983230072969 + 3 ^ 40 * 3060767 * 2
def baseEnd_3060767 : Nat := 1047763094946754312490863

theorem tailTrace_3060767 : CollatzResearch.WordTrace tailWord_3060767 prefixEnd_3060767 1047763094946754312490863 := by
  unfold tailWord_3060767
  simp only [CollatzResearch.WordTrace]
  refine ⟨111635343702371371231460555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74423562468247580820973703 111635343702371371231460555)
  ·
    refine ⟨167453015553557056847190833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111635343702371371231460555 167453015553557056847190833)
    ·
      refine ⟨125589761665167792635393125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167453015553557056847190833 125589761665167792635393125)
      ·
        refine ⟨23548080312218961119136211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125589761665167792635393125 23548080312218961119136211)
        ·
          refine ⟨35322120468328441678704317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23548080312218961119136211 35322120468328441678704317)
          ·
            refine ⟨13245795175623165629514119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35322120468328441678704317 13245795175623165629514119)
            ·
              refine ⟨19868692763434748444271179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13245795175623165629514119 19868692763434748444271179)
              ·
                refine ⟨29803039145152122666406769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19868692763434748444271179 29803039145152122666406769)
                ·
                  refine ⟨22352279358864091999805077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29803039145152122666406769 22352279358864091999805077)
                  ·
                    refine ⟨1047763094946754312490863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22352279358864091999805077 1047763094946754312490863)
                    ·
                      rfl

theorem cell22_3060767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_3060767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060767 prefixEnd_3060767 := by exact prefixLift 3060767
  have htrace : WordTrace (prefixWord ++ tailWord_3060767) baseStart_3060767 baseEnd_3060767 := by
    simpa [prefixWord, tailWord_3060767, baseEnd_3060767] using wordTrace_append hprefix tailTrace_3060767
  have hstable : (prefixWord ++ tailWord_3060767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060767).length < 2 ^ (prefixWord ++ tailWord_3060767).sum := by decide
  have hdescent : baseEnd_3060767 < baseStart_3060767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060846 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3060846 : Nat := 118140960795 + 3060846 * 2 ^ 59
def prefixEnd_3060846 : Nat := 4983230072969 + 3 ^ 40 * 3060846 * 2
def baseEnd_3060846 : Nat := 1047790138261224439765621

theorem tailTrace_3060846 : CollatzResearch.WordTrace tailWord_3060846 prefixEnd_3060846 1047790138261224439765621 := by
  unfold tailWord_3060846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954778133635645965448299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74425483379390111815724261 13954778133635645965448299)
  ·
    refine ⟨20932167200453468948172449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13954778133635645965448299 20932167200453468948172449)
    ·
      refine ⟨15699125400340101711129337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20932167200453468948172449 15699125400340101711129337)
      ·
        refine ⟨11774344050255076283347003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15699125400340101711129337 11774344050255076283347003)
        ·
          refine ⟨17661516075382614425020505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11774344050255076283347003 17661516075382614425020505)
          ·
            refine ⟨13246137056536960818765379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17661516075382614425020505 13246137056536960818765379)
            ·
              refine ⟨19869205584805441228148069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13246137056536960818765379 19869205584805441228148069)
              ·
                refine ⟨3725476047151020230277763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19869205584805441228148069 3725476047151020230277763)
                ·
                  refine ⟨5588214070726530345416645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725476047151020230277763 5588214070726530345416645)
                  ·
                    refine ⟨1047790138261224439765621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5588214070726530345416645 1047790138261224439765621)
                    ·
                      rfl

theorem cell22_3060846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3060846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060846 prefixEnd_3060846 := by exact prefixLift 3060846
  have htrace : WordTrace (prefixWord ++ tailWord_3060846) baseStart_3060846 baseEnd_3060846 := by
    simpa [prefixWord, tailWord_3060846, baseEnd_3060846] using wordTrace_append hprefix tailTrace_3060846
  have hstable : (prefixWord ++ tailWord_3060846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060846).length < 2 ^ (prefixWord ++ tailWord_3060846).sum := by decide
  have hdescent : baseEnd_3060846 < baseStart_3060846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060906 : List Nat := [3, 1, 5, 1, 1, 1, 2, 8]
def baseStart_3060906 : Nat := 118140960795 + 3060906 * 2 ^ 59
def prefixEnd_3060906 : Nat := 4983230072969 + 3 ^ 40 * 3060906 * 2
def baseEnd_3060906 : Nat := 116423408609711587029493

theorem tailTrace_3060906 : CollatzResearch.WordTrace tailWord_3060906 prefixEnd_3060906 116423408609711587029493 := by
  unfold tailWord_3060906
  simp only [CollatzResearch.WordTrace]
  refine ⟨27910103362216949492692643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74426942299245198647180381 27910103362216949492692643)
  ·
    refine ⟨41865155043325424239038965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27910103362216949492692643 41865155043325424239038965)
    ·
      refine ⟨3924858285311758522409903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41865155043325424239038965 3924858285311758522409903)
      ·
        refine ⟨5887287427967637783614855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924858285311758522409903 5887287427967637783614855)
        ·
          refine ⟨8830931141951456675422283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887287427967637783614855 8830931141951456675422283)
          ·
            refine ⟨13246396712927185013133425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830931141951456675422283 13246396712927185013133425)
            ·
              refine ⟨9934797534695388759850069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13246396712927185013133425 9934797534695388759850069)
              ·
                refine ⟨116423408609711587029493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9934797534695388759850069 116423408609711587029493)
                ·
                  rfl

theorem cell22_3060906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_3060906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060906 prefixEnd_3060906 := by exact prefixLift 3060906
  have htrace : WordTrace (prefixWord ++ tailWord_3060906) baseStart_3060906 baseEnd_3060906 := by
    simpa [prefixWord, tailWord_3060906, baseEnd_3060906] using wordTrace_append hprefix tailTrace_3060906
  have hstable : (prefixWord ++ tailWord_3060906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060906).length < 2 ^ (prefixWord ++ tailWord_3060906).sum := by decide
  have hdescent : baseEnd_3060906 < baseStart_3060906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060996 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_3060996 : Nat := 118140960795 + 3060996 * 2 ^ 59
def prefixEnd_3060996 : Nat := 4983230072969 + 3 ^ 40 * 3060996 * 2
def baseEnd_3060996 : Nat := 349280495442224682838387

theorem tailTrace_3060996 : CollatzResearch.WordTrace tailWord_3060996 prefixEnd_3060996 349280495442224682838387 := by
  unfold tailWord_3060996
  simp only [CollatzResearch.WordTrace]
  refine ⟨55821848009270871670773421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74429130679027828894364561 55821848009270871670773421)
  ·
    refine ⟨20933193003476576876540033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55821848009270871670773421 20933193003476576876540033)
    ·
      refine ⟨15699894752607432657405025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20933193003476576876540033 15699894752607432657405025)
      ·
        refine ⟨11774921064455574493053769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15699894752607432657405025 11774921064455574493053769)
        ·
          refine ⟨8831190798341680869790327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11774921064455574493053769 8831190798341680869790327)
          ·
            refine ⟨13246786197512521304685491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8831190798341680869790327 13246786197512521304685491)
            ·
              refine ⟨19870179296268781957028237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13246786197512521304685491 19870179296268781957028237)
              ·
                refine ⟨7451317236100793233885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19870179296268781957028237 7451317236100793233885589)
                ·
                  refine ⟨349280495442224682838387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7451317236100793233885589 349280495442224682838387)
                  ·
                    rfl

theorem cell22_3060996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_3060996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060996 prefixEnd_3060996 := by exact prefixLift 3060996
  have htrace : WordTrace (prefixWord ++ tailWord_3060996) baseStart_3060996 baseEnd_3060996 := by
    simpa [prefixWord, tailWord_3060996, baseEnd_3060996] using wordTrace_append hprefix tailTrace_3060996
  have hstable : (prefixWord ++ tailWord_3060996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060996).length < 2 ^ (prefixWord ++ tailWord_3060996).sum := by decide
  have hdescent : baseEnd_3060996 < baseStart_3060996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061009 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3061009 : Nat := 118140960795 + 3061009 * 2 ^ 59
def prefixEnd_3061009 : Nat := 4983230072969 + 3 ^ 40 * 3061009 * 2
def baseEnd_3061009 : Nat := 1047845936492346347940121

theorem tailTrace_3061009 : CollatzResearch.WordTrace tailWord_3061009 prefixEnd_3061009 1047845936492346347940121 := by
  unfold tailWord_3061009
  simp only [CollatzResearch.WordTrace]
  refine ⟨111644170167494646561770081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74429446778329764374513387 111644170167494646561770081)
  ·
    refine ⟨83733127625620984921327561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111644170167494646561770081 83733127625620984921327561)
    ·
      refine ⟨62799845719215738690995671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83733127625620984921327561 62799845719215738690995671)
      ·
        refine ⟨94199768578823608036493507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62799845719215738690995671 94199768578823608036493507)
        ·
          refine ⟨141299652868235412054740261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94199768578823608036493507 141299652868235412054740261)
          ·
            refine ⟨26493684912794139760263799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141299652868235412054740261 26493684912794139760263799)
            ·
              refine ⟨39740527369191209640395699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26493684912794139760263799 39740527369191209640395699)
              ·
                refine ⟨59610791053786814460593549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39740527369191209640395699 59610791053786814460593549)
                ·
                  refine ⟨22354046645170055422722581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59610791053786814460593549 22354046645170055422722581)
                  ·
                    refine ⟨1047845936492346347940121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22354046645170055422722581 1047845936492346347940121)
                    ·
                      rfl

theorem cell22_3061009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3061009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061009 prefixEnd_3061009 := by exact prefixLift 3061009
  have htrace : WordTrace (prefixWord ++ tailWord_3061009) baseStart_3061009 baseEnd_3061009 := by
    simpa [prefixWord, tailWord_3061009, baseEnd_3061009] using wordTrace_append hprefix tailTrace_3061009
  have hstable : (prefixWord ++ tailWord_3061009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061009).length < 2 ^ (prefixWord ++ tailWord_3061009).sum := by decide
  have hdescent : baseEnd_3061009 < baseStart_3061009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061041 : List Nat := [1, 2, 2, 3, 3, 3, 8]
def baseStart_3061041 : Nat := 118140960795 + 3061041 * 2 ^ 59
def prefixEnd_3061041 : Nat := 4983230072969 + 3 ^ 40 * 3061041 * 2
def baseEnd_3061041 : Nat := 38809514472085515968149

theorem tailTrace_3061041 : CollatzResearch.WordTrace tailWord_3061041 prefixEnd_3061041 38809514472085515968149 := by
  unfold tailWord_3061041
  simp only [CollatzResearch.WordTrace]
  refine ⟨111645337303378716026934977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74430224868919144017956651 111645337303378716026934977)
  ·
    refine ⟨83734002977534037020201233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111645337303378716026934977 83734002977534037020201233)
    ·
      refine ⟨62800502233150527765150925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83734002977534037020201233 62800502233150527765150925)
      ·
        refine ⟨23550188337431447911931597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62800502233150527765150925 23550188337431447911931597)
        ·
          refine ⟨8831320626536792966974349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23550188337431447911931597 8831320626536792966974349)
          ·
            refine ⟨3311745234951297362615381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8831320626536792966974349 3311745234951297362615381)
            ·
              refine ⟨38809514472085515968149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3311745234951297362615381 38809514472085515968149)
              ·
                rfl

theorem cell22_3061041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 8].length) (baseStart_3061041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061041 prefixEnd_3061041 := by exact prefixLift 3061041
  have htrace : WordTrace (prefixWord ++ tailWord_3061041) baseStart_3061041 baseEnd_3061041 := by
    simpa [prefixWord, tailWord_3061041, baseEnd_3061041] using wordTrace_append hprefix tailTrace_3061041
  have hstable : (prefixWord ++ tailWord_3061041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061041).length < 2 ^ (prefixWord ++ tailWord_3061041).sum := by decide
  have hdescent : baseEnd_3061041 < baseStart_3061041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061116 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_3061116 : Nat := 118140960795 + 3061116 * 2 ^ 59
def prefixEnd_3061116 : Nat := 4983230072969 + 3 ^ 40 * 3061116 * 2
def baseEnd_3061116 : Nat := 1047882564779033735514793

theorem tailTrace_3061116 : CollatzResearch.WordTrace tailWord_3061116 prefixEnd_3061116 1047882564779033735514793 := by
  unfold tailWord_3061116
  simp only [CollatzResearch.WordTrace]
  refine ⟨55824036389053501917957601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74432048518738002557276801 55824036389053501917957601)
  ·
    refine ⟨41868027291790126438468201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55824036389053501917957601 41868027291790126438468201)
    ·
      refine ⟨31401020468842594828851151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41868027291790126438468201 31401020468842594828851151)
      ·
        refine ⟨47101530703263892243276727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31401020468842594828851151 47101530703263892243276727)
        ·
          refine ⟨70652296054895838364915091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47101530703263892243276727 70652296054895838364915091)
          ·
            refine ⟨105978444082343757547372637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70652296054895838364915091 105978444082343757547372637)
            ·
              refine ⟨39741916530878909080264739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105978444082343757547372637 39741916530878909080264739)
              ·
                refine ⟨59612874796318363620397109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39741916530878909080264739 59612874796318363620397109)
                ·
                  refine ⟨5588707012154846589412229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59612874796318363620397109 5588707012154846589412229)
                  ·
                    refine ⟨1047882564779033735514793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5588707012154846589412229 1047882564779033735514793)
                    ·
                      rfl

theorem cell22_3061116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_3061116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061116 prefixEnd_3061116 := by exact prefixLift 3061116
  have htrace : WordTrace (prefixWord ++ tailWord_3061116) baseStart_3061116 baseEnd_3061116 := by
    simpa [prefixWord, tailWord_3061116, baseEnd_3061116] using wordTrace_append hprefix tailTrace_3061116
  have hstable : (prefixWord ++ tailWord_3061116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061116).length < 2 ^ (prefixWord ++ tailWord_3061116).sum := by decide
  have hdescent : baseEnd_3061116 < baseStart_3061116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061131 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 6]
def baseStart_3061131 : Nat := 118140960795 + 3061131 * 2 ^ 59
def prefixEnd_3061131 : Nat := 4983230072969 + 3 ^ 40 * 3061131 * 2
def baseEnd_3061131 : Nat := 349295899861859565463249

theorem tailTrace_3061131 : CollatzResearch.WordTrace tailWord_3061131 prefixEnd_3061131 349295899861859565463249 := by
  unfold tailWord_3061131
  simp only [CollatzResearch.WordTrace]
  refine ⟨111648619873052661397711247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74432413248701774265140831 111648619873052661397711247)
  ·
    refine ⟨167472929809578992096566871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111648619873052661397711247 167472929809578992096566871)
    ·
      refine ⟨251209394714368488144850307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167472929809578992096566871 251209394714368488144850307)
      ·
        refine ⟨376814092071552732217275461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251209394714368488144850307 376814092071552732217275461)
        ·
          refine ⟨70652642263416137290739149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376814092071552732217275461 70652642263416137290739149)
          ·
            refine ⟨26494740848781051484027181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70652642263416137290739149 26494740848781051484027181)
            ·
              refine ⟨9935527818292894306510193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26494740848781051484027181 9935527818292894306510193)
              ·
                refine ⟨7451645863719670729882645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9935527818292894306510193 7451645863719670729882645)
                ·
                  refine ⟨349295899861859565463249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7451645863719670729882645 349295899861859565463249)
                  ·
                    rfl

theorem cell22_3061131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_3061131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061131 prefixEnd_3061131 := by exact prefixLift 3061131
  have htrace : WordTrace (prefixWord ++ tailWord_3061131) baseStart_3061131 baseEnd_3061131 := by
    simpa [prefixWord, tailWord_3061131, baseEnd_3061131] using wordTrace_append hprefix tailTrace_3061131
  have hstable : (prefixWord ++ tailWord_3061131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061131).length < 2 ^ (prefixWord ++ tailWord_3061131).sum := by decide
  have hdescent : baseEnd_3061131 < baseStart_3061131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061165 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 6]
def baseStart_3061165 : Nat := 118140960795 + 3061165 * 2 ^ 59
def prefixEnd_3061165 : Nat := 4983230072969 + 3 ^ 40 * 3061165 * 2
def baseEnd_3061165 : Nat := 349299779493471313679881

theorem tailTrace_3061165 : CollatzResearch.WordTrace tailWord_3061165 prefixEnd_3061165 349299779493471313679881 := by
  unfold tailWord_3061165
  simp only [CollatzResearch.WordTrace]
  refine ⟨111649859954929485204448949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74433239969952990136299299 111649859954929485204448949)
  ·
    refine ⟨10467174370774639237917089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111649859954929485204448949 10467174370774639237917089)
    ·
      refine ⟨7850380778080979428437817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10467174370774639237917089 7850380778080979428437817)
      ·
        refine ⟨5887785583560734571328363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7850380778080979428437817 5887785583560734571328363)
        ·
          refine ⟨8831678375341101856992545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887785583560734571328363 8831678375341101856992545)
          ·
            refine ⟨6623758781505826392744409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8831678375341101856992545 6623758781505826392744409)
            ·
              refine ⟨4967819086129369794558307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623758781505826392744409 4967819086129369794558307)
              ·
                refine ⟨7451728629194054691837461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967819086129369794558307 7451728629194054691837461)
                ·
                  refine ⟨349299779493471313679881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7451728629194054691837461 349299779493471313679881)
                  ·
                    rfl

theorem cell22_3061165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_3061165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061165 prefixEnd_3061165 := by exact prefixLift 3061165
  have htrace : WordTrace (prefixWord ++ tailWord_3061165) baseStart_3061165 baseEnd_3061165 := by
    simpa [prefixWord, tailWord_3061165, baseEnd_3061165] using wordTrace_append hprefix tailTrace_3061165
  have hstable : (prefixWord ++ tailWord_3061165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061165).length < 2 ^ (prefixWord ++ tailWord_3061165).sum := by decide
  have hdescent : baseEnd_3061165 < baseStart_3061165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061191 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3061191 : Nat := 118140960795 + 3061191 * 2 ^ 59
def prefixEnd_3061191 : Nat := 4983230072969 + 3 ^ 40 * 3061191 * 2
def baseEnd_3061191 : Nat := 1047908238811758539889563

theorem tailTrace_3061191 : CollatzResearch.WordTrace tailWord_3061191 prefixEnd_3061191 1047908238811758539889563 := by
  unfold tailWord_3061191
  simp only [CollatzResearch.WordTrace]
  refine ⟨111650808252835291644895427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74433872168556861096596951 111650808252835291644895427)
  ·
    refine ⟨167476212379252937467343141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111650808252835291644895427 167476212379252937467343141)
    ·
      refine ⟨31401789821109925775126839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167476212379252937467343141 31401789821109925775126839)
      ·
        refine ⟨47102684731664888662690259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31401789821109925775126839 47102684731664888662690259)
        ·
          refine ⟨70654027097497332994035389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47102684731664888662690259 70654027097497332994035389)
          ·
            refine ⟨26495260161561499872763271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70654027097497332994035389 26495260161561499872763271)
            ·
              refine ⟨39742890242342249809144907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26495260161561499872763271 39742890242342249809144907)
              ·
                refine ⟨59614335363513374713717361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39742890242342249809144907 59614335363513374713717361)
                ·
                  refine ⟨44710751522635031035288021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59614335363513374713717361 44710751522635031035288021)
                  ·
                    refine ⟨1047908238811758539889563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44710751522635031035288021 1047908238811758539889563)
                    ·
                      rfl

theorem cell22_3061191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3061191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061191 prefixEnd_3061191 := by exact prefixLift 3061191
  have htrace : WordTrace (prefixWord ++ tailWord_3061191) baseStart_3061191 baseEnd_3061191 := by
    simpa [prefixWord, tailWord_3061191, baseEnd_3061191] using wordTrace_append hprefix tailTrace_3061191
  have hstable : (prefixWord ++ tailWord_3061191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061191).length < 2 ^ (prefixWord ++ tailWord_3061191).sum := by decide
  have hdescent : baseEnd_3061191 < baseStart_3061191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061208 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_3061208 : Nat := 118140960795 + 3061208 * 2 ^ 59
def prefixEnd_3061208 : Nat := 4983230072969 + 3 ^ 40 * 3061208 * 2
def baseEnd_3061208 : Nat := 1047914058259176162214511

theorem tailTrace_3061208 : CollatzResearch.WordTrace tailWord_3061208 prefixEnd_3061208 1047914058259176162214511 := by
  unfold tailWord_3061208
  simp only [CollatzResearch.WordTrace]
  refine ⟨55825714146886851774132139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74434285529182469032176185 55825714146886851774132139)
  ·
    refine ⟨83738571220330277661198209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55825714146886851774132139 83738571220330277661198209)
    ·
      refine ⟨62803928415247708245898657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83738571220330277661198209 62803928415247708245898657)
      ·
        refine ⟨47102946311435781184423993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62803928415247708245898657 47102946311435781184423993)
        ·
          refine ⟨35327209733576835888317995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47102946311435781184423993 35327209733576835888317995)
          ·
            refine ⟨52990814600365253832476993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35327209733576835888317995 52990814600365253832476993)
            ·
              refine ⟨39743110950273940374357745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52990814600365253832476993 39743110950273940374357745)
              ·
                refine ⟨29807333212705455280768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39743110950273940374357745 29807333212705455280768309)
                ·
                  refine ⟨2794437488691136432572029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29807333212705455280768309 2794437488691136432572029)
                  ·
                    refine ⟨1047914058259176162214511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2794437488691136432572029 1047914058259176162214511)
                    ·
                      rfl

theorem cell22_3061208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_3061208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061208 prefixEnd_3061208 := by exact prefixLift 3061208
  have htrace : WordTrace (prefixWord ++ tailWord_3061208) baseStart_3061208 baseEnd_3061208 := by
    simpa [prefixWord, tailWord_3061208, baseEnd_3061208] using wordTrace_append hprefix tailTrace_3061208
  have hstable : (prefixWord ++ tailWord_3061208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061208).length < 2 ^ (prefixWord ++ tailWord_3061208).sum := by decide
  have hdescent : baseEnd_3061208 < baseStart_3061208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061319 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3061319 : Nat := 118140960795 + 3061319 * 2 ^ 59
def prefixEnd_3061319 : Nat := 4983230072969 + 3 ^ 40 * 3061319 * 2
def baseEnd_3061319 : Nat := 1047952055827608872689171

theorem tailTrace_3061319 : CollatzResearch.WordTrace tailWord_3061319 prefixEnd_3061319 1047952055827608872689171 := by
  unfold tailWord_3061319
  simp only [CollatzResearch.WordTrace]
  refine ⟨111655476796371569505555011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74436984530914379670370007 111655476796371569505555011)
  ·
    refine ⟨167483215194557354258332517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111655476796371569505555011 167483215194557354258332517)
    ·
      refine ⟨31403102848979503923437347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167483215194557354258332517 31403102848979503923437347)
      ·
        refine ⟨47104654273469255885156021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31403102848979503923437347 47104654273469255885156021)
        ·
          refine ⟨4416061338137742739233377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47104654273469255885156021 4416061338137742739233377)
          ·
            refine ⟨3312046003603307054425033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416061338137742739233377 3312046003603307054425033)
            ·
              refine ⟨2484034502702480290818775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3312046003603307054425033 2484034502702480290818775)
              ·
                refine ⟨3726051754053720436228163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484034502702480290818775 3726051754053720436228163)
                ·
                  refine ⟨5589077631080580654342245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726051754053720436228163 5589077631080580654342245)
                  ·
                    refine ⟨1047952055827608872689171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589077631080580654342245 1047952055827608872689171)
                    ·
                      rfl

theorem cell22_3061319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3061319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061319 prefixEnd_3061319 := by exact prefixLift 3061319
  have htrace : WordTrace (prefixWord ++ tailWord_3061319) baseStart_3061319 baseEnd_3061319 := by
    simpa [prefixWord, tailWord_3061319, baseEnd_3061319] using wordTrace_append hprefix tailTrace_3061319
  have hstable : (prefixWord ++ tailWord_3061319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061319).length < 2 ^ (prefixWord ++ tailWord_3061319).sum := by decide
  have hdescent : baseEnd_3061319 < baseStart_3061319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061349 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_3061349 : Nat := 118140960795 + 3061349 * 2 ^ 59
def prefixEnd_3061349 : Nat := 4983230072969 + 3 ^ 40 * 3061349 * 2
def baseEnd_3061349 : Nat := 1047962325440698794439079

theorem tailTrace_3061349 : CollatzResearch.WordTrace tailWord_3061349 prefixEnd_3061349 1047962325440698794439079 := by
  unfold tailWord_3061349
  simp only [CollatzResearch.WordTrace]
  refine ⟨111656570986262884629147101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74437713990841923086098067 111656570986262884629147101)
  ·
    refine ⟨41871214119848581735930163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111656570986262884629147101 41871214119848581735930163)
    ·
      refine ⟨62806821179772872603895245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41871214119848581735930163 62806821179772872603895245)
      ·
        refine ⟨23552557942414827226460717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62806821179772872603895245 23552557942414827226460717)
        ·
          refine ⟨8832209228405560209922769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23552557942414827226460717 8832209228405560209922769)
          ·
            refine ⟨6624156921304170157442077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8832209228405560209922769 6624156921304170157442077)
            ·
              refine ⟨2484058845489063809040779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6624156921304170157442077 2484058845489063809040779)
              ·
                refine ⟨3726088268233595713561169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484058845489063809040779 3726088268233595713561169)
                ·
                  refine ⟨2794566201175196785170877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3726088268233595713561169 2794566201175196785170877)
                  ·
                    refine ⟨1047962325440698794439079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2794566201175196785170877 1047962325440698794439079)
                    ·
                      rfl

theorem cell22_3061349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_3061349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061349 prefixEnd_3061349 := by exact prefixLift 3061349
  have htrace : WordTrace (prefixWord ++ tailWord_3061349) baseStart_3061349 baseEnd_3061349 := by
    simpa [prefixWord, tailWord_3061349, baseEnd_3061349] using wordTrace_append hprefix tailTrace_3061349
  have hstable : (prefixWord ++ tailWord_3061349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061349).length < 2 ^ (prefixWord ++ tailWord_3061349).sum := by decide
  have hdescent : baseEnd_3061349 < baseStart_3061349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061362 : List Nat := [3, 2, 1, 2, 3, 3, 2, 6]
def baseStart_3061362 : Nat := 118140960795 + 3061362 * 2 ^ 59
def prefixEnd_3061362 : Nat := 4983230072969 + 3 ^ 40 * 3061362 * 2
def baseEnd_3061362 : Nat := 116440752845152343762671

theorem tailTrace_3061362 : CollatzResearch.WordTrace tailWord_3061362 prefixEnd_3061362 116440752845152343762671 := by
  unfold tailWord_3061362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27914261283803946962342585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74438030090143858566246893 27914261283803946962342585)
  ·
    refine ⟨20935695962852960221756939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27914261283803946962342585 20935695962852960221756939)
    ·
      refine ⟨31403543944279440332635409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20935695962852960221756939 31403543944279440332635409)
      ·
        refine ⟨23552657958209580249476557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31403543944279440332635409 23552657958209580249476557)
        ·
          refine ⟨8832246734328592593553709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23552657958209580249476557 8832246734328592593553709)
          ·
            refine ⟨3312092525373222222582641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8832246734328592593553709 3312092525373222222582641)
            ·
              refine ⟨2484069394029916666936981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3312092525373222222582641 2484069394029916666936981)
              ·
                refine ⟨116440752845152343762671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2484069394029916666936981 116440752845152343762671)
                ·
                  rfl

theorem cell22_3061362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_3061362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061362 prefixEnd_3061362 := by exact prefixLift 3061362
  have htrace : WordTrace (prefixWord ++ tailWord_3061362) baseStart_3061362 baseEnd_3061362 := by
    simpa [prefixWord, tailWord_3061362, baseEnd_3061362] using wordTrace_append hprefix tailTrace_3061362
  have hstable : (prefixWord ++ tailWord_3061362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061362).length < 2 ^ (prefixWord ++ tailWord_3061362).sum := by decide
  have hdescent : baseEnd_3061362 < baseStart_3061362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061390 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3061390 : Nat := 118140960795 + 3061390 * 2 ^ 59
def prefixEnd_3061390 : Nat := 4983230072969 + 3 ^ 40 * 3061390 * 2
def baseEnd_3061390 : Nat := 349325453526196118054651

theorem tailTrace_3061390 : CollatzResearch.WordTrace tailWord_3061390 prefixEnd_3061390 349325453526196118054651 := by
  unfold tailWord_3061390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957258297389293578923703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74438710919409565754259749 13957258297389293578923703)
  ·
    refine ⟨20935887446083940368385555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13957258297389293578923703 20935887446083940368385555)
    ·
      refine ⟨31403831169125910552578333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20935887446083940368385555 31403831169125910552578333)
      ·
        refine ⟨11776436688422216457216875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31403831169125910552578333 11776436688422216457216875)
        ·
          refine ⟨17664655032633324685825313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11776436688422216457216875 17664655032633324685825313)
          ·
            refine ⟨13248491274474993514368985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17664655032633324685825313 13248491274474993514368985)
            ·
              refine ⟨9936368455856245135776739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13248491274474993514368985 9936368455856245135776739)
              ·
                refine ⟨14904552683784367703665109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936368455856245135776739 14904552683784367703665109)
                ·
                  refine ⟨349325453526196118054651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14904552683784367703665109 349325453526196118054651)
                  ·
                    rfl

theorem cell22_3061390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3061390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061390 prefixEnd_3061390 := by exact prefixLift 3061390
  have htrace : WordTrace (prefixWord ++ tailWord_3061390) baseStart_3061390 baseEnd_3061390 := by
    simpa [prefixWord, tailWord_3061390, baseEnd_3061390] using wordTrace_append hprefix tailTrace_3061390
  have hstable : (prefixWord ++ tailWord_3061390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061390).length < 2 ^ (prefixWord ++ tailWord_3061390).sum := by decide
  have hdescent : baseEnd_3061390 < baseStart_3061390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061469 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 6]
def baseStart_3061469 : Nat := 118140960795 + 3061469 * 2 ^ 59
def prefixEnd_3061469 : Nat := 4983230072969 + 3 ^ 40 * 3061469 * 2
def baseEnd_3061469 : Nat := 349334467964352827146237

theorem tailTrace_3061469 : CollatzResearch.WordTrace tailWord_3061469 prefixEnd_3061469 349334467964352827146237 := by
  unfold tailWord_3061469
  simp only [CollatzResearch.WordTrace]
  refine ⟨111660947745828145123515461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74440631830552096749010307 111660947745828145123515461)
  ·
    refine ⟨20936427702342777210659149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111660947745828145123515461 20936427702342777210659149)
    ·
      refine ⟨7851160388378541453997181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20936427702342777210659149 7851160388378541453997181)
      ·
        refine ⟨2944185145641953045248943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7851160388378541453997181 2944185145641953045248943)
        ·
          refine ⟨4416277718462929567873415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944185145641953045248943 4416277718462929567873415)
          ·
            refine ⟨6624416577694394351810123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416277718462929567873415 6624416577694394351810123)
            ·
              refine ⟨9936624866541591527715185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624416577694394351810123 9936624866541591527715185)
              ·
                refine ⟨7452468649906193645786389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9936624866541591527715185 7452468649906193645786389)
                ·
                  refine ⟨349334467964352827146237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7452468649906193645786389 349334467964352827146237)
                  ·
                    rfl

theorem cell22_3061469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_3061469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061469 prefixEnd_3061469 := by exact prefixLift 3061469
  have htrace : WordTrace (prefixWord ++ tailWord_3061469) baseStart_3061469 baseEnd_3061469 := by
    simpa [prefixWord, tailWord_3061469, baseEnd_3061469] using wordTrace_append hprefix tailTrace_3061469
  have hstable : (prefixWord ++ tailWord_3061469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061469).length < 2 ^ (prefixWord ++ tailWord_3061469).sum := by decide
  have hdescent : baseEnd_3061469 < baseStart_3061469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061482 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3061482 : Nat := 118140960795 + 3061482 * 2 ^ 59
def prefixEnd_3061482 : Nat := 4983230072969 + 3 ^ 40 * 3061482 * 2
def baseEnd_3061482 : Nat := 1048007854058730780863671

theorem tailTrace_3061482 : CollatzResearch.WordTrace tailWord_3061482 prefixEnd_3061482 1048007854058730780863671 := by
  unfold tailWord_3061482
  simp only [CollatzResearch.WordTrace]
  refine ⟨27915355473695262085934675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74440947929854032229159133 27915355473695262085934675)
  ·
    refine ⟨41873033210542893128902013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27915355473695262085934675 41873033210542893128902013)
    ·
      refine ⟨15702387453953584923338255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41873033210542893128902013 15702387453953584923338255)
      ·
        refine ⟨23553581180930377385007383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15702387453953584923338255 23553581180930377385007383)
        ·
          refine ⟨35330371771395566077511075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23553581180930377385007383 35330371771395566077511075)
          ·
            refine ⟨52995557657093349116266613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35330371771395566077511075 52995557657093349116266613)
            ·
              refine ⟨4968333530352501479649995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52995557657093349116266613 4968333530352501479649995)
              ·
                refine ⟨7452500295528752219474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968333530352501479649995 7452500295528752219474993)
                ·
                  refine ⟨5589375221646564164606245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7452500295528752219474993 5589375221646564164606245)
                  ·
                    refine ⟨1048007854058730780863671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589375221646564164606245 1048007854058730780863671)
                    ·
                      rfl

theorem cell22_3061482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3061482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061482 prefixEnd_3061482 := by exact prefixLift 3061482
  have htrace : WordTrace (prefixWord ++ tailWord_3061482) baseStart_3061482 baseEnd_3061482 := by
    simpa [prefixWord, tailWord_3061482, baseEnd_3061482] using wordTrace_append hprefix tailTrace_3061482
  have hstable : (prefixWord ++ tailWord_3061482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061482).length < 2 ^ (prefixWord ++ tailWord_3061482).sum := by decide
  have hdescent : baseEnd_3061482 < baseStart_3061482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061589 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3061589 : Nat := 118140960795 + 3061589 * 2 ^ 59
def prefixEnd_3061589 : Nat := 4983230072969 + 3 ^ 40 * 3061589 * 2
def baseEnd_3061589 : Nat := 1048044482345418168438343

theorem tailTrace_3061589 : CollatzResearch.WordTrace tailWord_3061589 prefixEnd_3061589 1048044482345418168438343 := by
  unfold tailWord_3061589
  simp only [CollatzResearch.WordTrace]
  refine ⟨111665324505393405617883821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74443549670262270411922547 111665324505393405617883821)
  ·
    refine ⟨41874496689522527106706433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111665324505393405617883821 41874496689522527106706433)
    ·
      refine ⟨31405872517141895330029825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41874496689522527106706433 31405872517141895330029825)
      ·
        refine ⟨23554404387856421497522369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31405872517141895330029825 23554404387856421497522369)
        ·
          refine ⟨17665803290892316123141777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23554404387856421497522369 17665803290892316123141777)
          ·
            refine ⟨13249352468169237092356333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17665803290892316123141777 13249352468169237092356333)
            ·
              refine ⟨4968507175563463909633625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13249352468169237092356333 4968507175563463909633625)
              ·
                refine ⟨3726380381672597932225219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4968507175563463909633625 3726380381672597932225219)
                ·
                  refine ⟨5589570572508896898337829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726380381672597932225219 5589570572508896898337829)
                  ·
                    refine ⟨1048044482345418168438343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589570572508896898337829 1048044482345418168438343)
                    ·
                      rfl

theorem cell22_3061589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3061589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061589 prefixEnd_3061589 := by exact prefixLift 3061589
  have htrace : WordTrace (prefixWord ++ tailWord_3061589) baseStart_3061589 baseEnd_3061589 := by
    simpa [prefixWord, tailWord_3061589, baseEnd_3061589] using wordTrace_append hprefix tailTrace_3061589
  have hstable : (prefixWord ++ tailWord_3061589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061589).length < 2 ^ (prefixWord ++ tailWord_3061589).sum := by decide
  have hdescent : baseEnd_3061589 < baseStart_3061589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061617 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3061617 : Nat := 118140960795 + 3061617 * 2 ^ 59
def prefixEnd_3061617 : Nat := 4983230072969 + 3 ^ 40 * 3061617 * 2
def baseEnd_3061617 : Nat := 1048054067317635428738257

theorem tailTrace_3061617 : CollatzResearch.WordTrace tailWord_3061617 prefixEnd_3061617 1048054067317635428738257 := by
  unfold tailWord_3061617
  simp only [CollatzResearch.WordTrace]
  refine ⟨111666345749291966399903105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74444230499527977599935403 111666345749291966399903105)
  ·
    refine ⟨83749759311968974799927329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111666345749291966399903105 83749759311968974799927329)
    ·
      refine ⟨62812319483976731099945497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83749759311968974799927329 62812319483976731099945497)
      ·
        refine ⟨47109239612982548324959123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62812319483976731099945497 47109239612982548324959123)
        ·
          refine ⟨70663859419473822487438685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47109239612982548324959123 70663859419473822487438685)
          ·
            refine ⟨26498947282302683432789507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70663859419473822487438685 26498947282302683432789507)
            ·
              refine ⟨39748420923454025149184261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26498947282302683432789507 39748420923454025149184261)
              ·
                refine ⟨7452828923147629715472049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39748420923454025149184261 7452828923147629715472049)
                ·
                  refine ⟨5589621692360722286604037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7452828923147629715472049 5589621692360722286604037)
                  ·
                    refine ⟨1048054067317635428738257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589621692360722286604037 1048054067317635428738257)
                    ·
                      rfl

theorem cell22_3061617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3061617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061617 prefixEnd_3061617 := by exact prefixLift 3061617
  have htrace : WordTrace (prefixWord ++ tailWord_3061617) baseStart_3061617 baseEnd_3061617 := by
    simpa [prefixWord, tailWord_3061617, baseEnd_3061617] using wordTrace_append hprefix tailTrace_3061617
  have hstable : (prefixWord ++ tailWord_3061617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061617).length < 2 ^ (prefixWord ++ tailWord_3061617).sum := by decide
  have hdescent : baseEnd_3061617 < baseStart_3061617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061681 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_3061681 : Nat := 118140960795 + 3061681 * 2 ^ 59
def prefixEnd_3061681 : Nat := 4983230072969 + 3 ^ 40 * 3061681 * 2
def baseEnd_3061681 : Nat := 1048075975825560595138061

theorem tailTrace_3061681 : CollatzResearch.WordTrace tailWord_3061681 prefixEnd_3061681 1048075975825560595138061 := by
  unfold tailWord_3061681
  simp only [CollatzResearch.WordTrace]
  refine ⟨111668680021060105330232897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74445786680706736886821931 111668680021060105330232897)
  ·
    refine ⟨83751510015795078997674673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111668680021060105330232897 83751510015795078997674673)
    ·
      refine ⟨62813632511846309248256005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83751510015795078997674673 62813632511846309248256005)
      ·
        refine ⟨11777556095971182984048001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62813632511846309248256005 11777556095971182984048001)
        ·
          refine ⟨8833167071978387238036001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11777556095971182984048001 8833167071978387238036001)
          ·
            refine ⟨6624875303983790428527001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8833167071978387238036001 6624875303983790428527001)
            ·
              refine ⟨4968656477987842821395251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6624875303983790428527001 4968656477987842821395251)
              ·
                refine ⟨7452984716981764232092877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968656477987842821395251 7452984716981764232092877)
                ·
                  refine ⟨2794869268868161587034829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7452984716981764232092877 2794869268868161587034829)
                  ·
                    refine ⟨1048075975825560595138061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2794869268868161587034829 1048075975825560595138061)
                    ·
                      rfl

theorem cell22_3061681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_3061681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061681 prefixEnd_3061681 := by exact prefixLift 3061681
  have htrace : WordTrace (prefixWord ++ tailWord_3061681) baseStart_3061681 baseEnd_3061681 := by
    simpa [prefixWord, tailWord_3061681, baseEnd_3061681] using wordTrace_append hprefix tailTrace_3061681
  have hstable : (prefixWord ++ tailWord_3061681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061681).length < 2 ^ (prefixWord ++ tailWord_3061681).sum := by decide
  have hdescent : baseEnd_3061681 < baseStart_3061681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061739 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 4]
def baseStart_3061739 : Nat := 118140960795 + 3061739 * 2 ^ 59
def prefixEnd_3061739 : Nat := 4983230072969 + 3 ^ 40 * 3061739 * 2
def baseEnd_3061739 : Nat := 349365276803622592395961

theorem tailTrace_3061739 : CollatzResearch.WordTrace tailWord_3061739 prefixEnd_3061739 349365276803622592395961 := by
  unfold tailWord_3061739
  simp only [CollatzResearch.WordTrace]
  refine ⟨111670795454849981235844271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74447196969899987490562847 111670795454849981235844271)
  ·
    refine ⟨167506193182274971853766407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111670795454849981235844271 167506193182274971853766407)
    ·
      refine ⟨251259289773412457780649611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167506193182274971853766407 251259289773412457780649611)
      ·
        refine ⟨376888934660118686670974417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251259289773412457780649611 376888934660118686670974417)
        ·
          refine ⟨282666700995089015003230813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376888934660118686670974417 282666700995089015003230813)
          ·
            refine ⟨106000012873158380626211555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282666700995089015003230813 106000012873158380626211555)
            ·
              refine ⟨159000019309737570939317333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106000012873158380626211555 159000019309737570939317333)
              ·
                refine ⟨1863281476285987159445125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 159000019309737570939317333 1863281476285987159445125)
                ·
                  refine ⟨349365276803622592395961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863281476285987159445125 349365276803622592395961)
                  ·
                    rfl

theorem cell22_3061739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 4].length) (baseStart_3061739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061739 prefixEnd_3061739 := by exact prefixLift 3061739
  have htrace : WordTrace (prefixWord ++ tailWord_3061739) baseStart_3061739 baseEnd_3061739 := by
    simpa [prefixWord, tailWord_3061739, baseEnd_3061739] using wordTrace_append hprefix tailTrace_3061739
  have hstable : (prefixWord ++ tailWord_3061739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061739).length < 2 ^ (prefixWord ++ tailWord_3061739).sum := by decide
  have hdescent : baseEnd_3061739 < baseStart_3061739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061752 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_3061752 : Nat := 118140960795 + 3061752 * 2 ^ 59
def prefixEnd_3061752 : Nat := 4983230072969 + 3 ^ 40 * 3061752 * 2
def baseEnd_3061752 : Nat := 1048100280576540076612843

theorem tailTrace_3061752 : CollatzResearch.WordTrace tailWord_3061752 prefixEnd_3061752 1048100280576540076612843 := by
  unfold tailWord_3061752
  simp only [CollatzResearch.WordTrace]
  refine ⟨55835634801901442228033755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74447513069201922970711673 55835634801901442228033755)
  ·
    refine ⟨83753452202852163342050633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55835634801901442228033755 83753452202852163342050633)
    ·
      refine ⟨62815089152139122506537975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83753452202852163342050633 62815089152139122506537975)
      ·
        refine ⟨94222633728208683759806963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62815089152139122506537975 94222633728208683759806963)
        ·
          refine ⟨141333950592313025639710445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94222633728208683759806963 141333950592313025639710445)
          ·
            refine ⟨53000231472117384614891417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141333950592313025639710445 53000231472117384614891417)
            ·
              refine ⟨39750173604088038461168563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53000231472117384614891417 39750173604088038461168563)
              ·
                refine ⟨59625260406132057691752845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39750173604088038461168563 59625260406132057691752845)
                ·
                  refine ⟨22359472652299521634407317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59625260406132057691752845 22359472652299521634407317)
                  ·
                    refine ⟨1048100280576540076612843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22359472652299521634407317 1048100280576540076612843)
                    ·
                      rfl

theorem cell22_3061752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_3061752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061752 prefixEnd_3061752 := by exact prefixLift 3061752
  have htrace : WordTrace (prefixWord ++ tailWord_3061752) baseStart_3061752 baseEnd_3061752 := by
    simpa [prefixWord, tailWord_3061752, baseEnd_3061752] using wordTrace_append hprefix tailTrace_3061752
  have hstable : (prefixWord ++ tailWord_3061752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061752).length < 2 ^ (prefixWord ++ tailWord_3061752).sum := by decide
  have hdescent : baseEnd_3061752 < baseStart_3061752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061758 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3061758 : Nat := 118140960795 + 3061758 * 2 ^ 59
def prefixEnd_3061758 : Nat := 4983230072969 + 3 ^ 40 * 3061758 * 2
def baseEnd_3061758 : Nat := 1048102334499158060962825

theorem tailTrace_3061758 : CollatzResearch.WordTrace tailWord_3061758 prefixEnd_3061758 1048102334499158060962825 := by
  unfold tailWord_3061758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13958936055222643435098241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74447658961187431653857285 13958936055222643435098241)
  ·
    refine ⟨10469202041416982576323681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13958936055222643435098241 10469202041416982576323681)
    ·
      refine ⟨7851901531062736932242761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10469202041416982576323681 7851901531062736932242761)
      ·
        refine ⟨5888926148297052699182071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7851901531062736932242761 5888926148297052699182071)
        ·
          refine ⟨8833389222445579048773107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5888926148297052699182071 8833389222445579048773107)
          ·
            refine ⟨13250083833668368573159661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8833389222445579048773107 13250083833668368573159661)
            ·
              refine ⟨4968781437625638214934873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13250083833668368573159661 4968781437625638214934873)
              ·
                refine ⟨3726586078219228661201155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4968781437625638214934873 3726586078219228661201155)
                ·
                  refine ⟨5589879117328842991801733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726586078219228661201155 5589879117328842991801733)
                  ·
                    refine ⟨1048102334499158060962825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589879117328842991801733 1048102334499158060962825)
                    ·
                      rfl

theorem cell22_3061758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3061758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061758 prefixEnd_3061758 := by exact prefixLift 3061758
  have htrace : WordTrace (prefixWord ++ tailWord_3061758) baseStart_3061758 baseEnd_3061758 := by
    simpa [prefixWord, tailWord_3061758, baseEnd_3061758] using wordTrace_append hprefix tailTrace_3061758
  have hstable : (prefixWord ++ tailWord_3061758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061758).length < 2 ^ (prefixWord ++ tailWord_3061758).sum := by decide
  have hdescent : baseEnd_3061758 < baseStart_3061758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061788 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3061788 : Nat := 118140960795 + 3061788 * 2 ^ 59
def prefixEnd_3061788 : Nat := 4983230072969 + 3 ^ 40 * 3061788 * 2
def baseEnd_3061788 : Nat := 1048112604112247982712733

theorem tailTrace_3061788 : CollatzResearch.WordTrace tailWord_3061788 prefixEnd_3061788 1048112604112247982712733 := by
  unfold tailWord_3061788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55836291315836231302189009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74448388421114975069585345 55836291315836231302189009)
  ·
    refine ⟨41877218486877173476641757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55836291315836231302189009 41877218486877173476641757)
    ·
      refine ⟨15703956932578940053740659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41877218486877173476641757 15703956932578940053740659)
      ·
        refine ⟨23555935398868410080610989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15703956932578940053740659 23555935398868410080610989)
        ·
          refine ⟨8833475774575653780229121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23555935398868410080610989 8833475774575653780229121)
          ·
            refine ⟨6625106830931740335171841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8833475774575653780229121 6625106830931740335171841)
            ·
              refine ⟨4968830123198805251378881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6625106830931740335171841 4968830123198805251378881)
              ·
                refine ⟨3726622592399103938534161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4968830123198805251378881 3726622592399103938534161)
                ·
                  refine ⟨2794966944299327953900621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3726622592399103938534161 2794966944299327953900621)
                  ·
                    refine ⟨1048112604112247982712733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2794966944299327953900621 1048112604112247982712733)
                    ·
                      rfl

theorem cell22_3061788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3061788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061788 prefixEnd_3061788 := by exact prefixLift 3061788
  have htrace : WordTrace (prefixWord ++ tailWord_3061788) baseStart_3061788 baseEnd_3061788 := by
    simpa [prefixWord, tailWord_3061788, baseEnd_3061788] using wordTrace_append hprefix tailTrace_3061788
  have hstable : (prefixWord ++ tailWord_3061788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061788).length < 2 ^ (prefixWord ++ tailWord_3061788).sum := by decide
  have hdescent : baseEnd_3061788 < baseStart_3061788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061833 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 1, 3]
def baseStart_3061833 : Nat := 118140960795 + 3061833 * 2 ^ 59
def prefixEnd_3061833 : Nat := 4983230072969 + 3 ^ 40 * 3061833 * 2
def baseEnd_3061833 : Nat := 1048128008531882865337595

theorem tailTrace_3061833 : CollatzResearch.WordTrace tailWord_3061833 prefixEnd_3061833 1048128008531882865337595 := by
  unfold tailWord_3061833
  simp only [CollatzResearch.WordTrace]
  refine ⟨111674223916509435289766153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74449482611006290193177435 111674223916509435289766153)
  ·
    refine ⟨83755667937382076467324615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111674223916509435289766153 83755667937382076467324615)
    ·
      refine ⟨125633501906073114700986923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83755667937382076467324615 125633501906073114700986923)
      ·
        refine ⟨188450252859109672051480385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125633501906073114700986923 188450252859109672051480385)
        ·
          refine ⟨141337689644332254038610289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188450252859109672051480385 141337689644332254038610289)
          ·
            refine ⟨106003267233249190528957717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141337689644332254038610289 106003267233249190528957717)
            ·
              refine ⟨4968903151558555806044893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106003267233249190528957717 4968903151558555806044893)
              ·
                refine ⟨1863338681834458427266835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4968903151558555806044893 1863338681834458427266835)
                ·
                  refine ⟨2795008022751687640900253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863338681834458427266835 2795008022751687640900253)
                  ·
                    refine ⟨1048128008531882865337595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795008022751687640900253 1048128008531882865337595)
                    ·
                      rfl

theorem cell22_3061833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_3061833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061833 prefixEnd_3061833 := by exact prefixLift 3061833
  have htrace : WordTrace (prefixWord ++ tailWord_3061833) baseStart_3061833 baseEnd_3061833 := by
    simpa [prefixWord, tailWord_3061833, baseEnd_3061833] using wordTrace_append hprefix tailTrace_3061833
  have hstable : (prefixWord ++ tailWord_3061833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061833).length < 2 ^ (prefixWord ++ tailWord_3061833).sum := by decide
  have hdescent : baseEnd_3061833 < baseStart_3061833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061859 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_3061859 : Nat := 118140960795 + 3061859 * 2 ^ 59
def prefixEnd_3061859 : Nat := 4983230072969 + 3 ^ 40 * 3061859 * 2
def baseEnd_3061859 : Nat := 1048136908863227464187515

theorem tailTrace_3061859 : CollatzResearch.WordTrace tailWord_3061859 prefixEnd_3061859 1048136908863227464187515 := by
  unfold tailWord_3061859
  simp only [CollatzResearch.WordTrace]
  refine ⟨111675172214415241730212631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74450114809610161153475087 111675172214415241730212631)
  ·
    refine ⟨167512758321622862595318947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111675172214415241730212631 167512758321622862595318947)
    ·
      refine ⟨251269137482434293892978421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167512758321622862595318947 251269137482434293892978421)
      ·
        refine ⟨23556481638978215052466727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251269137482434293892978421 23556481638978215052466727)
        ·
          refine ⟨35334722458467322578700091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23556481638978215052466727 35334722458467322578700091)
          ·
            refine ⟨53002083687700983868050137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35334722458467322578700091 53002083687700983868050137)
            ·
              refine ⟨39751562765775737901037603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53002083687700983868050137 39751562765775737901037603)
              ·
                refine ⟨59627344148663606851556405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39751562765775737901037603 59627344148663606851556405)
                ·
                  refine ⟨5590063513937213142333413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59627344148663606851556405 5590063513937213142333413)
                  ·
                    refine ⟨1048136908863227464187515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590063513937213142333413 1048136908863227464187515)
                    ·
                      rfl

theorem cell22_3061859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_3061859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061859 prefixEnd_3061859 := by exact prefixLift 3061859
  have htrace : WordTrace (prefixWord ++ tailWord_3061859) baseStart_3061859 baseEnd_3061859 := by
    simpa [prefixWord, tailWord_3061859, baseEnd_3061859] using wordTrace_append hprefix tailTrace_3061859
  have hstable : (prefixWord ++ tailWord_3061859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061859).length < 2 ^ (prefixWord ++ tailWord_3061859).sum := by decide
  have hdescent : baseEnd_3061859 < baseStart_3061859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061927 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3061927 : Nat := 118140960795 + 3061927 * 2 ^ 59
def prefixEnd_3061927 : Nat := 4983230072969 + 3 ^ 40 * 3061927 * 2
def baseEnd_3061927 : Nat := 1048160186652897953487307

theorem tailTrace_3061927 : CollatzResearch.WordTrace tailWord_3061927 prefixEnd_3061927 1048160186652897953487307 := by
  unfold tailWord_3061927
  simp only [CollatzResearch.WordTrace]
  refine ⟨111677652378168889343688035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74451768252112592895792023 111677652378168889343688035)
  ·
    refine ⟨167516478567253334015532053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111677652378168889343688035 167516478567253334015532053)
    ·
      refine ⟨7852334932840000031978065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167516478567253334015532053 7852334932840000031978065)
      ·
        refine ⟨5889251199630000023983549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7852334932840000031978065 5889251199630000023983549)
        ·
          refine ⟨2208469199861250008993831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5889251199630000023983549 2208469199861250008993831)
          ·
            refine ⟨3312703799791875013490747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208469199861250008993831 3312703799791875013490747)
            ·
              refine ⟨4969055699687812520236121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3312703799791875013490747 4969055699687812520236121)
              ·
                refine ⟨3726791774765859390177091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4969055699687812520236121 3726791774765859390177091)
                ·
                  refine ⟨5590187662148789085265637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726791774765859390177091 5590187662148789085265637)
                  ·
                    refine ⟨1048160186652897953487307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590187662148789085265637 1048160186652897953487307)
                    ·
                      rfl

theorem cell22_3061927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3061927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061927 prefixEnd_3061927 := by exact prefixLift 3061927
  have htrace : WordTrace (prefixWord ++ tailWord_3061927) baseStart_3061927 baseEnd_3061927 := by
    simpa [prefixWord, tailWord_3061927, baseEnd_3061927] using wordTrace_append hprefix tailTrace_3061927
  have hstable : (prefixWord ++ tailWord_3061927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061927).length < 2 ^ (prefixWord ++ tailWord_3061927).sum := by decide
  have hdescent : baseEnd_3061927 < baseStart_3061927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061953 : List Nat := [1, 2, 6, 1, 3, 9]
def baseStart_3061953 : Nat := 118140960795 + 3061953 * 2 ^ 59
def prefixEnd_3061953 : Nat := 4983230072969 + 3 ^ 40 * 3061953 * 2
def baseEnd_3061953 : Nat := 12940359098570895707867

theorem tailTrace_3061953 : CollatzResearch.WordTrace tailWord_3061953 prefixEnd_3061953 12940359098570895707867 := by
  unfold tailWord_3061953
  simp only [CollatzResearch.WordTrace]
  refine ⟨111678600676074695784134513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74452400450716463856089675 111678600676074695784134513)
  ·
    refine ⟨83758950507056021838100885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111678600676074695784134513 83758950507056021838100885)
    ·
      refine ⟨3926200805018251023660979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83758950507056021838100885 3926200805018251023660979)
      ·
        refine ⟨5889301207527376535491469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926200805018251023660979 5889301207527376535491469)
        ·
          refine ⟨2208487952822766200809301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5889301207527376535491469 2208487952822766200809301)
          ·
            refine ⟨12940359098570895707867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2208487952822766200809301 12940359098570895707867)
            ·
              rfl

theorem cell22_3061953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 9].length) (baseStart_3061953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061953 prefixEnd_3061953 := by exact prefixLift 3061953
  have htrace : WordTrace (prefixWord ++ tailWord_3061953) baseStart_3061953 baseEnd_3061953 := by
    simpa [prefixWord, tailWord_3061953, baseEnd_3061953] using wordTrace_append hprefix tailTrace_3061953
  have hstable : (prefixWord ++ tailWord_3061953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061953).length < 2 ^ (prefixWord ++ tailWord_3061953).sum := by decide
  have hdescent : baseEnd_3061953 < baseStart_3061953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061966 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3061966 : Nat := 118140960795 + 3061966 * 2 ^ 59
def prefixEnd_3061966 : Nat := 4983230072969 + 3 ^ 40 * 3061966 * 2
def baseEnd_3061966 : Nat := 1048173537149914851762187

theorem tailTrace_3061966 : CollatzResearch.WordTrace tailWord_3061966 prefixEnd_3061966 1048173537149914851762187 := by
  unfold tailWord_3061966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959884353128449875544719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74452716550018399336238501 13959884353128449875544719)
  ·
    refine ⟨20939826529692674813317079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13959884353128449875544719 20939826529692674813317079)
    ·
      refine ⟨31409739794539012219975619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20939826529692674813317079 31409739794539012219975619)
      ·
        refine ⟨47114609691808518329963429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31409739794539012219975619 47114609691808518329963429)
        ·
          refine ⟨8833989317214097186868143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47114609691808518329963429 8833989317214097186868143)
          ·
            refine ⟨13250983975821145780302215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8833989317214097186868143 13250983975821145780302215)
            ·
              refine ⟨19876475963731718670453323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13250983975821145780302215 19876475963731718670453323)
              ·
                refine ⟨29814713945597578005679985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19876475963731718670453323 29814713945597578005679985)
                ·
                  refine ⟨22361035459198183504259989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29814713945597578005679985 22361035459198183504259989)
                  ·
                    refine ⟨1048173537149914851762187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22361035459198183504259989 1048173537149914851762187)
                    ·
                      rfl

theorem cell22_3061966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3061966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061966 prefixEnd_3061966 := by exact prefixLift 3061966
  have htrace : WordTrace (prefixWord ++ tailWord_3061966) baseStart_3061966 baseEnd_3061966 := by
    simpa [prefixWord, tailWord_3061966, baseEnd_3061966] using wordTrace_append hprefix tailTrace_3061966
  have hstable : (prefixWord ++ tailWord_3061966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061966).length < 2 ^ (prefixWord ++ tailWord_3061966).sum := by decide
  have hdescent : baseEnd_3061966 < baseStart_3061966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061979 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_3061979 : Nat := 118140960795 + 3061979 * 2 ^ 59
def prefixEnd_3061979 : Nat := 4983230072969 + 3 ^ 40 * 3061979 * 2
def baseEnd_3061979 : Nat := 1048177987315587151187147

theorem tailTrace_3061979 : CollatzResearch.WordTrace tailWord_3061979 prefixEnd_3061979 1048177987315587151187147 := by
  unfold tailWord_3061979
  simp only [CollatzResearch.WordTrace]
  refine ⟨111679548973980502224580991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74453032649320334816387327 111679548973980502224580991)
  ·
    refine ⟨167519323460970753336871487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111679548973980502224580991 167519323460970753336871487)
    ·
      refine ⟨251278985191456130005307231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167519323460970753336871487 251278985191456130005307231)
      ·
        refine ⟨376918477787184195007960847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251278985191456130005307231 376918477787184195007960847)
        ·
          refine ⟨565377716680776292511941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376918477787184195007960847 565377716680776292511941271)
          ·
            refine ⟨848066575021164438767911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565377716680776292511941271 848066575021164438767911907)
            ·
              refine ⟨1272099862531746658151867861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848066575021164438767911907 1272099862531746658151867861)
              ·
                refine ⟨29814840528087812300434403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1272099862531746658151867861 29814840528087812300434403)
                ·
                  refine ⟨44722260792131718450651605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29814840528087812300434403 44722260792131718450651605)
                  ·
                    refine ⟨1048177987315587151187147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44722260792131718450651605 1048177987315587151187147)
                    ·
                      rfl

theorem cell22_3061979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_3061979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3061979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3061979 prefixEnd_3061979 := by exact prefixLift 3061979
  have htrace : WordTrace (prefixWord ++ tailWord_3061979) baseStart_3061979 baseEnd_3061979 := by
    simpa [prefixWord, tailWord_3061979, baseEnd_3061979] using wordTrace_append hprefix tailTrace_3061979
  have hstable : (prefixWord ++ tailWord_3061979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061979).length < 2 ^ (prefixWord ++ tailWord_3061979).sum := by decide
  have hdescent : baseEnd_3061979 < baseStart_3061979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062002 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3062002 : Nat := 118140960795 + 3062002 * 2 ^ 59
def prefixEnd_3062002 : Nat := 4983230072969 + 3 ^ 40 * 3062002 * 2
def baseEnd_3062002 : Nat := 1048185860685622757862077

theorem tailTrace_3062002 : CollatzResearch.WordTrace tailWord_3062002 prefixEnd_3062002 1048185860685622757862077 := by
  unfold tailWord_3062002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920096963224294288167065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74453591901931451435112173 27920096963224294288167065)
  ·
    refine ⟨20940072722418220716125299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27920096963224294288167065 20940072722418220716125299)
    ·
      refine ⟨31410109083627331074187949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20940072722418220716125299 31410109083627331074187949)
      ·
        refine ⟨11778790906360249152820481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31410109083627331074187949 11778790906360249152820481)
        ·
          refine ⟨8834093179770186864615361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11778790906360249152820481 8834093179770186864615361)
          ·
            refine ⟨6625569884827640148461521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8834093179770186864615361 6625569884827640148461521)
            ·
              refine ⟨4969177413620730111346141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6625569884827640148461521 4969177413620730111346141)
              ·
                refine ⟨1863441530107773791754803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4969177413620730111346141 1863441530107773791754803)
                ·
                  refine ⟨2795162295161660687632205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863441530107773791754803 2795162295161660687632205)
                  ·
                    refine ⟨1048185860685622757862077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795162295161660687632205 1048185860685622757862077)
                    ·
                      rfl

theorem cell22_3062002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3062002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062002 prefixEnd_3062002 := by exact prefixLift 3062002
  have htrace : WordTrace (prefixWord ++ tailWord_3062002) baseStart_3062002 baseEnd_3062002 := by
    simpa [prefixWord, tailWord_3062002, baseEnd_3062002] using wordTrace_append hprefix tailTrace_3062002
  have hstable : (prefixWord ++ tailWord_3062002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062002).length < 2 ^ (prefixWord ++ tailWord_3062002).sum := by decide
  have hdescent : baseEnd_3062002 < baseStart_3062002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062026 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_3062026 : Nat := 118140960795 + 3062026 * 2 ^ 59
def prefixEnd_3062026 : Nat := 4983230072969 + 3 ^ 40 * 3062026 * 2
def baseEnd_3062026 : Nat := 349398025458698231754001

theorem tailTrace_3062026 : CollatzResearch.WordTrace tailWord_3062026 prefixEnd_3062026 349398025458698231754001 := by
  unfold tailWord_3062026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920315801202557312885483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74454175469873486167694621 27920315801202557312885483)
  ·
    refine ⟨41880473701803835969328225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27920315801202557312885483 41880473701803835969328225)
    ·
      refine ⟨31410355276352876976996169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41880473701803835969328225 31410355276352876976996169)
      ·
        refine ⟨23557766457264657732747127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31410355276352876976996169 23557766457264657732747127)
        ·
          refine ⟨35336649685896986599120691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23557766457264657732747127 35336649685896986599120691)
          ·
            refine ⟨53004974528845479898681037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35336649685896986599120691 53004974528845479898681037)
            ·
              refine ⟨19876865448317054962005389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53004974528845479898681037 19876865448317054962005389)
              ·
                refine ⟨7453824543118895610752021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19876865448317054962005389 7453824543118895610752021)
                ·
                  refine ⟨349398025458698231754001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7453824543118895610752021 349398025458698231754001)
                  ·
                    rfl

theorem cell22_3062026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_3062026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062026 prefixEnd_3062026 := by exact prefixLift 3062026
  have htrace : WordTrace (prefixWord ++ tailWord_3062026) baseStart_3062026 baseEnd_3062026 := by
    simpa [prefixWord, tailWord_3062026, baseEnd_3062026] using wordTrace_append hprefix tailTrace_3062026
  have hstable : (prefixWord ++ tailWord_3062026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062026).length < 2 ^ (prefixWord ++ tailWord_3062026).sum := by decide
  have hdescent : baseEnd_3062026 < baseStart_3062026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062073 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_3062073 : Nat := 118140960795 + 3062073 * 2 ^ 59
def prefixEnd_3062073 : Nat := 4983230072969 + 3 ^ 40 * 3062073 * 2
def baseEnd_3062073 : Nat := 1048210165436602239336859

theorem tailTrace_3062073 : CollatzResearch.WordTrace tailWord_3062073 prefixEnd_3062073 1048210165436602239336859 := by
  unfold tailWord_3062073
  simp only [CollatzResearch.WordTrace]
  refine ⟨111682977435639956278502873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74455318290426637519001915 111682977435639956278502873)
  ·
    refine ⟨83762233076729967208877155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111682977435639956278502873 83762233076729967208877155)
    ·
      refine ⟨125643349615094950813315733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83762233076729967208877155 125643349615094950813315733)
      ·
        refine ⟨5889532013207575819374175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125643349615094950813315733 5889532013207575819374175)
        ·
          refine ⟨8834298019811363729061263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5889532013207575819374175 8834298019811363729061263)
          ·
            refine ⟨13251447029717045593591895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8834298019811363729061263 13251447029717045593591895)
            ·
              refine ⟨19877170544575568390387843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13251447029717045593591895 19877170544575568390387843)
              ·
                refine ⟨29815755816863352585581765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877170544575568390387843 29815755816863352585581765)
                ·
                  refine ⟨5590454215661878609796581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29815755816863352585581765 5590454215661878609796581)
                  ·
                    refine ⟨1048210165436602239336859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590454215661878609796581 1048210165436602239336859)
                    ·
                      rfl

theorem cell22_3062073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_3062073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062073 prefixEnd_3062073 := by exact prefixLift 3062073
  have htrace : WordTrace (prefixWord ++ tailWord_3062073) baseStart_3062073 baseEnd_3062073 := by
    simpa [prefixWord, tailWord_3062073, baseEnd_3062073] using wordTrace_append hprefix tailTrace_3062073
  have hstable : (prefixWord ++ tailWord_3062073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062073).length < 2 ^ (prefixWord ++ tailWord_3062073).sum := by decide
  have hdescent : baseEnd_3062073 < baseStart_3062073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062103 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 5, 3]
def baseStart_3062103 : Nat := 118140960795 + 3062103 * 2 ^ 59
def prefixEnd_3062103 : Nat := 4983230072969 + 3 ^ 40 * 3062103 * 2
def baseEnd_3062103 : Nat := 1048220435049692161086767

theorem tailTrace_3062103 : CollatzResearch.WordTrace tailWord_3062103 prefixEnd_3062103 1048220435049692161086767 := by
  unfold tailWord_3062103
  simp only [CollatzResearch.WordTrace]
  refine ⟨111684071625531271402094963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74456047750354180934729975 111684071625531271402094963)
  ·
    refine ⟨167526107438296907103142445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111684071625531271402094963 167526107438296907103142445)
    ·
      refine ⟨62822290289361340163678417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167526107438296907103142445 62822290289361340163678417)
      ·
        refine ⟨47116717717021005122758813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62822290289361340163678417 47116717717021005122758813)
        ·
          refine ⟨17668769143882876921034555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47116717717021005122758813 17668769143882876921034555)
          ·
            refine ⟨26503153715824315381551833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17668769143882876921034555 26503153715824315381551833)
            ·
              refine ⟨19877365286868236536163875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26503153715824315381551833 19877365286868236536163875)
              ·
                refine ⟨29816047930302354804245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877365286868236536163875 29816047930302354804245813)
                ·
                  refine ⟨2795254493465845762898045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29816047930302354804245813 2795254493465845762898045)
                  ·
                    refine ⟨1048220435049692161086767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795254493465845762898045 1048220435049692161086767)
                    ·
                      rfl

theorem cell22_3062103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_3062103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062103 prefixEnd_3062103 := by exact prefixLift 3062103
  have htrace : WordTrace (prefixWord ++ tailWord_3062103) baseStart_3062103 baseEnd_3062103 := by
    simpa [prefixWord, tailWord_3062103, baseEnd_3062103] using wordTrace_append hprefix tailTrace_3062103
  have hstable : (prefixWord ++ tailWord_3062103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062103).length < 2 ^ (prefixWord ++ tailWord_3062103).sum := by decide
  have hdescent : baseEnd_3062103 < baseStart_3062103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062131 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_3062131 : Nat := 118140960795 + 3062131 * 2 ^ 59
def prefixEnd_3062131 : Nat := 4983230072969 + 3 ^ 40 * 3062131 * 2
def baseEnd_3062131 : Nat := 1048230020021909421386681

theorem tailTrace_3062131 : CollatzResearch.WordTrace tailWord_3062131 prefixEnd_3062131 1048230020021909421386681 := by
  unfold tailWord_3062131
  simp only [CollatzResearch.WordTrace]
  refine ⟨111685092869429832184114247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74456728579619888122742831 111685092869429832184114247)
  ·
    refine ⟨167527639304144748276171371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111685092869429832184114247 167527639304144748276171371)
    ·
      refine ⟨251291458956217122414257057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167527639304144748276171371 251291458956217122414257057)
      ·
        refine ⟨188468594217162841810692793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251291458956217122414257057 188468594217162841810692793)
        ·
          refine ⟨141351445662872131358019595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188468594217162841810692793 141351445662872131358019595)
          ·
            refine ⟨212027168494308197037029393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141351445662872131358019595 212027168494308197037029393)
            ·
              refine ⟨159020376370731147777772045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212027168494308197037029393 159020376370731147777772045)
              ·
                refine ⟨59632641139024180416664517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159020376370731147777772045 59632641139024180416664517)
                ·
                  refine ⟨11181120213567033828124597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59632641139024180416664517 11181120213567033828124597)
                  ·
                    refine ⟨1048230020021909421386681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11181120213567033828124597 1048230020021909421386681)
                    ·
                      rfl

theorem cell22_3062131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_3062131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062131 prefixEnd_3062131 := by exact prefixLift 3062131
  have htrace : WordTrace (prefixWord ++ tailWord_3062131) baseStart_3062131 baseEnd_3062131 := by
    simpa [prefixWord, tailWord_3062131, baseEnd_3062131] using wordTrace_append hprefix tailTrace_3062131
  have hstable : (prefixWord ++ tailWord_3062131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062131).length < 2 ^ (prefixWord ++ tailWord_3062131).sum := by decide
  have hdescent : baseEnd_3062131 < baseStart_3062131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062148 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_3062148 : Nat := 118140960795 + 3062148 * 2 ^ 59
def prefixEnd_3062148 : Nat := 4983230072969 + 3 ^ 40 * 3062148 * 2
def baseEnd_3062148 : Nat := 1048235839469327043711629

theorem tailTrace_3062148 : CollatzResearch.WordTrace tailWord_3062148 prefixEnd_3062148 1048235839469327043711629 := by
  unfold tailWord_3062148
  simp only [CollatzResearch.WordTrace]
  refine ⟨55842856455184122043741549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74457141940245496058322065 55842856455184122043741549)
  ·
    refine ⟨20941071170694045766403081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55842856455184122043741549 20941071170694045766403081)
    ·
      refine ⟨15705803378020534324802311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20941071170694045766403081 15705803378020534324802311)
      ·
        refine ⟨23558705067030801487203467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705803378020534324802311 23558705067030801487203467)
        ·
          refine ⟨35338057600546202230805201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23558705067030801487203467 35338057600546202230805201)
          ·
            refine ⟨26503543200409651673103901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35338057600546202230805201 26503543200409651673103901)
            ·
              refine ⟨9938828700153619377413963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26503543200409651673103901 9938828700153619377413963)
              ·
                refine ⟨14908243050230429066120945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9938828700153619377413963 14908243050230429066120945)
                ·
                  refine ⟨11181182287672821799590709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14908243050230429066120945 11181182287672821799590709)
                  ·
                    refine ⟨1048235839469327043711629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11181182287672821799590709 1048235839469327043711629)
                    ·
                      rfl

theorem cell22_3062148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_3062148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062148 prefixEnd_3062148 := by exact prefixLift 3062148
  have htrace : WordTrace (prefixWord ++ tailWord_3062148) baseStart_3062148 baseEnd_3062148 := by
    simpa [prefixWord, tailWord_3062148, baseEnd_3062148] using wordTrace_append hprefix tailTrace_3062148
  have hstable : (prefixWord ++ tailWord_3062148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062148).length < 2 ^ (prefixWord ++ tailWord_3062148).sum := by decide
  have hdescent : baseEnd_3062148 < baseStart_3062148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062178 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3062178 : Nat := 118140960795 + 3062178 * 2 ^ 59
def prefixEnd_3062178 : Nat := 4983230072969 + 3 ^ 40 * 3062178 * 2
def baseEnd_3062178 : Nat := 349415369694138988487179

theorem tailTrace_3062178 : CollatzResearch.WordTrace tailWord_3062178 prefixEnd_3062178 349415369694138988487179 := by
  unfold tailWord_3062178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27921701775064889802768797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74457871400173039474050125 27921701775064889802768797)
  ·
    refine ⟨10470638165649333676038299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27921701775064889802768797 10470638165649333676038299)
    ·
      refine ⟨15705957248474000514057449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10470638165649333676038299 15705957248474000514057449)
      ·
        refine ⟨11779467936355500385543087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15705957248474000514057449 11779467936355500385543087)
        ·
          refine ⟨17669201904533250578314631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11779467936355500385543087 17669201904533250578314631)
          ·
            refine ⟨26503802856799875867471947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669201904533250578314631 26503802856799875867471947)
            ·
              refine ⟨39755704285199813801207921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26503802856799875867471947 39755704285199813801207921)
              ·
                refine ⟨29816778213899860350905941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39755704285199813801207921 29816778213899860350905941)
                ·
                  refine ⟨349415369694138988487179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29816778213899860350905941 349415369694138988487179)
                  ·
                    rfl

theorem cell22_3062178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3062178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062178 prefixEnd_3062178 := by exact prefixLift 3062178
  have htrace : WordTrace (prefixWord ++ tailWord_3062178) baseStart_3062178 baseEnd_3062178 := by
    simpa [prefixWord, tailWord_3062178, baseEnd_3062178] using wordTrace_append hprefix tailTrace_3062178
  have hstable : (prefixWord ++ tailWord_3062178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062178).length < 2 ^ (prefixWord ++ tailWord_3062178).sum := by decide
  have hdescent : baseEnd_3062178 < baseStart_3062178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062330 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_3062330 : Nat := 118140960795 + 3062330 * 2 ^ 59
def prefixEnd_3062330 : Nat := 4983230072969 + 3 ^ 40 * 3062330 * 2
def baseEnd_3062330 : Nat := 349432713929579745220357

theorem tailTrace_3062330 : CollatzResearch.WordTrace tailWord_3062330 prefixEnd_3062330 349432713929579745220357 := by
  unfold tailWord_3062330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27923087748927222292652111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74461567330472592780405629 27923087748927222292652111)
  ·
    refine ⟨41884631623390833438978167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27923087748927222292652111 41884631623390833438978167)
    ·
      refine ⟨62826947435086250158467251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41884631623390833438978167 62826947435086250158467251)
      ·
        refine ⟨94240421152629375237700877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62826947435086250158467251 94240421152629375237700877)
        ·
          refine ⟨35340157932236015714137829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94240421152629375237700877 35340157932236015714137829)
          ·
            refine ⟨6626279612294252946400843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35340157932236015714137829 6626279612294252946400843)
            ·
              refine ⟨9939419418441379419601265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626279612294252946400843 9939419418441379419601265)
              ·
                refine ⟨7454564563831034564700949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9939419418441379419601265 7454564563831034564700949)
                ·
                  refine ⟨349432713929579745220357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7454564563831034564700949 349432713929579745220357)
                  ·
                    rfl

theorem cell22_3062330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_3062330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062330 prefixEnd_3062330 := by exact prefixLift 3062330
  have htrace : WordTrace (prefixWord ++ tailWord_3062330) baseStart_3062330 baseEnd_3062330 := by
    simpa [prefixWord, tailWord_3062330, baseEnd_3062330] using wordTrace_append hprefix tailTrace_3062330
  have hstable : (prefixWord ++ tailWord_3062330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062330).length < 2 ^ (prefixWord ++ tailWord_3062330).sum := by decide
  have hdescent : baseEnd_3062330 < baseStart_3062330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062340 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3062340 : Nat := 118140960795 + 3062340 * 2 ^ 59
def prefixEnd_3062340 : Nat := 4983230072969 + 3 ^ 40 * 3062340 * 2
def baseEnd_3062340 : Nat := 1048301564993102542911041

theorem tailTrace_3062340 : CollatzResearch.WordTrace tailWord_3062340 prefixEnd_3062340 1048301564993102542911041 := by
  unfold tailWord_3062340
  simp only [CollatzResearch.WordTrace]
  refine ⟨55846357862836330439236237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74461810483781773918981649 55846357862836330439236237)
  ·
    refine ⟨20942384198563623914713589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55846357862836330439236237 20942384198563623914713589)
    ·
      refine ⟨1963348518615339742004399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20942384198563623914713589 1963348518615339742004399)
      ·
        refine ⟨2945022777923009613006599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963348518615339742004399 2945022777923009613006599)
        ·
          refine ⟨4417534166884514419509899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945022777923009613006599 4417534166884514419509899)
          ·
            refine ⟨6626301250326771629264849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417534166884514419509899 6626301250326771629264849)
            ·
              refine ⟨4969725937745078721948637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626301250326771629264849 4969725937745078721948637)
              ·
                refine ⟨1863647226654404520730739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4969725937745078721948637 1863647226654404520730739)
                ·
                  refine ⟨2795470839981606781096109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863647226654404520730739 2795470839981606781096109)
                  ·
                    refine ⟨1048301564993102542911041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795470839981606781096109 1048301564993102542911041)
                    ·
                      rfl

theorem cell22_3062340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3062340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062340 prefixEnd_3062340 := by exact prefixLift 3062340
  have htrace : WordTrace (prefixWord ++ tailWord_3062340) baseStart_3062340 baseEnd_3062340 := by
    simpa [prefixWord, tailWord_3062340, baseEnd_3062340] using wordTrace_append hprefix tailTrace_3062340
  have hstable : (prefixWord ++ tailWord_3062340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062340).length < 2 ^ (prefixWord ++ tailWord_3062340).sum := by decide
  have hdescent : baseEnd_3062340 < baseStart_3062340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062349 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3062349 : Nat := 118140960795 + 3062349 * 2 ^ 59
def prefixEnd_3062349 : Nat := 4983230072969 + 3 ^ 40 * 3062349 * 2
def baseEnd_3062349 : Nat := 1048304645877029519436013

theorem tailTrace_3062349 : CollatzResearch.WordTrace tailWord_3062349 prefixEnd_3062349 1048304645877029519436013 := by
  unfold tailWord_3062349
  simp only [CollatzResearch.WordTrace]
  refine ⟨111693043982640055415550101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74462029321760036943700067 111693043982640055415550101)
  ·
    refine ⟨5235611436686252597603911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111693043982640055415550101 5235611436686252597603911)
    ·
      refine ⟨7853417155029378896405867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235611436686252597603911 7853417155029378896405867)
      ·
        refine ⟨11780125732544068344608801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7853417155029378896405867 11780125732544068344608801)
        ·
          refine ⟨8835094299408051258456601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11780125732544068344608801 8835094299408051258456601)
          ·
            refine ⟨6626320724556038443842451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8835094299408051258456601 6626320724556038443842451)
            ·
              refine ⟨9939481086834057665763677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626320724556038443842451 9939481086834057665763677)
              ·
                refine ⟨3727305407562771624661379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9939481086834057665763677 3727305407562771624661379)
                ·
                  refine ⟨5590958111344157436992069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727305407562771624661379 5590958111344157436992069)
                  ·
                    refine ⟨1048304645877029519436013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590958111344157436992069 1048304645877029519436013)
                    ·
                      rfl

theorem cell22_3062349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3062349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062349 prefixEnd_3062349 := by exact prefixLift 3062349
  have htrace : WordTrace (prefixWord ++ tailWord_3062349) baseStart_3062349 baseEnd_3062349 := by
    simpa [prefixWord, tailWord_3062349, baseEnd_3062349] using wordTrace_append hprefix tailTrace_3062349
  have hstable : (prefixWord ++ tailWord_3062349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062349).length < 2 ^ (prefixWord ++ tailWord_3062349).sum := by decide
  have hdescent : baseEnd_3062349 < baseStart_3062349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062360 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3062360 : Nat := 118140960795 + 3062360 * 2 ^ 59
def prefixEnd_3062360 : Nat := 4983230072969 + 3 ^ 40 * 3062360 * 2
def baseEnd_3062360 : Nat := 1048308411401829157410979

theorem tailTrace_3062360 : CollatzResearch.WordTrace tailWord_3062360 prefixEnd_3062360 1048308411401829157410979 := by
  unfold tailWord_3062360
  simp only [CollatzResearch.WordTrace]
  refine ⟨55846722592800102147100267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74462296790400136196133689 55846722592800102147100267)
  ·
    refine ⟨83770083889200153220650401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55846722592800102147100267 83770083889200153220650401)
    ·
      refine ⟨62827562916900114915487801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83770083889200153220650401 62827562916900114915487801)
      ·
        refine ⟨47120672187675086186615851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62827562916900114915487801 47120672187675086186615851)
        ·
          refine ⟨70681008281512629279923777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47120672187675086186615851 70681008281512629279923777)
          ·
            refine ⟨53010756211134471959942833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70681008281512629279923777 53010756211134471959942833)
            ·
              refine ⟨39758067158350853969957125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53010756211134471959942833 39758067158350853969957125)
              ·
                refine ⟨7454637592190785119366961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39758067158350853969957125 7454637592190785119366961)
                ·
                  refine ⟨5590978194143088839525221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7454637592190785119366961 5590978194143088839525221)
                  ·
                    refine ⟨1048308411401829157410979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590978194143088839525221 1048308411401829157410979)
                    ·
                      rfl

theorem cell22_3062360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3062360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062360 prefixEnd_3062360 := by exact prefixLift 3062360
  have htrace : WordTrace (prefixWord ++ tailWord_3062360) baseStart_3062360 baseEnd_3062360 := by
    simpa [prefixWord, tailWord_3062360, baseEnd_3062360] using wordTrace_append hprefix tailTrace_3062360
  have hstable : (prefixWord ++ tailWord_3062360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062360).length < 2 ^ (prefixWord ++ tailWord_3062360).sum := by decide
  have hdescent : baseEnd_3062360 < baseStart_3062360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062497 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3062497 : Nat := 118140960795 + 3062497 * 2 ^ 59
def prefixEnd_3062497 : Nat := 4983230072969 + 3 ^ 40 * 3062497 * 2
def baseEnd_3062497 : Nat := 1048355309301606466735559

theorem tailTrace_3062497 : CollatzResearch.WordTrace tailWord_3062497 prefixEnd_3062497 1048355309301606466735559 := by
  unfold tailWord_3062497
  simp only [CollatzResearch.WordTrace]
  refine ⟨111698441986103876691937745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74465627990735917794625163 111698441986103876691937745)
  ·
    refine ⟨83773831489577907518953309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111698441986103876691937745 83773831489577907518953309)
    ·
      refine ⟨31415186808591715319607491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83773831489577907518953309 31415186808591715319607491)
      ·
        refine ⟨47122780212887572979411237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31415186808591715319607491 47122780212887572979411237)
        ·
          refine ⟨8835521289916419933639607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47122780212887572979411237 8835521289916419933639607)
          ·
            refine ⟨13253281934874629900459411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835521289916419933639607 13253281934874629900459411)
            ·
              refine ⟨19879922902311944850689117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13253281934874629900459411 19879922902311944850689117)
              ·
                refine ⟨7454971088366979319008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19879922902311944850689117 7454971088366979319008419)
                ·
                  refine ⟨11182456632550468978512629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454971088366979319008419 11182456632550468978512629)
                  ·
                    refine ⟨1048355309301606466735559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11182456632550468978512629 1048355309301606466735559)
                    ·
                      rfl

theorem cell22_3062497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3062497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062497 prefixEnd_3062497 := by exact prefixLift 3062497
  have htrace : WordTrace (prefixWord ++ tailWord_3062497) baseStart_3062497 baseEnd_3062497 := by
    simpa [prefixWord, tailWord_3062497, baseEnd_3062497] using wordTrace_append hprefix tailTrace_3062497
  have hstable : (prefixWord ++ tailWord_3062497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062497).length < 2 ^ (prefixWord ++ tailWord_3062497).sum := by decide
  have hdescent : baseEnd_3062497 < baseStart_3062497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062555 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 11]
def baseStart_3062555 : Nat := 118140960795 + 3062555 * 2 ^ 59
def prefixEnd_3062555 : Nat := 4983230072969 + 3 ^ 40 * 3062555 * 2
def baseEnd_3062555 : Nat := 349458387962304549595127

theorem tailTrace_3062555 : CollatzResearch.WordTrace tailWord_3062555 prefixEnd_3062555 349458387962304549595127 := by
  unfold tailWord_3062555
  simp only [CollatzResearch.WordTrace]
  refine ⟨111700557419893752597549119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74467038279929168398366079 111700557419893752597549119)
  ·
    refine ⟨167550836129840628896323679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111700557419893752597549119 167550836129840628896323679)
    ·
      refine ⟨251326254194760943344485519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167550836129840628896323679 251326254194760943344485519)
      ·
        refine ⟨376989381292141415016728279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251326254194760943344485519 376989381292141415016728279)
        ·
          refine ⟨565484071938212122525092419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376989381292141415016728279 565484071938212122525092419)
          ·
            refine ⟨848226107907318183787638629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565484071938212122525092419 848226107907318183787638629)
            ·
              refine ⟨159042395232622159460182243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 848226107907318183787638629 159042395232622159460182243)
              ·
                refine ⟨238563592848933239190273365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159042395232622159460182243 238563592848933239190273365)
                ·
                  refine ⟨349458387962304549595127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 238563592848933239190273365 349458387962304549595127)
                  ·
                    rfl

theorem cell22_3062555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_3062555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062555 prefixEnd_3062555 := by exact prefixLift 3062555
  have htrace : WordTrace (prefixWord ++ tailWord_3062555) baseStart_3062555 baseEnd_3062555 := by
    simpa [prefixWord, tailWord_3062555, baseEnd_3062555] using wordTrace_append hprefix tailTrace_3062555
  have hstable : (prefixWord ++ tailWord_3062555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062555).length < 2 ^ (prefixWord ++ tailWord_3062555).sum := by decide
  have hdescent : baseEnd_3062555 < baseStart_3062555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062559 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 3, 3]
def baseStart_3062559 : Nat := 118140960795 + 3062559 * 2 ^ 59
def prefixEnd_3062559 : Nat := 4983230072969 + 3 ^ 40 * 3062559 * 2
def baseEnd_3062559 : Nat := 1048376533168658971685369

theorem tailTrace_3062559 : CollatzResearch.WordTrace tailWord_3062559 prefixEnd_3062559 1048376533168658971685369 := by
  unfold tailWord_3062559
  simp only [CollatzResearch.WordTrace]
  refine ⟨111700703311879261280694731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74467135541252840853796487 111700703311879261280694731)
  ·
    refine ⟨167551054967818891921042097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111700703311879261280694731 167551054967818891921042097)
    ·
      refine ⟨125663291225864168940781573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167551054967818891921042097 125663291225864168940781573)
      ·
        refine ⟨23561867104849531676396545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125663291225864168940781573 23561867104849531676396545)
        ·
          refine ⟨17671400328637148757297409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23561867104849531676396545 17671400328637148757297409)
          ·
            refine ⟨13253550246477861567973057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17671400328637148757297409 13253550246477861567973057)
            ·
              refine ⟨9940162684858396175979793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13253550246477861567973057 9940162684858396175979793)
              ·
                refine ⟨7455122013643797131984845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9940162684858396175979793 7455122013643797131984845)
                ·
                  refine ⟨2795670755116423924494317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7455122013643797131984845 2795670755116423924494317)
                  ·
                    refine ⟨1048376533168658971685369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795670755116423924494317 1048376533168658971685369)
                    ·
                      rfl

theorem cell22_3062559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_3062559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062559 prefixEnd_3062559 := by exact prefixLift 3062559
  have htrace : WordTrace (prefixWord ++ tailWord_3062559) baseStart_3062559 baseEnd_3062559 := by
    simpa [prefixWord, tailWord_3062559, baseEnd_3062559] using wordTrace_append hprefix tailTrace_3062559
  have hstable : (prefixWord ++ tailWord_3062559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062559).length < 2 ^ (prefixWord ++ tailWord_3062559).sum := by decide
  have hdescent : baseEnd_3062559 < baseStart_3062559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062636 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_3062636 : Nat := 118140960795 + 3062636 * 2 ^ 59
def prefixEnd_3062636 : Nat := 4983230072969 + 3 ^ 40 * 3062636 * 2
def baseEnd_3062636 : Nat := 1048402891842256437510133

theorem tailTrace_3062636 : CollatzResearch.WordTrace tailWord_3062636 prefixEnd_3062636 1048402891842256437510133 := by
  unfold tailWord_3062636
  simp only [CollatzResearch.WordTrace]
  refine ⟨55851755866300151715623881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74469007821733535620831841 55851755866300151715623881)
  ·
    refine ⟨41888816899725113786717911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55851755866300151715623881 41888816899725113786717911)
    ·
      refine ⟨62833225349587670680076867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41888816899725113786717911 62833225349587670680076867)
      ·
        refine ⟨94249838024381506020115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62833225349587670680076867 94249838024381506020115301)
        ·
          refine ⟨17671844629571532378771619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94249838024381506020115301 17671844629571532378771619)
          ·
            refine ⟨26507766944357298568157429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17671844629571532378771619 26507766944357298568157429)
            ·
              refine ⟨2485103151033496740764759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26507766944357298568157429 2485103151033496740764759)
              ·
                refine ⟨3727654726550245111147139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485103151033496740764759 3727654726550245111147139)
                ·
                  refine ⟨5591482089825367666720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727654726550245111147139 5591482089825367666720709)
                  ·
                    refine ⟨1048402891842256437510133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5591482089825367666720709 1048402891842256437510133)
                    ·
                      rfl

theorem cell22_3062636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_3062636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062636 prefixEnd_3062636 := by exact prefixLift 3062636
  have htrace : WordTrace (prefixWord ++ tailWord_3062636) baseStart_3062636 baseEnd_3062636 := by
    simpa [prefixWord, tailWord_3062636, baseEnd_3062636] using wordTrace_append hprefix tailTrace_3062636
  have hstable : (prefixWord ++ tailWord_3062636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062636).length < 2 ^ (prefixWord ++ tailWord_3062636).sum := by decide
  have hdescent : baseEnd_3062636 < baseStart_3062636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062651 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 4]
def baseStart_3062651 : Nat := 118140960795 + 3062651 * 2 ^ 59
def prefixEnd_3062651 : Nat := 4983230072969 + 3 ^ 40 * 3062651 * 2
def baseEnd_3062651 : Nat := 349469342216267132795029

theorem tailTrace_3062651 : CollatzResearch.WordTrace tailWord_3062651 prefixEnd_3062651 349469342216267132795029 := by
  unfold tailWord_3062651
  simp only [CollatzResearch.WordTrace]
  refine ⟨111704058827545960993043807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74469372551697307328695871 111704058827545960993043807)
  ·
    refine ⟨167556088241318941489565711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111704058827545960993043807 167556088241318941489565711)
    ·
      refine ⟨251334132361978412234348567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167556088241318941489565711 251334132361978412234348567)
      ·
        refine ⟨377001198542967618351522851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251334132361978412234348567 377001198542967618351522851)
        ·
          refine ⟨565501797814451427527284277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377001198542967618351522851 565501797814451427527284277)
          ·
            refine ⟨53015793545104821330682901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 565501797814451427527284277 53015793545104821330682901)
            ·
              refine ⟨2485115322426788499875761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53015793545104821330682901 2485115322426788499875761)
              ·
                refine ⟨1863836491820091374906821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485115322426788499875761 1863836491820091374906821)
                ·
                  refine ⟨349469342216267132795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863836491820091374906821 349469342216267132795029)
                  ·
                    rfl

theorem cell22_3062651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 4].length) (baseStart_3062651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062651 prefixEnd_3062651 := by exact prefixLift 3062651
  have htrace : WordTrace (prefixWord ++ tailWord_3062651) baseStart_3062651 baseEnd_3062651 := by
    simpa [prefixWord, tailWord_3062651, baseEnd_3062651] using wordTrace_append hprefix tailTrace_3062651
  have hstable : (prefixWord ++ tailWord_3062651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062651).length < 2 ^ (prefixWord ++ tailWord_3062651).sum := by decide
  have hdescent : baseEnd_3062651 < baseStart_3062651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062666 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3062666 : Nat := 118140960795 + 3062666 * 2 ^ 59
def prefixEnd_3062666 : Nat := 4983230072969 + 3 ^ 40 * 3062666 * 2
def baseEnd_3062666 : Nat := 1048413161455346359260041

theorem tailTrace_3062666 : CollatzResearch.WordTrace tailWord_3062666 prefixEnd_3062666 1048413161455346359260041 := by
  unfold tailWord_3062666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27926151480622904638709963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74469737281661079036559901 27926151480622904638709963)
  ·
    refine ⟨41889227220934356958064945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27926151480622904638709963 41889227220934356958064945)
    ·
      refine ⟨31416920415700767718548709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41889227220934356958064945 31416920415700767718548709)
      ·
        refine ⟨5890672577943893947227883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31416920415700767718548709 5890672577943893947227883)
        ·
          refine ⟨8836008866915840920841825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890672577943893947227883 8836008866915840920841825)
          ·
            refine ⟨6627006650186880690631369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836008866915840920841825 6627006650186880690631369)
            ·
              refine ⟨4970254987640160517973527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627006650186880690631369 4970254987640160517973527)
              ·
                refine ⟨7455382481460240776960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970254987640160517973527 7455382481460240776960291)
                ·
                  refine ⟨11183073722190361165440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455382481460240776960291 11183073722190361165440437)
                  ·
                    refine ⟨1048413161455346359260041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11183073722190361165440437 1048413161455346359260041)
                    ·
                      rfl

theorem cell22_3062666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3062666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062666 prefixEnd_3062666 := by exact prefixLift 3062666
  have htrace : WordTrace (prefixWord ++ tailWord_3062666) baseStart_3062666 baseEnd_3062666 := by
    simpa [prefixWord, tailWord_3062666, baseEnd_3062666] using wordTrace_append hprefix tailTrace_3062666
  have hstable : (prefixWord ++ tailWord_3062666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062666).length < 2 ^ (prefixWord ++ tailWord_3062666).sum := by decide
  have hdescent : baseEnd_3062666 < baseStart_3062666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062679 : List Nat := [1, 1, 3, 3, 1, 2, 5, 6]
def baseStart_3062679 : Nat := 118140960795 + 3062679 * 2 ^ 59
def prefixEnd_3062679 : Nat := 4983230072969 + 3 ^ 40 * 3062679 * 2
def baseEnd_3062679 : Nat := 116490845735668739853889

theorem tailTrace_3062679 : CollatzResearch.WordTrace tailWord_3062679 prefixEnd_3062679 116490845735668739853889 := by
  unfold tailWord_3062679
  simp only [CollatzResearch.WordTrace]
  refine ⟨111705080071444521775063091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74470053380963014516708727 111705080071444521775063091)
  ·
    refine ⟨167557620107166782662594637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111705080071444521775063091 167557620107166782662594637)
    ·
      refine ⟨62834107540187543498472989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167557620107166782662594637 62834107540187543498472989)
      ·
        refine ⟨23562790327570328811927371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62834107540187543498472989 23562790327570328811927371)
        ·
          refine ⟨35344185491355493217891057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23562790327570328811927371 35344185491355493217891057)
          ·
            refine ⟨26508139118516619913418293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35344185491355493217891057 26508139118516619913418293)
            ·
              refine ⟨2485138042360933116882965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26508139118516619913418293 2485138042360933116882965)
              ·
                refine ⟨116490845735668739853889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2485138042360933116882965 116490845735668739853889)
                ·
                  rfl

theorem cell22_3062679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 6].length) (baseStart_3062679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062679 prefixEnd_3062679 := by exact prefixLift 3062679
  have htrace : WordTrace (prefixWord ++ tailWord_3062679) baseStart_3062679 baseEnd_3062679 := by
    simpa [prefixWord, tailWord_3062679, baseEnd_3062679] using wordTrace_append hprefix tailTrace_3062679
  have hstable : (prefixWord ++ tailWord_3062679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062679).length < 2 ^ (prefixWord ++ tailWord_3062679).sum := by decide
  have hdescent : baseEnd_3062679 < baseStart_3062679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062745 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 1, 3]
def baseStart_3062745 : Nat := 118140960795 + 3062745 * 2 ^ 59
def prefixEnd_3062745 : Nat := 4983230072969 + 3 ^ 40 * 3062745 * 2
def baseEnd_3062745 : Nat := 1048440204769816486534799

theorem tailTrace_3062745 : CollatzResearch.WordTrace tailWord_3062745 prefixEnd_3062745 1048440204769816486534799 := by
  unfold tailWord_3062745
  simp only [CollatzResearch.WordTrace]
  refine ⟨111707487289205415046965689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74471658192803610031310459 111707487289205415046965689)
  ·
    refine ⟨83780615466904061285224267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111707487289205415046965689 83780615466904061285224267)
    ·
      refine ⟨125670923200356091927836401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83780615466904061285224267 125670923200356091927836401)
      ·
        refine ⟨94253192400267068945877301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125670923200356091927836401 94253192400267068945877301)
        ·
          refine ⟨8836236787525037713675997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94253192400267068945877301 8836236787525037713675997)
          ·
            refine ⟨3313588795321889142628499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8836236787525037713675997 3313588795321889142628499)
            ·
              refine ⟨4970383192982833713942749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313588795321889142628499 4970383192982833713942749)
              ·
                refine ⟨1863893697368562642728531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4970383192982833713942749 1863893697368562642728531)
                ·
                  refine ⟨2795840546052843964092797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863893697368562642728531 2795840546052843964092797)
                  ·
                    refine ⟨1048440204769816486534799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795840546052843964092797 1048440204769816486534799)
                    ·
                      rfl

theorem cell22_3062745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_3062745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062745 prefixEnd_3062745 := by exact prefixLift 3062745
  have htrace : WordTrace (prefixWord ++ tailWord_3062745) baseStart_3062745 baseEnd_3062745 := by
    simpa [prefixWord, tailWord_3062745, baseEnd_3062745] using wordTrace_append hprefix tailTrace_3062745
  have hstable : (prefixWord ++ tailWord_3062745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062745).length < 2 ^ (prefixWord ++ tailWord_3062745).sum := by decide
  have hdescent : baseEnd_3062745 < baseStart_3062745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062814 : List Nat := [4, 3, 15]
def baseStart_3062814 : Nat := 118140960795 + 3062814 * 2 ^ 59
def prefixEnd_3062814 : Nat := 4983230072969 + 3 ^ 40 * 3062814 * 2
def baseEnd_3062814 : Nat := 479407327334212760201

theorem tailTrace_3062814 : CollatzResearch.WordTrace tailWord_3062814 prefixEnd_3062814 479407327334212760201 := by
  unfold tailWord_3062814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963750490744429978903437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74473335950636959887484997 13963750490744429978903437)
  ·
    refine ⟨5236406434029161242088789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13963750490744429978903437 5236406434029161242088789)
    ·
      refine ⟨479407327334212760201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 5236406434029161242088789 479407327334212760201)
      ·
        rfl

theorem cell22_3062814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 15].length) (baseStart_3062814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062814 prefixEnd_3062814 := by exact prefixLift 3062814
  have htrace : WordTrace (prefixWord ++ tailWord_3062814) baseStart_3062814 baseEnd_3062814 := by
    simpa [prefixWord, tailWord_3062814, baseEnd_3062814] using wordTrace_append hprefix tailTrace_3062814
  have hstable : (prefixWord ++ tailWord_3062814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062814).length < 2 ^ (prefixWord ++ tailWord_3062814).sum := by decide
  have hdescent : baseEnd_3062814 < baseStart_3062814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062818 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3062818 : Nat := 118140960795 + 3062818 * 2 ^ 59
def prefixEnd_3062818 : Nat := 4983230072969 + 3 ^ 40 * 3062818 * 2
def baseEnd_3062818 : Nat := 1048465194161668629459575

theorem tailTrace_3062818 : CollatzResearch.WordTrace tailWord_3062818 prefixEnd_3062818 1048465194161668629459575 := by
  unfold tailWord_3062818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27927537454485237128593277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74473433211960632342915405 27927537454485237128593277)
  ·
    refine ⟨10472826545431963923222479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27927537454485237128593277 10472826545431963923222479)
    ·
      refine ⟨15709239818147945884833719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10472826545431963923222479 15709239818147945884833719)
      ·
        refine ⟨23563859727221918827250579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15709239818147945884833719 23563859727221918827250579)
        ·
          refine ⟨35345789590832878240875869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23563859727221918827250579 35345789590832878240875869)
          ·
            refine ⟨13254671096562329340328451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35345789590832878240875869 13254671096562329340328451)
            ·
              refine ⟨19882006644843494010492677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13254671096562329340328451 19882006644843494010492677)
              ·
                refine ⟨3727876245908155126967377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19882006644843494010492677 3727876245908155126967377)
                ·
                  refine ⟨2795907184431116345225533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3727876245908155126967377 2795907184431116345225533)
                  ·
                    refine ⟨1048465194161668629459575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795907184431116345225533 1048465194161668629459575)
                    ·
                      rfl

theorem cell22_3062818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3062818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062818 prefixEnd_3062818 := by exact prefixLift 3062818
  have htrace : WordTrace (prefixWord ++ tailWord_3062818) baseStart_3062818 baseEnd_3062818 := by
    simpa [prefixWord, tailWord_3062818, baseEnd_3062818] using wordTrace_append hprefix tailTrace_3062818
  have hstable : (prefixWord ++ tailWord_3062818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062818).length < 2 ^ (prefixWord ++ tailWord_3062818).sum := by decide
  have hdescent : baseEnd_3062818 < baseStart_3062818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062820 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_3062820 : Nat := 118140960795 + 3062820 * 2 ^ 59
def prefixEnd_3062820 : Nat := 4983230072969 + 3 ^ 40 * 3062820 * 2
def baseEnd_3062820 : Nat := 349488626267513763636523

theorem tailTrace_3062820 : CollatzResearch.WordTrace tailWord_3062820 prefixEnd_3062820 349488626267513763636523 := by
  unfold tailWord_3062820
  simp only [CollatzResearch.WordTrace]
  refine ⟨55855111381966851427972957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74473481842622468570630609 55855111381966851427972957)
  ·
    refine ⟨20945666768237569285489859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55855111381966851427972957 20945666768237569285489859)
    ·
      refine ⟨31418500152356353928234789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20945666768237569285489859 31418500152356353928234789)
      ·
        refine ⟨5890968778566816361544023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31418500152356353928234789 5890968778566816361544023)
        ·
          refine ⟨8836453167850224542316035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890968778566816361544023 8836453167850224542316035)
          ·
            refine ⟨13254679751775336813474053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836453167850224542316035 13254679751775336813474053)
            ·
              refine ⟨2485252453457875652526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13254679751775336813474053 2485252453457875652526385)
              ·
                refine ⟨1863939340093406739394789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485252453457875652526385 1863939340093406739394789)
                ·
                  refine ⟨349488626267513763636523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863939340093406739394789 349488626267513763636523)
                  ·
                    rfl

theorem cell22_3062820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_3062820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062820 prefixEnd_3062820 := by exact prefixLift 3062820
  have htrace : WordTrace (prefixWord ++ tailWord_3062820) baseStart_3062820 baseEnd_3062820 := by
    simpa [prefixWord, tailWord_3062820, baseEnd_3062820] using wordTrace_append hprefix tailTrace_3062820
  have hstable : (prefixWord ++ tailWord_3062820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062820).length < 2 ^ (prefixWord ++ tailWord_3062820).sum := by decide
  have hdescent : baseEnd_3062820 < baseStart_3062820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062876 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_3062876 : Nat := 118140960795 + 3062876 * 2 ^ 59
def prefixEnd_3062876 : Nat := 4983230072969 + 3 ^ 40 * 3062876 * 2
def baseEnd_3062876 : Nat := 349495016248991937169799

theorem tailTrace_3062876 : CollatzResearch.WordTrace tailWord_3062876 prefixEnd_3062876 349495016248991937169799 := by
  unfold tailWord_3062876
  simp only [CollatzResearch.WordTrace]
  refine ⟨55856132625865412209992241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74474843501153882946656321 55856132625865412209992241)
  ·
    refine ⟨41892099469399059157494181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55856132625865412209992241 41892099469399059157494181)
    ·
      refine ⟨7854768650512323592030159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41892099469399059157494181 7854768650512323592030159)
      ·
        refine ⟨11782152975768485388045239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7854768650512323592030159 11782152975768485388045239)
        ·
          refine ⟨17673229463652728082067859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11782152975768485388045239 17673229463652728082067859)
          ·
            refine ⟨26509844195479092123101789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17673229463652728082067859 26509844195479092123101789)
            ·
              refine ⟨9941191573304659546163171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26509844195479092123101789 9941191573304659546163171)
              ·
                refine ⟨14911787359956989319244757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941191573304659546163171 14911787359956989319244757)
                ·
                  refine ⟨349495016248991937169799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14911787359956989319244757 349495016248991937169799)
                  ·
                    rfl

theorem cell22_3062876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_3062876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062876 prefixEnd_3062876 := by exact prefixLift 3062876
  have htrace : WordTrace (prefixWord ++ tailWord_3062876) baseStart_3062876 baseEnd_3062876 := by
    simpa [prefixWord, tailWord_3062876, baseEnd_3062876] using wordTrace_append hprefix tailTrace_3062876
  have hstable : (prefixWord ++ tailWord_3062876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062876).length < 2 ^ (prefixWord ++ tailWord_3062876).sum := by decide
  have hdescent : baseEnd_3062876 < baseStart_3062876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062938 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_3062938 : Nat := 118140960795 + 3062938 * 2 ^ 59
def prefixEnd_3062938 : Nat := 4983230072969 + 3 ^ 40 * 3062938 * 2
def baseEnd_3062938 : Nat := 349502090871342772153069

theorem tailTrace_3062938 : CollatzResearch.WordTrace tailWord_3062938 prefixEnd_3062938 349502090871342772153069 := by
  unfold tailWord_3062938
  simp only [CollatzResearch.WordTrace]
  refine ⟨27928631644376552252185367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74476351051670806005827645 27928631644376552252185367)
  ·
    refine ⟨41892947466564828378278051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27928631644376552252185367 41892947466564828378278051)
    ·
      refine ⟨62839421199847242567417077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41892947466564828378278051 62839421199847242567417077)
      ·
        refine ⟨5891195737485678990695351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62839421199847242567417077 5891195737485678990695351)
        ·
          refine ⟨8836793606228518486043027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891195737485678990695351 8836793606228518486043027)
          ·
            refine ⟨13255190409342777729064541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836793606228518486043027 13255190409342777729064541)
            ·
              refine ⟨4970696403503541648399203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13255190409342777729064541 4970696403503541648399203)
              ·
                refine ⟨7456044605255312472598805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970696403503541648399203 7456044605255312472598805)
                ·
                  refine ⟨349502090871342772153069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7456044605255312472598805 349502090871342772153069)
                  ·
                    rfl

theorem cell22_3062938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_3062938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062938 prefixEnd_3062938 := by exact prefixLift 3062938
  have htrace : WordTrace (prefixWord ++ tailWord_3062938) baseStart_3062938 baseEnd_3062938 := by
    simpa [prefixWord, tailWord_3062938, baseEnd_3062938] using wordTrace_append hprefix tailTrace_3062938
  have hstable : (prefixWord ++ tailWord_3062938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062938).length < 2 ^ (prefixWord ++ tailWord_3062938).sum := by decide
  have hdescent : baseEnd_3062938 < baseStart_3062938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062957 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3062957 : Nat := 118140960795 + 3062957 * 2 ^ 59
def prefixEnd_3062957 : Nat := 4983230072969 + 3 ^ 40 * 3062957 * 2
def baseEnd_3062957 : Nat := 1048512776702318600234149

theorem tailTrace_3062957 : CollatzResearch.WordTrace tailWord_3062957 prefixEnd_3062957 1048512776702318600234149 := by
  unfold tailWord_3062957
  simp only [CollatzResearch.WordTrace]
  refine ⟨111715219564437375253683125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74476813042958250169122083 111715219564437375253683125)
  ·
    refine ⟨10473301834166003930032793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111715219564437375253683125 10473301834166003930032793)
    ·
      refine ⟨7854976375624502947524595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10473301834166003930032793 7854976375624502947524595)
      ·
        refine ⟨11782464563436754421286893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7854976375624502947524595 11782464563436754421286893)
        ·
          refine ⟨4418424211288782907982585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11782464563436754421286893 4418424211288782907982585)
          ·
            refine ⟨3313818158466587180986939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4418424211288782907982585 3313818158466587180986939)
            ·
              refine ⟨4970727237699880771480409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313818158466587180986939 4970727237699880771480409)
              ·
                refine ⟨3728045428274910578610307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970727237699880771480409 3728045428274910578610307)
                ·
                  refine ⟨5592068142412365867915461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728045428274910578610307 5592068142412365867915461)
                  ·
                    refine ⟨1048512776702318600234149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592068142412365867915461 1048512776702318600234149)
                    ·
                      rfl

theorem cell22_3062957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3062957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062957 prefixEnd_3062957 := by exact prefixLift 3062957
  have htrace : WordTrace (prefixWord ++ tailWord_3062957) baseStart_3062957 baseEnd_3062957 := by
    simpa [prefixWord, tailWord_3062957, baseEnd_3062957] using wordTrace_append hprefix tailTrace_3062957
  have hstable : (prefixWord ++ tailWord_3062957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062957).length < 2 ^ (prefixWord ++ tailWord_3062957).sum := by decide
  have hdescent : baseEnd_3062957 < baseStart_3062957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062989 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3062989 : Nat := 118140960795 + 3062989 * 2 ^ 59
def prefixEnd_3062989 : Nat := 4983230072969 + 3 ^ 40 * 3062989 * 2
def baseEnd_3062989 : Nat := 349507910318760394478017

theorem tailTrace_3062989 : CollatzResearch.WordTrace tailWord_3062989 prefixEnd_3062989 349507910318760394478017 := by
  unfold tailWord_3062989
  simp only [CollatzResearch.WordTrace]
  refine ⟨111716386700321444718848021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74477591133547629812565347 111716386700321444718848021)
  ·
    refine ⟨5236705626577567721196001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111716386700321444718848021 5236705626577567721196001)
    ·
      refine ⟨3927529219933175790897001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5236705626577567721196001 3927529219933175790897001)
      ·
        refine ⟨2945646914949881843172751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3927529219933175790897001 2945646914949881843172751)
        ·
          refine ⟨4418470372424822764759127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945646914949881843172751 4418470372424822764759127)
          ·
            refine ⟨6627705558637234147138691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418470372424822764759127 6627705558637234147138691)
            ·
              refine ⟨9941558337955851220708037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627705558637234147138691 9941558337955851220708037)
              ·
                refine ⟨1864042188366722103882757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9941558337955851220708037 1864042188366722103882757)
                ·
                  refine ⟨349507910318760394478017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864042188366722103882757 349507910318760394478017)
                  ·
                    rfl

theorem cell22_3062989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3062989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3062989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3062989 prefixEnd_3062989 := by exact prefixLift 3062989
  have htrace : WordTrace (prefixWord ++ tailWord_3062989) baseStart_3062989 baseEnd_3062989 := by
    simpa [prefixWord, tailWord_3062989, baseEnd_3062989] using wordTrace_append hprefix tailTrace_3062989
  have hstable : (prefixWord ++ tailWord_3062989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062989).length < 2 ^ (prefixWord ++ tailWord_3062989).sum := by decide
  have hdescent : baseEnd_3062989 < baseStart_3062989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063000 : List Nat := [2, 1, 2, 2, 6, 1, 1, 7]
def baseStart_3063000 : Nat := 118140960795 + 3063000 * 2 ^ 59
def prefixEnd_3063000 : Nat := 4983230072969 + 3 ^ 40 * 3063000 * 2
def baseEnd_3063000 : Nat := 116503055164564535712113

theorem tailTrace_3063000 : CollatzResearch.WordTrace tailWord_3063000 prefixEnd_3063000 116503055164564535712113 := by
  unfold tailWord_3063000
  simp only [CollatzResearch.WordTrace]
  refine ⟨55858393951640796798749227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74477858602187729064998969 55858393951640796798749227)
  ·
    refine ⟨83787590927461195198123841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55858393951640796798749227 83787590927461195198123841)
    ·
      refine ⟨62840693195595896398592881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83787590927461195198123841 62840693195595896398592881)
      ·
        refine ⟨47130519896696922298944661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62840693195595896398592881 47130519896696922298944661)
        ·
          refine ⟨2209243120157668232763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47130519896696922298944661 2209243120157668232763031)
          ·
            refine ⟨3313864680236502349144547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209243120157668232763031 3313864680236502349144547)
            ·
              refine ⟨4970797020354753523716821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313864680236502349144547 4970797020354753523716821)
              ·
                refine ⟨116503055164564535712113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4970797020354753523716821 116503055164564535712113)
                ·
                  rfl

theorem cell22_3063000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_3063000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063000 prefixEnd_3063000 := by exact prefixLift 3063000
  have htrace : WordTrace (prefixWord ++ tailWord_3063000) baseStart_3063000 baseEnd_3063000 := by
    simpa [prefixWord, tailWord_3063000, baseEnd_3063000] using wordTrace_append hprefix tailTrace_3063000
  have hstable : (prefixWord ++ tailWord_3063000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063000).length < 2 ^ (prefixWord ++ tailWord_3063000).sum := by decide
  have hdescent : baseEnd_3063000 < baseStart_3063000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063075 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 1, 4]
def baseStart_3063075 : Nat := 118140960795 + 3063075 * 2 ^ 59
def prefixEnd_3063075 : Nat := 4983230072969 + 3 ^ 40 * 3063075 * 2
def baseEnd_3063075 : Nat := 1048553170513805625783787

theorem tailTrace_3063075 : CollatzResearch.WordTrace tailWord_3063075 prefixEnd_3063075 1048553170513805625783787 := by
  unfold tailWord_3063075
  simp only [CollatzResearch.WordTrace]
  refine ⟨111719523378009881406478679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74479682252006587604319119 111719523378009881406478679)
  ·
    refine ⟨167579285067014822109718019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111719523378009881406478679 167579285067014822109718019)
    ·
      refine ⟨251368927600522233164577029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167579285067014822109718019 251368927600522233164577029)
      ·
        refine ⟨47131673925097918718358193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251368927600522233164577029 47131673925097918718358193)
        ·
          refine ⟨35348755443823439038768645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47131673925097918718358193 35348755443823439038768645)
          ·
            refine ⟨6627891645716894819769121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35348755443823439038768645 6627891645716894819769121)
            ·
              refine ⟨4970918734287671114826841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627891645716894819769121 4970918734287671114826841)
              ·
                refine ⟨3728189050715753336120131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970918734287671114826841 3728189050715753336120131)
                ·
                  refine ⟨5592283576073630004180197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728189050715753336120131 5592283576073630004180197)
                  ·
                    refine ⟨1048553170513805625783787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592283576073630004180197 1048553170513805625783787)
                    ·
                      rfl

theorem cell22_3063075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4].length) (baseStart_3063075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063075 prefixEnd_3063075 := by exact prefixLift 3063075
  have htrace : WordTrace (prefixWord ++ tailWord_3063075) baseStart_3063075 baseEnd_3063075 := by
    simpa [prefixWord, tailWord_3063075, baseEnd_3063075] using wordTrace_append hprefix tailTrace_3063075
  have hstable : (prefixWord ++ tailWord_3063075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063075).length < 2 ^ (prefixWord ++ tailWord_3063075).sum := by decide
  have hdescent : baseEnd_3063075 < baseStart_3063075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063088 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_3063088 : Nat := 118140960795 + 3063088 * 2 ^ 59
def prefixEnd_3063088 : Nat := 4983230072969 + 3 ^ 40 * 3063088 * 2
def baseEnd_3063088 : Nat := 1048557620679477925208747

theorem tailTrace_3063088 : CollatzResearch.WordTrace tailWord_3063088 prefixEnd_3063088 1048557620679477925208747 := by
  unfold tailWord_3063088
  simp only [CollatzResearch.WordTrace]
  refine ⟨55859998763481392313350959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74479998351308523084467945 55859998763481392313350959)
  ·
    refine ⟨83789998145222088470026439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55859998763481392313350959 83789998145222088470026439)
    ·
      refine ⟨125684997217833132705039659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83789998145222088470026439 125684997217833132705039659)
      ·
        refine ⟨188527495826749699057559489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125684997217833132705039659 188527495826749699057559489)
        ·
          refine ⟨141395621870062274293169617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188527495826749699057559489 141395621870062274293169617)
          ·
            refine ⟨106046716402546705719877213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141395621870062274293169617 106046716402546705719877213)
            ·
              refine ⟨39767518650955014644953955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106046716402546705719877213 39767518650955014644953955)
              ·
                refine ⟨59651277976432521967430933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39767518650955014644953955 59651277976432521967430933)
                ·
                  refine ⟨2796153655145274467223325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59651277976432521967430933 2796153655145274467223325)
                  ·
                    refine ⟨1048557620679477925208747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2796153655145274467223325 1048557620679477925208747)
                    ·
                      rfl

theorem cell22_3063088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_3063088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063088 prefixEnd_3063088 := by exact prefixLift 3063088
  have htrace : WordTrace (prefixWord ++ tailWord_3063088) baseStart_3063088 baseEnd_3063088 := by
    simpa [prefixWord, tailWord_3063088, baseEnd_3063088] using wordTrace_append hprefix tailTrace_3063088
  have hstable : (prefixWord ++ tailWord_3063088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063088).length < 2 ^ (prefixWord ++ tailWord_3063088).sum := by decide
  have hdescent : baseEnd_3063088 < baseStart_3063088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063103 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_3063103 : Nat := 118140960795 + 3063103 * 2 ^ 59
def prefixEnd_3063103 : Nat := 4983230072969 + 3 ^ 40 * 3063103 * 2
def baseEnd_3063103 : Nat := 1048562755486022886083701

theorem tailTrace_3063103 : CollatzResearch.WordTrace tailWord_3063103 prefixEnd_3063103 1048562755486022886083701 := by
  unfold tailWord_3063103
  simp only [CollatzResearch.WordTrace]
  refine ⟨111720544621908442188497963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74480363081272294792331975 111720544621908442188497963)
  ·
    refine ⟨167580816932862663282746945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111720544621908442188497963 167580816932862663282746945)
    ·
      refine ⟨125685612699646997462060209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167580816932862663282746945 125685612699646997462060209)
      ·
        refine ⟨94264209524735248096545157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125685612699646997462060209 94264209524735248096545157)
        ·
          refine ⟨17674539285887859018102217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94264209524735248096545157 17674539285887859018102217)
          ·
            refine ⟨13255904464415894263576663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17674539285887859018102217 13255904464415894263576663)
            ·
              refine ⟨19883856696623841395364995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13255904464415894263576663 19883856696623841395364995)
              ·
                refine ⟨29825785044935762093047493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19883856696623841395364995 29825785044935762093047493)
                ·
                  refine ⟨5592334695925455392446405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29825785044935762093047493 5592334695925455392446405)
                  ·
                    refine ⟨1048562755486022886083701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592334695925455392446405 1048562755486022886083701)
                    ·
                      rfl

theorem cell22_3063103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_3063103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063103 prefixEnd_3063103 := by exact prefixLift 3063103
  have htrace : WordTrace (prefixWord ++ tailWord_3063103) baseStart_3063103 baseEnd_3063103 := by
    simpa [prefixWord, tailWord_3063103, baseEnd_3063103] using wordTrace_append hprefix tailTrace_3063103
  have hstable : (prefixWord ++ tailWord_3063103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063103).length < 2 ^ (prefixWord ++ tailWord_3063103).sum := by decide
  have hdescent : baseEnd_3063103 < baseStart_3063103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063118 : List Nat := [4, 1, 1, 1, 1, 1, 6, 7]
def baseStart_3063118 : Nat := 118140960795 + 3063118 * 2 ^ 59
def prefixEnd_3063118 : Nat := 4983230072969 + 3 ^ 40 * 3063118 * 2
def baseEnd_3063118 : Nat := 116507543365840871884295

theorem tailTrace_3063118 : CollatzResearch.WordTrace tailWord_3063118 prefixEnd_3063118 116507543365840871884295 := by
  unfold tailWord_3063118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13965136464606762468786751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74480727811236066500196005 13965136464606762468786751)
  ·
    refine ⟨20947704696910143703180127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13965136464606762468786751 20947704696910143703180127)
    ·
      refine ⟨31421557045365215554770191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20947704696910143703180127 31421557045365215554770191)
      ·
        refine ⟨47132335568047823332155287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31421557045365215554770191 47132335568047823332155287)
        ·
          refine ⟨70698503352071734998232931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47132335568047823332155287 70698503352071734998232931)
          ·
            refine ⟨106047755028107602497349397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70698503352071734998232931 106047755028107602497349397)
            ·
              refine ⟨4970988516942543867063253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106047755028107602497349397 4970988516942543867063253)
              ·
                refine ⟨116507543365840871884295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4970988516942543867063253 116507543365840871884295)
                ·
                  rfl

theorem cell22_3063118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_3063118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063118 prefixEnd_3063118 := by exact prefixLift 3063118
  have htrace : WordTrace (prefixWord ++ tailWord_3063118) baseStart_3063118 baseEnd_3063118 := by
    simpa [prefixWord, tailWord_3063118, baseEnd_3063118] using wordTrace_append hprefix tailTrace_3063118
  have hstable : (prefixWord ++ tailWord_3063118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063118).length < 2 ^ (prefixWord ++ tailWord_3063118).sum := by decide
  have hdescent : baseEnd_3063118 < baseStart_3063118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063126 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3063126 : Nat := 118140960795 + 3063126 * 2 ^ 59
def prefixEnd_3063126 : Nat := 4983230072969 + 3 ^ 40 * 3063126 * 2
def baseEnd_3063126 : Nat := 1048570628856058492758631

theorem tailTrace_3063126 : CollatzResearch.WordTrace tailWord_3063126 prefixEnd_3063126 1048570628856058492758631 := by
  unfold tailWord_3063126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982586468801569819786577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74480922333883411411056821 6982586468801569819786577)
  ·
    refine ⟨5236939851601177364839933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6982586468801569819786577 5236939851601177364839933)
    ·
      refine ⟨1963852444350441511814975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5236939851601177364839933 1963852444350441511814975)
      ·
        refine ⟨2945778666525662267722463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963852444350441511814975 2945778666525662267722463)
        ·
          refine ⟨4418667999788493401583695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945778666525662267722463 4418667999788493401583695)
          ·
            refine ⟨6628001999682740102375543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418667999788493401583695 6628001999682740102375543)
            ·
              refine ⟨9942002999524110153563315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628001999682740102375543 9942002999524110153563315)
              ·
                refine ⟨14913004499286165230344973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942002999524110153563315 14913004499286165230344973)
                ·
                  refine ⟨5592376687232311961379365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14913004499286165230344973 5592376687232311961379365)
                  ·
                    refine ⟨1048570628856058492758631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592376687232311961379365 1048570628856058492758631)
                    ·
                      rfl

theorem cell22_3063126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3063126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063126 prefixEnd_3063126 := by exact prefixLift 3063126
  have htrace : WordTrace (prefixWord ++ tailWord_3063126) baseStart_3063126 baseEnd_3063126 := by
    simpa [prefixWord, tailWord_3063126, baseEnd_3063126] using wordTrace_append hprefix tailTrace_3063126
  have hstable : (prefixWord ++ tailWord_3063126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063126).length < 2 ^ (prefixWord ++ tailWord_3063126).sum := by decide
  have hdescent : baseEnd_3063126 < baseStart_3063126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063420 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_3063420 : Nat := 118140960795 + 3063420 * 2 ^ 59
def prefixEnd_3063420 : Nat := 4983230072969 + 3 ^ 40 * 3063420 * 2
def baseEnd_3063420 : Nat := 1048671271064339725907729

theorem tailTrace_3063420 : CollatzResearch.WordTrace tailWord_3063420 prefixEnd_3063420 1048671271064339725907729 := by
  unfold tailWord_3063420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55866053280880002663893857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74488071041173336885191809 55866053280880002663893857)
  ·
    refine ⟨41899539960660001997920393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55866053280880002663893857 41899539960660001997920393)
    ·
      refine ⟨31424654970495001498440295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41899539960660001997920393 31424654970495001498440295)
      ·
        refine ⟨47136982455742502247660443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31424654970495001498440295 47136982455742502247660443)
        ·
          refine ⟨70705473683613753371490665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47136982455742502247660443 70705473683613753371490665)
          ·
            refine ⟨53029105262710315028617999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70705473683613753371490665 53029105262710315028617999)
            ·
              refine ⟨79543657894065472542926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53029105262710315028617999 79543657894065472542926999)
              ·
                refine ⟨119315486841098208814390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79543657894065472542926999 119315486841098208814390499)
                ·
                  refine ⟨178973230261647313221585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119315486841098208814390499 178973230261647313221585749)
                  ·
                    refine ⟨1048671271064339725907729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178973230261647313221585749 1048671271064339725907729)
                    ·
                      rfl

theorem cell22_3063420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_3063420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063420 prefixEnd_3063420 := by exact prefixLift 3063420
  have htrace : WordTrace (prefixWord ++ tailWord_3063420) baseStart_3063420 baseEnd_3063420 := by
    simpa [prefixWord, tailWord_3063420, baseEnd_3063420] using wordTrace_append hprefix tailTrace_3063420
  have hstable : (prefixWord ++ tailWord_3063420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063420).length < 2 ^ (prefixWord ++ tailWord_3063420).sum := by decide
  have hdescent : baseEnd_3063420 < baseStart_3063420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063428 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_3063428 : Nat := 118140960795 + 3063428 * 2 ^ 59
def prefixEnd_3063428 : Nat := 4983230072969 + 3 ^ 40 * 3063428 * 2
def baseEnd_3063428 : Nat := 349558003209276790569235

theorem tailTrace_3063428 : CollatzResearch.WordTrace tailWord_3063428 prefixEnd_3063428 349558003209276790569235 := by
  unfold tailWord_3063428
  simp only [CollatzResearch.WordTrace]
  refine ⟨55866199172865511347039469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74488265563820681796052625 55866199172865511347039469)
  ·
    refine ⟨20949824689824566755139801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55866199172865511347039469 20949824689824566755139801)
    ·
      refine ⟨15712368517368425066354851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20949824689824566755139801 15712368517368425066354851)
      ·
        refine ⟨23568552776052637599532277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15712368517368425066354851 23568552776052637599532277)
        ·
          refine ⟨2209551822754934774956151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23568552776052637599532277 2209551822754934774956151)
          ·
            refine ⟨3314327734132402162434227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209551822754934774956151 3314327734132402162434227)
            ·
              refine ⟨4971491601198603243651341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314327734132402162434227 4971491601198603243651341)
              ·
                refine ⟨1864309350449476216369253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4971491601198603243651341 1864309350449476216369253)
                ·
                  refine ⟨349558003209276790569235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864309350449476216369253 349558003209276790569235)
                  ·
                    rfl

theorem cell22_3063428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_3063428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063428 prefixEnd_3063428 := by exact prefixLift 3063428
  have htrace : WordTrace (prefixWord ++ tailWord_3063428) baseStart_3063428 baseEnd_3063428 := by
    simpa [prefixWord, tailWord_3063428, baseEnd_3063428] using wordTrace_append hprefix tailTrace_3063428
  have hstable : (prefixWord ++ tailWord_3063428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063428).length < 2 ^ (prefixWord ++ tailWord_3063428).sum := by decide
  have hdescent : baseEnd_3063428 < baseStart_3063428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063501 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3063501 : Nat := 118140960795 + 3063501 * 2 ^ 59
def prefixEnd_3063501 : Nat := 4983230072969 + 3 ^ 40 * 3063501 * 2
def baseEnd_3063501 : Nat := 349566333006560838210827

theorem tailTrace_3063501 : CollatzResearch.WordTrace tailWord_3063501 prefixEnd_3063501 349566333006560838210827 := by
  unfold tailWord_3063501
  simp only [CollatzResearch.WordTrace]
  refine ⟨111735060874466556161486357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74490040582977704107657571 111735060874466556161486357)
  ·
    refine ⟨5237580978490619820069673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111735060874466556161486357 5237580978490619820069673)
    ·
      refine ⟨3928185733867964865052255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237580978490619820069673 3928185733867964865052255)
      ·
        refine ⟨5892278600801947297578383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928185733867964865052255 5892278600801947297578383)
        ·
          refine ⟨8838417901202920946367575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892278600801947297578383 8838417901202920946367575)
          ·
            refine ⟨13257626851804381419551363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838417901202920946367575 13257626851804381419551363)
            ·
              refine ⟨19886440277706572129327045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13257626851804381419551363 19886440277706572129327045)
              ·
                refine ⟨3728707552069982274248821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19886440277706572129327045 3728707552069982274248821)
                ·
                  refine ⟨349566333006560838210827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3728707552069982274248821 349566333006560838210827)
                  ·
                    rfl

theorem cell22_3063501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3063501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063501 prefixEnd_3063501 := by exact prefixLift 3063501
  have htrace : WordTrace (prefixWord ++ tailWord_3063501) baseStart_3063501 baseEnd_3063501 := by
    simpa [prefixWord, tailWord_3063501, baseEnd_3063501] using wordTrace_append hprefix tailTrace_3063501
  have hstable : (prefixWord ++ tailWord_3063501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063501).length < 2 ^ (prefixWord ++ tailWord_3063501).sum := by decide
  have hdescent : baseEnd_3063501 < baseStart_3063501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063512 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_3063512 : Nat := 118140960795 + 3063512 * 2 ^ 59
def prefixEnd_3063512 : Nat := 4983230072969 + 3 ^ 40 * 3063512 * 2
def baseEnd_3063512 : Nat := 349567588181494050869149

theorem tailTrace_3063512 : CollatzResearch.WordTrace tailWord_3063512 prefixEnd_3063512 349567588181494050869149 := by
  unfold tailWord_3063512
  simp only [CollatzResearch.WordTrace]
  refine ⟨55867731038713352520068395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74490308051617803360091193 55867731038713352520068395)
  ·
    refine ⟨83801596558070028780102593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55867731038713352520068395 83801596558070028780102593)
    ·
      refine ⟨62851197418552521585076945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83801596558070028780102593 62851197418552521585076945)
      ·
        refine ⟨47138398063914391188807709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62851197418552521585076945 47138398063914391188807709)
        ·
          refine ⟨17676899273967896695802891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47138398063914391188807709 17676899273967896695802891)
          ·
            refine ⟨26515348910951845043704337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676899273967896695802891 26515348910951845043704337)
            ·
              refine ⟨19886511683213883782778253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26515348910951845043704337 19886511683213883782778253)
              ·
                refine ⟨7457441881205206418541845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19886511683213883782778253 7457441881205206418541845)
                ·
                  refine ⟨349567588181494050869149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7457441881205206418541845 349567588181494050869149)
                  ·
                    rfl

theorem cell22_3063512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_3063512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063512 prefixEnd_3063512 := by exact prefixLift 3063512
  have htrace : WordTrace (prefixWord ++ tailWord_3063512) baseStart_3063512 baseEnd_3063512 := by
    simpa [prefixWord, tailWord_3063512, baseEnd_3063512] using wordTrace_append hprefix tailTrace_3063512
  have hstable : (prefixWord ++ tailWord_3063512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063512).length < 2 ^ (prefixWord ++ tailWord_3063512).sum := by decide
  have hdescent : baseEnd_3063512 < baseStart_3063512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063516 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3063516 : Nat := 118140960795 + 3063516 * 2 ^ 59
def prefixEnd_3063516 : Nat := 4983230072969 + 3 ^ 40 * 3063516 * 2
def baseEnd_3063516 : Nat := 1048704133826227475507435

theorem tailTrace_3063516 : CollatzResearch.WordTrace tailWord_3063516 prefixEnd_3063516 1048704133826227475507435 := by
  unfold tailWord_3063516
  simp only [CollatzResearch.WordTrace]
  refine ⟨55867803984706106861641201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74490405312941475815521601 55867803984706106861641201)
  ·
    refine ⟨41900852988529580146230901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55867803984706106861641201 41900852988529580146230901)
    ·
      refine ⟨3928204967674648138709147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41900852988529580146230901 3928204967674648138709147)
      ·
        refine ⟨5892307451511972208063721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928204967674648138709147 5892307451511972208063721)
        ·
          refine ⟨4419230588633979156047791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5892307451511972208063721 4419230588633979156047791)
          ·
            refine ⟨6628845882950968734071687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419230588633979156047791 6628845882950968734071687)
            ·
              refine ⟨9943268824426453101107531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628845882950968734071687 9943268824426453101107531)
              ·
                refine ⟨14914903236639679651661297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9943268824426453101107531 14914903236639679651661297)
                ·
                  refine ⟨11186177427479759738745973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14914903236639679651661297 11186177427479759738745973)
                  ·
                    refine ⟨1048704133826227475507435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11186177427479759738745973 1048704133826227475507435)
                    ·
                      rfl

theorem cell22_3063516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3063516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063516 prefixEnd_3063516 := by exact prefixLift 3063516
  have htrace : WordTrace (prefixWord ++ tailWord_3063516) baseStart_3063516 baseEnd_3063516 := by
    simpa [prefixWord, tailWord_3063516, baseEnd_3063516] using wordTrace_append hprefix tailTrace_3063516
  have hstable : (prefixWord ++ tailWord_3063516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063516).length < 2 ^ (prefixWord ++ tailWord_3063516).sum := by decide
  have hdescent : baseEnd_3063516 < baseStart_3063516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063578 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_3063578 : Nat := 118140960795 + 3063578 * 2 ^ 59
def prefixEnd_3063578 : Nat := 4983230072969 + 3 ^ 40 * 3063578 * 2
def baseEnd_3063578 : Nat := 1048725357693279980457245

theorem tailTrace_3063578 : CollatzResearch.WordTrace tailWord_3063578 prefixEnd_3063578 1048725357693279980457245 := by
  unfold tailWord_3063578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934467323796899578009847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74491912863458398874692925 27934467323796899578009847)
  ·
    refine ⟨41901700985695349367014771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27934467323796899578009847 41901700985695349367014771)
    ·
      refine ⟨62852551478543024050522157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41901700985695349367014771 62852551478543024050522157)
      ·
        refine ⟨23569706804453634018945809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62852551478543024050522157 23569706804453634018945809)
        ·
          refine ⟨17677280103340225514209357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23569706804453634018945809 17677280103340225514209357)
          ·
            refine ⟨6628980038752584567828509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17677280103340225514209357 6628980038752584567828509)
            ·
              refine ⟨2485867514532219212935691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6628980038752584567828509 2485867514532219212935691)
              ·
                refine ⟨3728801271798328819403537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485867514532219212935691 3728801271798328819403537)
                ·
                  refine ⟨2796600953848746614552653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728801271798328819403537 2796600953848746614552653)
                  ·
                    refine ⟨1048725357693279980457245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2796600953848746614552653 1048725357693279980457245)
                    ·
                      rfl

theorem cell22_3063578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_3063578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063578 prefixEnd_3063578 := by exact prefixLift 3063578
  have htrace : WordTrace (prefixWord ++ tailWord_3063578) baseStart_3063578 baseEnd_3063578 := by
    simpa [prefixWord, tailWord_3063578, baseEnd_3063578] using wordTrace_append hprefix tailTrace_3063578
  have hstable : (prefixWord ++ tailWord_3063578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063578).length < 2 ^ (prefixWord ++ tailWord_3063578).sum := by decide
  have hdescent : baseEnd_3063578 < baseStart_3063578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063587 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_3063587 : Nat := 118140960795 + 3063587 * 2 ^ 59
def prefixEnd_3063587 : Nat := 4983230072969 + 3 ^ 40 * 3063587 * 2
def baseEnd_3063587 : Nat := 1048728438577206956982217

theorem tailTrace_3063587 : CollatzResearch.WordTrace tailWord_3063587 prefixEnd_3063587 1048728438577206956982217 := by
  unfold tailWord_3063587
  simp only [CollatzResearch.WordTrace]
  refine ⟨111738197552154992849117015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74492131701436661899411343 111738197552154992849117015)
  ·
    refine ⟨167607296328232489273675523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111738197552154992849117015 167607296328232489273675523)
    ·
      refine ⟨251410944492348733910513285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167607296328232489273675523 251410944492348733910513285)
      ·
        refine ⟨47139552092315387608221241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251410944492348733910513285 47139552092315387608221241)
        ·
          refine ⟨35354664069236540706165931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47139552092315387608221241 35354664069236540706165931)
          ·
            refine ⟨53031996103854811059248897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35354664069236540706165931 53031996103854811059248897)
            ·
              refine ⟨39773997077891108294436673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53031996103854811059248897 39773997077891108294436673)
              ·
                refine ⟨29830497808418331220827505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39773997077891108294436673 29830497808418331220827505)
                ·
                  refine ⟨22372873356313748415620629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29830497808418331220827505 22372873356313748415620629)
                  ·
                    refine ⟨1048728438577206956982217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22372873356313748415620629 1048728438577206956982217)
                    ·
                      rfl

theorem cell22_3063587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_3063587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063587 prefixEnd_3063587 := by exact prefixLift 3063587
  have htrace : WordTrace (prefixWord ++ tailWord_3063587) baseStart_3063587 baseEnd_3063587 := by
    simpa [prefixWord, tailWord_3063587, baseEnd_3063587] using wordTrace_append hprefix tailTrace_3063587
  have hstable : (prefixWord ++ tailWord_3063587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063587).length < 2 ^ (prefixWord ++ tailWord_3063587).sum := by decide
  have hdescent : baseEnd_3063587 < baseStart_3063587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063632 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_3063632 : Nat := 118140960795 + 3063632 * 2 ^ 59
def prefixEnd_3063632 : Nat := 4983230072969 + 3 ^ 40 * 3063632 * 2
def baseEnd_3063632 : Nat := 1048743842996841839607079

theorem tailTrace_3063632 : CollatzResearch.WordTrace tailWord_3063632 prefixEnd_3063632 1048743842996841839607079 := by
  unfold tailWord_3063632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55869919418495982767252575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74493225891327977023003433 55869919418495982767252575)
  ·
    refine ⟨83804879127743974150878863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55869919418495982767252575 83804879127743974150878863)
    ·
      refine ⟨125707318691615961226318295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83804879127743974150878863 125707318691615961226318295)
      ·
        refine ⟨188560978037423941839477443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125707318691615961226318295 188560978037423941839477443)
        ·
          refine ⟨282841467056135912759216165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188560978037423941839477443 282841467056135912759216165)
          ·
            refine ⟨53032775073025483642353031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282841467056135912759216165 53032775073025483642353031)
            ·
              refine ⟨79549162609538225463529547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53032775073025483642353031 79549162609538225463529547)
              ·
                refine ⟨119323743914307338195294321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79549162609538225463529547 119323743914307338195294321)
                ·
                  refine ⟨89492807935730503646470741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119323743914307338195294321 89492807935730503646470741)
                  ·
                    refine ⟨1048743842996841839607079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89492807935730503646470741 1048743842996841839607079)
                    ·
                      rfl

theorem cell22_3063632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_3063632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063632 prefixEnd_3063632 := by exact prefixLift 3063632
  have htrace : WordTrace (prefixWord ++ tailWord_3063632) baseStart_3063632 baseEnd_3063632 := by
    simpa [prefixWord, tailWord_3063632, baseEnd_3063632] using wordTrace_append hprefix tailTrace_3063632
  have hstable : (prefixWord ++ tailWord_3063632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063632).length < 2 ^ (prefixWord ++ tailWord_3063632).sum := by decide
  have hdescent : baseEnd_3063632 < baseStart_3063632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063636 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3063636 : Nat := 118140960795 + 3063636 * 2 ^ 59
def prefixEnd_3063636 : Nat := 4983230072969 + 3 ^ 40 * 3063636 * 2
def baseEnd_3063636 : Nat := 349581737426195720835689

theorem tailTrace_3063636 : CollatzResearch.WordTrace tailWord_3063636 prefixEnd_3063636 349581737426195720835689 := by
  unfold tailWord_3063636
  simp only [CollatzResearch.WordTrace]
  refine ⟨55869992364488737108825381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74493323152651649478433841 55869992364488737108825381)
  ·
    refine ⟨10475623568341638207904759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55869992364488737108825381 10475623568341638207904759)
    ·
      refine ⟨15713435352512457311857139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10475623568341638207904759 15713435352512457311857139)
      ·
        refine ⟨23570153028768685967785709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15713435352512457311857139 23570153028768685967785709)
        ·
          refine ⟨8838807385788257237919641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23570153028768685967785709 8838807385788257237919641)
          ·
            refine ⟨6629105539341192928439731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8838807385788257237919641 6629105539341192928439731)
            ·
              refine ⟨9943658309011789392659597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629105539341192928439731 9943658309011789392659597)
              ·
                refine ⟨3728871865879421022247349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9943658309011789392659597 3728871865879421022247349)
                ·
                  refine ⟨349581737426195720835689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3728871865879421022247349 349581737426195720835689)
                  ·
                    rfl

theorem cell22_3063636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3063636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063636 prefixEnd_3063636 := by exact prefixLift 3063636
  have htrace : WordTrace (prefixWord ++ tailWord_3063636) baseStart_3063636 baseEnd_3063636 := by
    simpa [prefixWord, tailWord_3063636, baseEnd_3063636] using wordTrace_append hprefix tailTrace_3063636
  have hstable : (prefixWord ++ tailWord_3063636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063636).length < 2 ^ (prefixWord ++ tailWord_3063636).sum := by decide
  have hdescent : baseEnd_3063636 < baseStart_3063636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063649 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3063649 : Nat := 118140960795 + 3063649 * 2 ^ 59
def prefixEnd_3063649 : Nat := 4983230072969 + 3 ^ 40 * 3063649 * 2
def baseEnd_3063649 : Nat := 1048749662444259461932027

theorem tailTrace_3063649 : CollatzResearch.WordTrace tailWord_3063649 prefixEnd_3063649 1048749662444259461932027 := by
  unfold tailWord_3063649
  simp only [CollatzResearch.WordTrace]
  refine ⟨111740458877930377437874001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74493639251953584958582667 111740458877930377437874001)
  ·
    refine ⟨83805344158447783078405501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111740458877930377437874001 83805344158447783078405501)
    ·
      refine ⟨31427004059417918654402063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83805344158447783078405501 31427004059417918654402063)
      ·
        refine ⟨47140506089126877981603095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31427004059417918654402063 47140506089126877981603095)
        ·
          refine ⟨70710759133690316972404643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47140506089126877981603095 70710759133690316972404643)
          ·
            refine ⟨106066138700535475458606965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70710759133690316972404643 106066138700535475458606965)
            ·
              refine ⟨9943700503175200824244403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106066138700535475458606965 9943700503175200824244403)
              ·
                refine ⟨14915550754762801236366605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9943700503175200824244403 14915550754762801236366605)
                ·
                  refine ⟨5593331533036050463637477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14915550754762801236366605 5593331533036050463637477)
                  ·
                    refine ⟨1048749662444259461932027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593331533036050463637477 1048749662444259461932027)
                    ·
                      rfl

theorem cell22_3063649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3063649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063649 prefixEnd_3063649 := by exact prefixLift 3063649
  have htrace : WordTrace (prefixWord ++ tailWord_3063649) baseStart_3063649 baseEnd_3063649 := by
    simpa [prefixWord, tailWord_3063649, baseEnd_3063649] using wordTrace_append hprefix tailTrace_3063649
  have hstable : (prefixWord ++ tailWord_3063649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063649).length < 2 ^ (prefixWord ++ tailWord_3063649).sum := by decide
  have hdescent : baseEnd_3063649 < baseStart_3063649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063711 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 6]
def baseStart_3063711 : Nat := 118140960795 + 3063711 * 2 ^ 59
def prefixEnd_3063711 : Nat := 4983230072969 + 3 ^ 40 * 3063711 * 2
def baseEnd_3063711 : Nat := 1048770886311311966881837

theorem tailTrace_3063711 : CollatzResearch.WordTrace tailWord_3063711 prefixEnd_3063711 1048770886311311966881837 := by
  unfold tailWord_3063711
  simp only [CollatzResearch.WordTrace]
  refine ⟨111742720203705762026630987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74495146802470508017753991 111742720203705762026630987)
  ·
    refine ⟨167614080305558643039946481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111742720203705762026630987 167614080305558643039946481)
    ·
      refine ⟨125710560229168982279959861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167614080305558643039946481 125710560229168982279959861)
      ·
        refine ⟨11785365021484592088746237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125710560229168982279959861 11785365021484592088746237)
        ·
          refine ⟨4419511883056722033279839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11785365021484592088746237 4419511883056722033279839)
          ·
            refine ⟨6629267824585083049919759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419511883056722033279839 6629267824585083049919759)
            ·
              refine ⟨9943901736877624574879639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629267824585083049919759 9943901736877624574879639)
              ·
                refine ⟨14915852605316436862319459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9943901736877624574879639 14915852605316436862319459)
                ·
                  refine ⟨22373778907974655293479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14915852605316436862319459 22373778907974655293479189)
                  ·
                    refine ⟨1048770886311311966881837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22373778907974655293479189 1048770886311311966881837)
                    ·
                      rfl

theorem cell22_3063711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_3063711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063711 prefixEnd_3063711 := by exact prefixLift 3063711
  have htrace : WordTrace (prefixWord ++ tailWord_3063711) baseStart_3063711 baseEnd_3063711 := by
    simpa [prefixWord, tailWord_3063711, baseEnd_3063711] using wordTrace_append hprefix tailTrace_3063711
  have hstable : (prefixWord ++ tailWord_3063711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063711).length < 2 ^ (prefixWord ++ tailWord_3063711).sum := by decide
  have hdescent : baseEnd_3063711 < baseStart_3063711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063775 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 1, 3]
def baseStart_3063775 : Nat := 118140960795 + 3063775 * 2 ^ 59
def prefixEnd_3063775 : Nat := 4983230072969 + 3 ^ 40 * 3063775 * 2
def baseEnd_3063775 : Nat := 1048792794819237133281641

theorem tailTrace_3063775 : CollatzResearch.WordTrace tailWord_3063775 prefixEnd_3063775 1048792794819237133281641 := by
  unfold tailWord_3063775
  simp only [CollatzResearch.WordTrace]
  refine ⟨111745054475473900956960779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74496702983649267304640519 111745054475473900956960779)
  ·
    refine ⟨167617581713210851435441169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111745054475473900956960779 167617581713210851435441169)
    ·
      refine ⟨125713186284908138576580877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167617581713210851435441169 125713186284908138576580877)
      ·
        refine ⟨47142444856840551966217829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125713186284908138576580877 47142444856840551966217829)
        ·
          refine ⟨8839208410657603493665843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47142444856840551966217829 8839208410657603493665843)
          ·
            refine ⟨13258812615986405240498765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839208410657603493665843 13258812615986405240498765)
            ·
              refine ⟨4972054730994901965187037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13258812615986405240498765 4972054730994901965187037)
              ·
                refine ⟨1864520524123088236945139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4972054730994901965187037 1864520524123088236945139)
                ·
                  refine ⟨2796780786184632355417709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864520524123088236945139 2796780786184632355417709)
                  ·
                    refine ⟨1048792794819237133281641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2796780786184632355417709 1048792794819237133281641)
                    ·
                      rfl

theorem cell22_3063775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_3063775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063775 prefixEnd_3063775 := by exact prefixLift 3063775
  have htrace : WordTrace (prefixWord ++ tailWord_3063775) baseStart_3063775 baseEnd_3063775 := by
    simpa [prefixWord, tailWord_3063775, baseEnd_3063775] using wordTrace_append hprefix tailTrace_3063775
  have hstable : (prefixWord ++ tailWord_3063775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063775).length < 2 ^ (prefixWord ++ tailWord_3063775).sum := by decide
  have hdescent : baseEnd_3063775 < baseStart_3063775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063818 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3063818 : Nat := 118140960795 + 3063818 * 2 ^ 59
def prefixEnd_3063818 : Nat := 4983230072969 + 3 ^ 40 * 3063818 * 2
def baseEnd_3063818 : Nat := 1048807514597999354456509

theorem tailTrace_3063818 : CollatzResearch.WordTrace tailWord_3063818 prefixEnd_3063818 1048807514597999354456509 := by
  unfold tailWord_3063818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936655703579529825194027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74497748542878746200517405 27936655703579529825194027)
  ·
    refine ⟨41904983555369294737791041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27936655703579529825194027 41904983555369294737791041)
    ·
      refine ⟨31428737666526971053343281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41904983555369294737791041 31428737666526971053343281)
      ·
        refine ⟨23571553249895228290007461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31428737666526971053343281 23571553249895228290007461)
        ·
          refine ⟨4419666234355355304376399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23571553249895228290007461 4419666234355355304376399)
          ·
            refine ⟨6629499351533032956564599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419666234355355304376399 6629499351533032956564599)
            ·
              refine ⟨9944249027299549434846899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629499351533032956564599 9944249027299549434846899)
              ·
                refine ⟨14916373540949324152270349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9944249027299549434846899 14916373540949324152270349)
                ·
                  refine ⟨5593640077855996557101381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14916373540949324152270349 5593640077855996557101381)
                  ·
                    refine ⟨1048807514597999354456509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593640077855996557101381 1048807514597999354456509)
                    ·
                      rfl

theorem cell22_3063818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3063818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063818 prefixEnd_3063818 := by exact prefixLift 3063818
  have htrace : WordTrace (prefixWord ++ tailWord_3063818) baseStart_3063818 baseEnd_3063818 := by
    simpa [prefixWord, tailWord_3063818, baseEnd_3063818] using wordTrace_append hprefix tailTrace_3063818
  have hstable : (prefixWord ++ tailWord_3063818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063818).length < 2 ^ (prefixWord ++ tailWord_3063818).sum := by decide
  have hdescent : baseEnd_3063818 < baseStart_3063818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063850 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_3063850 : Nat := 118140960795 + 3063850 * 2 ^ 59
def prefixEnd_3063850 : Nat := 4983230072969 + 3 ^ 40 * 3063850 * 2
def baseEnd_3063850 : Nat := 349606156283987312552137

theorem tailTrace_3063850 : CollatzResearch.WordTrace tailWord_3063850 prefixEnd_3063850 349606156283987312552137 := by
  unfold tailWord_3063850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936947487550547191485251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74498526633468125843960669 27936947487550547191485251)
  ·
    refine ⟨41905421231325820787227877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27936947487550547191485251 41905421231325820787227877)
    ·
      refine ⟨7857266480873591397605227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41905421231325820787227877 7857266480873591397605227)
      ·
        refine ⟨11785899721310387096407841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857266480873591397605227 11785899721310387096407841)
        ·
          refine ⟨8839424790982790322305881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11785899721310387096407841 8839424790982790322305881)
          ·
            refine ⟨6629568593237092741729411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839424790982790322305881 6629568593237092741729411)
            ·
              refine ⟨9944352889855639112594117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629568593237092741729411 9944352889855639112594117)
              ·
                refine ⟨1864566166847932333611397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9944352889855639112594117 1864566166847932333611397)
                ·
                  refine ⟨349606156283987312552137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864566166847932333611397 349606156283987312552137)
                  ·
                    rfl

theorem cell22_3063850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_3063850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063850 prefixEnd_3063850 := by exact prefixLift 3063850
  have htrace : WordTrace (prefixWord ++ tailWord_3063850) baseStart_3063850 baseEnd_3063850 := by
    simpa [prefixWord, tailWord_3063850, baseEnd_3063850] using wordTrace_append hprefix tailTrace_3063850
  have hstable : (prefixWord ++ tailWord_3063850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063850).length < 2 ^ (prefixWord ++ tailWord_3063850).sum := by decide
  have hdescent : baseEnd_3063850 < baseStart_3063850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063861 : List Nat := [1, 3, 3, 1, 1, 1, 5, 7]
def baseStart_3063861 : Nat := 118140960795 + 3063861 * 2 ^ 59
def prefixEnd_3063861 : Nat := 4983230072969 + 3 ^ 40 * 3063861 * 2
def baseEnd_3063861 : Nat := 116535803819640175070153

theorem tailTrace_3063861 : CollatzResearch.WordTrace tailWord_3063861 prefixEnd_3063861 116535803819640175070153 := by
  unfold tailWord_3063861
  simp only [CollatzResearch.WordTrace]
  refine ⟨111748191153162337644591437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74498794102108225096394291 111748191153162337644591437)
  ·
    refine ⟨41905571682435876616721789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111748191153162337644591437 41905571682435876616721789)
    ·
      refine ⟨15714589380913453731270671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41905571682435876616721789 15714589380913453731270671)
      ·
        refine ⟨23571884071370180596906007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15714589380913453731270671 23571884071370180596906007)
        ·
          refine ⟨35357826107055270895359011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23571884071370180596906007 35357826107055270895359011)
          ·
            refine ⟨53036739160582906343038517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35357826107055270895359011 53036739160582906343038517)
            ·
              refine ⟨4972194296304647469659861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53036739160582906343038517 4972194296304647469659861)
              ·
                refine ⟨116535803819640175070153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4972194296304647469659861 116535803819640175070153)
                ·
                  rfl

theorem cell22_3063861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 7].length) (baseStart_3063861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063861 prefixEnd_3063861 := by exact prefixLift 3063861
  have htrace : WordTrace (prefixWord ++ tailWord_3063861) baseStart_3063861 baseEnd_3063861 := by
    simpa [prefixWord, tailWord_3063861, baseEnd_3063861] using wordTrace_append hprefix tailTrace_3063861
  have hstable : (prefixWord ++ tailWord_3063861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063861).length < 2 ^ (prefixWord ++ tailWord_3063861).sum := by decide
  have hdescent : baseEnd_3063861 < baseStart_3063861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063921 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3063921 : Nat := 118140960795 + 3063921 * 2 ^ 59
def prefixEnd_3063921 : Nat := 4983230072969 + 3 ^ 40 * 3063921 * 2
def baseEnd_3063921 : Nat := 1048842773602941419131193

theorem tailTrace_3063921 : CollatzResearch.WordTrace tailWord_3063921 prefixEnd_3063921 1048842773602941419131193 := by
  unfold tailWord_3063921
  simp only [CollatzResearch.WordTrace]
  refine ⟨111750379532944967891775617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74500253021963311927850411 111750379532944967891775617)
  ·
    refine ⟨83812784649708725918831713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111750379532944967891775617 83812784649708725918831713)
    ·
      refine ⟨62859588487281544439123785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83812784649708725918831713 62859588487281544439123785)
      ·
        refine ⟨47144691365461158329342839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62859588487281544439123785 47144691365461158329342839)
        ·
          refine ⟨70717037048191737494014259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47144691365461158329342839 70717037048191737494014259)
          ·
            refine ⟨106075555572287606241021389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70717037048191737494014259 106075555572287606241021389)
            ·
              refine ⟨39778333339607852340383021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106075555572287606241021389 39778333339607852340383021)
              ·
                refine ⟨14916875002352944627643633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39778333339607852340383021 14916875002352944627643633)
                ·
                  refine ⟨11187656251764708470732725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14916875002352944627643633 11187656251764708470732725)
                  ·
                    refine ⟨1048842773602941419131193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11187656251764708470732725 1048842773602941419131193)
                    ·
                      rfl

theorem cell22_3063921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3063921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063921 prefixEnd_3063921 := by exact prefixLift 3063921
  have htrace : WordTrace (prefixWord ++ tailWord_3063921) baseStart_3063921 baseEnd_3063921 := by
    simpa [prefixWord, tailWord_3063921, baseEnd_3063921] using wordTrace_append hprefix tailTrace_3063921
  have hstable : (prefixWord ++ tailWord_3063921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063921).length < 2 ^ (prefixWord ++ tailWord_3063921).sum := by decide
  have hdescent : baseEnd_3063921 < baseStart_3063921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063944 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 1, 3]
def baseStart_3063944 : Nat := 118140960795 + 3063944 * 2 ^ 59
def prefixEnd_3063944 : Nat := 4983230072969 + 3 ^ 40 * 3063944 * 2
def baseEnd_3063944 : Nat := 1048850646972977025806123

theorem tailTrace_3063944 : CollatzResearch.WordTrace tailWord_3063944 prefixEnd_3063944 1048850646972977025806123 := by
  unfold tailWord_3063944
  simp only [CollatzResearch.WordTrace]
  refine ⟨55875609205930821409931443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74500812274574428546575257 55875609205930821409931443)
  ·
    refine ⟨83813413808896232114897165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55875609205930821409931443 83813413808896232114897165)
    ·
      refine ⟨31430030178336087043086437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83813413808896232114897165 31430030178336087043086437)
      ·
        refine ⟨5893130658438016320578707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31430030178336087043086437 5893130658438016320578707)
        ·
          refine ⟨8839695987657024480868061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5893130658438016320578707 8839695987657024480868061)
          ·
            refine ⟨3314885995371384180325523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8839695987657024480868061 3314885995371384180325523)
            ·
              refine ⟨4972328993057076270488285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314885995371384180325523 4972328993057076270488285)
              ·
                refine ⟨1864623372396403601433107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4972328993057076270488285 1864623372396403601433107)
                ·
                  refine ⟨2796935058594605402149661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864623372396403601433107 2796935058594605402149661)
                  ·
                    refine ⟨1048850646972977025806123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2796935058594605402149661 1048850646972977025806123)
                    ·
                      rfl

theorem cell22_3063944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_3063944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063944 prefixEnd_3063944 := by exact prefixLift 3063944
  have htrace : WordTrace (prefixWord ++ tailWord_3063944) baseStart_3063944 baseEnd_3063944 := by
    simpa [prefixWord, tailWord_3063944, baseEnd_3063944] using wordTrace_append hprefix tailTrace_3063944
  have hstable : (prefixWord ++ tailWord_3063944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063944).length < 2 ^ (prefixWord ++ tailWord_3063944).sum := by decide
  have hdescent : baseEnd_3063944 < baseStart_3063944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063968 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_3063968 : Nat := 118140960795 + 3063968 * 2 ^ 59
def prefixEnd_3063968 : Nat := 4983230072969 + 3 ^ 40 * 3063968 * 2
def baseEnd_3063968 : Nat := 349619620887816321068683

theorem tailTrace_3063968 : CollatzResearch.WordTrace tailWord_3063968 prefixEnd_3063968 349619620887816321068683 := by
  unfold tailWord_3063968
  simp only [CollatzResearch.WordTrace]
  refine ⟨55876046881887347459368279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74501395842516463279157705 55876046881887347459368279)
  ·
    refine ⟨83814070322831021189052419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55876046881887347459368279 83814070322831021189052419)
    ·
      refine ⟨125721105484246531783578629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83814070322831021189052419 125721105484246531783578629)
      ·
        refine ⟨23572707278296224709420993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125721105484246531783578629 23572707278296224709420993)
        ·
          refine ⟨17679530458722168532065745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23572707278296224709420993 17679530458722168532065745)
          ·
            refine ⟨13259647844041626399049309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17679530458722168532065745 13259647844041626399049309)
            ·
              refine ⟨4972367941515609899643491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13259647844041626399049309 4972367941515609899643491)
              ·
                refine ⟨7458551912273414849465237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972367941515609899643491 7458551912273414849465237)
                ·
                  refine ⟨349619620887816321068683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7458551912273414849465237 349619620887816321068683)
                  ·
                    rfl

theorem cell22_3063968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_3063968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3063968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3063968 prefixEnd_3063968 := by exact prefixLift 3063968
  have htrace : WordTrace (prefixWord ++ tailWord_3063968) baseStart_3063968 baseEnd_3063968 := by
    simpa [prefixWord, tailWord_3063968, baseEnd_3063968] using wordTrace_append hprefix tailTrace_3063968
  have hstable : (prefixWord ++ tailWord_3063968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063968).length < 2 ^ (prefixWord ++ tailWord_3063968).sum := by decide
  have hdescent : baseEnd_3063968 < baseStart_3063968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064013 : List Nat := [1, 6, 2, 13]
def baseStart_3064013 : Nat := 118140960795 + 3064013 * 2 ^ 59
def prefixEnd_3064013 : Nat := 4983230072969 + 3 ^ 40 * 3064013 * 2
def baseEnd_3064013 : Nat := 1438785002857453835159

theorem tailTrace_3064013 : CollatzResearch.WordTrace tailWord_3064013 prefixEnd_3064013 1438785002857453835159 := by
  unfold tailWord_3064013
  simp only [CollatzResearch.WordTrace]
  refine ⟨111753735048611667604124693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74502490032407778402749795 111753735048611667604124693)
  ·
    refine ⟨5238456330403671918943345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111753735048611667604124693 5238456330403671918943345)
    ·
      refine ⟨3928842247802753939207509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5238456330403671918943345 3928842247802753939207509)
      ·
        refine ⟨1438785002857453835159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3928842247802753939207509 1438785002857453835159)
        ·
          rfl

theorem cell22_3064013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 13].length) (baseStart_3064013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064013 prefixEnd_3064013 := by exact prefixLift 3064013
  have htrace : WordTrace (prefixWord ++ tailWord_3064013) baseStart_3064013 baseEnd_3064013 := by
    simpa [prefixWord, tailWord_3064013, baseEnd_3064013] using wordTrace_append hprefix tailTrace_3064013
  have hstable : (prefixWord ++ tailWord_3064013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064013).length < 2 ^ (prefixWord ++ tailWord_3064013).sum := by decide
  have hdescent : baseEnd_3064013 < baseStart_3064013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064073 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_3064073 : Nat := 118140960795 + 3064073 * 2 ^ 59
def prefixEnd_3064073 : Nat := 4983230072969 + 3 ^ 40 * 3064073 * 2
def baseEnd_3064073 : Nat := 1048894806309263689330727

theorem tailTrace_3064073 : CollatzResearch.WordTrace tailWord_3064073 prefixEnd_3064073 1048894806309263689330727 := by
  unfold tailWord_3064073
  simp only [CollatzResearch.WordTrace]
  refine ⟨111755923428394297851308873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74503948952262865234205915 111755923428394297851308873)
  ·
    refine ⟨83816942571295723388481655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111755923428394297851308873 83816942571295723388481655)
    ·
      refine ⟨125725413856943585082722483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83816942571295723388481655 125725413856943585082722483)
      ·
        refine ⟨188588120785415377624083725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125725413856943585082722483 188588120785415377624083725)
        ·
          refine ⟨70720545294530766609031397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188588120785415377624083725 70720545294530766609031397)
          ·
            refine ⟨13260102242724518739193387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70720545294530766609031397 13260102242724518739193387)
            ·
              refine ⟨19890153364086778108790081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13260102242724518739193387 19890153364086778108790081)
              ·
                refine ⟨14917615023065083581592561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19890153364086778108790081 14917615023065083581592561)
                ·
                  refine ⟨11188211267298812686194421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14917615023065083581592561 11188211267298812686194421)
                  ·
                    refine ⟨1048894806309263689330727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11188211267298812686194421 1048894806309263689330727)
                    ·
                      rfl

theorem cell22_3064073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_3064073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064073 prefixEnd_3064073 := by exact prefixLift 3064073
  have htrace : WordTrace (prefixWord ++ tailWord_3064073) baseStart_3064073 baseEnd_3064073 := by
    simpa [prefixWord, tailWord_3064073, baseEnd_3064073] using wordTrace_append hprefix tailTrace_3064073
  have hstable : (prefixWord ++ tailWord_3064073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064073).length < 2 ^ (prefixWord ++ tailWord_3064073).sum := by decide
  have hdescent : baseEnd_3064073 < baseStart_3064073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064135 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3064135 : Nat := 118140960795 + 3064135 * 2 ^ 59
def prefixEnd_3064135 : Nat := 4983230072969 + 3 ^ 40 * 3064135 * 2
def baseEnd_3064135 : Nat := 1048916030176316194280537

theorem tailTrace_3064135 : CollatzResearch.WordTrace tailWord_3064135 prefixEnd_3064135 1048916030176316194280537 := by
  unfold tailWord_3064135
  simp only [CollatzResearch.WordTrace]
  refine ⟨111758184754169682440065859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74505456502779788293377239 111758184754169682440065859)
  ·
    refine ⟨167637277131254523660098789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111758184754169682440065859 167637277131254523660098789)
    ·
      refine ⟨31431989462110223186268523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167637277131254523660098789 31431989462110223186268523)
      ·
        refine ⟨47147984193165334779402785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31431989462110223186268523 47147984193165334779402785)
        ·
          refine ⟨35360988144874001084552089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47147984193165334779402785 35360988144874001084552089)
          ·
            refine ⟨26520741108655500813414067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35360988144874001084552089 26520741108655500813414067)
            ·
              refine ⟨39781111662983251220121101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26520741108655500813414067 39781111662983251220121101)
              ·
                refine ⟨14917916873618719207545413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39781111662983251220121101 14917916873618719207545413)
                ·
                  refine ⟨2797109413803509851414765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14917916873618719207545413 2797109413803509851414765)
                  ·
                    refine ⟨1048916030176316194280537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797109413803509851414765 1048916030176316194280537)
                    ·
                      rfl

theorem cell22_3064135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3064135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064135 prefixEnd_3064135 := by exact prefixLift 3064135
  have htrace : WordTrace (prefixWord ++ tailWord_3064135) baseStart_3064135 baseEnd_3064135 := by
    simpa [prefixWord, tailWord_3064135, baseEnd_3064135] using wordTrace_append hprefix tailTrace_3064135
  have hstable : (prefixWord ++ tailWord_3064135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064135).length < 2 ^ (prefixWord ++ tailWord_3064135).sum := by decide
  have hdescent : baseEnd_3064135 < baseStart_3064135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064156 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3064156 : Nat := 118140960795 + 3064156 * 2 ^ 59
def prefixEnd_3064156 : Nat := 4983230072969 + 3 ^ 40 * 3064156 * 2
def baseEnd_3064156 : Nat := 1048923218905479139505473

theorem tailTrace_3064156 : CollatzResearch.WordTrace tailWord_3064156 prefixEnd_3064156 1048923218905479139505473 := by
  unfold tailWord_3064156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55879475343546801513290161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74505967124729068684386881 55879475343546801513290161)
  ·
    refine ⟨41909606507660101134967621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55879475343546801513290161 41909606507660101134967621)
    ·
      refine ⟨7858051220186268962806429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41909606507660101134967621 7858051220186268962806429)
      ·
        refine ⟨2946769207569850861052411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7858051220186268962806429 2946769207569850861052411)
        ·
          refine ⟨4420153811354776291578617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946769207569850861052411 4420153811354776291578617)
          ·
            refine ⟨3315115358516082218683963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420153811354776291578617 3315115358516082218683963)
            ·
              refine ⟨4972673037774123328025945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315115358516082218683963 4972673037774123328025945)
              ·
                refine ⟨3729504778330592496019459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4972673037774123328025945 3729504778330592496019459)
                ·
                  refine ⟨5594257167495888744029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729504778330592496019459 5594257167495888744029189)
                  ·
                    refine ⟨1048923218905479139505473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594257167495888744029189 1048923218905479139505473)
                    ·
                      rfl

theorem cell22_3064156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3064156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064156 prefixEnd_3064156 := by exact prefixLift 3064156
  have htrace : WordTrace (prefixWord ++ tailWord_3064156) baseStart_3064156 baseEnd_3064156 := by
    simpa [prefixWord, tailWord_3064156, baseEnd_3064156] using wordTrace_append hprefix tailTrace_3064156
  have hstable : (prefixWord ++ tailWord_3064156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064156).length < 2 ^ (prefixWord ++ tailWord_3064156).sum := by decide
  have hdescent : baseEnd_3064156 < baseStart_3064156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064167 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3064167 : Nat := 118140960795 + 3064167 * 2 ^ 59
def prefixEnd_3064167 : Nat := 4983230072969 + 3 ^ 40 * 3064167 * 2
def baseEnd_3064167 : Nat := 1048926984430278777480439

theorem tailTrace_3064167 : CollatzResearch.WordTrace tailWord_3064167 prefixEnd_3064167 1048926984430278777480439 := by
  unfold tailWord_3064167
  simp only [CollatzResearch.WordTrace]
  refine ⟨111759351890053751905230755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74506234593369167936820503 111759351890053751905230755)
  ·
    refine ⟨167639027835080627857846133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111759351890053751905230755 167639027835080627857846133)
    ·
      refine ⟨15716158859538808861673075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167639027835080627857846133 15716158859538808861673075)
      ·
        refine ⟨23574238289308213292509613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716158859538808861673075 23574238289308213292509613)
        ·
          refine ⟨8840339358490579984691105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23574238289308213292509613 8840339358490579984691105)
          ·
            refine ⟨6630254518867934988518329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8840339358490579984691105 6630254518867934988518329)
            ·
              refine ⟨4972690889150951241388747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630254518867934988518329 4972690889150951241388747)
              ·
                refine ⟨7459036333726426862083121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972690889150951241388747 7459036333726426862083121)
                ·
                  refine ⟨5594277250294820146562341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7459036333726426862083121 5594277250294820146562341)
                  ·
                    refine ⟨1048926984430278777480439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594277250294820146562341 1048926984430278777480439)
                    ·
                      rfl

theorem cell22_3064167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3064167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064167 prefixEnd_3064167 := by exact prefixLift 3064167
  have htrace : WordTrace (prefixWord ++ tailWord_3064167) baseStart_3064167 baseEnd_3064167 := by
    simpa [prefixWord, tailWord_3064167, baseEnd_3064167] using wordTrace_append hprefix tailTrace_3064167
  have hstable : (prefixWord ++ tailWord_3064167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064167).length < 2 ^ (prefixWord ++ tailWord_3064167).sum := by decide
  have hdescent : baseEnd_3064167 < baseStart_3064167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064182 : List Nat := [5, 1, 1, 4, 1, 10]
def baseStart_3064182 : Nat := 118140960795 + 3064182 * 2 ^ 59
def prefixEnd_3064182 : Nat := 4983230072969 + 3 ^ 40 * 3064182 * 2
def baseEnd_3064182 : Nat := 12949779249837330103153

theorem tailTrace_3064182 : CollatzResearch.WordTrace tailWord_3064182 prefixEnd_3064182 12949779249837330103153 := by
  unfold tailWord_3064182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984993686562463091689175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74506599323332939644684533 6984993686562463091689175)
  ·
    refine ⟨10477490529843694637533763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6984993686562463091689175 10477490529843694637533763)
    ·
      refine ⟨15716235794765541956300645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477490529843694637533763 15716235794765541956300645)
      ·
        refine ⟨2946794211518539116806371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15716235794765541956300645 2946794211518539116806371)
        ·
          refine ⟨4420191317277808675209557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946794211518539116806371 4420191317277808675209557)
          ·
            refine ⟨12949779249837330103153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4420191317277808675209557 12949779249837330103153)
            ·
              rfl

theorem cell22_3064182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 10].length) (baseStart_3064182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064182 prefixEnd_3064182 := by exact prefixLift 3064182
  have htrace : WordTrace (prefixWord ++ tailWord_3064182) baseStart_3064182 baseEnd_3064182 := by
    simpa [prefixWord, tailWord_3064182, baseEnd_3064182] using wordTrace_append hprefix tailTrace_3064182
  have hstable : (prefixWord ++ tailWord_3064182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064182).length < 2 ^ (prefixWord ++ tailWord_3064182).sum := by decide
  have hdescent : baseEnd_3064182 < baseStart_3064182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064231 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3064231 : Nat := 118140960795 + 3064231 * 2 ^ 59
def prefixEnd_3064231 : Nat := 4983230072969 + 3 ^ 40 * 3064231 * 2
def baseEnd_3064231 : Nat := 1048948892938203943880243

theorem tailTrace_3064231 : CollatzResearch.WordTrace tailWord_3064231 prefixEnd_3064231 1048948892938203943880243 := by
  unfold tailWord_3064231
  simp only [CollatzResearch.WordTrace]
  refine ⟨111761686161821890835560547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74507790774547927223707031 111761686161821890835560547)
  ·
    refine ⟨167642529242732836253340821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111761686161821890835560547 167642529242732836253340821)
    ·
      refine ⟨7858243558253101699375351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167642529242732836253340821 7858243558253101699375351)
      ·
        refine ⟨11787365337379652549063027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7858243558253101699375351 11787365337379652549063027)
        ·
          refine ⟨17681048006069478823594541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11787365337379652549063027 17681048006069478823594541)
          ·
            refine ⟨6630393002276054558847953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17681048006069478823594541 6630393002276054558847953)
            ·
              refine ⟨4972794751707040919135965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630393002276054558847953 4972794751707040919135965)
              ·
                refine ⟨1864798031890140344675987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4972794751707040919135965 1864798031890140344675987)
                ·
                  refine ⟨2797197047835210517013981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864798031890140344675987 2797197047835210517013981)
                  ·
                    refine ⟨1048948892938203943880243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797197047835210517013981 1048948892938203943880243)
                    ·
                      rfl

theorem cell22_3064231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3064231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064231 prefixEnd_3064231 := by exact prefixLift 3064231
  have htrace : WordTrace (prefixWord ++ tailWord_3064231) baseStart_3064231 baseEnd_3064231 := by
    simpa [prefixWord, tailWord_3064231, baseEnd_3064231] using wordTrace_append hprefix tailTrace_3064231
  have hstable : (prefixWord ++ tailWord_3064231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064231).length < 2 ^ (prefixWord ++ tailWord_3064231).sum := by decide
  have hdescent : baseEnd_3064231 < baseStart_3064231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064287 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 4, 3]
def baseStart_3064287 : Nat := 118140960795 + 3064287 * 2 ^ 59
def prefixEnd_3064287 : Nat := 4983230072969 + 3 ^ 40 * 3064287 * 2
def baseEnd_3064287 : Nat := 1048968062882638464480071

theorem tailTrace_3064287 : CollatzResearch.WordTrace tailWord_3064287 prefixEnd_3064287 1048968062882638464480071 := by
  unfold tailWord_3064287
  simp only [CollatzResearch.WordTrace]
  refine ⟨111763728649619012399599115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74509152433079341599732743 111763728649619012399599115)
  ·
    refine ⟨167645592974428518599398673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111763728649619012399599115 167645592974428518599398673)
    ·
      refine ⟨125734194730821388949549005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167645592974428518599398673 125734194730821388949549005)
      ·
        refine ⟨47150323024058020856080877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125734194730821388949549005 47150323024058020856080877)
        ·
          refine ⟨17681371134021757821030329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47150323024058020856080877 17681371134021757821030329)
          ·
            refine ⟨13261028350516318365772747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681371134021757821030329 13261028350516318365772747)
            ·
              refine ⟨19891542525774477548659121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13261028350516318365772747 19891542525774477548659121)
              ·
                refine ⟨14918656894330858161494341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19891542525774477548659121 14918656894330858161494341)
                ·
                  refine ⟨2797248167687035905280189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14918656894330858161494341 2797248167687035905280189)
                  ·
                    refine ⟨1048968062882638464480071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797248167687035905280189 1048968062882638464480071)
                    ·
                      rfl

theorem cell22_3064287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_3064287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064287 prefixEnd_3064287 := by exact prefixLift 3064287
  have htrace : WordTrace (prefixWord ++ tailWord_3064287) baseStart_3064287 baseEnd_3064287 := by
    simpa [prefixWord, tailWord_3064287, baseEnd_3064287] using wordTrace_append hprefix tailTrace_3064287
  have hstable : (prefixWord ++ tailWord_3064287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064287).length < 2 ^ (prefixWord ++ tailWord_3064287).sum := by decide
  have hdescent : baseEnd_3064287 < baseStart_3064287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064302 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3064302 : Nat := 118140960795 + 3064302 * 2 ^ 59
def prefixEnd_3064302 : Nat := 4983230072969 + 3 ^ 40 * 3064302 * 2
def baseEnd_3064302 : Nat := 1048973197689183425355025

theorem tailTrace_3064302 : CollatzResearch.WordTrace tailWord_3064302 prefixEnd_3064302 1048973197689183425355025 := by
  unfold tailWord_3064302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970534468070583745174395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74509517163043113307596773 13970534468070583745174395)
  ·
    refine ⟨20955801702105875617761593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13970534468070583745174395 20955801702105875617761593)
    ·
      refine ⟨15716851276579406713321195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20955801702105875617761593 15716851276579406713321195)
      ·
        refine ⟨23575276914869110069981793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716851276579406713321195 23575276914869110069981793)
        ·
          refine ⟨17681457686151832552486345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23575276914869110069981793 17681457686151832552486345)
          ·
            refine ⟨13261093264613874414364759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681457686151832552486345 13261093264613874414364759)
            ·
              refine ⟨19891639896920811621547139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13261093264613874414364759 19891639896920811621547139)
              ·
                refine ⟨29837459845381217432320709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19891639896920811621547139 29837459845381217432320709)
                ·
                  refine ⟨5594523721008978268560133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29837459845381217432320709 5594523721008978268560133)
                  ·
                    refine ⟨1048973197689183425355025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594523721008978268560133 1048973197689183425355025)
                    ·
                      rfl

theorem cell22_3064302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3064302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064302 prefixEnd_3064302 := by exact prefixLift 3064302
  have htrace : WordTrace (prefixWord ++ tailWord_3064302) baseStart_3064302 baseEnd_3064302 := by
    simpa [prefixWord, tailWord_3064302, baseEnd_3064302] using wordTrace_append hprefix tailTrace_3064302
  have hstable : (prefixWord ++ tailWord_3064302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064302).length < 2 ^ (prefixWord ++ tailWord_3064302).sum := by decide
  have hdescent : baseEnd_3064302 < baseStart_3064302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064306 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3064306 : Nat := 118140960795 + 3064306 * 2 ^ 59
def prefixEnd_3064306 : Nat := 4983230072969 + 3 ^ 40 * 3064306 * 2
def baseEnd_3064306 : Nat := 349658188990309582751671

theorem tailTrace_3064306 : CollatzResearch.WordTrace tailWord_3064306 prefixEnd_3064306 349658188990309582751671 := by
  unfold tailWord_3064306
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941105409137544661135193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74509614424366785763027181 27941105409137544661135193)
  ·
    refine ⟨20955829056853158495851395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27941105409137544661135193 20955829056853158495851395)
    ·
      refine ⟨31433743585279737743777093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20955829056853158495851395 31433743585279737743777093)
      ·
        refine ⟨5893826922239950826958205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31433743585279737743777093 5893826922239950826958205)
        ·
          refine ⟨2210185095839981560109327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5893826922239950826958205 2210185095839981560109327)
          ·
            refine ⟨3315277643759972340163991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210185095839981560109327 3315277643759972340163991)
            ·
              refine ⟨4972916465639958510245987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315277643759972340163991 4972916465639958510245987)
              ·
                refine ⟨7459374698459937765368981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972916465639958510245987 7459374698459937765368981)
                ·
                  refine ⟨349658188990309582751671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7459374698459937765368981 349658188990309582751671)
                  ·
                    rfl

theorem cell22_3064306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3064306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064306 prefixEnd_3064306 := by exact prefixLift 3064306
  have htrace : WordTrace (prefixWord ++ tailWord_3064306) baseStart_3064306 baseEnd_3064306 := by
    simpa [prefixWord, tailWord_3064306, baseEnd_3064306] using wordTrace_append hprefix tailTrace_3064306
  have hstable : (prefixWord ++ tailWord_3064306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064306).length < 2 ^ (prefixWord ++ tailWord_3064306).sum := by decide
  have hdescent : baseEnd_3064306 < baseStart_3064306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064321 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3064321 : Nat := 118140960795 + 3064321 * 2 ^ 59
def prefixEnd_3064321 : Nat := 4983230072969 + 3 ^ 40 * 3064321 * 2
def baseEnd_3064321 : Nat := 1048979701777473709129967

theorem tailTrace_3064321 : CollatzResearch.WordTrace tailWord_3064321 prefixEnd_3064321 1048979701777473709129967 := by
  unfold tailWord_3064321
  simp only [CollatzResearch.WordTrace]
  refine ⟨111764968731495836206336817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74509979154330557470891211 111764968731495836206336817)
  ·
    refine ⟨83823726548621877154752613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111764968731495836206336817 83823726548621877154752613)
    ·
      refine ⟨15716948727866601966516115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83823726548621877154752613 15716948727866601966516115)
      ·
        refine ⟨23575423091799902949774173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716948727866601966516115 23575423091799902949774173)
        ·
          refine ⟨8840783659424963606165315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23575423091799902949774173 8840783659424963606165315)
          ·
            refine ⟨13261175489137445409247973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8840783659424963606165315 13261175489137445409247973)
            ·
              refine ⟨2486470404213271014233995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13261175489137445409247973 2486470404213271014233995)
              ·
                refine ⟨3729705606319906521350993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486470404213271014233995 3729705606319906521350993)
                ·
                  refine ⟨2797279204739929891013245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729705606319906521350993 2797279204739929891013245)
                  ·
                    refine ⟨1048979701777473709129967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797279204739929891013245 1048979701777473709129967)
                    ·
                      rfl

theorem cell22_3064321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3064321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064321 prefixEnd_3064321 := by exact prefixLift 3064321
  have htrace : WordTrace (prefixWord ++ tailWord_3064321) baseStart_3064321 baseEnd_3064321 := by
    simpa [prefixWord, tailWord_3064321, baseEnd_3064321] using wordTrace_append hprefix tailTrace_3064321
  have hstable : (prefixWord ++ tailWord_3064321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064321).length < 2 ^ (prefixWord ++ tailWord_3064321).sum := by decide
  have hdescent : baseEnd_3064321 < baseStart_3064321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064377 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_3064377 : Nat := 118140960795 + 3064377 * 2 ^ 59
def prefixEnd_3064377 : Nat := 4983230072969 + 3 ^ 40 * 3064377 * 2
def baseEnd_3064377 : Nat := 1048998871721908229729795

theorem tailTrace_3064377 : CollatzResearch.WordTrace tailWord_3064377 prefixEnd_3064377 1048998871721908229729795 := by
  unfold tailWord_3064377
  simp only [CollatzResearch.WordTrace]
  refine ⟨111767011219292957770375385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74511340812861971846916923 111767011219292957770375385)
  ·
    refine ⟨83825258414469718327781539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111767011219292957770375385 83825258414469718327781539)
    ·
      refine ⟨125737887621704577491672309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83825258414469718327781539 125737887621704577491672309)
      ·
        refine ⟨11787926964534804139844279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125737887621704577491672309 11787926964534804139844279)
        ·
          refine ⟨17681890446802206209766419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11787926964534804139844279 17681890446802206209766419)
          ·
            refine ⟨26522835670203309314649629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17681890446802206209766419 26522835670203309314649629)
            ·
              refine ⟨9946063376326240992993611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26522835670203309314649629 9946063376326240992993611)
              ·
                refine ⟨14919095064489361489490417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946063376326240992993611 14919095064489361489490417)
                ·
                  refine ⟨11189321298367021117117813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14919095064489361489490417 11189321298367021117117813)
                  ·
                    refine ⟨1048998871721908229729795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11189321298367021117117813 1048998871721908229729795)
                    ·
                      rfl

theorem cell22_3064377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_3064377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064377 prefixEnd_3064377 := by exact prefixLift 3064377
  have htrace : WordTrace (prefixWord ++ tailWord_3064377) baseStart_3064377 baseEnd_3064377 := by
    simpa [prefixWord, tailWord_3064377, baseEnd_3064377] using wordTrace_append hprefix tailTrace_3064377
  have hstable : (prefixWord ++ tailWord_3064377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064377).length < 2 ^ (prefixWord ++ tailWord_3064377).sum := by decide
  have hdescent : baseEnd_3064377 < baseStart_3064377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064439 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 2, 3]
def baseStart_3064439 : Nat := 118140960795 + 3064439 * 2 ^ 59
def prefixEnd_3064439 : Nat := 4983230072969 + 3 ^ 40 * 3064439 * 2
def baseEnd_3064439 : Nat := 1049020095588960734679605

theorem tailTrace_3064439 : CollatzResearch.WordTrace tailWord_3064439 prefixEnd_3064439 1049020095588960734679605 := by
  unfold tailWord_3064439
  simp only [CollatzResearch.WordTrace]
  refine ⟨111769272545068342359132371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74512848363378894906088247 111769272545068342359132371)
  ·
    refine ⟨167653908817602513538698557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111769272545068342359132371 167653908817602513538698557)
    ·
      refine ⟨62870215806600942577011959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167653908817602513538698557 62870215806600942577011959)
      ·
        refine ⟨94305323709901413865517939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62870215806600942577011959 94305323709901413865517939)
        ·
          refine ⟨141457985564852120798276909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94305323709901413865517939 141457985564852120798276909)
          ·
            refine ⟨53046744586819545299353841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141457985564852120798276909 53046744586819545299353841)
            ·
              refine ⟨39785058440114658974515381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53046744586819545299353841 39785058440114658974515381)
              ·
                refine ⟨3729849228760749278860817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39785058440114658974515381 3729849228760749278860817)
                ·
                  refine ⟨2797386921570561959145613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729849228760749278860817 2797386921570561959145613)
                  ·
                    refine ⟨1049020095588960734679605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797386921570561959145613 1049020095588960734679605)
                    ·
                      rfl

theorem cell22_3064439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_3064439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064439 prefixEnd_3064439 := by exact prefixLift 3064439
  have htrace : WordTrace (prefixWord ++ tailWord_3064439) baseStart_3064439 baseEnd_3064439 := by
    simpa [prefixWord, tailWord_3064439, baseEnd_3064439] using wordTrace_append hprefix tailTrace_3064439
  have hstable : (prefixWord ++ tailWord_3064439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064439).length < 2 ^ (prefixWord ++ tailWord_3064439).sum := by decide
  have hdescent : baseEnd_3064439 < baseStart_3064439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064458 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_3064458 : Nat := 118140960795 + 3064458 * 2 ^ 59
def prefixEnd_3064458 : Nat := 4983230072969 + 3 ^ 40 * 3064458 * 2
def baseEnd_3064458 : Nat := 349675533225750339484849

theorem tailTrace_3064458 : CollatzResearch.WordTrace tailWord_3064458 prefixEnd_3064458 349675533225750339484849 := by
  unfold tailWord_3064458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942491382999877151018507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74513310354666339069382685 27942491382999877151018507)
  ·
    refine ⟨41913737074499815726527761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27942491382999877151018507 41913737074499815726527761)
    ·
      refine ⟨31435302805874861794895821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41913737074499815726527761 31435302805874861794895821)
      ·
        refine ⟨11788238552203073173085933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31435302805874861794895821 11788238552203073173085933)
        ·
          refine ⟨4420589457076152439907225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11788238552203073173085933 4420589457076152439907225)
          ·
            refine ⟨3315442092807114329930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420589457076152439907225 3315442092807114329930419)
            ·
              refine ⟨4973163139210671494895629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315442092807114329930419 4973163139210671494895629)
              ·
                refine ⟨1864936177204001810585861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4973163139210671494895629 1864936177204001810585861)
                ·
                  refine ⟨349675533225750339484849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864936177204001810585861 349675533225750339484849)
                  ·
                    rfl

theorem cell22_3064458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_3064458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064458 prefixEnd_3064458 := by exact prefixLift 3064458
  have htrace : WordTrace (prefixWord ++ tailWord_3064458) baseStart_3064458 baseEnd_3064458 := by
    simpa [prefixWord, tailWord_3064458, baseEnd_3064458] using wordTrace_append hprefix tailTrace_3064458
  have hstable : (prefixWord ++ tailWord_3064458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064458).length < 2 ^ (prefixWord ++ tailWord_3064458).sum := by decide
  have hdescent : baseEnd_3064458 < baseStart_3064458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064490 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3064490 : Nat := 118140960795 + 3064490 * 2 ^ 59
def prefixEnd_3064490 : Nat := 4983230072969 + 3 ^ 40 * 3064490 * 2
def baseEnd_3064490 : Nat := 1049037553931213601654449

theorem tailTrace_3064490 : CollatzResearch.WordTrace tailWord_3064490 prefixEnd_3064490 1049037553931213601654449 := by
  unfold tailWord_3064490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942783166970894517309731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74514088445255718712825949 27942783166970894517309731)
  ·
    refine ⟨41914174750456341775964597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27942783166970894517309731 41914174750456341775964597)
    ·
      refine ⟨3929453882855282041496681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41914174750456341775964597 3929453882855282041496681)
      ·
        refine ⟨2947090412141461531122511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3929453882855282041496681 2947090412141461531122511)
        ·
          refine ⟨4420635618212192296683767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947090412141461531122511 4420635618212192296683767)
          ·
            refine ⟨6630953427318288445025651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420635618212192296683767 6630953427318288445025651)
            ·
              refine ⟨9946430140977432667538477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630953427318288445025651 9946430140977432667538477)
              ·
                refine ⟨3729911302866537250326929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9946430140977432667538477 3729911302866537250326929)
                ·
                  refine ⟨2797433477149902937745197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729911302866537250326929 2797433477149902937745197)
                  ·
                    refine ⟨1049037553931213601654449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797433477149902937745197 1049037553931213601654449)
                    ·
                      rfl

theorem cell22_3064490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3064490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064490 prefixEnd_3064490 := by exact prefixLift 3064490
  have htrace : WordTrace (prefixWord ++ tailWord_3064490) baseStart_3064490 baseEnd_3064490 := by
    simpa [prefixWord, tailWord_3064490, baseEnd_3064490] using wordTrace_append hprefix tailTrace_3064490
  have hstable : (prefixWord ++ tailWord_3064490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064490).length < 2 ^ (prefixWord ++ tailWord_3064490).sum := by decide
  have hdescent : baseEnd_3064490 < baseStart_3064490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064535 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 1, 3]
def baseStart_3064535 : Nat := 118140960795 + 3064535 * 2 ^ 59
def prefixEnd_3064535 : Nat := 4983230072969 + 3 ^ 40 * 3064535 * 2
def baseEnd_3064535 : Nat := 1049052958350848484279311

theorem tailTrace_3064535 : CollatzResearch.WordTrace tailWord_3064535 prefixEnd_3064535 1049052958350848484279311 := by
  unfold tailWord_3064535
  simp only [CollatzResearch.WordTrace]
  refine ⟨111772773952720550754627059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74515182635147033836418039 111772773952720550754627059)
  ·
    refine ⟨167659160929080826131940589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111772773952720550754627059 167659160929080826131940589)
    ·
      refine ⟨62872185348405309799477721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167659160929080826131940589 62872185348405309799477721)
      ·
        refine ⟨47154139011303982349608291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62872185348405309799477721 47154139011303982349608291)
        ·
          refine ⟨70731208516955973524412437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47154139011303982349608291 70731208516955973524412437)
          ·
            refine ⟨3315525399232311258956833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70731208516955973524412437 3315525399232311258956833)
            ·
              refine ⟨2486644049424233444217625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315525399232311258956833 2486644049424233444217625)
              ·
                refine ⟨1864983037068175083163219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486644049424233444217625 1864983037068175083163219)
                ·
                  refine ⟨2797474555602262624744829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864983037068175083163219 2797474555602262624744829)
                  ·
                    refine ⟨1049052958350848484279311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797474555602262624744829 1049052958350848484279311)
                    ·
                      rfl

theorem cell22_3064535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_3064535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064535 prefixEnd_3064535 := by exact prefixLift 3064535
  have htrace : WordTrace (prefixWord ++ tailWord_3064535) baseStart_3064535 baseEnd_3064535 := by
    simpa [prefixWord, tailWord_3064535, baseEnd_3064535] using wordTrace_append hprefix tailTrace_3064535
  have hstable : (prefixWord ++ tailWord_3064535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064535).length < 2 ^ (prefixWord ++ tailWord_3064535).sum := by decide
  have hdescent : baseEnd_3064535 < baseStart_3064535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064559 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 6]
def baseStart_3064559 : Nat := 118140960795 + 3064559 * 2 ^ 59
def prefixEnd_3064559 : Nat := 4983230072969 + 3 ^ 40 * 3064559 * 2
def baseEnd_3064559 : Nat := 349687058013773473893079

theorem tailTrace_3064559 : CollatzResearch.WordTrace tailWord_3064559 prefixEnd_3064559 349687058013773473893079 := by
  unfold tailWord_3064559
  simp only [CollatzResearch.WordTrace]
  refine ⟨111773649304633602853500731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74515766203089068569000487 111773649304633602853500731)
  ·
    refine ⟨167660473956950404280251097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111773649304633602853500731 167660473956950404280251097)
    ·
      refine ⟨125745355467712803210188323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167660473956950404280251097 125745355467712803210188323)
      ·
        refine ⟨188618033201569204815282485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125745355467712803210188323 188618033201569204815282485)
        ·
          refine ⟨17682940612647112951432733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188618033201569204815282485 17682940612647112951432733)
          ·
            refine ⟨6631102729742667356787275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17682940612647112951432733 6631102729742667356787275)
            ·
              refine ⟨9946654094614001035180913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631102729742667356787275 9946654094614001035180913)
              ·
                refine ⟨7459990570960500776385685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9946654094614001035180913 7459990570960500776385685)
                ·
                  refine ⟨349687058013773473893079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7459990570960500776385685 349687058013773473893079)
                  ·
                    rfl

theorem cell22_3064559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_3064559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064559 prefixEnd_3064559 := by exact prefixLift 3064559
  have htrace : WordTrace (prefixWord ++ tailWord_3064559) baseStart_3064559 baseEnd_3064559 := by
    simpa [prefixWord, tailWord_3064559, baseEnd_3064559] using wordTrace_append hprefix tailTrace_3064559
  have hstable : (prefixWord ++ tailWord_3064559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064559).length < 2 ^ (prefixWord ++ tailWord_3064559).sum := by decide
  have hdescent : baseEnd_3064559 < baseStart_3064559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064578 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3064578 : Nat := 118140960795 + 3064578 * 2 ^ 59
def prefixEnd_3064578 : Nat := 4983230072969 + 3 ^ 40 * 3064578 * 2
def baseEnd_3064578 : Nat := 1049067678129610705454179

theorem tailTrace_3064578 : CollatzResearch.WordTrace tailWord_3064578 prefixEnd_3064578 1049067678129610705454179 := by
  unfold tailWord_3064578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27943585572891192274610597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74516228194376512732294925 27943585572891192274610597)
  ·
    refine ⟨5239422294917098551489487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27943585572891192274610597 5239422294917098551489487)
    ·
      refine ⟨7859133442375647827234231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239422294917098551489487 7859133442375647827234231)
      ·
        refine ⟨11788700163563471740851347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859133442375647827234231 11788700163563471740851347)
        ·
          refine ⟨17683050245345207611277021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11788700163563471740851347 17683050245345207611277021)
          ·
            refine ⟨6631143842004452854228883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17683050245345207611277021 6631143842004452854228883)
            ·
              refine ⟨9946715763006679281343325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631143842004452854228883 9946715763006679281343325)
              ·
                refine ⟨3730018411127504730503747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9946715763006679281343325 3730018411127504730503747)
                ·
                  refine ⟨5595027616691257095755621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730018411127504730503747 5595027616691257095755621)
                  ·
                    refine ⟨1049067678129610705454179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5595027616691257095755621 1049067678129610705454179)
                    ·
                      rfl

theorem cell22_3064578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3064578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064578 prefixEnd_3064578 := by exact prefixLift 3064578
  have htrace : WordTrace (prefixWord ++ tailWord_3064578) baseStart_3064578 baseEnd_3064578 := by
    simpa [prefixWord, tailWord_3064578, baseEnd_3064578] using wordTrace_append hprefix tailTrace_3064578
  have hstable : (prefixWord ++ tailWord_3064578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064578).length < 2 ^ (prefixWord ++ tailWord_3064578).sum := by decide
  have hdescent : baseEnd_3064578 < baseStart_3064578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064638 : List Nat := [4, 2, 1, 2, 4, 1, 8]
def baseStart_3064638 : Nat := 118140960795 + 3064638 * 2 ^ 59
def prefixEnd_3064638 : Nat := 4983230072969 + 3 ^ 40 * 3064638 * 2
def baseEnd_3064638 : Nat := 38855119161325575887185

theorem tailTrace_3064638 : CollatzResearch.WordTrace tailWord_3064638 prefixEnd_3064638 38855119161325575887185 := by
  unfold tailWord_3064638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972066333918424918203321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74517687114231599563751045 13972066333918424918203321)
  ·
    refine ⟨10479049750438818688652491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13972066333918424918203321 10479049750438818688652491)
    ·
      refine ⟨15718574625658228032978737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479049750438818688652491 15718574625658228032978737)
      ·
        refine ⟨11788930969243671024734053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15718574625658228032978737 11788930969243671024734053)
        ·
          refine ⟨2210424556733188317137635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11788930969243671024734053 2210424556733188317137635)
          ·
            refine ⟨3315636835099782475706453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210424556733188317137635 3315636835099782475706453)
            ·
              refine ⟨38855119161325575887185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3315636835099782475706453 38855119161325575887185)
              ·
                rfl

theorem cell22_3064638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 8].length) (baseStart_3064638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064638 prefixEnd_3064638 := by exact prefixLift 3064638
  have htrace : WordTrace (prefixWord ++ tailWord_3064638) baseStart_3064638 baseEnd_3064638 := by
    simpa [prefixWord, tailWord_3064638, baseEnd_3064638] using wordTrace_append hprefix tailTrace_3064638
  have hstable : (prefixWord ++ tailWord_3064638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064638).length < 2 ^ (prefixWord ++ tailWord_3064638).sum := by decide
  have hdescent : baseEnd_3064638 < baseStart_3064638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064649 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 7]
def baseStart_3064649 : Nat := 118140960795 + 3064649 * 2 ^ 59
def prefixEnd_3064649 : Nat := 4983230072969 + 3 ^ 40 * 3064649 * 2
def baseEnd_3064649 : Nat := 349697327626863395642987

theorem tailTrace_3064649 : CollatzResearch.WordTrace tailWord_3064649 prefixEnd_3064649 349697327626863395642987 := by
  unfold tailWord_3064649
  simp only [CollatzResearch.WordTrace]
  refine ⟨111776931874307548224277001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74517954582871698816184667 111776931874307548224277001)
  ·
    refine ⟨83832698905730661168207751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111776931874307548224277001 83832698905730661168207751)
    ·
      refine ⟨125749048358595991752311627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83832698905730661168207751 125749048358595991752311627)
      ·
        refine ⟨188623572537893987628467441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125749048358595991752311627 188623572537893987628467441)
        ·
          refine ⟨141467679403420490721350581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188623572537893987628467441 141467679403420490721350581)
          ·
            refine ⟨13262594944070671005126617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141467679403420490721350581 13262594944070671005126617)
            ·
              refine ⟨9946946208053003253844963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13262594944070671005126617 9946946208053003253844963)
              ·
                refine ⟨14920419312079504880767445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946946208053003253844963 14920419312079504880767445)
                ·
                  refine ⟨349697327626863395642987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14920419312079504880767445 349697327626863395642987)
                  ·
                    rfl

theorem cell22_3064649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_3064649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064649 prefixEnd_3064649 := by exact prefixLift 3064649
  have htrace : WordTrace (prefixWord ++ tailWord_3064649) baseStart_3064649 baseEnd_3064649 := by
    simpa [prefixWord, tailWord_3064649, baseEnd_3064649] using wordTrace_append hprefix tailTrace_3064649
  have hstable : (prefixWord ++ tailWord_3064649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064649).length < 2 ^ (prefixWord ++ tailWord_3064649).sum := by decide
  have hdescent : baseEnd_3064649 < baseStart_3064649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064664 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3064664 : Nat := 118140960795 + 3064664 * 2 ^ 59
def prefixEnd_3064664 : Nat := 4983230072969 + 3 ^ 40 * 3064664 * 2
def baseEnd_3064664 : Nat := 1049097117687135147803915

theorem tailTrace_3064664 : CollatzResearch.WordTrace tailWord_3064664 prefixEnd_3064664 1049097117687135147803915 := by
  unfold tailWord_3064664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55888739484626602893036523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74518319312835470524048697 55888739484626602893036523)
  ·
    refine ⟨83833109226939904339554785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55888739484626602893036523 83833109226939904339554785)
    ·
      refine ⟨62874831920204928254666089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83833109226939904339554785 62874831920204928254666089)
      ·
        refine ⟨47156123940153696190999567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62874831920204928254666089 47156123940153696190999567)
        ·
          refine ⟨70734185910230544286499351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47156123940153696190999567 70734185910230544286499351)
          ·
            refine ⟨106101278865345816429749027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70734185910230544286499351 106101278865345816429749027)
            ·
              refine ⟨159151918298018724644623541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106101278865345816429749027 159151918298018724644623541)
              ·
                refine ⟨14920492340439255435433457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159151918298018724644623541 14920492340439255435433457)
                ·
                  refine ⟨11190369255329441576575093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14920492340439255435433457 11190369255329441576575093)
                  ·
                    refine ⟨1049097117687135147803915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11190369255329441576575093 1049097117687135147803915)
                    ·
                      rfl

theorem cell22_3064664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3064664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064664 prefixEnd_3064664 := by exact prefixLift 3064664
  have htrace : WordTrace (prefixWord ++ tailWord_3064664) baseStart_3064664 baseEnd_3064664 := by
    simpa [prefixWord, tailWord_3064664, baseEnd_3064664] using wordTrace_append hprefix tailTrace_3064664
  have hstable : (prefixWord ++ tailWord_3064664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064664).length < 2 ^ (prefixWord ++ tailWord_3064664).sum := by decide
  have hdescent : baseEnd_3064664 < baseStart_3064664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064666 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_3064666 : Nat := 118140960795 + 3064666 * 2 ^ 59
def prefixEnd_3064666 : Nat := 4983230072969 + 3 ^ 40 * 3064666 * 2
def baseEnd_3064666 : Nat := 349699267442669269751303

theorem tailTrace_3064666 : CollatzResearch.WordTrace tailWord_3064666 prefixEnd_3064666 349699267442669269751303 := by
  unfold tailWord_3064666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27944387978811490031911463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74518367943497306751763901 27944387978811490031911463)
  ·
    refine ⟨41916581968217235047867195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27944387978811490031911463 41916581968217235047867195)
    ·
      refine ⟨62874872952325852571800793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41916581968217235047867195 62874872952325852571800793)
      ·
        refine ⟨47156154714244389428850595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62874872952325852571800793 47156154714244389428850595)
        ·
          refine ⟨70734232071366584143275893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47156154714244389428850595 70734232071366584143275893)
          ·
            refine ⟨6631334256690617263432115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70734232071366584143275893 6631334256690617263432115)
            ·
              refine ⟨9947001385035925895148173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631334256690617263432115 9947001385035925895148173)
              ·
                refine ⟨3730125519388472210680565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9947001385035925895148173 3730125519388472210680565)
                ·
                  refine ⟨349699267442669269751303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730125519388472210680565 349699267442669269751303)
                  ·
                    rfl

theorem cell22_3064666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_3064666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064666 prefixEnd_3064666 := by exact prefixLift 3064666
  have htrace : WordTrace (prefixWord ++ tailWord_3064666) baseStart_3064666 baseEnd_3064666 := by
    simpa [prefixWord, tailWord_3064666, baseEnd_3064666] using wordTrace_append hprefix tailTrace_3064666
  have hstable : (prefixWord ++ tailWord_3064666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064666).length < 2 ^ (prefixWord ++ tailWord_3064666).sum := by decide
  have hdescent : baseEnd_3064666 < baseStart_3064666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064739 : List Nat := [1, 1, 1, 4, 1, 2, 2, 10]
def baseStart_3064739 : Nat := 118140960795 + 3064739 * 2 ^ 59
def prefixEnd_3064739 : Nat := 4983230072969 + 3 ^ 40 * 3064739 * 2
def baseEnd_3064739 : Nat := 116569199079984439130965

theorem tailTrace_3064739 : CollatzResearch.WordTrace tailWord_3064739 prefixEnd_3064739 116569199079984439130965 := by
  unfold tailWord_3064739
  simp only [CollatzResearch.WordTrace]
  refine ⟨111780214443981493595053271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74520142962654329063368847 111780214443981493595053271)
  ·
    refine ⟨167670321665972240392579907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111780214443981493595053271 167670321665972240392579907)
    ·
      refine ⟨251505482498958360588869861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167670321665972240392579907 251505482498958360588869861)
      ·
        refine ⟨47157277968554692610413099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251505482498958360588869861 47157277968554692610413099)
        ·
          refine ⟨70735916952832038915619649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47157277968554692610413099 70735916952832038915619649)
          ·
            refine ⟨53051937714624029186714737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70735916952832038915619649 53051937714624029186714737)
            ·
              refine ⟨39788953285968021890036053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53051937714624029186714737 39788953285968021890036053)
              ·
                refine ⟨116569199079984439130965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39788953285968021890036053 116569199079984439130965)
                ·
                  rfl

theorem cell22_3064739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 10].length) (baseStart_3064739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064739 prefixEnd_3064739 := by exact prefixLift 3064739
  have htrace : WordTrace (prefixWord ++ tailWord_3064739) baseStart_3064739 baseEnd_3064739 := by
    simpa [prefixWord, tailWord_3064739, baseEnd_3064739] using wordTrace_append hprefix tailTrace_3064739
  have hstable : (prefixWord ++ tailWord_3064739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064739).length < 2 ^ (prefixWord ++ tailWord_3064739).sum := by decide
  have hdescent : baseEnd_3064739 < baseStart_3064739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064760 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_3064760 : Nat := 118140960795 + 3064760 * 2 ^ 59
def prefixEnd_3064760 : Nat := 4983230072969 + 3 ^ 40 * 3064760 * 2
def baseEnd_3064760 : Nat := 1049129980449022897403621

theorem tailTrace_3064760 : CollatzResearch.WordTrace tailWord_3064760 prefixEnd_3064760 1049129980449022897403621 := by
  unfold tailWord_3064760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55890490188452707090783867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74520653584603609454378489 55890490188452707090783867)
  ·
    refine ⟨83835735282679060636175801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55890490188452707090783867 83835735282679060636175801)
    ·
      refine ⟨62876801462009295477131851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83835735282679060636175801 62876801462009295477131851)
      ·
        refine ⟨94315202193013943215697777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62876801462009295477131851 94315202193013943215697777)
        ·
          refine ⟨70736401644760457411773333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94315202193013943215697777 70736401644760457411773333)
          ·
            refine ⟨3315768827098146441176875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70736401644760457411773333 3315768827098146441176875)
            ·
              refine ⟨4973653240647219661765313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315768827098146441176875 4973653240647219661765313)
              ·
                refine ⟨3730239930485414746323985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4973653240647219661765313 3730239930485414746323985)
                ·
                  refine ⟨2797679947864061059742989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730239930485414746323985 2797679947864061059742989)
                  ·
                    refine ⟨1049129980449022897403621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797679947864061059742989 1049129980449022897403621)
                    ·
                      rfl

theorem cell22_3064760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_3064760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064760 prefixEnd_3064760 := by exact prefixLift 3064760
  have htrace : WordTrace (prefixWord ++ tailWord_3064760) baseStart_3064760 baseEnd_3064760 := by
    simpa [prefixWord, tailWord_3064760, baseEnd_3064760] using wordTrace_append hprefix tailTrace_3064760
  have hstable : (prefixWord ++ tailWord_3064760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064760).length < 2 ^ (prefixWord ++ tailWord_3064760).sum := by decide
  have hdescent : baseEnd_3064760 < baseStart_3064760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064771 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 7, 3]
def baseStart_3064771 : Nat := 118140960795 + 3064771 * 2 ^ 59
def prefixEnd_3064771 : Nat := 4983230072969 + 3 ^ 40 * 3064771 * 2
def baseEnd_3064771 : Nat := 1049133745973822535378587

theorem tailTrace_3064771 : CollatzResearch.WordTrace tailWord_3064771 prefixEnd_3064771 1049133745973822535378587 := by
  unfold tailWord_3064771
  simp only [CollatzResearch.WordTrace]
  refine ⟨111781381579865563060218167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74520921053243708706812111 111781381579865563060218167)
  ·
    refine ⟨167672072369798344590327251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111781381579865563060218167 167672072369798344590327251)
    ·
      refine ⟨251508108554697516885490877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167672072369798344590327251 251508108554697516885490877)
      ·
        refine ⟨94315540708011568832059079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251508108554697516885490877 94315540708011568832059079)
        ·
          refine ⟨141473311062017353248088619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94315540708011568832059079 141473311062017353248088619)
          ·
            refine ⟨212209966593026029872132929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141473311062017353248088619 212209966593026029872132929)
            ·
              refine ⟨159157474944769522404099697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212209966593026029872132929 159157474944769522404099697)
              ·
                refine ⟨119368106208577141803074773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159157474944769522404099697 119368106208577141803074773)
                ·
                  refine ⟨2797689989263526761009565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119368106208577141803074773 2797689989263526761009565)
                  ·
                    refine ⟨1049133745973822535378587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797689989263526761009565 1049133745973822535378587)
                    ·
                      rfl

theorem cell22_3064771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3].length) (baseStart_3064771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064771 prefixEnd_3064771 := by exact prefixLift 3064771
  have htrace : WordTrace (prefixWord ++ tailWord_3064771) baseStart_3064771 baseEnd_3064771 := by
    simpa [prefixWord, tailWord_3064771, baseEnd_3064771] using wordTrace_append hprefix tailTrace_3064771
  have hstable : (prefixWord ++ tailWord_3064771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064771).length < 2 ^ (prefixWord ++ tailWord_3064771).sum := by decide
  have hdescent : baseEnd_3064771 < baseStart_3064771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064790 : List Nat := [5, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3064790 : Nat := 118140960795 + 3064790 * 2 ^ 59
def prefixEnd_3064790 : Nat := 4983230072969 + 3 ^ 40 * 3064790 * 2
def baseEnd_3064790 : Nat := 116571138895790313239281

theorem tailTrace_3064790 : CollatzResearch.WordTrace tailWord_3064790 prefixEnd_3064790 116571138895790313239281 := by
  unfold tailWord_3064790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986379660424795581572489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74521383044531152870106549 6986379660424795581572489)
  ·
    refine ⟨5239784745318596686179367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6986379660424795581572489 5239784745318596686179367)
    ·
      refine ⟨7859677117977895029269051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239784745318596686179367 7859677117977895029269051)
      ·
        refine ⟨11789515676966842543903577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859677117977895029269051 11789515676966842543903577)
        ·
          refine ⟨8842136757725131907927683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11789515676966842543903577 8842136757725131907927683)
          ·
            refine ⟨13263205136587697861891525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842136757725131907927683 13263205136587697861891525)
            ·
              refine ⟨2486850963110193349104661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13263205136587697861891525 2486850963110193349104661)
              ·
                refine ⟨116571138895790313239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2486850963110193349104661 116571138895790313239281)
                ·
                  rfl

theorem cell22_3064790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3064790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064790 prefixEnd_3064790 := by exact prefixLift 3064790
  have htrace : WordTrace (prefixWord ++ tailWord_3064790) baseStart_3064790 baseEnd_3064790 := by
    simpa [prefixWord, tailWord_3064790, baseEnd_3064790] using wordTrace_append hprefix tailTrace_3064790
  have hstable : (prefixWord ++ tailWord_3064790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064790).length < 2 ^ (prefixWord ++ tailWord_3064790).sum := by decide
  have hdescent : baseEnd_3064790 < baseStart_3064790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064822 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3064822 : Nat := 118140960795 + 3064822 * 2 ^ 59
def prefixEnd_3064822 : Nat := 4983230072969 + 3 ^ 40 * 3064822 * 2
def baseEnd_3064822 : Nat := 1049151204316075402353431

theorem tailTrace_3064822 : CollatzResearch.WordTrace tailWord_3064822 prefixEnd_3064822 1049151204316075402353431 := by
  unfold tailWord_3064822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986452606417549923145295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74522161135120532513549813 6986452606417549923145295)
  ·
    refine ⟨10479678909626324884717943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986452606417549923145295 10479678909626324884717943)
    ·
      refine ⟨15719518364439487327076915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479678909626324884717943 15719518364439487327076915)
      ·
        refine ⟨23579277546659230990615373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15719518364439487327076915 23579277546659230990615373)
        ·
          refine ⟨8842229079997211621480765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23579277546659230990615373 8842229079997211621480765)
          ·
            refine ⟨3315835904998954358055287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8842229079997211621480765 3315835904998954358055287)
            ·
              refine ⟨4973753857498431537082931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315835904998954358055287 4973753857498431537082931)
              ·
                refine ⟨7460630786247647305624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973753857498431537082931 7460630786247647305624397)
                ·
                  refine ⟨2797736544842867739609149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7460630786247647305624397 2797736544842867739609149)
                  ·
                    refine ⟨1049151204316075402353431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797736544842867739609149 1049151204316075402353431)
                    ·
                      rfl

theorem cell22_3064822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3064822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064822 prefixEnd_3064822 := by exact prefixLift 3064822
  have htrace : WordTrace (prefixWord ++ tailWord_3064822) baseStart_3064822 baseEnd_3064822 := by
    simpa [prefixWord, tailWord_3064822, baseEnd_3064822] using wordTrace_append hprefix tailTrace_3064822
  have hstable : (prefixWord ++ tailWord_3064822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064822).length < 2 ^ (prefixWord ++ tailWord_3064822).sum := by decide
  have hdescent : baseEnd_3064822 < baseStart_3064822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064878 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3064878 : Nat := 118140960795 + 3064878 * 2 ^ 59
def prefixEnd_3064878 : Nat := 4983230072969 + 3 ^ 40 * 3064878 * 2
def baseEnd_3064878 : Nat := 1049170374260509922953259

theorem tailTrace_3064878 : CollatzResearch.WordTrace tailWord_3064878 prefixEnd_3064878 1049170374260509922953259 := by
  unfold tailWord_3064878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973160523809740041795411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74523522793651946889575525 13973160523809740041795411)
  ·
    refine ⟨20959740785714610062693117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973160523809740041795411 20959740785714610062693117)
    ·
      refine ⟨7859902794642978773509919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20959740785714610062693117 7859902794642978773509919)
      ·
        refine ⟨11789854191964468160264879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859902794642978773509919 11789854191964468160264879)
        ·
          refine ⟨17684781287946702240397319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11789854191964468160264879 17684781287946702240397319)
          ·
            refine ⟨26527171931920053360595979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17684781287946702240397319 26527171931920053360595979)
            ·
              refine ⟨39790757897880080040893969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26527171931920053360595979 39790757897880080040893969)
              ·
                refine ⟨29843068423410060030670477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39790757897880080040893969 29843068423410060030670477)
                ·
                  refine ⟨11191150658778772511501429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29843068423410060030670477 11191150658778772511501429)
                  ·
                    refine ⟨1049170374260509922953259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11191150658778772511501429 1049170374260509922953259)
                    ·
                      rfl

theorem cell22_3064878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3064878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064878 prefixEnd_3064878 := by exact prefixLift 3064878
  have htrace : WordTrace (prefixWord ++ tailWord_3064878) baseStart_3064878 baseEnd_3064878 := by
    simpa [prefixWord, tailWord_3064878, baseEnd_3064878] using wordTrace_append hprefix tailTrace_3064878
  have hstable : (prefixWord ++ tailWord_3064878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064878).length < 2 ^ (prefixWord ++ tailWord_3064878).sum := by decide
  have hdescent : baseEnd_3064878 < baseStart_3064878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064921 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_3064921 : Nat := 118140960795 + 3064921 * 2 ^ 59
def prefixEnd_3064921 : Nat := 4983230072969 + 3 ^ 40 * 3064921 * 2
def baseEnd_3064921 : Nat := 1049185094039272144128127

theorem tailTrace_3064921 : CollatzResearch.WordTrace tailWord_3064921 prefixEnd_3064921 1049185094039272144128127 := by
  unfold tailWord_3064921
  simp only [CollatzResearch.WordTrace]
  refine ⟨111786852529322138678178617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74524568352881425785452411 111786852529322138678178617)
  ·
    refine ⟨83840139396991604008633963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111786852529322138678178617 83840139396991604008633963)
    ·
      refine ⟨125760209095487406012950945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83840139396991604008633963 125760209095487406012950945)
      ·
        refine ⟨94320156821615554509713209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125760209095487406012950945 94320156821615554509713209)
        ·
          refine ⟨70740117616211665882284907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94320156821615554509713209 70740117616211665882284907)
          ·
            refine ⟨106110176424317498823427361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70740117616211665882284907 106110176424317498823427361)
            ·
              refine ⟨79582632318238124117570521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106110176424317498823427361 79582632318238124117570521)
              ·
                refine ⟨59686974238678593088177891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79582632318238124117570521 59686974238678593088177891)
                ·
                  refine ⟨89530461358017889632266837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59686974238678593088177891 89530461358017889632266837)
                  ·
                    refine ⟨1049185094039272144128127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89530461358017889632266837 1049185094039272144128127)
                    ·
                      rfl

theorem cell22_3064921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_3064921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064921 prefixEnd_3064921 := by exact prefixLift 3064921
  have htrace : WordTrace (prefixWord ++ tailWord_3064921) baseStart_3064921 baseEnd_3064921 := by
    simpa [prefixWord, tailWord_3064921, baseEnd_3064921] using wordTrace_append hprefix tailTrace_3064921
  have hstable : (prefixWord ++ tailWord_3064921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064921).length < 2 ^ (prefixWord ++ tailWord_3064921).sum := by decide
  have hdescent : baseEnd_3064921 < baseStart_3064921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064925 : List Nat := [1, 4, 4, 1, 2, 1, 9]
def baseStart_3064925 : Nat := 118140960795 + 3064925 * 2 ^ 59
def prefixEnd_3064925 : Nat := 4983230072969 + 3 ^ 40 * 3064925 * 2
def baseEnd_3064925 : Nat := 38858757900778424704745

theorem tailTrace_3064925 : CollatzResearch.WordTrace tailWord_3064925 prefixEnd_3064925 38858757900778424704745 := by
  unfold tailWord_3064925
  simp only [CollatzResearch.WordTrace]
  refine ⟨111786998421307647361324229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74524665614205098240882819 111786998421307647361324229)
  ·
    refine ⟨20960062203995183880248293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111786998421307647361324229 20960062203995183880248293)
    ·
      refine ⟨3930011663249096977546555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20960062203995183880248293 3930011663249096977546555)
      ·
        refine ⟨5895017494873645466319833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930011663249096977546555 5895017494873645466319833)
        ·
          refine ⟨4421263121155234099739875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5895017494873645466319833 4421263121155234099739875)
          ·
            refine ⟨6631894681732851149609813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421263121155234099739875 6631894681732851149609813)
            ·
              refine ⟨38858757900778424704745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6631894681732851149609813 38858757900778424704745)
              ·
                rfl

theorem cell22_3064925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 9].length) (baseStart_3064925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064925 prefixEnd_3064925 := by exact prefixLift 3064925
  have htrace : WordTrace (prefixWord ++ tailWord_3064925) baseStart_3064925 baseEnd_3064925 := by
    simpa [prefixWord, tailWord_3064925, baseEnd_3064925] using wordTrace_append hprefix tailTrace_3064925
  have hstable : (prefixWord ++ tailWord_3064925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064925).length < 2 ^ (prefixWord ++ tailWord_3064925).sum := by decide
  have hdescent : baseEnd_3064925 < baseStart_3064925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064940 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_3064940 : Nat := 118140960795 + 3064940 * 2 ^ 59
def prefixEnd_3064940 : Nat := 4983230072969 + 3 ^ 40 * 3064940 * 2
def baseEnd_3064940 : Nat := 1049191598127562427903069

theorem tailTrace_3064940 : CollatzResearch.WordTrace tailWord_3064940 prefixEnd_3064940 1049191598127562427903069 := by
  unfold tailWord_3064940
  simp only [CollatzResearch.WordTrace]
  refine ⟨55893772758126652461560137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74525030344168869948746849 55893772758126652461560137)
  ·
    refine ⟨41920329568594989346170103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55893772758126652461560137 41920329568594989346170103)
    ·
      refine ⟨62880494352892484019255155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41920329568594989346170103 62880494352892484019255155)
      ·
        refine ⟨94320741529338726028882733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62880494352892484019255155 94320741529338726028882733)
        ·
          refine ⟨35370278073502022260831025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94320741529338726028882733 35370278073502022260831025)
          ·
            refine ⟨26527708555126516695623269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35370278073502022260831025 26527708555126516695623269)
            ·
              refine ⟨4973945354086221880429363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26527708555126516695623269 4973945354086221880429363)
              ·
                refine ⟨7460918031129332820644045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973945354086221880429363 7460918031129332820644045)
                ·
                  refine ⟨2797844261673499807741517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7460918031129332820644045 2797844261673499807741517)
                  ·
                    refine ⟨1049191598127562427903069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797844261673499807741517 1049191598127562427903069)
                    ·
                      rfl

theorem cell22_3064940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_3064940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064940 prefixEnd_3064940 := by exact prefixLift 3064940
  have htrace : WordTrace (prefixWord ++ tailWord_3064940) baseStart_3064940 baseEnd_3064940 := by
    simpa [prefixWord, tailWord_3064940, baseEnd_3064940] using wordTrace_append hprefix tailTrace_3064940
  have hstable : (prefixWord ++ tailWord_3064940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064940).length < 2 ^ (prefixWord ++ tailWord_3064940).sum := by decide
  have hdescent : baseEnd_3064940 < baseStart_3064940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064974 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_3064974 : Nat := 118140960795 + 3064974 * 2 ^ 59
def prefixEnd_3064974 : Nat := 4983230072969 + 3 ^ 40 * 3064974 * 2
def baseEnd_3064974 : Nat := 1049203237022397672552965

theorem tailTrace_3064974 : CollatzResearch.WordTrace tailWord_3064974 prefixEnd_3064974 1049203237022397672552965 := by
  unfold tailWord_3064974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973598199766266091232247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74525857065420085819905317 13973598199766266091232247)
  ·
    refine ⟨20960397299649399136848371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973598199766266091232247 20960397299649399136848371)
    ·
      refine ⟨31440595949474098705272557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20960397299649399136848371 31440595949474098705272557)
      ·
        refine ⟨11790223481052787014477209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31440595949474098705272557 11790223481052787014477209)
        ·
          refine ⟨8842667610789590260857907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11790223481052787014477209 8842667610789590260857907)
          ·
            refine ⟨13264001416184385391286861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842667610789590260857907 13264001416184385391286861)
            ·
              refine ⟨4974000531069144521732573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13264001416184385391286861 4974000531069144521732573)
              ·
                refine ⟨1865250199150929195649715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4974000531069144521732573 1865250199150929195649715)
                ·
                  refine ⟨2797875298726393793474573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865250199150929195649715 2797875298726393793474573)
                  ·
                    refine ⟨1049203237022397672552965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797875298726393793474573 1049203237022397672552965)
                    ·
                      rfl

theorem cell22_3064974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_3064974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064974 prefixEnd_3064974 := by exact prefixLift 3064974
  have htrace : WordTrace (prefixWord ++ tailWord_3064974) baseStart_3064974 baseEnd_3064974 := by
    simpa [prefixWord, tailWord_3064974, baseEnd_3064974] using wordTrace_append hprefix tailTrace_3064974
  have hstable : (prefixWord ++ tailWord_3064974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064974).length < 2 ^ (prefixWord ++ tailWord_3064974).sum := by decide
  have hdescent : baseEnd_3064974 < baseStart_3064974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064991 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 1, 3]
def baseStart_3064991 : Nat := 118140960795 + 3064991 * 2 ^ 59
def prefixEnd_3064991 : Nat := 4983230072969 + 3 ^ 40 * 3064991 * 2
def baseEnd_3064991 : Nat := 1049209056469815294877913

theorem tailTrace_3064991 : CollatzResearch.WordTrace tailWord_3064991 prefixEnd_3064991 1049209056469815294877913 := by
  unfold tailWord_3064991
  simp only [CollatzResearch.WordTrace]
  refine ⟨111789405639068540633226827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74526270426045693755484551 111789405639068540633226827)
  ·
    refine ⟨167684108458602810949840241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111789405639068540633226827 167684108458602810949840241)
    ·
      refine ⟨125763081343952108212380181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167684108458602810949840241 125763081343952108212380181)
      ·
        refine ⟨5895144437997755072455321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125763081343952108212380181 5895144437997755072455321)
        ·
          refine ⟨4421358328498316304341491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5895144437997755072455321 4421358328498316304341491)
          ·
            refine ⟨6632037492747474456512237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421358328498316304341491 6632037492747474456512237)
            ·
              refine ⟨2487014059780302921192089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632037492747474456512237 2487014059780302921192089)
              ·
                refine ⟨1865260544835227190894067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487014059780302921192089 1865260544835227190894067)
                ·
                  refine ⟨2797890817252840786341101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865260544835227190894067 2797890817252840786341101)
                  ·
                    refine ⟨1049209056469815294877913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797890817252840786341101 1049209056469815294877913)
                    ·
                      rfl

theorem cell22_3064991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_3064991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3064991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3064991 prefixEnd_3064991 := by exact prefixLift 3064991
  have htrace : WordTrace (prefixWord ++ tailWord_3064991) baseStart_3064991 baseEnd_3064991 := by
    simpa [prefixWord, tailWord_3064991, baseEnd_3064991] using wordTrace_append hprefix tailTrace_3064991
  have hstable : (prefixWord ++ tailWord_3064991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064991).length < 2 ^ (prefixWord ++ tailWord_3064991).sum := by decide
  have hdescent : baseEnd_3064991 < baseStart_3064991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065017 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_3065017 : Nat := 118140960795 + 3065017 * 2 ^ 59
def prefixEnd_3065017 : Nat := 4983230072969 + 3 ^ 40 * 3065017 * 2
def baseEnd_3065017 : Nat := 1049217956801159893727833

theorem tailTrace_3065017 : CollatzResearch.WordTrace tailWord_3065017 prefixEnd_3065017 1049217956801159893727833 := by
  unfold tailWord_3065017
  simp only [CollatzResearch.WordTrace]
  refine ⟨111790353936974347073673305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74526902624649564715782203 111790353936974347073673305)
  ·
    refine ⟨83842765452730760305254979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111790353936974347073673305 83842765452730760305254979)
    ·
      refine ⟨125764148179096140457882469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83842765452730760305254979 125764148179096140457882469)
      ·
        refine ⟨23580777783580526335852963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125764148179096140457882469 23580777783580526335852963)
        ·
          refine ⟨35371166675370789503779445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23580777783580526335852963 35371166675370789503779445)
          ·
            refine ⟨3316046875816011515979323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35371166675370789503779445 3316046875816011515979323)
            ·
              refine ⟨4974070313724017273968985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316046875816011515979323 4974070313724017273968985)
              ·
                refine ⟨3730552735293012955476739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974070313724017273968985 3730552735293012955476739)
                ·
                  refine ⟨5595829102939519433215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730552735293012955476739 5595829102939519433215109)
                  ·
                    refine ⟨1049217956801159893727833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5595829102939519433215109 1049217956801159893727833)
                    ·
                      rfl

theorem cell22_3065017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_3065017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065017 prefixEnd_3065017 := by exact prefixLift 3065017
  have htrace : WordTrace (prefixWord ++ tailWord_3065017) baseStart_3065017 baseEnd_3065017 := by
    simpa [prefixWord, tailWord_3065017, baseEnd_3065017] using wordTrace_append hprefix tailTrace_3065017
  have hstable : (prefixWord ++ tailWord_3065017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065017).length < 2 ^ (prefixWord ++ tailWord_3065017).sum := by decide
  have hdescent : baseEnd_3065017 < baseStart_3065017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065073 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3065073 : Nat := 118140960795 + 3065073 * 2 ^ 59
def prefixEnd_3065073 : Nat := 4983230072969 + 3 ^ 40 * 3065073 * 2
def baseEnd_3065073 : Nat := 1049237126745594414327661

theorem tailTrace_3065073 : CollatzResearch.WordTrace tailWord_3065073 prefixEnd_3065073 1049237126745594414327661 := by
  unfold tailWord_3065073
  simp only [CollatzResearch.WordTrace]
  refine ⟨111792396424771468637711873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74528264283180979091807915 111792396424771468637711873)
  ·
    refine ⟨83844297318578601478283905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111792396424771468637711873 83844297318578601478283905)
    ·
      refine ⟨62883222988933951108712929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83844297318578601478283905 62883222988933951108712929)
      ·
        refine ⟨47162417241700463331534697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62883222988933951108712929 47162417241700463331534697)
        ·
          refine ⟨35371812931275347498651023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47162417241700463331534697 35371812931275347498651023)
          ·
            refine ⟨53057719396913021247976535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35371812931275347498651023 53057719396913021247976535)
            ·
              refine ⟨79586579095369531871964803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53057719396913021247976535 79586579095369531871964803)
              ·
                refine ⟨119379868643054297807947205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79586579095369531871964803 119379868643054297807947205)
                ·
                  refine ⟨22383725370572680838990101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119379868643054297807947205 22383725370572680838990101)
                  ·
                    refine ⟨1049237126745594414327661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22383725370572680838990101 1049237126745594414327661)
                    ·
                      rfl

theorem cell22_3065073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3065073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065073 prefixEnd_3065073 := by exact prefixLift 3065073
  have htrace : WordTrace (prefixWord ++ tailWord_3065073) baseStart_3065073 baseEnd_3065073 := by
    simpa [prefixWord, tailWord_3065073, baseEnd_3065073] using wordTrace_append hprefix tailTrace_3065073
  have hstable : (prefixWord ++ tailWord_3065073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065073).length < 2 ^ (prefixWord ++ tailWord_3065073).sum := by decide
  have hdescent : baseEnd_3065073 < baseStart_3065073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065075 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 5, 3]
def baseStart_3065075 : Nat := 118140960795 + 3065075 * 2 ^ 59
def prefixEnd_3065075 : Nat := 4983230072969 + 3 ^ 40 * 3065075 * 2
def baseEnd_3065075 : Nat := 1049237811386467075777655

theorem tailTrace_3065075 : CollatzResearch.WordTrace tailWord_3065075 prefixEnd_3065075 1049237811386467075777655 := by
  unfold tailWord_3065075
  simp only [CollatzResearch.WordTrace]
  refine ⟨111792469370764222979284679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74528312913842815319523119 111792469370764222979284679)
  ·
    refine ⟨167688704056146334468927019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111792469370764222979284679 167688704056146334468927019)
    ·
      refine ⟨251533056084219501703390529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167688704056146334468927019 251533056084219501703390529)
      ·
        refine ⟨188649792063164626277542897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251533056084219501703390529 188649792063164626277542897)
        ·
          refine ⟨141487344047373469708157173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188649792063164626277542897 141487344047373469708157173)
          ·
            refine ⟨13264438504441262785139735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141487344047373469708157173 13264438504441262785139735)
            ·
              refine ⟨19896657756661894177709603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264438504441262785139735 19896657756661894177709603)
              ·
                refine ⟨29844986634992841266564405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19896657756661894177709603 29844986634992841266564405)
                ·
                  refine ⟨2797967497030578868740413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29844986634992841266564405 2797967497030578868740413)
                  ·
                    refine ⟨1049237811386467075777655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797967497030578868740413 1049237811386467075777655)
                    ·
                      rfl

theorem cell22_3065075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3].length) (baseStart_3065075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065075 prefixEnd_3065075 := by exact prefixLift 3065075
  have htrace : WordTrace (prefixWord ++ tailWord_3065075) baseStart_3065075 baseEnd_3065075 := by
    simpa [prefixWord, tailWord_3065075, baseEnd_3065075] using wordTrace_append hprefix tailTrace_3065075
  have hstable : (prefixWord ++ tailWord_3065075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065075).length < 2 ^ (prefixWord ++ tailWord_3065075).sum := by decide
  have hdescent : baseEnd_3065075 < baseStart_3065075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065088 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_3065088 : Nat := 118140960795 + 3065088 * 2 ^ 59
def prefixEnd_3065088 : Nat := 4983230072969 + 3 ^ 40 * 3065088 * 2
def baseEnd_3065088 : Nat := 349747420517379791734205

theorem tailTrace_3065088 : CollatzResearch.WordTrace tailWord_3065088 prefixEnd_3065088 349747420517379791734205 := by
  unfold tailWord_3065088
  simp only [CollatzResearch.WordTrace]
  refine ⟨55896471759858563099753959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74528629013144750799671945 55896471759858563099753959)
  ·
    refine ⟨83844707639787844649630939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55896471759858563099753959 83844707639787844649630939)
    ·
      refine ⟨125767061459681766974446409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83844707639787844649630939 125767061459681766974446409)
      ·
        refine ⟨94325296094761325230834807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125767061459681766974446409 94325296094761325230834807)
        ·
          refine ⟨141487944142141987846252211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94325296094761325230834807 141487944142141987846252211)
          ·
            refine ⟨212231916213212981769378317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141487944142141987846252211 212231916213212981769378317)
            ·
              refine ⟨79586968579954868163516869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212231916213212981769378317 79586968579954868163516869)
              ·
                refine ⟨14922556608741537780659413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79586968579954868163516869 14922556608741537780659413)
                ·
                  refine ⟨349747420517379791734205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14922556608741537780659413 349747420517379791734205)
                  ·
                    rfl

theorem cell22_3065088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_3065088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065088 prefixEnd_3065088 := by exact prefixLift 3065088
  have htrace : WordTrace (prefixWord ++ tailWord_3065088) baseStart_3065088 baseEnd_3065088 := by
    simpa [prefixWord, tailWord_3065088, baseEnd_3065088] using wordTrace_append hprefix tailTrace_3065088
  have hstable : (prefixWord ++ tailWord_3065088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065088).length < 2 ^ (prefixWord ++ tailWord_3065088).sum := by decide
  have hdescent : baseEnd_3065088 < baseStart_3065088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065197 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3065197 : Nat := 118140960795 + 3065197 * 2 ^ 59
def prefixEnd_3065197 : Nat := 4983230072969 + 3 ^ 40 * 3065197 * 2
def baseEnd_3065197 : Nat := 1049279574479699424227281

theorem tailTrace_3065197 : CollatzResearch.WordTrace tailWord_3065197 prefixEnd_3065197 1049279574479699424227281 := by
  unfold tailWord_3065197
  simp only [CollatzResearch.WordTrace]
  refine ⟨111796919076322237815225845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74531279384214825210150563 111796919076322237815225845)
  ·
    refine ⟨10480961163405209795177423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111796919076322237815225845 10480961163405209795177423)
    ·
      refine ⟨15721441745107814692766135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10480961163405209795177423 15721441745107814692766135)
      ·
        refine ⟨23582162617661722039149203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721441745107814692766135 23582162617661722039149203)
        ·
          refine ⟨35373243926492583058723805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23582162617661722039149203 35373243926492583058723805)
          ·
            refine ⟨13264966472434718647021427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35373243926492583058723805 13264966472434718647021427)
            ·
              refine ⟨19897449708652077970532141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264966472434718647021427 19897449708652077970532141)
              ·
                refine ⟨7461543640744529238949553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19897449708652077970532141 7461543640744529238949553)
                ·
                  refine ⟨5596157730558396929212165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7461543640744529238949553 5596157730558396929212165)
                  ·
                    refine ⟨1049279574479699424227281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596157730558396929212165 1049279574479699424227281)
                    ·
                      rfl

theorem cell22_3065197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3065197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065197 prefixEnd_3065197 := by exact prefixLift 3065197
  have htrace : WordTrace (prefixWord ++ tailWord_3065197) baseStart_3065197 baseEnd_3065197 := by
    simpa [prefixWord, tailWord_3065197, baseEnd_3065197] using wordTrace_append hprefix tailTrace_3065197
  have hstable : (prefixWord ++ tailWord_3065197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065197).length < 2 ^ (prefixWord ++ tailWord_3065197).sum := by decide
  have hdescent : baseEnd_3065197 < baseStart_3065197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065218 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3065218 : Nat := 118140960795 + 3065218 * 2 ^ 59
def prefixEnd_3065218 : Nat := 4983230072969 + 3 ^ 40 * 3065218 * 2
def baseEnd_3065218 : Nat := 349762254402954123150739

theorem tailTrace_3065218 : CollatzResearch.WordTrace tailWord_3065218 prefixEnd_3065218 349762254402954123150739 := by
  unfold tailWord_3065218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27949421252311539600435077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74531790006164105601160205 27949421252311539600435077)
  ·
    refine ⟨5240516484808413675081577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27949421252311539600435077 5240516484808413675081577)
    ·
      refine ⟨3930387363606310256311183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5240516484808413675081577 3930387363606310256311183)
      ·
        refine ⟨5895581045409465384466775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930387363606310256311183 5895581045409465384466775)
        ·
          refine ⟨8843371568114198076700163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895581045409465384466775 8843371568114198076700163)
          ·
            refine ⟨13265057352171297115050245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843371568114198076700163 13265057352171297115050245)
            ·
              refine ⟨2487198253532118209071921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13265057352171297115050245 2487198253532118209071921)
              ·
                refine ⟨1865398690149088656803941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487198253532118209071921 1865398690149088656803941)
                ·
                  refine ⟨349762254402954123150739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865398690149088656803941 349762254402954123150739)
                  ·
                    rfl

theorem cell22_3065218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3065218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065218 prefixEnd_3065218 := by exact prefixLift 3065218
  have htrace : WordTrace (prefixWord ++ tailWord_3065218) baseStart_3065218 baseEnd_3065218 := by
    simpa [prefixWord, tailWord_3065218, baseEnd_3065218] using wordTrace_append hprefix tailTrace_3065218
  have hstable : (prefixWord ++ tailWord_3065218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065218).length < 2 ^ (prefixWord ++ tailWord_3065218).sum := by decide
  have hdescent : baseEnd_3065218 < baseStart_3065218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065227 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 3, 3]
def baseStart_3065227 : Nat := 118140960795 + 3065227 * 2 ^ 59
def prefixEnd_3065227 : Nat := 4983230072969 + 3 ^ 40 * 3065227 * 2
def baseEnd_3065227 : Nat := 1049289844092789345977189

theorem tailTrace_3065227 : CollatzResearch.WordTrace tailWord_3065227 prefixEnd_3065227 1049289844092789345977189 := by
  unfold tailWord_3065227
  simp only [CollatzResearch.WordTrace]
  refine ⟨111798013266213552938817935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74532008844142368625878623 111798013266213552938817935)
  ·
    refine ⟨167697019899320329408226903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111798013266213552938817935 167697019899320329408226903)
    ·
      refine ⟨251545529848980494112340355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167697019899320329408226903 251545529848980494112340355)
      ·
        refine ⟨377318294773470741168510533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251545529848980494112340355 377318294773470741168510533)
        ·
          refine ⟨70747180270025763969095725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377318294773470741168510533 70747180270025763969095725)
          ·
            refine ⟨26530192601259661488410897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70747180270025763969095725 26530192601259661488410897)
            ·
              refine ⟨19897644450944746116308173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26530192601259661488410897 19897644450944746116308173)
              ·
                refine ⟨7461616669104279793615565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19897644450944746116308173 7461616669104279793615565)
                ·
                  refine ⟨2798106250914104922605837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7461616669104279793615565 2798106250914104922605837)
                  ·
                    refine ⟨1049289844092789345977189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798106250914104922605837 1049289844092789345977189)
                    ·
                      rfl

theorem cell22_3065227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3].length) (baseStart_3065227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065227 prefixEnd_3065227 := by exact prefixLift 3065227
  have htrace : WordTrace (prefixWord ++ tailWord_3065227) baseStart_3065227 baseEnd_3065227 := by
    simpa [prefixWord, tailWord_3065227, baseEnd_3065227] using wordTrace_append hprefix tailTrace_3065227
  have hstable : (prefixWord ++ tailWord_3065227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065227).length < 2 ^ (prefixWord ++ tailWord_3065227).sum := by decide
  have hdescent : baseEnd_3065227 < baseStart_3065227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065246 : List Nat := [4, 3, 1, 2, 2, 1, 3, 6]
def baseStart_3065246 : Nat := 118140960795 + 3065246 * 2 ^ 59
def prefixEnd_3065246 : Nat := 4983230072969 + 3 ^ 40 * 3065246 * 2
def baseEnd_3065246 : Nat := 116588483131231069972459

theorem tailTrace_3065246 : CollatzResearch.WordTrace tailWord_3065246 prefixEnd_3065246 116588483131231069972459 := by
  unfold tailWord_3065246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13974838281643089897969949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74532470835429812789173061 13974838281643089897969949)
  ·
    refine ⟨5240564355616158711738731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13974838281643089897969949 5240564355616158711738731)
    ·
      refine ⟨7860846533424238067608097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240564355616158711738731 7860846533424238067608097)
      ·
        refine ⟨5895634900068178550706073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7860846533424238067608097 5895634900068178550706073)
        ·
          refine ⟨4421726175051133913029555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5895634900068178550706073 4421726175051133913029555)
          ·
            refine ⟨6632589262576700869544333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421726175051133913029555 6632589262576700869544333)
            ·
              refine ⟨2487220973466262826079125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632589262576700869544333 2487220973466262826079125)
              ·
                refine ⟨116588483131231069972459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2487220973466262826079125 116588483131231069972459)
                ·
                  rfl

theorem cell22_3065246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_3065246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065246 prefixEnd_3065246 := by exact prefixLift 3065246
  have htrace : WordTrace (prefixWord ++ tailWord_3065246) baseStart_3065246 baseEnd_3065246 := by
    simpa [prefixWord, tailWord_3065246, baseEnd_3065246] using wordTrace_append hprefix tailTrace_3065246
  have hstable : (prefixWord ++ tailWord_3065246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065246).length < 2 ^ (prefixWord ++ tailWord_3065246).sum := by decide
  have hdescent : baseEnd_3065246 < baseStart_3065246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065336 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_3065336 : Nat := 118140960795 + 3065336 * 2 ^ 59
def prefixEnd_3065336 : Nat := 4983230072969 + 3 ^ 40 * 3065336 * 2
def baseEnd_3065336 : Nat := 349775719006783131667285

theorem tailTrace_3065336 : CollatzResearch.WordTrace tailWord_3065336 prefixEnd_3065336 349775719006783131667285 := by
  unfold tailWord_3065336
  simp only [CollatzResearch.WordTrace]
  refine ⟨55900994411409332277267931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74534659215212443036357241 55900994411409332277267931)
  ·
    refine ⟨83851491617113998415901897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55900994411409332277267931 83851491617113998415901897)
    ·
      refine ⟨62888618712835498811926423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83851491617113998415901897 62888618712835498811926423)
      ·
        refine ⟨94332928069253248217889635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62888618712835498811926423 94332928069253248217889635)
        ·
          refine ⟨141499392103879872326834453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94332928069253248217889635 141499392103879872326834453)
          ·
            refine ⟨6632784004869369015320365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141499392103879872326834453 6632784004869369015320365)
            ·
              refine ⟨2487294001826013380745137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632784004869369015320365 2487294001826013380745137)
              ·
                refine ⟨1865470501369510035558853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487294001826013380745137 1865470501369510035558853)
                ·
                  refine ⟨349775719006783131667285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865470501369510035558853 349775719006783131667285)
                  ·
                    rfl

theorem cell22_3065336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_3065336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065336 prefixEnd_3065336 := by exact prefixLift 3065336
  have htrace : WordTrace (prefixWord ++ tailWord_3065336) baseStart_3065336 baseEnd_3065336 := by
    simpa [prefixWord, tailWord_3065336, baseEnd_3065336] using wordTrace_append hprefix tailTrace_3065336
  have hstable : (prefixWord ++ tailWord_3065336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065336).length < 2 ^ (prefixWord ++ tailWord_3065336).sum := by decide
  have hdescent : baseEnd_3065336 < baseStart_3065336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065351 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3065351 : Nat := 118140960795 + 3065351 * 2 ^ 59
def prefixEnd_3065351 : Nat := 4983230072969 + 3 ^ 40 * 3065351 * 2
def baseEnd_3065351 : Nat := 1049332291826894355876809

theorem tailTrace_3065351 : CollatzResearch.WordTrace tailWord_3065351 prefixEnd_3065351 1049332291826894355876809 := by
  unfold tailWord_3065351
  simp only [CollatzResearch.WordTrace]
  refine ⟨111802535917764322116331907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74535023945176214744221271 111802535917764322116331907)
  ·
    refine ⟨167703803876646483174497861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111802535917764322116331907 167703803876646483174497861)
    ·
      refine ⟨31444463226871215595218349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167703803876646483174497861 31444463226871215595218349)
      ·
        refine ⟨11791673710076705848206881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31444463226871215595218349 11791673710076705848206881)
        ·
          refine ⟨8843755282557529386155161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791673710076705848206881 8843755282557529386155161)
          ·
            refine ⟨6632816461918147039616371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8843755282557529386155161 6632816461918147039616371)
            ·
              refine ⟨9949224692877220559424557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632816461918147039616371 9949224692877220559424557)
              ·
                refine ⟨3730959259828957709784209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9949224692877220559424557 3730959259828957709784209)
                ·
                  refine ⟨2798219444871718282338157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730959259828957709784209 2798219444871718282338157)
                  ·
                    refine ⟨1049332291826894355876809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798219444871718282338157 1049332291826894355876809)
                    ·
                      rfl

theorem cell22_3065351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3065351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065351 prefixEnd_3065351 := by exact prefixLift 3065351
  have htrace : WordTrace (prefixWord ++ tailWord_3065351) baseStart_3065351 baseEnd_3065351 := by
    simpa [prefixWord, tailWord_3065351, baseEnd_3065351] using wordTrace_append hprefix tailTrace_3065351
  have hstable : (prefixWord ++ tailWord_3065351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065351).length < 2 ^ (prefixWord ++ tailWord_3065351).sum := by decide
  have hdescent : baseEnd_3065351 < baseStart_3065351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065398 : List Nat := [5, 1, 2, 1, 4, 1, 1, 7]
def baseStart_3065398 : Nat := 118140960795 + 3065398 * 2 ^ 59
def prefixEnd_3065398 : Nat := 4983230072969 + 3 ^ 40 * 3065398 * 2
def baseEnd_3065398 : Nat := 116594264543044655550185

theorem tailTrace_3065398 : CollatzResearch.WordTrace tailWord_3065398 prefixEnd_3065398 116594264543044655550185 := by
  unfold tailWord_3065398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987765634287128071455803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74536166765729366095528565 6987765634287128071455803)
  ·
    refine ⟨10481648451430692107183705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987765634287128071455803 10481648451430692107183705)
    ·
      refine ⟨7861236338573019080387779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10481648451430692107183705 7861236338573019080387779)
      ·
        refine ⟨11791854507859528620581669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861236338573019080387779 11791854507859528620581669)
        ·
          refine ⟨2210972720223661616359063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11791854507859528620581669 2210972720223661616359063)
          ·
            refine ⟨3316459080335492424538595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210972720223661616359063 3316459080335492424538595)
            ·
              refine ⟨4974688620503238636807893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316459080335492424538595 4974688620503238636807893)
              ·
                refine ⟨116594264543044655550185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4974688620503238636807893 116594264543044655550185)
                ·
                  rfl

theorem cell22_3065398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_3065398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065398 prefixEnd_3065398 := by exact prefixLift 3065398
  have htrace : WordTrace (prefixWord ++ tailWord_3065398) baseStart_3065398 baseEnd_3065398 := by
    simpa [prefixWord, tailWord_3065398, baseEnd_3065398] using wordTrace_append hprefix tailTrace_3065398
  have hstable : (prefixWord ++ tailWord_3065398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065398).length < 2 ^ (prefixWord ++ tailWord_3065398).sum := by decide
  have hdescent : baseEnd_3065398 < baseStart_3065398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065407 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3065407 : Nat := 118140960795 + 3065407 * 2 ^ 59
def prefixEnd_3065407 : Nat := 4983230072969 + 3 ^ 40 * 3065407 * 2
def baseEnd_3065407 : Nat := 1049351461771328876476637

theorem tailTrace_3065407 : CollatzResearch.WordTrace tailWord_3065407 prefixEnd_3065407 1049351461771328876476637 := by
  unfold tailWord_3065407
  simp only [CollatzResearch.WordTrace]
  refine ⟨111804578405561443680370475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74536385603707629120246983 111804578405561443680370475)
  ·
    refine ⟨167706867608342165520555713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111804578405561443680370475 167706867608342165520555713)
    ·
      refine ⟨125780150706256624140416785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167706867608342165520555713 125780150706256624140416785)
      ·
        refine ⟨94335113029692468105312589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125780150706256624140416785 94335113029692468105312589)
        ·
          refine ⟨35375667386134675539492221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94335113029692468105312589 35375667386134675539492221)
          ·
            refine ⟨13265875269800503327309583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35375667386134675539492221 13265875269800503327309583)
            ·
              refine ⟨19898812904700754990964375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265875269800503327309583 19898812904700754990964375)
              ·
                refine ⟨29848219357051132486446563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19898812904700754990964375 29848219357051132486446563)
                ·
                  refine ⟨44772329035576698729669845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29848219357051132486446563 44772329035576698729669845)
                  ·
                    refine ⟨1049351461771328876476637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44772329035576698729669845 1049351461771328876476637)
                    ·
                      rfl

theorem cell22_3065407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3065407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065407 prefixEnd_3065407 := by exact prefixLift 3065407
  have htrace : WordTrace (prefixWord ++ tailWord_3065407) baseStart_3065407 baseEnd_3065407 := by
    simpa [prefixWord, tailWord_3065407, baseEnd_3065407] using wordTrace_append hprefix tailTrace_3065407
  have hstable : (prefixWord ++ tailWord_3065407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065407).length < 2 ^ (prefixWord ++ tailWord_3065407).sum := by decide
  have hdescent : baseEnd_3065407 < baseStart_3065407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065409 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 5]
def baseStart_3065409 : Nat := 118140960795 + 3065409 * 2 ^ 59
def prefixEnd_3065409 : Nat := 4983230072969 + 3 ^ 40 * 3065409 * 2
def baseEnd_3065409 : Nat := 349784048804067179308877

theorem tailTrace_3065409 : CollatzResearch.WordTrace tailWord_3065409 prefixEnd_3065409 349784048804067179308877 := by
  unfold tailWord_3065409
  simp only [CollatzResearch.WordTrace]
  refine ⟨111804651351554198021943281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74536434234369465347962187 111804651351554198021943281)
  ·
    refine ⟨83853488513665648516457461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111804651351554198021943281 83853488513665648516457461)
    ·
      refine ⟨7861264548156154548417887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83853488513665648516457461 7861264548156154548417887)
      ·
        refine ⟨11791896822234231822626831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861264548156154548417887 11791896822234231822626831)
        ·
          refine ⟨17687845233351347733940247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11791896822234231822626831 17687845233351347733940247)
          ·
            refine ⟨26531767850027021600910371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17687845233351347733940247 26531767850027021600910371)
            ·
              refine ⟨39797651775040532401365557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26531767850027021600910371 39797651775040532401365557)
              ·
                refine ⟨3731029853910049912628021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39797651775040532401365557 3731029853910049912628021)
                ·
                  refine ⟨349784048804067179308877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3731029853910049912628021 349784048804067179308877)
                  ·
                    rfl

theorem cell22_3065409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_3065409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065409 prefixEnd_3065409 := by exact prefixLift 3065409
  have htrace : WordTrace (prefixWord ++ tailWord_3065409) baseStart_3065409 baseEnd_3065409 := by
    simpa [prefixWord, tailWord_3065409, baseEnd_3065409] using wordTrace_append hprefix tailTrace_3065409
  have hstable : (prefixWord ++ tailWord_3065409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065409).length < 2 ^ (prefixWord ++ tailWord_3065409).sum := by decide
  have hdescent : baseEnd_3065409 < baseStart_3065409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065467 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_3065467 : Nat := 118140960795 + 3065467 * 2 ^ 59
def prefixEnd_3065467 : Nat := 4983230072969 + 3 ^ 40 * 3065467 * 2
def baseEnd_3065467 : Nat := 1049372000997508719976453

theorem tailTrace_3065467 : CollatzResearch.WordTrace tailWord_3065467 prefixEnd_3065467 1049372000997508719976453 := by
  unfold tailWord_3065467
  simp only [CollatzResearch.WordTrace]
  refine ⟨111806766785344073927554655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74537844523562715951703103 111806766785344073927554655)
  ·
    refine ⟨167710150178016110891331983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111806766785344073927554655 167710150178016110891331983)
    ·
      refine ⟨251565225267024166336997975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167710150178016110891331983 251565225267024166336997975)
      ·
        refine ⟨377347837900536249505496963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251565225267024166336997975 377347837900536249505496963)
        ·
          refine ⟨566021756850804374258245445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377347837900536249505496963 566021756850804374258245445)
          ·
            refine ⟨106129079409525820173421021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 566021756850804374258245445 106129079409525820173421021)
            ·
              refine ⟨39798404778572182565032883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106129079409525820173421021 39798404778572182565032883)
              ·
                refine ⟨59697607167858273847549325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39798404778572182565032883 59697607167858273847549325)
                ·
                  refine ⟨22386602687946852692830997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59697607167858273847549325 22386602687946852692830997)
                  ·
                    refine ⟨1049372000997508719976453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22386602687946852692830997 1049372000997508719976453)
                    ·
                      rfl

theorem cell22_3065467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_3065467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065467 prefixEnd_3065467 := by exact prefixLift 3065467
  have htrace : WordTrace (prefixWord ++ tailWord_3065467) baseStart_3065467 baseEnd_3065467 := by
    simpa [prefixWord, tailWord_3065467, baseEnd_3065467] using wordTrace_append hprefix tailTrace_3065467
  have hstable : (prefixWord ++ tailWord_3065467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065467).length < 2 ^ (prefixWord ++ tailWord_3065467).sum := by decide
  have hdescent : baseEnd_3065467 < baseStart_3065467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065484 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_3065484 : Nat := 118140960795 + 3065484 * 2 ^ 59
def prefixEnd_3065484 : Nat := 4983230072969 + 3 ^ 40 * 3065484 * 2
def baseEnd_3065484 : Nat := 1049377820444926342301401

theorem tailTrace_3065484 : CollatzResearch.WordTrace tailWord_3065484 prefixEnd_3065484 1049377820444926342301401 := by
  unfold tailWord_3065484
  simp only [CollatzResearch.WordTrace]
  refine ⟨55903693413141242915461753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74538257884188323887282337 55903693413141242915461753)
  ·
    refine ⟨41927770059855932186596315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55903693413141242915461753 41927770059855932186596315)
    ·
      refine ⟨62891655089783898279894473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41927770059855932186596315 62891655089783898279894473)
      ·
        refine ⟨47168741317337923709920855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62891655089783898279894473 47168741317337923709920855)
        ·
          refine ⟨70753111976006885564881283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47168741317337923709920855 70753111976006885564881283)
          ·
            refine ⟨106129667964010328347321925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70753111976006885564881283 106129667964010328347321925)
            ·
              refine ⟨19899312743251936565122861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106129667964010328347321925 19899312743251936565122861)
              ·
                refine ⟨7462242278719476211921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19899312743251936565122861 7462242278719476211921073)
                ·
                  refine ⟨5596681709039607158940805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7462242278719476211921073 5596681709039607158940805)
                  ·
                    refine ⟨1049377820444926342301401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596681709039607158940805 1049377820444926342301401)
                    ·
                      rfl

theorem cell22_3065484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_3065484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065484 prefixEnd_3065484 := by exact prefixLift 3065484
  have htrace : WordTrace (prefixWord ++ tailWord_3065484) baseStart_3065484 baseEnd_3065484 := by
    simpa [prefixWord, tailWord_3065484, baseEnd_3065484] using wordTrace_append hprefix tailTrace_3065484
  have hstable : (prefixWord ++ tailWord_3065484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065484).length < 2 ^ (prefixWord ++ tailWord_3065484).sum := by decide
  have hdescent : baseEnd_3065484 < baseStart_3065484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065486 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3065486 : Nat := 118140960795 + 3065486 * 2 ^ 59
def prefixEnd_3065486 : Nat := 4983230072969 + 3 ^ 40 * 3065486 * 2
def baseEnd_3065486 : Nat := 1049378505085799003751395

theorem tailTrace_3065486 : CollatzResearch.WordTrace tailWord_3065486 prefixEnd_3065486 1049378505085799003751395 := by
  unfold tailWord_3065486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975932471534405021562039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74538306514850160114997541 13975932471534405021562039)
  ·
    refine ⟨20963898707301607532343059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13975932471534405021562039 20963898707301607532343059)
    ·
      refine ⟨31445848060952411298514589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20963898707301607532343059 31445848060952411298514589)
      ·
        refine ⟨11792193022857154236942971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31445848060952411298514589 11792193022857154236942971)
        ·
          refine ⟨17688289534285731355414457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792193022857154236942971 17688289534285731355414457)
          ·
            refine ⟨13266217150714298516560843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17688289534285731355414457 13266217150714298516560843)
            ·
              refine ⟨19899325726071447774841265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266217150714298516560843 19899325726071447774841265)
              ·
                refine ⟨14924494294553585831130949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19899325726071447774841265 14924494294553585831130949)
                ·
                  refine ⟨2798342680228797343337053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14924494294553585831130949 2798342680228797343337053)
                  ·
                    refine ⟨1049378505085799003751395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798342680228797343337053 1049378505085799003751395)
                    ·
                      rfl

theorem cell22_3065486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3065486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065486 prefixEnd_3065486 := by exact prefixLift 3065486
  have htrace : WordTrace (prefixWord ++ tailWord_3065486) baseStart_3065486 baseEnd_3065486 := by
    simpa [prefixWord, tailWord_3065486, baseEnd_3065486] using wordTrace_append hprefix tailTrace_3065486
  have hstable : (prefixWord ++ tailWord_3065486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065486).length < 2 ^ (prefixWord ++ tailWord_3065486).sum := by decide
  have hdescent : baseEnd_3065486 < baseStart_3065486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065559 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3065559 : Nat := 118140960795 + 3065559 * 2 ^ 59
def prefixEnd_3065559 : Nat := 4983230072969 + 3 ^ 40 * 3065559 * 2
def baseEnd_3065559 : Nat := 1049403494477651146676171

theorem tailTrace_3065559 : CollatzResearch.WordTrace tailWord_3065559 prefixEnd_3065559 1049403494477651146676171 := by
  unfold tailWord_3065559
  simp only [CollatzResearch.WordTrace]
  refine ⟨111810122301010773639903731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74540081534007182426602487 111810122301010773639903731)
  ·
    refine ⟨167715183451516160459855597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111810122301010773639903731 167715183451516160459855597)
    ·
      refine ⟨62893193794318560172445849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167715183451516160459855597 62893193794318560172445849)
      ·
        refine ⟨47169895345738920129334387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62893193794318560172445849 47169895345738920129334387)
        ·
          refine ⟨70754843018608380194001581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47169895345738920129334387 70754843018608380194001581)
          ·
            refine ⟨26533066131978142572750593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70754843018608380194001581 26533066131978142572750593)
            ·
              refine ⟨19899799598983606929562945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26533066131978142572750593 19899799598983606929562945)
              ·
                refine ⟨14924849699237705197172209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19899799598983606929562945 14924849699237705197172209)
                ·
                  refine ⟨11193637274428278897879157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14924849699237705197172209 11193637274428278897879157)
                  ·
                    refine ⟨1049403494477651146676171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11193637274428278897879157 1049403494477651146676171)
                    ·
                      rfl

theorem cell22_3065559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3065559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065559 prefixEnd_3065559 := by exact prefixLift 3065559
  have htrace : WordTrace (prefixWord ++ tailWord_3065559) baseStart_3065559 baseEnd_3065559 := by
    simpa [prefixWord, tailWord_3065559, baseEnd_3065559] using wordTrace_append hprefix tailTrace_3065559
  have hstable : (prefixWord ++ tailWord_3065559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065559).length < 2 ^ (prefixWord ++ tailWord_3065559).sum := by decide
  have hdescent : baseEnd_3065559 < baseStart_3065559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065561 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 5]
def baseStart_3065561 : Nat := 118140960795 + 3065561 * 2 ^ 59
def prefixEnd_3065561 : Nat := 4983230072969 + 3 ^ 40 * 3065561 * 2
def baseEnd_3065561 : Nat := 349801393039507936042055

theorem tailTrace_3065561 : CollatzResearch.WordTrace tailWord_3065561 prefixEnd_3065561 349801393039507936042055 := by
  unfold tailWord_3065561
  simp only [CollatzResearch.WordTrace]
  refine ⟨111810195247003527981476537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74540130164669018654317691 111810195247003527981476537)
  ·
    refine ⟨83857646435252645986107403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111810195247003527981476537 83857646435252645986107403)
    ·
      refine ⟨125786469652878968979161105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83857646435252645986107403 125786469652878968979161105)
      ·
        refine ⟨94339852239659226734370829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125786469652878968979161105 94339852239659226734370829)
        ·
          refine ⟨35377444589872210025389061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94339852239659226734370829 35377444589872210025389061)
          ·
            refine ⟨6633270860601039379760449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35377444589872210025389061 6633270860601039379760449)
            ·
              refine ⟨4974953145450779534820337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633270860601039379760449 4974953145450779534820337)
              ·
                refine ⟨3731214859088084651115253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974953145450779534820337 3731214859088084651115253)
                ·
                  refine ⟨349801393039507936042055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3731214859088084651115253 349801393039507936042055)
                  ·
                    rfl

theorem cell22_3065561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_3065561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065561 prefixEnd_3065561 := by exact prefixLift 3065561
  have htrace : WordTrace (prefixWord ++ tailWord_3065561) baseStart_3065561 baseEnd_3065561 := by
    simpa [prefixWord, tailWord_3065561, baseEnd_3065561] using wordTrace_append hprefix tailTrace_3065561
  have hstable : (prefixWord ++ tailWord_3065561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065561).length < 2 ^ (prefixWord ++ tailWord_3065561).sum := by decide
  have hdescent : baseEnd_3065561 < baseStart_3065561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065576 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3065576 : Nat := 118140960795 + 3065576 * 2 ^ 59
def prefixEnd_3065576 : Nat := 4983230072969 + 3 ^ 40 * 3065576 * 2
def baseEnd_3065576 : Nat := 1049409313925068769001119

theorem tailTrace_3065576 : CollatzResearch.WordTrace tailWord_3065576 prefixEnd_3065576 1049409313925068769001119 := by
  unfold tailWord_3065576
  simp only [CollatzResearch.WordTrace]
  refine ⟨55905371170974592771636291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74540494894632790362181721 55905371170974592771636291)
  ·
    refine ⟨83858056756461889157454437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55905371170974592771636291 83858056756461889157454437)
    ·
      refine ⟨15723385641836604217022707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83858056756461889157454437 15723385641836604217022707)
      ·
        refine ⟨23585078462754906325534061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15723385641836604217022707 23585078462754906325534061)
        ·
          refine ⟨8844404423533089872075273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23585078462754906325534061 8844404423533089872075273)
          ·
            refine ⟨6633303317649817404056455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8844404423533089872075273 6633303317649817404056455)
            ·
              refine ⟨9949954976474726106084683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633303317649817404056455 9949954976474726106084683)
              ·
                refine ⟨14924932464712089159127025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9949954976474726106084683 14924932464712089159127025)
                ·
                  refine ⟨11193699348534066869345269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14924932464712089159127025 11193699348534066869345269)
                  ·
                    refine ⟨1049409313925068769001119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11193699348534066869345269 1049409313925068769001119)
                    ·
                      rfl

theorem cell22_3065576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3065576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065576 prefixEnd_3065576 := by exact prefixLift 3065576
  have htrace : WordTrace (prefixWord ++ tailWord_3065576) baseStart_3065576 baseEnd_3065576 := by
    simpa [prefixWord, tailWord_3065576, baseEnd_3065576] using wordTrace_append hprefix tailTrace_3065576
  have hstable : (prefixWord ++ tailWord_3065576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065576).length < 2 ^ (prefixWord ++ tailWord_3065576).sum := by decide
  have hdescent : baseEnd_3065576 < baseStart_3065576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065623 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 4]
def baseStart_3065623 : Nat := 118140960795 + 3065623 * 2 ^ 59
def prefixEnd_3065623 : Nat := 4983230072969 + 3 ^ 40 * 3065623 * 2
def baseEnd_3065623 : Nat := 349808467661858771025325

theorem tailTrace_3065623 : CollatzResearch.WordTrace tailWord_3065623 prefixEnd_3065623 349808467661858771025325 := by
  unfold tailWord_3065623
  simp only [CollatzResearch.WordTrace]
  refine ⟨111812456572778912570233523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74541637715185941713489015 111812456572778912570233523)
  ·
    refine ⟨167718684859168368855350285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111812456572778912570233523 167718684859168368855350285)
    ·
      refine ⟨62894506822188138320756357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167718684859168368855350285 62894506822188138320756357)
      ·
        refine ⟨11792720029160275935141817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62894506822188138320756357 11792720029160275935141817)
        ·
          refine ⟨8844540021870206951356363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792720029160275935141817 8844540021870206951356363)
          ·
            refine ⟨13266810032805310427034545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844540021870206951356363 13266810032805310427034545)
            ·
              refine ⟨9950107524603982820275909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13266810032805310427034545 9950107524603982820275909)
              ·
                refine ⟨1865645160863246778801733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9950107524603982820275909 1865645160863246778801733)
                ·
                  refine ⟨349808467661858771025325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865645160863246778801733 349808467661858771025325)
                  ·
                    rfl

theorem cell22_3065623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 4].length) (baseStart_3065623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065623 prefixEnd_3065623 := by exact prefixLift 3065623
  have htrace : WordTrace (prefixWord ++ tailWord_3065623) baseStart_3065623 baseEnd_3065623 := by
    simpa [prefixWord, tailWord_3065623, baseEnd_3065623] using wordTrace_append hprefix tailTrace_3065623
  have hstable : (prefixWord ++ tailWord_3065623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065623).length < 2 ^ (prefixWord ++ tailWord_3065623).sum := by decide
  have hdescent : baseEnd_3065623 < baseStart_3065623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065636 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_3065636 : Nat := 118140960795 + 3065636 * 2 ^ 59
def prefixEnd_3065636 : Nat := 4983230072969 + 3 ^ 40 * 3065636 * 2
def baseEnd_3065636 : Nat := 1049429853151248612500935

theorem tailTrace_3065636 : CollatzResearch.WordTrace tailWord_3065636 prefixEnd_3065636 1049429853151248612500935 := by
  unfold tailWord_3065636
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906465360865907895228381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74541953814487877193637841 55906465360865907895228381)
  ·
    refine ⟨20964924510324715460710643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55906465360865907895228381 20964924510324715460710643)
    ·
      refine ⟨31447386765487073191065965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20964924510324715460710643 31447386765487073191065965)
      ·
        refine ⟨11792770037057652446649737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31447386765487073191065965 11792770037057652446649737)
        ·
          refine ⟨8844577527793239334987303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792770037057652446649737 8844577527793239334987303)
          ·
            refine ⟨13266866291689859002480955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844577527793239334987303 13266866291689859002480955)
            ·
              refine ⟨19900299437534788503721433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266866291689859002480955 19900299437534788503721433)
              ·
                refine ⟨14925224578151091377791075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19900299437534788503721433 14925224578151091377791075)
                ·
                  refine ⟨22387836867226637066686613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14925224578151091377791075 22387836867226637066686613)
                  ·
                    refine ⟨1049429853151248612500935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22387836867226637066686613 1049429853151248612500935)
                    ·
                      rfl

theorem cell22_3065636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_3065636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065636 prefixEnd_3065636 := by exact prefixLift 3065636
  have htrace : WordTrace (prefixWord ++ tailWord_3065636) baseStart_3065636 baseEnd_3065636 := by
    simpa [prefixWord, tailWord_3065636, baseEnd_3065636] using wordTrace_append hprefix tailTrace_3065636
  have hstable : (prefixWord ++ tailWord_3065636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065636).length < 2 ^ (prefixWord ++ tailWord_3065636).sum := by decide
  have hdescent : baseEnd_3065636 < baseStart_3065636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065651 : List Nat := [1, 1, 1, 2, 7, 1, 1, 8]
def baseStart_3065651 : Nat := 118140960795 + 3065651 * 2 ^ 59
def prefixEnd_3065651 : Nat := 4983230072969 + 3 ^ 40 * 3065651 * 2
def baseEnd_3065651 : Nat := 116603887550865952597321

theorem tailTrace_3065651 : CollatzResearch.WordTrace tailWord_3065651 prefixEnd_3065651 116603887550865952597321 := by
  unfold tailWord_3065651
  simp only [CollatzResearch.WordTrace]
  refine ⟨111813477816677473352252807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74542318544451648901501871 111813477816677473352252807)
  ·
    refine ⟨167720216725016210028379211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111813477816677473352252807 167720216725016210028379211)
    ·
      refine ⟨251580325087524315042568817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167720216725016210028379211 251580325087524315042568817)
      ·
        refine ⟨188685243815643236281926613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251580325087524315042568817 188685243815643236281926613)
        ·
          refine ⟨4422310401929138350357655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 188685243815643236281926613 4422310401929138350357655)
          ·
            refine ⟨6633465602893707525536483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422310401929138350357655 6633465602893707525536483)
            ·
              refine ⟨9950198404340561288304725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633465602893707525536483 9950198404340561288304725)
              ·
                refine ⟨116603887550865952597321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9950198404340561288304725 116603887550865952597321)
                ·
                  rfl

theorem cell22_3065651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 8].length) (baseStart_3065651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065651 prefixEnd_3065651 := by exact prefixLift 3065651
  have htrace : WordTrace (prefixWord ++ tailWord_3065651) baseStart_3065651 baseEnd_3065651 := by
    simpa [prefixWord, tailWord_3065651, baseEnd_3065651] using wordTrace_append hprefix tailTrace_3065651
  have hstable : (prefixWord ++ tailWord_3065651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065651).length < 2 ^ (prefixWord ++ tailWord_3065651).sum := by decide
  have hdescent : baseEnd_3065651 < baseStart_3065651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065657 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 4]
def baseStart_3065657 : Nat := 118140960795 + 3065657 * 2 ^ 59
def prefixEnd_3065657 : Nat := 4983230072969 + 3 ^ 40 * 3065657 * 2
def baseEnd_3065657 : Nat := 349812347293470519241957

theorem tailTrace_3065657 : CollatzResearch.WordTrace tailWord_3065657 prefixEnd_3065657 349812347293470519241957 := by
  unfold tailWord_3065657
  simp only [CollatzResearch.WordTrace]
  refine ⟨111813696654655736376971225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74542464436437157584647483 111813696654655736376971225)
  ·
    refine ⟨83860272490991802282728419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111813696654655736376971225 83860272490991802282728419)
    ·
      refine ⟨125790408736487703424092629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83860272490991802282728419 125790408736487703424092629)
      ·
        refine ⟨2948212704761430549002171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125790408736487703424092629 2948212704761430549002171)
        ·
          refine ⟨4422319057142145823503257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948212704761430549002171 4422319057142145823503257)
          ·
            refine ⟨3316739292856609367627443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422319057142145823503257 3316739292856609367627443)
            ·
              refine ⟨4975108939284914051441165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316739292856609367627443 4975108939284914051441165)
              ·
                refine ⟨1865665852231842769290437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4975108939284914051441165 1865665852231842769290437)
                ·
                  refine ⟨349812347293470519241957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865665852231842769290437 349812347293470519241957)
                  ·
                    rfl

theorem cell22_3065657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_3065657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065657 prefixEnd_3065657 := by exact prefixLift 3065657
  have htrace : WordTrace (prefixWord ++ tailWord_3065657) baseStart_3065657 baseEnd_3065657 := by
    simpa [prefixWord, tailWord_3065657, baseEnd_3065657] using wordTrace_append hprefix tailTrace_3065657
  have hstable : (prefixWord ++ tailWord_3065657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065657).length < 2 ^ (prefixWord ++ tailWord_3065657).sum := by decide
  have hdescent : baseEnd_3065657 < baseStart_3065657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065664 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_3065664 : Nat := 118140960795 + 3065664 * 2 ^ 59
def prefixEnd_3065664 : Nat := 4983230072969 + 3 ^ 40 * 3065664 * 2
def baseEnd_3065664 : Nat := 1049439438123465872800849

theorem tailTrace_3065664 : CollatzResearch.WordTrace tailWord_3065664 prefixEnd_3065664 1049439438123465872800849 := by
  unfold tailWord_3065664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906975982815188286238023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74542634643753584381650697 55906975982815188286238023)
  ·
    refine ⟨83860463974222782429357035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55906975982815188286238023 83860463974222782429357035)
    ·
      refine ⟨125790695961334173644035553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83860463974222782429357035 125790695961334173644035553)
      ·
        refine ⟨94343021971000630233026665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125790695961334173644035553 94343021971000630233026665)
        ·
          refine ⟨70757266478250472674769999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94343021971000630233026665 70757266478250472674769999)
          ·
            refine ⟨106135899717375709012154999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70757266478250472674769999 106135899717375709012154999)
            ·
              refine ⟨159203849576063563518232499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106135899717375709012154999 159203849576063563518232499)
              ·
                refine ⟨238805774364095345277348749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159203849576063563518232499 238805774364095345277348749)
                ·
                  refine ⟨89552165386535754479005781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238805774364095345277348749 89552165386535754479005781)
                  ·
                    refine ⟨1049439438123465872800849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89552165386535754479005781 1049439438123465872800849)
                    ·
                      rfl

theorem cell22_3065664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_3065664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065664 prefixEnd_3065664 := by exact prefixLift 3065664
  have htrace : WordTrace (prefixWord ++ tailWord_3065664) baseStart_3065664 baseEnd_3065664 := by
    simpa [prefixWord, tailWord_3065664, baseEnd_3065664] using wordTrace_append hprefix tailTrace_3065664
  have hstable : (prefixWord ++ tailWord_3065664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065664).length < 2 ^ (prefixWord ++ tailWord_3065664).sum := by decide
  have hdescent : baseEnd_3065664 < baseStart_3065664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065670 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3065670 : Nat := 118140960795 + 3065670 * 2 ^ 59
def prefixEnd_3065670 : Nat := 4983230072969 + 3 ^ 40 * 3065670 * 2
def baseEnd_3065670 : Nat := 1049441492046083857150831

theorem tailTrace_3065670 : CollatzResearch.WordTrace tailWord_3065670 prefixEnd_3065670 1049441492046083857150831 := by
  unfold tailWord_3065670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494192837612769987412327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74542780535739093064796309 3494192837612769987412327)
  ·
    refine ⟨5241289256419154981118491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494192837612769987412327 5241289256419154981118491)
    ·
      refine ⟨7861933884628732471677737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241289256419154981118491 7861933884628732471677737)
      ·
        refine ⟨5896450413471549353758303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7861933884628732471677737 5896450413471549353758303)
        ·
          refine ⟨8844675620207324030637455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5896450413471549353758303 8844675620207324030637455)
          ·
            refine ⟨13267013430310986045956183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844675620207324030637455 13267013430310986045956183)
            ·
              refine ⟨19900520145466479068934275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13267013430310986045956183 19900520145466479068934275)
              ·
                refine ⟨29850780218199718603401413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19900520145466479068934275 29850780218199718603401413)
                ·
                  refine ⟨5597021290912447238137765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29850780218199718603401413 5597021290912447238137765)
                  ·
                    refine ⟨1049441492046083857150831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597021290912447238137765 1049441492046083857150831)
                    ·
                      rfl

theorem cell22_3065670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3065670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065670 prefixEnd_3065670 := by exact prefixLift 3065670
  have htrace : WordTrace (prefixWord ++ tailWord_3065670) baseStart_3065670 baseEnd_3065670 := by
    simpa [prefixWord, tailWord_3065670, baseEnd_3065670] using wordTrace_append hprefix tailTrace_3065670
  have hstable : (prefixWord ++ tailWord_3065670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065670).length < 2 ^ (prefixWord ++ tailWord_3065670).sum := by decide
  have hdescent : baseEnd_3065670 < baseStart_3065670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065777 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_3065777 : Nat := 118140960795 + 3065777 * 2 ^ 59
def prefixEnd_3065777 : Nat := 4983230072969 + 3 ^ 40 * 3065777 * 2
def baseEnd_3065777 : Nat := 1049478120332771244725503

theorem tailTrace_3065777 : CollatzResearch.WordTrace tailWord_3065777 prefixEnd_3065777 1049478120332771244725503 := by
  unfold tailWord_3065777
  simp only [CollatzResearch.WordTrace]
  refine ⟨111818073414220996871339585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74545382276147331247559723 111818073414220996871339585)
  ·
    refine ⟨83863555060665747653504689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111818073414220996871339585 83863555060665747653504689)
    ·
      refine ⟨62897666295499310740128517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83863555060665747653504689 62897666295499310740128517)
      ·
        refine ⟨11793312430406120763774097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62897666295499310740128517 11793312430406120763774097)
        ·
          refine ⟨8844984322804590572830573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11793312430406120763774097 8844984322804590572830573)
          ·
            refine ⟨3316869121051721464811465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8844984322804590572830573 3316869121051721464811465)
            ·
              refine ⟨2487651840788791098608599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316869121051721464811465 2487651840788791098608599)
              ·
                refine ⟨3731477761183186647912899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487651840788791098608599 3731477761183186647912899)
                ·
                  refine ⟨5597216641774779971869349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731477761183186647912899 5597216641774779971869349)
                  ·
                    refine ⟨1049478120332771244725503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597216641774779971869349 1049478120332771244725503)
                    ·
                      rfl

theorem cell22_3065777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_3065777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065777 prefixEnd_3065777 := by exact prefixLift 3065777
  have htrace : WordTrace (prefixWord ++ tailWord_3065777) baseStart_3065777 baseEnd_3065777 := by
    simpa [prefixWord, tailWord_3065777, baseEnd_3065777] using wordTrace_append hprefix tailTrace_3065777
  have hstable : (prefixWord ++ tailWord_3065777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065777).length < 2 ^ (prefixWord ++ tailWord_3065777).sum := by decide
  have hdescent : baseEnd_3065777 < baseStart_3065777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065790 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_3065790 : Nat := 118140960795 + 3065790 * 2 ^ 59
def prefixEnd_3065790 : Nat := 4983230072969 + 3 ^ 40 * 3065790 * 2
def baseEnd_3065790 : Nat := 1049482570498443544150463

theorem tailTrace_3065790 : CollatzResearch.WordTrace tailWord_3065790 prefixEnd_3065790 1049482570498443544150463 := by
  unfold tailWord_3065790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977318445396737511445353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74545698375449266727708549 13977318445396737511445353)
  ·
    refine ⟨10482988834047553133584015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13977318445396737511445353 10482988834047553133584015)
    ·
      refine ⟨15724483251071329700376023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10482988834047553133584015 15724483251071329700376023)
      ·
        refine ⟨23586724876606994550564035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15724483251071329700376023 23586724876606994550564035)
        ·
          refine ⟨35380087314910491825846053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23586724876606994550564035 35380087314910491825846053)
          ·
            refine ⟨6633766371545717217346135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35380087314910491825846053 6633766371545717217346135)
            ·
              refine ⟨9950649557318575826019203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633766371545717217346135 9950649557318575826019203)
              ·
                refine ⟨14925974335977863739028805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950649557318575826019203 14925974335977863739028805)
                ·
                  refine ⟨2798620187995849451067901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14925974335977863739028805 2798620187995849451067901)
                  ·
                    refine ⟨1049482570498443544150463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798620187995849451067901 1049482570498443544150463)
                    ·
                      rfl

theorem cell22_3065790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_3065790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065790 prefixEnd_3065790 := by exact prefixLift 3065790
  have htrace : WordTrace (prefixWord ++ tailWord_3065790) baseStart_3065790 baseEnd_3065790 := by
    simpa [prefixWord, tailWord_3065790, baseEnd_3065790] using wordTrace_append hprefix tailTrace_3065790
  have hstable : (prefixWord ++ tailWord_3065790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065790).length < 2 ^ (prefixWord ++ tailWord_3065790).sum := by decide
  have hdescent : baseEnd_3065790 < baseStart_3065790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065826 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3065826 : Nat := 118140960795 + 3065826 * 2 ^ 59
def prefixEnd_3065826 : Nat := 4983230072969 + 3 ^ 40 * 3065826 * 2
def baseEnd_3065826 : Nat := 349831631344717150083451

theorem tailTrace_3065826 : CollatzResearch.WordTrace tailWord_3065826 prefixEnd_3065826 349831631344717150083451 := by
  unfold tailWord_3065826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27954965147760869559968333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74546573727362318826582221 27954965147760869559968333)
  ·
    refine ⟨10483111930410326084988125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27954965147760869559968333 10483111930410326084988125)
    ·
      refine ⟨3931166973903872281870547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10483111930410326084988125 3931166973903872281870547)
      ·
        refine ⟨5896750460855808422805821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931166973903872281870547 5896750460855808422805821)
        ·
          refine ⟨2211281422820928158552183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5896750460855808422805821 2211281422820928158552183)
          ·
            refine ⟨3316922134231392237828275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211281422820928158552183 3316922134231392237828275)
            ·
              refine ⟨4975383201347088356742413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316922134231392237828275 4975383201347088356742413)
              ·
                refine ⟨1865768700505158133778405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4975383201347088356742413 1865768700505158133778405)
                ·
                  refine ⟨349831631344717150083451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865768700505158133778405 349831631344717150083451)
                  ·
                    rfl

theorem cell22_3065826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3065826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065826 prefixEnd_3065826 := by exact prefixLift 3065826
  have htrace : WordTrace (prefixWord ++ tailWord_3065826) baseStart_3065826 baseEnd_3065826 := by
    simpa [prefixWord, tailWord_3065826, baseEnd_3065826] using wordTrace_append hprefix tailTrace_3065826
  have hstable : (prefixWord ++ tailWord_3065826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065826).length < 2 ^ (prefixWord ++ tailWord_3065826).sum := by decide
  have hdescent : baseEnd_3065826 < baseStart_3065826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065837 : List Nat := [1, 5, 1, 4, 2, 1, 8]
def baseStart_3065837 : Nat := 118140960795 + 3065837 * 2 ^ 59
def prefixEnd_3065837 : Nat := 4983230072969 + 3 ^ 40 * 3065837 * 2
def baseEnd_3065837 : Nat := 38870320724405595860197

theorem tailTrace_3065837 : CollatzResearch.WordTrace tailWord_3065837 prefixEnd_3065837 38870320724405595860197 := by
  unfold tailWord_3065837
  simp only [CollatzResearch.WordTrace]
  refine ⟨111820261794003627118523765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74546841196002418079015843 111820261794003627118523765)
  ·
    refine ⟨10483149543187840042361603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111820261794003627118523765 10483149543187840042361603)
    ·
      refine ⟨15724724314781760063542405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483149543187840042361603 15724724314781760063542405)
      ·
        refine ⟨2948385809021580011914201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15724724314781760063542405 2948385809021580011914201)
        ·
          refine ⟨2211289356766185008935651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948385809021580011914201 2211289356766185008935651)
          ·
            refine ⟨3316934035149277513403477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211289356766185008935651 3316934035149277513403477)
            ·
              refine ⟨38870320724405595860197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3316934035149277513403477 38870320724405595860197)
              ·
                rfl

theorem cell22_3065837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 8].length) (baseStart_3065837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065837 prefixEnd_3065837 := by exact prefixLift 3065837
  have htrace : WordTrace (prefixWord ++ tailWord_3065837) baseStart_3065837 baseEnd_3065837 := by
    simpa [prefixWord, tailWord_3065837, baseEnd_3065837] using wordTrace_append hprefix tailTrace_3065837
  have hstable : (prefixWord ++ tailWord_3065837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065837).length < 2 ^ (prefixWord ++ tailWord_3065837).sum := by decide
  have hdescent : baseEnd_3065837 < baseStart_3065837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065910 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_3065910 : Nat := 118140960795 + 3065910 * 2 ^ 59
def prefixEnd_3065910 : Nat := 4983230072969 + 3 ^ 40 * 3065910 * 2
def baseEnd_3065910 : Nat := 349841216316934410383365

theorem tailTrace_3065910 : CollatzResearch.WordTrace tailWord_3065910 prefixEnd_3065910 349841216316934410383365 := by
  unfold tailWord_3065910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6988932770171197536620699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74548616215159440390620789 6988932770171197536620699)
  ·
    refine ⟨10483399155256796304931049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6988932770171197536620699 10483399155256796304931049)
    ·
      refine ⟨7862549366442597228698287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10483399155256796304931049 7862549366442597228698287)
      ·
        refine ⟨11793824049663895843047431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862549366442597228698287 11793824049663895843047431)
        ·
          refine ⟨17690736074495843764571147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11793824049663895843047431 17690736074495843764571147)
          ·
            refine ⟨26536104111743765646856721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17690736074495843764571147 26536104111743765646856721)
            ·
              refine ⟨19902078083807824235142541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26536104111743765646856721 19902078083807824235142541)
              ·
                refine ⟨7463279281427934088178453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19902078083807824235142541 7463279281427934088178453)
                ·
                  refine ⟨349841216316934410383365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7463279281427934088178453 349841216316934410383365)
                  ·
                    rfl

theorem cell22_3065910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_3065910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3065910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3065910 prefixEnd_3065910 := by exact prefixLift 3065910
  have htrace : WordTrace (prefixWord ++ tailWord_3065910) baseStart_3065910 baseEnd_3065910 := by
    simpa [prefixWord, tailWord_3065910, baseEnd_3065910] using wordTrace_append hprefix tailTrace_3065910
  have hstable : (prefixWord ++ tailWord_3065910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065910).length < 2 ^ (prefixWord ++ tailWord_3065910).sum := by decide
  have hdescent : baseEnd_3065910 < baseStart_3065910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066139 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 1, 3]
def baseStart_3066139 : Nat := 118140960795 + 3066139 * 2 ^ 59
def prefixEnd_3066139 : Nat := 4983230072969 + 3 ^ 40 * 3066139 * 2
def baseEnd_3066139 : Nat := 1049602040330722967174393

theorem tailTrace_3066139 : CollatzResearch.WordTrace tailWord_3066139 prefixEnd_3066139 1049602040330722967174393 := by
  unfold tailWord_3066139
  simp only [CollatzResearch.WordTrace]
  refine ⟨111831276638909532696017471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74554184425939688464011647 111831276638909532696017471)
  ·
    refine ⟨167746914958364299044026207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111831276638909532696017471 167746914958364299044026207)
    ·
      refine ⟨251620372437546448566039311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167746914958364299044026207 251620372437546448566039311)
      ·
        refine ⟨377430558656319672849058967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251620372437546448566039311 377430558656319672849058967)
        ·
          refine ⟨566145837984479509273588451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377430558656319672849058967 566145837984479509273588451)
          ·
            refine ⟨849218756976719263910382677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566145837984479509273588451 849218756976719263910382677)
            ·
              refine ⟨9951782308320928873949797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 849218756976719263910382677 9951782308320928873949797)
              ·
                refine ⟨1865959182810174163865587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9951782308320928873949797 1865959182810174163865587)
                ·
                  refine ⟨2798938774215261245798381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865959182810174163865587 2798938774215261245798381)
                  ·
                    refine ⟨1049602040330722967174393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798938774215261245798381 1049602040330722967174393)
                    ·
                      rfl

theorem cell22_3066139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 3].length) (baseStart_3066139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066139 prefixEnd_3066139 := by exact prefixLift 3066139
  have htrace : WordTrace (prefixWord ++ tailWord_3066139) baseStart_3066139 baseEnd_3066139 := by
    simpa [prefixWord, tailWord_3066139, baseEnd_3066139] using wordTrace_append hprefix tailTrace_3066139
  have hstable : (prefixWord ++ tailWord_3066139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066139).length < 2 ^ (prefixWord ++ tailWord_3066139).sum := by decide
  have hdescent : baseEnd_3066139 < baseStart_3066139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066158 : List Nat := [4, 1, 3, 3, 2, 1, 2, 6]
def baseStart_3066158 : Nat := 118140960795 + 3066158 * 2 ^ 59
def prefixEnd_3066158 : Nat := 4983230072969 + 3 ^ 40 * 3066158 * 2
def baseEnd_3066158 : Nat := 116623171602112583438815

theorem tailTrace_3066158 : CollatzResearch.WordTrace tailWord_3066158 prefixEnd_3066158 116623171602112583438815 := by
  unfold tailWord_3066158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978996203230087367619891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74554646417227132627306085 13978996203230087367619891)
  ·
    refine ⟨20968494304845131051429837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13978996203230087367619891 20968494304845131051429837)
    ·
      refine ⟨7863185364316924144286189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20968494304845131051429837 7863185364316924144286189)
      ·
        refine ⟨2948694511618846554107321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7863185364316924144286189 2948694511618846554107321)
        ·
          refine ⟨2211520883714134915580491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948694511618846554107321 2211520883714134915580491)
          ·
            refine ⟨3317281325571202373370737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211520883714134915580491 3317281325571202373370737)
            ·
              refine ⟨2487960994178401780028053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3317281325571202373370737 2487960994178401780028053)
              ·
                refine ⟨116623171602112583438815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2487960994178401780028053 116623171602112583438815)
                ·
                  rfl

theorem cell22_3066158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_3066158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066158 prefixEnd_3066158 := by exact prefixLift 3066158
  have htrace : WordTrace (prefixWord ++ tailWord_3066158) baseStart_3066158 baseEnd_3066158 := by
    simpa [prefixWord, tailWord_3066158, baseEnd_3066158] using wordTrace_append hprefix tailTrace_3066158
  have hstable : (prefixWord ++ tailWord_3066158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066158).length < 2 ^ (prefixWord ++ tailWord_3066158).sum := by decide
  have hdescent : baseEnd_3066158 < baseStart_3066158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066195 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_3066195 : Nat := 118140960795 + 3066195 * 2 ^ 59
def prefixEnd_3066195 : Nat := 4983230072969 + 3 ^ 40 * 3066195 * 2
def baseEnd_3066195 : Nat := 1049621210275157487774221

theorem tailTrace_3066195 : CollatzResearch.WordTrace tailWord_3066195 prefixEnd_3066195 1049621210275157487774221 := by
  unfold tailWord_3066195
  simp only [CollatzResearch.WordTrace]
  refine ⟨111833319126706654260056039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74555546084471102840037359 111833319126706654260056039)
  ·
    refine ⟨167749978690059981390084059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111833319126706654260056039 167749978690059981390084059)
    ·
      refine ⟨251624968035089972085126089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167749978690059981390084059 251624968035089972085126089)
      ·
        refine ⟨188718726026317479063844567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251624968035089972085126089 188718726026317479063844567)
        ·
          refine ⟨283078089039476218595766851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188718726026317479063844567 283078089039476218595766851)
          ·
            refine ⟨424617133559214327893650277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283078089039476218595766851 424617133559214327893650277)
            ·
              refine ⟨79615712542352686480059427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424617133559214327893650277 79615712542352686480059427)
              ·
                refine ⟨119423568813529029720089141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79615712542352686480059427 119423568813529029720089141)
                ·
                  refine ⟨11195959576268346536258357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119423568813529029720089141 11195959576268346536258357)
                  ·
                    refine ⟨1049621210275157487774221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11195959576268346536258357 1049621210275157487774221)
                    ·
                      rfl

theorem cell22_3066195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_3066195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066195 prefixEnd_3066195 := by exact prefixLift 3066195
  have htrace : WordTrace (prefixWord ++ tailWord_3066195) baseStart_3066195 baseEnd_3066195 := by
    simpa [prefixWord, tailWord_3066195, baseEnd_3066195] using wordTrace_append hprefix tailTrace_3066195
  have hstable : (prefixWord ++ tailWord_3066195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066195).length < 2 ^ (prefixWord ++ tailWord_3066195).sum := by decide
  have hdescent : baseEnd_3066195 < baseStart_3066195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066212 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_3066212 : Nat := 118140960795 + 3066212 * 2 ^ 59
def prefixEnd_3066212 : Nat := 4983230072969 + 3 ^ 40 * 3066212 * 2
def baseEnd_3066212 : Nat := 1049627029722575110099169

theorem tailTrace_3066212 : CollatzResearch.WordTrace tailWord_3066212 prefixEnd_3066212 1049627029722575110099169 := by
  unfold tailWord_3066212
  simp only [CollatzResearch.WordTrace]
  refine ⟨55916969583822533081712445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74555959445096710775616593 55916969583822533081712445)
  ·
    refine ⟨20968863593933449905642167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55916969583822533081712445 20968863593933449905642167)
    ·
      refine ⟨31453295390900174858463251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20968863593933449905642167 31453295390900174858463251)
      ·
        refine ⟨47179943086350262287694877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31453295390900174858463251 47179943086350262287694877)
        ·
          refine ⟨17692478657381348357885579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47179943086350262287694877 17692478657381348357885579)
          ·
            refine ⟨26538717986072022536828369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17692478657381348357885579 26538717986072022536828369)
            ·
              refine ⟨19904038489554016902621277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26538717986072022536828369 19904038489554016902621277)
              ·
                refine ⟨7464014433582756338482979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19904038489554016902621277 7464014433582756338482979)
                ·
                  refine ⟨11196021650374134507724469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464014433582756338482979 11196021650374134507724469)
                  ·
                    refine ⟨1049627029722575110099169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11196021650374134507724469 1049627029722575110099169)
                    ·
                      rfl

theorem cell22_3066212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_3066212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066212 prefixEnd_3066212 := by exact prefixLift 3066212
  have htrace : WordTrace (prefixWord ++ tailWord_3066212) baseStart_3066212 baseEnd_3066212 := by
    simpa [prefixWord, tailWord_3066212, baseEnd_3066212] using wordTrace_append hprefix tailTrace_3066212
  have hstable : (prefixWord ++ tailWord_3066212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066212).length < 2 ^ (prefixWord ++ tailWord_3066212).sum := by decide
  have hdescent : baseEnd_3066212 < baseStart_3066212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066216 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_3066216 : Nat := 118140960795 + 3066216 * 2 ^ 59
def prefixEnd_3066216 : Nat := 4983230072969 + 3 ^ 40 * 3066216 * 2
def baseEnd_3066216 : Nat := 1049628399004320432999157

theorem tailTrace_3066216 : CollatzResearch.WordTrace tailWord_3066216 prefixEnd_3066216 1049628399004320432999157 := by
  unfold tailWord_3066216
  simp only [CollatzResearch.WordTrace]
  refine ⟨55917042529815287423285251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74556056706420383231047001 55917042529815287423285251)
  ·
    refine ⟨83875563794722931134927877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55917042529815287423285251 83875563794722931134927877)
    ·
      refine ⟨15726668211510549587798977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83875563794722931134927877 15726668211510549587798977)
      ·
        refine ⟨11795001158632912190849233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15726668211510549587798977 11795001158632912190849233)
        ·
          refine ⟨8846250868974684143136925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11795001158632912190849233 8846250868974684143136925)
          ·
            refine ⟨3317344075865506553676347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8846250868974684143136925 3317344075865506553676347)
            ·
              refine ⟨4976016113798259830514521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317344075865506553676347 4976016113798259830514521)
              ·
                refine ⟨3732012085348694872885891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976016113798259830514521 3732012085348694872885891)
                ·
                  refine ⟨5598018128023042309328837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732012085348694872885891 5598018128023042309328837)
                  ·
                    refine ⟨1049628399004320432999157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598018128023042309328837 1049628399004320432999157)
                    ·
                      rfl

theorem cell22_3066216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_3066216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066216 prefixEnd_3066216 := by exact prefixLift 3066216
  have htrace : WordTrace (prefixWord ++ tailWord_3066216) baseStart_3066216 baseEnd_3066216 := by
    simpa [prefixWord, tailWord_3066216, baseEnd_3066216] using wordTrace_append hprefix tailTrace_3066216
  have hstable : (prefixWord ++ tailWord_3066216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066216).length < 2 ^ (prefixWord ++ tailWord_3066216).sum := by decide
  have hdescent : baseEnd_3066216 < baseStart_3066216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066229 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3066229 : Nat := 118140960795 + 3066229 * 2 ^ 59
def prefixEnd_3066229 : Nat := 4983230072969 + 3 ^ 40 * 3066229 * 2
def baseEnd_3066229 : Nat := 1049632849169992732424117

theorem tailTrace_3066229 : CollatzResearch.WordTrace tailWord_3066229 prefixEnd_3066229 1049632849169992732424117 := by
  unfold tailWord_3066229
  simp only [CollatzResearch.WordTrace]
  refine ⟨111834559208583478066793741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74556372805722318711195827 111834559208583478066793741)
  ·
    refine ⟨41937959703218804275047653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111834559208583478066793741 41937959703218804275047653)
    ·
      refine ⟨7863367444353525801571435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41937959703218804275047653 7863367444353525801571435)
      ·
        refine ⟨11795051166530288702357153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863367444353525801571435 11795051166530288702357153)
        ·
          refine ⟨8846288374897716526767865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11795051166530288702357153 8846288374897716526767865)
          ·
            refine ⟨6634716281173287395075899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8846288374897716526767865 6634716281173287395075899)
            ·
              refine ⟨9952074421759931092613849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634716281173287395075899 9952074421759931092613849)
              ·
                refine ⟨7464055816319948319460387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9952074421759931092613849 7464055816319948319460387)
                ·
                  refine ⟨11196083724479922479190581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464055816319948319460387 11196083724479922479190581)
                  ·
                    refine ⟨1049632849169992732424117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11196083724479922479190581 1049632849169992732424117)
                    ·
                      rfl

theorem cell22_3066229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3066229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066229 prefixEnd_3066229 := by exact prefixLift 3066229
  have htrace : WordTrace (prefixWord ++ tailWord_3066229) baseStart_3066229 baseEnd_3066229 := by
    simpa [prefixWord, tailWord_3066229, baseEnd_3066229] using wordTrace_append hprefix tailTrace_3066229
  have hstable : (prefixWord ++ tailWord_3066229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066229).length < 2 ^ (prefixWord ++ tailWord_3066229).sum := by decide
  have hdescent : baseEnd_3066229 < baseStart_3066229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066308 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3066308 : Nat := 118140960795 + 3066308 * 2 ^ 59
def prefixEnd_3066308 : Nat := 4983230072969 + 3 ^ 40 * 3066308 * 2
def baseEnd_3066308 : Nat := 1049659892484462859698875

theorem tailTrace_3066308 : CollatzResearch.WordTrace tailWord_3066308 prefixEnd_3066308 1049659892484462859698875 := by
  unfold tailWord_3066308
  simp only [CollatzResearch.WordTrace]
  refine ⟨55918720287648637279459789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74558293716864849705946385 55918720287648637279459789)
  ·
    refine ⟨20969520107868238979797421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55918720287648637279459789 20969520107868238979797421)
    ·
      refine ⟨7863570040450589617424033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20969520107868238979797421 7863570040450589617424033)
      ·
        refine ⟨5897677530337942213068025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7863570040450589617424033 5897677530337942213068025)
        ·
          refine ⟨4423258147753456659801019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5897677530337942213068025 4423258147753456659801019)
          ·
            refine ⟨6634887221630184989701529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423258147753456659801019 6634887221630184989701529)
            ·
              refine ⟨4976165416222638742276147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634887221630184989701529 4976165416222638742276147)
              ·
                refine ⟨7464248124333958113414221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976165416222638742276147 7464248124333958113414221)
                ·
                  refine ⟨2799093046625234292530333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7464248124333958113414221 2799093046625234292530333)
                  ·
                    refine ⟨1049659892484462859698875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799093046625234292530333 1049659892484462859698875)
                    ·
                      rfl

theorem cell22_3066308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3066308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066308 prefixEnd_3066308 := by exact prefixLift 3066308
  have htrace : WordTrace (prefixWord ++ tailWord_3066308) baseStart_3066308 baseEnd_3066308 := by
    simpa [prefixWord, tailWord_3066308, baseEnd_3066308] using wordTrace_append hprefix tailTrace_3066308
  have hstable : (prefixWord ++ tailWord_3066308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066308).length < 2 ^ (prefixWord ++ tailWord_3066308).sum := by decide
  have hdescent : baseEnd_3066308 < baseStart_3066308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066347 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_3066347 : Nat := 118140960795 + 3066347 * 2 ^ 59
def prefixEnd_3066347 : Nat := 4983230072969 + 3 ^ 40 * 3066347 * 2
def baseEnd_3066347 : Nat := 1049673242981479757973755

theorem tailTrace_3066347 : CollatzResearch.WordTrace tailWord_3066347 prefixEnd_3066347 1049673242981479757973755 := by
  unfold tailWord_3066347
  simp only [CollatzResearch.WordTrace]
  refine ⟨111838863022155984219589295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74559242014770656146392863 111838863022155984219589295)
  ·
    refine ⟨167758294533233976329383943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111838863022155984219589295 167758294533233976329383943)
    ·
      refine ⟨251637441799850964494075915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167758294533233976329383943 251637441799850964494075915)
      ·
        refine ⟨377456162699776446741113873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251637441799850964494075915 377456162699776446741113873)
        ·
          refine ⟨283092122024832335055835405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377456162699776446741113873 283092122024832335055835405)
          ·
            refine ⟨106159545759312125645938277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283092122024832335055835405 106159545759312125645938277)
            ·
              refine ⟨19904914829871023558613427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106159545759312125645938277 19904914829871023558613427)
              ·
                refine ⟨29857372244806535337920141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19904914829871023558613427 29857372244806535337920141)
                ·
                  refine ⟨11196514591802450751720053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29857372244806535337920141 11196514591802450751720053)
                  ·
                    refine ⟨1049673242981479757973755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11196514591802450751720053 1049673242981479757973755)
                    ·
                      rfl

theorem cell22_3066347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_3066347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066347 prefixEnd_3066347 := by exact prefixLift 3066347
  have htrace : WordTrace (prefixWord ++ tailWord_3066347) baseStart_3066347 baseEnd_3066347 := by
    simpa [prefixWord, tailWord_3066347, baseEnd_3066347] using wordTrace_append hprefix tailTrace_3066347
  have hstable : (prefixWord ++ tailWord_3066347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066347).length < 2 ^ (prefixWord ++ tailWord_3066347).sum := by decide
  have hdescent : baseEnd_3066347 < baseStart_3066347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066362 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_3066362 : Nat := 118140960795 + 3066362 * 2 ^ 59
def prefixEnd_3066362 : Nat := 4983230072969 + 3 ^ 40 * 3066362 * 2
def baseEnd_3066362 : Nat := 1049678377788024718848709

theorem tailTrace_3066362 : CollatzResearch.WordTrace tailWord_3066362 prefixEnd_3066362 1049678377788024718848709 := by
  unfold tailWord_3066362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27959852529275410445346335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74559606744734427854256893 27959852529275410445346335)
  ·
    refine ⟨41939778793913115668019503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27959852529275410445346335 41939778793913115668019503)
    ·
      refine ⟨62909668190869673502029255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41939778793913115668019503 62909668190869673502029255)
      ·
        refine ⟨94364502286304510253043883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62909668190869673502029255 94364502286304510253043883)
        ·
          refine ⟨141546753429456765379565825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94364502286304510253043883 141546753429456765379565825)
          ·
            refine ⟨106160065072092574034674369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141546753429456765379565825 106160065072092574034674369)
            ·
              refine ⟨79620048804069430526005777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106160065072092574034674369 79620048804069430526005777)
              ·
                refine ⟨59715036603052072894504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79620048804069430526005777 59715036603052072894504333)
                ·
                  refine ⟨22393138726144527335439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59715036603052072894504333 22393138726144527335439125)
                  ·
                    refine ⟨1049678377788024718848709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22393138726144527335439125 1049678377788024718848709)
                    ·
                      rfl

theorem cell22_3066362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_3066362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066362 prefixEnd_3066362 := by exact prefixLift 3066362
  have htrace : WordTrace (prefixWord ++ tailWord_3066362) baseStart_3066362 baseEnd_3066362 := by
    simpa [prefixWord, tailWord_3066362, baseEnd_3066362] using wordTrace_append hprefix tailTrace_3066362
  have hstable : (prefixWord ++ tailWord_3066362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066362).length < 2 ^ (prefixWord ++ tailWord_3066362).sum := by decide
  have hdescent : baseEnd_3066362 < baseStart_3066362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066396 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3066396 : Nat := 118140960795 + 3066396 * 2 ^ 59
def prefixEnd_3066396 : Nat := 4983230072969 + 3 ^ 40 * 3066396 * 2
def baseEnd_3066396 : Nat := 1049690016682859963498605

theorem tailTrace_3066396 : CollatzResearch.WordTrace tailWord_3066396 prefixEnd_3066396 1049690016682859963498605 := by
  unfold tailWord_3066396
  simp only [CollatzResearch.WordTrace]
  refine ⟨55920325099489232794061521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74560433465985643725415361 55920325099489232794061521)
  ·
    refine ⟨41940243824616924595546141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55920325099489232794061521 41940243824616924595546141)
    ·
      refine ⟨15727591434231346723329803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41940243824616924595546141 15727591434231346723329803)
      ·
        refine ⟨23591387151347020084994705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15727591434231346723329803 23591387151347020084994705)
        ·
          refine ⟨17693540363510265063746029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23591387151347020084994705 17693540363510265063746029)
          ·
            refine ⟨6635077636316349398904761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17693540363510265063746029 6635077636316349398904761)
            ·
              refine ⟨4976308227237262049178571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635077636316349398904761 4976308227237262049178571)
              ·
                refine ⟨7464462340855893073767857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976308227237262049178571 7464462340855893073767857)
                ·
                  refine ⟨5598346755641919805325893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7464462340855893073767857 5598346755641919805325893)
                  ·
                    refine ⟨1049690016682859963498605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598346755641919805325893 1049690016682859963498605)
                    ·
                      rfl

theorem cell22_3066396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3066396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066396 prefixEnd_3066396 := by exact prefixLift 3066396
  have htrace : WordTrace (prefixWord ++ tailWord_3066396) baseStart_3066396 baseEnd_3066396 := by
    simpa [prefixWord, tailWord_3066396, baseEnd_3066396] using wordTrace_append hprefix tailTrace_3066396
  have hstable : (prefixWord ++ tailWord_3066396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066396).length < 2 ^ (prefixWord ++ tailWord_3066396).sum := by decide
  have hdescent : baseEnd_3066396 < baseStart_3066396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066535 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 6]
def baseStart_3066535 : Nat := 118140960795 + 3066535 * 2 ^ 59
def prefixEnd_3066535 : Nat := 4983230072969 + 3 ^ 40 * 3066535 * 2
def baseEnd_3066535 : Nat := 349912533074503311424393

theorem tailTrace_3066535 : CollatzResearch.WordTrace tailWord_3066535 prefixEnd_3066535 349912533074503311424393 := by
  unfold tailWord_3066535
  simp only [CollatzResearch.WordTrace]
  refine ⟨111845719945474892327433059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74563813296983261551622039 111845719945474892327433059)
  ·
    refine ⟨167768579918212338491149589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111845719945474892327433059 167768579918212338491149589)
    ·
      refine ⟨7864152183666203366772637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167768579918212338491149589 7864152183666203366772637)
      ·
        refine ⟨2949057068874826262539739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7864152183666203366772637 2949057068874826262539739)
        ·
          refine ⟨4423585603312239393809609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949057068874826262539739 4423585603312239393809609)
          ·
            refine ⟨3317689202484179545357207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423585603312239393809609 3317689202484179545357207)
            ·
              refine ⟨4976533803726269318035811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317689202484179545357207 4976533803726269318035811)
              ·
                refine ⟨7464800705589403977053717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976533803726269318035811 7464800705589403977053717)
                ·
                  refine ⟨349912533074503311424393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7464800705589403977053717 349912533074503311424393)
                  ·
                    rfl

theorem cell22_3066535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 6].length) (baseStart_3066535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066535 prefixEnd_3066535 := by exact prefixLift 3066535
  have htrace : WordTrace (prefixWord ++ tailWord_3066535) baseStart_3066535 baseEnd_3066535 := by
    simpa [prefixWord, tailWord_3066535, baseEnd_3066535] using wordTrace_append hprefix tailTrace_3066535
  have hstable : (prefixWord ++ tailWord_3066535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066535).length < 2 ^ (prefixWord ++ tailWord_3066535).sum := by decide
  have hdescent : baseEnd_3066535 < baseStart_3066535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066591 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 5]
def baseStart_3066591 : Nat := 118140960795 + 3066591 * 2 ^ 59
def prefixEnd_3066591 : Nat := 4983230072969 + 3 ^ 40 * 3066591 * 2
def baseEnd_3066591 : Nat := 349918923055981484957669

theorem tailTrace_3066591 : CollatzResearch.WordTrace tailWord_3066591 prefixEnd_3066591 349918923055981484957669 := by
  unfold tailWord_3066591
  simp only [CollatzResearch.WordTrace]
  refine ⟨111847762433272013891471627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74565174955514675927647751 111847762433272013891471627)
  ·
    refine ⟨167771643649908020837207441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111847762433272013891471627 167771643649908020837207441)
    ·
      refine ⟨125828732737431015627905581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167771643649908020837207441 125828732737431015627905581)
      ·
        refine ⟨47185774776536630860464593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125828732737431015627905581 47185774776536630860464593)
        ·
          refine ⟨35389331082402473145348445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47185774776536630860464593 35389331082402473145348445)
          ·
            refine ⟨13270999155900927429505667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35389331082402473145348445 13270999155900927429505667)
            ·
              refine ⟨19906498733851391144258501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13270999155900927429505667 19906498733851391144258501)
              ·
                refine ⟨3732468512597135839548469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19906498733851391144258501 3732468512597135839548469)
                ·
                  refine ⟨349918923055981484957669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3732468512597135839548469 349918923055981484957669)
                  ·
                    rfl

theorem cell22_3066591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 5].length) (baseStart_3066591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066591 prefixEnd_3066591 := by exact prefixLift 3066591
  have htrace : WordTrace (prefixWord ++ tailWord_3066591) baseStart_3066591 baseEnd_3066591 := by
    simpa [prefixWord, tailWord_3066591, baseEnd_3066591] using wordTrace_append hprefix tailTrace_3066591
  have hstable : (prefixWord ++ tailWord_3066591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066591).length < 2 ^ (prefixWord ++ tailWord_3066591).sum := by decide
  have hdescent : baseEnd_3066591 < baseStart_3066591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066606 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3066606 : Nat := 118140960795 + 3066606 * 2 ^ 59
def prefixEnd_3066606 : Nat := 4983230072969 + 3 ^ 40 * 3066606 * 2
def baseEnd_3066606 : Nat := 1049761903974489415747961

theorem tailTrace_3066606 : CollatzResearch.WordTrace tailWord_3066606 prefixEnd_3066606 1049761903974489415747961 := by
  unfold tailWord_3066606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981038691027208931658459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74565539685478447635511781 13981038691027208931658459)
  ·
    refine ⟨20971558036540813397487689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13981038691027208931658459 20971558036540813397487689)
    ·
      refine ⟨15728668527405610048115767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20971558036540813397487689 15728668527405610048115767)
      ·
        refine ⟨23593002791108415072173651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15728668527405610048115767 23593002791108415072173651)
        ·
          refine ⟨35389504186662622608260477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23593002791108415072173651 35389504186662622608260477)
          ·
            refine ⟨13271064069998483478097679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35389504186662622608260477 13271064069998483478097679)
            ·
              refine ⟨19906596104997725217146519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13271064069998483478097679 19906596104997725217146519)
              ·
                refine ⟨29859894157496587825719779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19906596104997725217146519 29859894157496587825719779)
                ·
                  refine ⟨44789841236244881738579669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29859894157496587825719779 44789841236244881738579669)
                  ·
                    refine ⟨1049761903974489415747961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44789841236244881738579669 1049761903974489415747961)
                    ·
                      rfl

theorem cell22_3066606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3066606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066606 prefixEnd_3066606 := by exact prefixLift 3066606
  have htrace : WordTrace (prefixWord ++ tailWord_3066606) baseStart_3066606 baseEnd_3066606 := by
    simpa [prefixWord, tailWord_3066606, baseEnd_3066606] using wordTrace_append hprefix tailTrace_3066606
  have hstable : (prefixWord ++ tailWord_3066606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066606).length < 2 ^ (prefixWord ++ tailWord_3066606).sum := by decide
  have hdescent : baseEnd_3066606 < baseStart_3066606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066621 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3066621 : Nat := 118140960795 + 3066621 * 2 ^ 59
def prefixEnd_3066621 : Nat := 4983230072969 + 3 ^ 40 * 3066621 * 2
def baseEnd_3066621 : Nat := 1049767038781034376622915

theorem tailTrace_3066621 : CollatzResearch.WordTrace tailWord_3066621 prefixEnd_3066621 1049767038781034376622915 := by
  unfold tailWord_3066621
  simp only [CollatzResearch.WordTrace]
  refine ⟨111848856623163329015063717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74565904415442219343375811 111848856623163329015063717)
  ·
    refine ⟨20971660616843124190324447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111848856623163329015063717 20971660616843124190324447)
    ·
      refine ⟨31457490925264686285486671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20971660616843124190324447 31457490925264686285486671)
      ·
        refine ⟨47186236387897029428230007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31457490925264686285486671 47186236387897029428230007)
        ·
          refine ⟨70779354581845544142345011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47186236387897029428230007 70779354581845544142345011)
          ·
            refine ⟨106169031872768316213517517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70779354581845544142345011 106169031872768316213517517)
            ·
              refine ⟨39813386952288118580069069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106169031872768316213517517 39813386952288118580069069)
              ·
                refine ⟨14930020107108044467525901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39813386952288118580069069 14930020107108044467525901)
                ·
                  refine ⟨5598757540165516675322213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14930020107108044467525901 5598757540165516675322213)
                  ·
                    refine ⟨1049767038781034376622915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598757540165516675322213 1049767038781034376622915)
                    ·
                      rfl

theorem cell22_3066621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3066621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066621 prefixEnd_3066621 := by exact prefixLift 3066621
  have htrace : WordTrace (prefixWord ++ tailWord_3066621) baseStart_3066621 baseEnd_3066621 := by
    simpa [prefixWord, tailWord_3066621, baseEnd_3066621] using wordTrace_append hprefix tailTrace_3066621
  have hstable : (prefixWord ++ tailWord_3066621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066621).length < 2 ^ (prefixWord ++ tailWord_3066621).sum := by decide
  have hdescent : baseEnd_3066621 < baseStart_3066621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066642 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_3066642 : Nat := 118140960795 + 3066642 * 2 ^ 59
def prefixEnd_3066642 : Nat := 4983230072969 + 3 ^ 40 * 3066642 * 2
def baseEnd_3066642 : Nat := 349924742503399107282617

theorem tailTrace_3066642 : CollatzResearch.WordTrace tailWord_3066642 prefixEnd_3066642 349924742503399107282617 := by
  unfold tailWord_3066642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27962405639021812400394545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74566415037391499734385453 27962405639021812400394545)
  ·
    refine ⟨20971804229266359300295909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27962405639021812400394545 20971804229266359300295909)
    ·
      refine ⟨3932213292987442368805483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20971804229266359300295909 3932213292987442368805483)
      ·
        refine ⟨5898319939481163553208225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932213292987442368805483 5898319939481163553208225)
        ·
          refine ⟨4423739954610872664906169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898319939481163553208225 4423739954610872664906169)
          ·
            refine ⟨3317804965958154498679627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423739954610872664906169 3317804965958154498679627)
            ·
              refine ⟨4976707448937231748019441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317804965958154498679627 4976707448937231748019441)
              ·
                refine ⟨3732530586702923811014581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976707448937231748019441 3732530586702923811014581)
                ·
                  refine ⟨349924742503399107282617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3732530586702923811014581 349924742503399107282617)
                  ·
                    rfl

theorem cell22_3066642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_3066642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066642 prefixEnd_3066642 := by exact prefixLift 3066642
  have htrace : WordTrace (prefixWord ++ tailWord_3066642) baseStart_3066642 baseEnd_3066642 := by
    simpa [prefixWord, tailWord_3066642, baseEnd_3066642] using wordTrace_append hprefix tailTrace_3066642
  have hstable : (prefixWord ++ tailWord_3066642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066642).length < 2 ^ (prefixWord ++ tailWord_3066642).sum := by decide
  have hdescent : baseEnd_3066642 < baseStart_3066642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066760 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_3066760 : Nat := 118140960795 + 3066760 * 2 ^ 59
def prefixEnd_3066760 : Nat := 4983230072969 + 3 ^ 40 * 3066760 * 2
def baseEnd_3066760 : Nat := 349938207107228115799163

theorem tailTrace_3066760 : CollatzResearch.WordTrace tailWord_3066760 prefixEnd_3066760 349938207107228115799163 := by
  unfold tailWord_3066760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55926963184829877877186867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74569284246439837169582489 55926963184829877877186867)
  ·
    refine ⟨83890444777244816815780301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55926963184829877877186867 83890444777244816815780301)
    ·
      refine ⟨31458916791466806305917613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83890444777244816815780301 31458916791466806305917613)
      ·
        refine ⟨11797093796800052364719105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31458916791466806305917613 11797093796800052364719105)
        ·
          refine ⟨8847820347600039273539329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11797093796800052364719105 8847820347600039273539329)
          ·
            refine ⟨6635865260700029455154497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8847820347600039273539329 6635865260700029455154497)
            ·
              refine ⟨4976898945525022091365873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635865260700029455154497 4976898945525022091365873)
              ·
                refine ⟨3732674209143766568524405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976898945525022091365873 3732674209143766568524405)
                ·
                  refine ⟨349938207107228115799163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3732674209143766568524405 349938207107228115799163)
                  ·
                    rfl

theorem cell22_3066760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_3066760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066760 prefixEnd_3066760 := by exact prefixLift 3066760
  have htrace : WordTrace (prefixWord ++ tailWord_3066760) baseStart_3066760 baseEnd_3066760 := by
    simpa [prefixWord, tailWord_3066760, baseEnd_3066760] using wordTrace_append hprefix tailTrace_3066760
  have hstable : (prefixWord ++ tailWord_3066760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066760).length < 2 ^ (prefixWord ++ tailWord_3066760).sum := by decide
  have hdescent : baseEnd_3066760 < baseStart_3066760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066773 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3066773 : Nat := 118140960795 + 3066773 * 2 ^ 59
def prefixEnd_3066773 : Nat := 4983230072969 + 3 ^ 40 * 3066773 * 2
def baseEnd_3066773 : Nat := 1049819071487356646822449

theorem tailTrace_3066773 : CollatzResearch.WordTrace tailWord_3066773 prefixEnd_3066773 1049819071487356646822449 := by
  unfold tailWord_3066773
  simp only [CollatzResearch.WordTrace]
  refine ⟨111854400518612658974596973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74569600345741772649731315 111854400518612658974596973)
  ·
    refine ⟨41945400194479747115473865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111854400518612658974596973 41945400194479747115473865)
    ·
      refine ⟨31459050145859810336605399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41945400194479747115473865 31459050145859810336605399)
      ·
        refine ⟨47188575218789715504908099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31459050145859810336605399 47188575218789715504908099)
        ·
          refine ⟨70782862828184573257362149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47188575218789715504908099 70782862828184573257362149)
          ·
            refine ⟨13271786780284607485755403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70782862828184573257362149 13271786780284607485755403)
            ·
              refine ⟨19907680170426911228633105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13271786780284607485755403 19907680170426911228633105)
              ·
                refine ⟨14930760127820183421474829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19907680170426911228633105 14930760127820183421474829)
                ·
                  refine ⟨5599035047932568783053061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14930760127820183421474829 5599035047932568783053061)
                  ·
                    refine ⟨1049819071487356646822449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599035047932568783053061 1049819071487356646822449)
                    ·
                      rfl

theorem cell22_3066773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3066773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066773 prefixEnd_3066773 := by exact prefixLift 3066773
  have htrace : WordTrace (prefixWord ++ tailWord_3066773) baseStart_3066773 baseEnd_3066773 := by
    simpa [prefixWord, tailWord_3066773, baseEnd_3066773] using wordTrace_append hprefix tailTrace_3066773
  have hstable : (prefixWord ++ tailWord_3066773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066773).length < 2 ^ (prefixWord ++ tailWord_3066773).sum := by decide
  have hdescent : baseEnd_3066773 < baseStart_3066773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066788 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_3066788 : Nat := 118140960795 + 3066788 * 2 ^ 59
def prefixEnd_3066788 : Nat := 4983230072969 + 3 ^ 40 * 3066788 * 2
def baseEnd_3066788 : Nat := 349941402097967202565801

theorem tailTrace_3066788 : CollatzResearch.WordTrace tailWord_3066788 prefixEnd_3066788 349941402097967202565801 := by
  unfold tailWord_3066788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55927473806779158268196509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74569965075705544357595345 55927473806779158268196509)
  ·
    refine ⟨20972802677542184350573691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55927473806779158268196509 20972802677542184350573691)
    ·
      refine ⟨31459204016313276525860537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20972802677542184350573691 31459204016313276525860537)
      ·
        refine ⟨23594403012234957394395403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31459204016313276525860537 23594403012234957394395403)
        ·
          refine ⟨35391604518352436091593105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23594403012234957394395403 35391604518352436091593105)
          ·
            refine ⟨26543703388764327068694829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35391604518352436091593105 26543703388764327068694829)
            ·
              refine ⟨9953888770786622650760561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26543703388764327068694829 9953888770786622650760561)
              ·
                refine ⟨7465416578089966988070421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9953888770786622650760561 7465416578089966988070421)
                ·
                  refine ⟨349941402097967202565801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7465416578089966988070421 349941402097967202565801)
                  ·
                    rfl

theorem cell22_3066788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_3066788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066788 prefixEnd_3066788 := by exact prefixLift 3066788
  have htrace : WordTrace (prefixWord ++ tailWord_3066788) baseStart_3066788 baseEnd_3066788 := by
    simpa [prefixWord, tailWord_3066788, baseEnd_3066788] using wordTrace_append hprefix tailTrace_3066788
  have hstable : (prefixWord ++ tailWord_3066788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066788).length < 2 ^ (prefixWord ++ tailWord_3066788).sum := by decide
  have hdescent : baseEnd_3066788 < baseStart_3066788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066837 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_3066837 : Nat := 118140960795 + 3066837 * 2 ^ 59
def prefixEnd_3066837 : Nat := 4983230072969 + 3 ^ 40 * 3066837 * 2
def baseEnd_3066837 : Nat := 1049840979995281813222253

theorem tailTrace_3066837 : CollatzResearch.WordTrace tailWord_3066837 prefixEnd_3066837 1049840979995281813222253 := by
  unfold tailWord_3066837
  simp only [CollatzResearch.WordTrace]
  refine ⟨111856734790380797904926765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74571156526920531936617843 111856734790380797904926765)
  ·
    refine ⟨41946275546392799214347537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111856734790380797904926765 41946275546392799214347537)
    ·
      refine ⟨31459706659794599410760653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41946275546392799214347537 31459706659794599410760653)
      ·
        refine ⟨11797389997422974779035245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31459706659794599410760653 11797389997422974779035245)
        ·
          refine ⟨4424021249033615542138217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11797389997422974779035245 4424021249033615542138217)
          ·
            refine ⟨3318015936775211656603663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4424021249033615542138217 3318015936775211656603663)
            ·
              refine ⟨4977023905162817484905495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318015936775211656603663 4977023905162817484905495)
              ·
                refine ⟨7465535857744226227358243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977023905162817484905495 7465535857744226227358243)
                ·
                  refine ⟨11198303786616339341037365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465535857744226227358243 11198303786616339341037365)
                  ·
                    refine ⟨1049840979995281813222253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11198303786616339341037365 1049840979995281813222253)
                    ·
                      rfl

theorem cell22_3066837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_3066837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066837 prefixEnd_3066837 := by exact prefixLift 3066837
  have htrace : WordTrace (prefixWord ++ tailWord_3066837) baseStart_3066837 baseEnd_3066837 := by
    simpa [prefixWord, tailWord_3066837, baseEnd_3066837] using wordTrace_append hprefix tailTrace_3066837
  have hstable : (prefixWord ++ tailWord_3066837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066837).length < 2 ^ (prefixWord ++ tailWord_3066837).sum := by decide
  have hdescent : baseEnd_3066837 < baseStart_3066837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066869 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3066869 : Nat := 118140960795 + 3066869 * 2 ^ 59
def prefixEnd_3066869 : Nat := 4983230072969 + 3 ^ 40 * 3066869 * 2
def baseEnd_3066869 : Nat := 1049851934249244396422155

theorem tailTrace_3066869 : CollatzResearch.WordTrace tailWord_3066869 prefixEnd_3066869 1049851934249244396422155 := by
  unfold tailWord_3066869
  simp only [CollatzResearch.WordTrace]
  refine ⟨111857901926264867370091661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74571934617509911580061107 111857901926264867370091661)
  ·
    refine ⟨41946713222349325263784373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111857901926264867370091661 41946713222349325263784373)
    ·
      refine ⟨3932504364595249243479785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41946713222349325263784373 3932504364595249243479785)
      ·
        refine ⟨2949378273446436932609839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3932504364595249243479785 2949378273446436932609839)
        ·
          refine ⟨4424067410169655398914759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949378273446436932609839 4424067410169655398914759)
          ·
            refine ⟨6636101115254483098372139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424067410169655398914759 6636101115254483098372139)
            ·
              refine ⟨9954151672881724647558209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636101115254483098372139 9954151672881724647558209)
              ·
                refine ⟨7465613754661293485668657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954151672881724647558209 7465613754661293485668657)
                ·
                  refine ⟨5599210315995970114251493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465613754661293485668657 5599210315995970114251493)
                  ·
                    refine ⟨1049851934249244396422155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599210315995970114251493 1049851934249244396422155)
                    ·
                      rfl

theorem cell22_3066869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3066869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066869 prefixEnd_3066869 := by exact prefixLift 3066869
  have htrace : WordTrace (prefixWord ++ tailWord_3066869) baseStart_3066869 baseEnd_3066869 := by
    simpa [prefixWord, tailWord_3066869, baseEnd_3066869] using wordTrace_append hprefix tailTrace_3066869
  have hstable : (prefixWord ++ tailWord_3066869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066869).length < 2 ^ (prefixWord ++ tailWord_3066869).sum := by decide
  have hdescent : baseEnd_3066869 < baseStart_3066869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066942 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_3066942 : Nat := 118140960795 + 3066942 * 2 ^ 59
def prefixEnd_3066942 : Nat := 4983230072969 + 3 ^ 40 * 3066942 * 2
def baseEnd_3066942 : Nat := 1049876923641096539346931

theorem tailTrace_3066942 : CollatzResearch.WordTrace tailWord_3066942 prefixEnd_3066942 1049876923641096539346931 := by
  unfold tailWord_3066942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982570556875050104687385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74573709636666933891666053 13982570556875050104687385)
  ·
    refine ⟨10486927917656287578515539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13982570556875050104687385 10486927917656287578515539)
    ·
      refine ⟨15730391876484431367773309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10486927917656287578515539 15730391876484431367773309)
      ·
        refine ⟨5898896953681661762914991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15730391876484431367773309 5898896953681661762914991)
        ·
          refine ⟨8848345430522492644372487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898896953681661762914991 8848345430522492644372487)
          ·
            refine ⟨13272518145783738966558731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8848345430522492644372487 13272518145783738966558731)
            ·
              refine ⟨19908777218675608449838097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13272518145783738966558731 19908777218675608449838097)
              ·
                refine ⟨14931582914006706337378573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19908777218675608449838097 14931582914006706337378573)
                ·
                  refine ⟨5599343592752514876516965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14931582914006706337378573 5599343592752514876516965)
                  ·
                    refine ⟨1049876923641096539346931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599343592752514876516965 1049876923641096539346931)
                    ·
                      rfl

theorem cell22_3066942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_3066942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066942 prefixEnd_3066942 := by exact prefixLift 3066942
  have htrace : WordTrace (prefixWord ++ tailWord_3066942) baseStart_3066942 baseEnd_3066942 := by
    simpa [prefixWord, tailWord_3066942, baseEnd_3066942] using wordTrace_append hprefix tailTrace_3066942
  have hstable : (prefixWord ++ tailWord_3066942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066942).length < 2 ^ (prefixWord ++ tailWord_3066942).sum := by decide
  have hdescent : baseEnd_3066942 < baseStart_3066942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066957 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3066957 : Nat := 118140960795 + 3066957 * 2 ^ 59
def prefixEnd_3066957 : Nat := 4983230072969 + 3 ^ 40 * 3066957 * 2
def baseEnd_3066957 : Nat := 349960686149213833407295

theorem tailTrace_3066957 : CollatzResearch.WordTrace tailWord_3066957 prefixEnd_3066957 349960686149213833407295 := by
  unfold tailWord_3066957
  simp only [CollatzResearch.WordTrace]
  refine ⟨111861111549946058399295125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74574074366630705599530083 111861111549946058399295125)
  ·
    refine ⟨5243489603903721487466959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111861111549946058399295125 5243489603903721487466959)
    ·
      refine ⟨7865234405855582231200439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5243489603903721487466959 7865234405855582231200439)
      ·
        refine ⟨11797851608783373346800659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7865234405855582231200439 11797851608783373346800659)
        ·
          refine ⟨17696777413175060020200989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797851608783373346800659 17696777413175060020200989)
          ·
            refine ⟨6636291529940647507575371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17696777413175060020200989 6636291529940647507575371)
            ·
              refine ⟨9954437294910971261363057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636291529940647507575371 9954437294910971261363057)
              ·
                refine ⟨7465827971183228446022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954437294910971261363057 7465827971183228446022293)
                ·
                  refine ⟨349960686149213833407295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7465827971183228446022293 349960686149213833407295)
                  ·
                    rfl

theorem cell22_3066957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3066957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066957 prefixEnd_3066957 := by exact prefixLift 3066957
  have htrace : WordTrace (prefixWord ++ tailWord_3066957) baseStart_3066957 baseEnd_3066957 := by
    simpa [prefixWord, tailWord_3066957, baseEnd_3066957] using wordTrace_append hprefix tailTrace_3066957
  have hstable : (prefixWord ++ tailWord_3066957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066957).length < 2 ^ (prefixWord ++ tailWord_3066957).sum := by decide
  have hdescent : baseEnd_3066957 < baseStart_3066957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066970 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_3066970 : Nat := 118140960795 + 3066970 * 2 ^ 59
def prefixEnd_3066970 : Nat := 4983230072969 + 3 ^ 40 * 3066970 * 2
def baseEnd_3066970 : Nat := 1049886508613313799646845

theorem tailTrace_3066970 : CollatzResearch.WordTrace tailWord_3066970 prefixEnd_3066970 1049886508613313799646845 := by
  unfold tailWord_3066970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27965396424724740404879591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74574390465932641079678909 27965396424724740404879591)
  ·
    refine ⟨41948094637087110607319387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27965396424724740404879591 41948094637087110607319387)
    ·
      refine ⟨62922141955630665910979081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41948094637087110607319387 62922141955630665910979081)
      ·
        refine ⟨47191606466722999433234311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62922141955630665910979081 47191606466722999433234311)
        ·
          refine ⟨70787409700084499149851467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47191606466722999433234311 70787409700084499149851467)
          ·
            refine ⟨106181114550126748724777201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70787409700084499149851467 106181114550126748724777201)
            ·
              refine ⟨79635835912595061543582901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106181114550126748724777201 79635835912595061543582901)
              ·
                refine ⟨7465859616805787019710897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79635835912595061543582901 7465859616805787019710897)
                ·
                  refine ⟨5599394712604340264783173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465859616805787019710897 5599394712604340264783173)
                  ·
                    refine ⟨1049886508613313799646845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599394712604340264783173 1049886508613313799646845)
                    ·
                      rfl

theorem cell22_3066970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_3066970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066970 prefixEnd_3066970 := by exact prefixLift 3066970
  have htrace : WordTrace (prefixWord ++ tailWord_3066970) baseStart_3066970 baseEnd_3066970 := by
    simpa [prefixWord, tailWord_3066970, baseEnd_3066970] using wordTrace_append hprefix tailTrace_3066970
  have hstable : (prefixWord ++ tailWord_3066970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066970).length < 2 ^ (prefixWord ++ tailWord_3066970).sum := by decide
  have hdescent : baseEnd_3066970 < baseStart_3066970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066972 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3066972 : Nat := 118140960795 + 3066972 * 2 ^ 59
def prefixEnd_3066972 : Nat := 4983230072969 + 3 ^ 40 * 3066972 * 2
def baseEnd_3066972 : Nat := 1049887193254186461096839

theorem tailTrace_3066972 : CollatzResearch.WordTrace tailWord_3066972 prefixEnd_3066972 1049887193254186461096839 := by
  unfold tailWord_3066972
  simp only [CollatzResearch.WordTrace]
  refine ⟨55930829322445857980545585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74574439096594477307394113 55930829322445857980545585)
  ·
    refine ⟨41948121991834393485409189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55930829322445857980545585 41948121991834393485409189)
    ·
      refine ⟨7865272873468948778514223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41948121991834393485409189 7865272873468948778514223)
      ·
        refine ⟨11797909310203423167771335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7865272873468948778514223 11797909310203423167771335)
        ·
          refine ⟨17696863965305134751657003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797909310203423167771335 17696863965305134751657003)
          ·
            refine ⟨26545295947957702127485505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17696863965305134751657003 26545295947957702127485505)
            ·
              refine ⟨19908971960968276595614129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26545295947957702127485505 19908971960968276595614129)
              ·
                refine ⟨14931728970726207446710597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19908971960968276595614129 14931728970726207446710597)
                ·
                  refine ⟨2799699182011163896258237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14931728970726207446710597 2799699182011163896258237)
                  ·
                    refine ⟨1049887193254186461096839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799699182011163896258237 1049887193254186461096839)
                    ·
                      rfl

theorem cell22_3066972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3066972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066972 prefixEnd_3066972 := by exact prefixLift 3066972
  have htrace : WordTrace (prefixWord ++ tailWord_3066972) baseStart_3066972 baseEnd_3066972 := by
    simpa [prefixWord, tailWord_3066972, baseEnd_3066972] using wordTrace_append hprefix tailTrace_3066972
  have hstable : (prefixWord ++ tailWord_3066972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066972).length < 2 ^ (prefixWord ++ tailWord_3066972).sum := by decide
  have hdescent : baseEnd_3066972 < baseStart_3066972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066989 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_3066989 : Nat := 118140960795 + 3066989 * 2 ^ 59
def prefixEnd_3066989 : Nat := 4983230072969 + 3 ^ 40 * 3066989 * 2
def baseEnd_3066989 : Nat := 1049893012701604083421787

theorem tailTrace_3066989 : CollatzResearch.WordTrace tailWord_3066989 prefixEnd_3066989 1049893012701604083421787 := by
  unfold tailWord_3066989
  simp only [CollatzResearch.WordTrace]
  refine ⟨111862278685830127864460021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74574852457220085242973347 111862278685830127864460021)
  ·
    refine ⟨10487088626796574487293127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111862278685830127864460021 10487088626796574487293127)
    ·
      refine ⟨15730632940194861730939691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10487088626796574487293127 15730632940194861730939691)
      ·
        refine ⟨23595949410292292596409537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15730632940194861730939691 23595949410292292596409537)
        ·
          refine ⟨17696962057719219447307153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23595949410292292596409537 17696962057719219447307153)
          ·
            refine ⟨13272721543289414585480365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17696962057719219447307153 13272721543289414585480365)
            ·
              refine ⟨4977270578733530469555137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13272721543289414585480365 4977270578733530469555137)
              ·
                refine ⟨3732952934050147852166353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977270578733530469555137 3732952934050147852166353)
                ·
                  refine ⟨2799714700537610889124765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732952934050147852166353 2799714700537610889124765)
                  ·
                    refine ⟨1049893012701604083421787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799714700537610889124765 1049893012701604083421787)
                    ·
                      rfl

theorem cell22_3066989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_3066989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3066989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3066989 prefixEnd_3066989 := by exact prefixLift 3066989
  have htrace : WordTrace (prefixWord ++ tailWord_3066989) baseStart_3066989 baseEnd_3066989 := by
    simpa [prefixWord, tailWord_3066989, baseEnd_3066989] using wordTrace_append hprefix tailTrace_3066989
  have hstable : (prefixWord ++ tailWord_3066989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066989).length < 2 ^ (prefixWord ++ tailWord_3066989).sum := by decide
  have hdescent : baseEnd_3066989 < baseStart_3066989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067017 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_3067017 : Nat := 118140960795 + 3067017 * 2 ^ 59
def prefixEnd_3067017 : Nat := 4983230072969 + 3 ^ 40 * 3067017 * 2
def baseEnd_3067017 : Nat := 1049902597673821343721701

theorem tailTrace_3067017 : CollatzResearch.WordTrace tailWord_3067017 prefixEnd_3067017 1049902597673821343721701 := by
  unfold tailWord_3067017
  simp only [CollatzResearch.WordTrace]
  refine ⟨111863299929728688646479305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74575533286485792430986203 111863299929728688646479305)
  ·
    refine ⟨83897474947296516484859479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111863299929728688646479305 83897474947296516484859479)
    ·
      refine ⟨125846212420944774727289219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83897474947296516484859479 125846212420944774727289219)
      ·
        refine ⟨188769318631417162090933829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125846212420944774727289219 188769318631417162090933829)
        ·
          refine ⟨35394247243390717892050093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188769318631417162090933829 35394247243390717892050093)
          ·
            refine ⟨13272842716271519209518785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35394247243390717892050093 13272842716271519209518785)
            ·
              refine ⟨9954632037203639407139089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13272842716271519209518785 9954632037203639407139089)
              ·
                refine ⟨7465974027902729555354317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954632037203639407139089 7465974027902729555354317)
                ·
                  refine ⟨2799740260463523583257869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7465974027902729555354317 2799740260463523583257869)
                  ·
                    refine ⟨1049902597673821343721701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799740260463523583257869 1049902597673821343721701)
                    ·
                      rfl

theorem cell22_3067017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_3067017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067017 prefixEnd_3067017 := by exact prefixLift 3067017
  have htrace : WordTrace (prefixWord ++ tailWord_3067017) baseStart_3067017 baseEnd_3067017 := by
    simpa [prefixWord, tailWord_3067017, baseEnd_3067017] using wordTrace_append hprefix tailTrace_3067017
  have hstable : (prefixWord ++ tailWord_3067017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067017).length < 2 ^ (prefixWord ++ tailWord_3067017).sum := by decide
  have hdescent : baseEnd_3067017 < baseStart_3067017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067047 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 7]
def baseStart_3067047 : Nat := 118140960795 + 3067047 * 2 ^ 59
def prefixEnd_3067047 : Nat := 4983230072969 + 3 ^ 40 * 3067047 * 2
def baseEnd_3067047 : Nat := 349970955762303755157203

theorem tailTrace_3067047 : CollatzResearch.WordTrace tailWord_3067047 prefixEnd_3067047 349970955762303755157203 := by
  unfold tailWord_3067047
  simp only [CollatzResearch.WordTrace]
  refine ⟨111864394119620003770071395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74576262746413335846714263 111864394119620003770071395)
  ·
    refine ⟨167796591179430005655107093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111864394119620003770071395 167796591179430005655107093)
    ·
      refine ⟨7865465211535781515083145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167796591179430005655107093 7865465211535781515083145)
      ·
        refine ⟨5899098908651836136312359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7865465211535781515083145 5899098908651836136312359)
        ·
          refine ⟨8848648362977754204468539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5899098908651836136312359 8848648362977754204468539)
          ·
            refine ⟨13272972544466631306702809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8848648362977754204468539 13272972544466631306702809)
            ·
              refine ⟨9954729408349973480027107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13272972544466631306702809 9954729408349973480027107)
              ·
                refine ⟨14932094112524960220040661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9954729408349973480027107 14932094112524960220040661)
                ·
                  refine ⟨349970955762303755157203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14932094112524960220040661 349970955762303755157203)
                  ·
                    rfl

theorem cell22_3067047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_3067047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067047 prefixEnd_3067047 := by exact prefixLift 3067047
  have htrace : WordTrace (prefixWord ++ tailWord_3067047) baseStart_3067047 baseEnd_3067047 := by
    simpa [prefixWord, tailWord_3067047, baseEnd_3067047] using wordTrace_append hprefix tailTrace_3067047
  have hstable : (prefixWord ++ tailWord_3067047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067047).length < 2 ^ (prefixWord ++ tailWord_3067047).sum := by decide
  have hdescent : baseEnd_3067047 < baseStart_3067047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067139 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 2, 4]
def baseStart_3067139 : Nat := 118140960795 + 3067139 * 2 ^ 59
def prefixEnd_3067139 : Nat := 4983230072969 + 3 ^ 40 * 3067139 * 2
def baseEnd_3067139 : Nat := 1049944360767053692171327

theorem tailTrace_3067139 : CollatzResearch.WordTrace tailWord_3067139 prefixEnd_3067139 1049944360767053692171327 := by
  unfold tailWord_3067139
  simp only [CollatzResearch.WordTrace]
  refine ⟨111867749635286703482420471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74578499756857802321613647 111867749635286703482420471)
  ·
    refine ⟨167801624452930055223630707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111867749635286703482420471 167801624452930055223630707)
    ·
      refine ⟨251702436679395082835446061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167801624452930055223630707 251702436679395082835446061)
      ·
        refine ⟨94388413754773156063292273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251702436679395082835446061 94388413754773156063292273)
        ·
          refine ⟨70791310316079867047469205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94388413754773156063292273 70791310316079867047469205)
          ·
            refine ⟨3318342671066243767850119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70791310316079867047469205 3318342671066243767850119)
            ·
              refine ⟨4977514006599365651775179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318342671066243767850119 4977514006599365651775179)
              ·
                refine ⟨7466271009899048477662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977514006599365651775179 7466271009899048477662769)
                ·
                  refine ⟨5599703257424286358247077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466271009899048477662769 5599703257424286358247077)
                  ·
                    refine ⟨1049944360767053692171327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599703257424286358247077 1049944360767053692171327)
                    ·
                      rfl

theorem cell22_3067139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4].length) (baseStart_3067139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067139 prefixEnd_3067139 := by exact prefixLift 3067139
  have htrace : WordTrace (prefixWord ++ tailWord_3067139) baseStart_3067139 baseEnd_3067139 := by
    simpa [prefixWord, tailWord_3067139, baseEnd_3067139] using wordTrace_append hprefix tailTrace_3067139
  have hstable : (prefixWord ++ tailWord_3067139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067139).length < 2 ^ (prefixWord ++ tailWord_3067139).sum := by decide
  have hdescent : baseEnd_3067139 < baseStart_3067139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067257 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_3067257 : Nat := 118140960795 + 3067257 * 2 ^ 59
def prefixEnd_3067257 : Nat := 4983230072969 + 3 ^ 40 * 3067257 * 2
def baseEnd_3067257 : Nat := 1049984754578540717720965

theorem tailTrace_3067257 : CollatzResearch.WordTrace tailWord_3067257 prefixEnd_3067257 1049984754578540717720965 := by
  unfold tailWord_3067257
  simp only [CollatzResearch.WordTrace]
  refine ⟨111872053448859209635216025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74581368965906139756810683 111872053448859209635216025)
  ·
    refine ⟨83904040086644407226412019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111872053448859209635216025 83904040086644407226412019)
    ·
      refine ⟨125856060129966610839618029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83904040086644407226412019 125856060129966610839618029)
      ·
        refine ⟨47196022548737479064856761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125856060129966610839618029 47196022548737479064856761)
        ·
          refine ⟨35397016911553109298642571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47196022548737479064856761 35397016911553109298642571)
          ·
            refine ⟨53095525367329663947963857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35397016911553109298642571 53095525367329663947963857)
            ·
              refine ⟨39821644025497247960972893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53095525367329663947963857 39821644025497247960972893)
              ·
                refine ⟨14933116509561467985364835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39821644025497247960972893 14933116509561467985364835)
                ·
                  refine ⟨22399674764342201978047253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14933116509561467985364835 22399674764342201978047253)
                  ·
                    refine ⟨1049984754578540717720965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22399674764342201978047253 1049984754578540717720965)
                    ·
                      rfl

theorem cell22_3067257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_3067257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067257 prefixEnd_3067257 := by exact prefixLift 3067257
  have htrace : WordTrace (prefixWord ++ tailWord_3067257) baseStart_3067257 baseEnd_3067257 := by
    simpa [prefixWord, tailWord_3067257, baseEnd_3067257] using wordTrace_append hprefix tailTrace_3067257
  have hstable : (prefixWord ++ tailWord_3067257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067257).length < 2 ^ (prefixWord ++ tailWord_3067257).sum := by decide
  have hdescent : baseEnd_3067257 < baseStart_3067257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067272 : List Nat := [2, 1, 3, 3, 1, 12]
def baseStart_3067272 : Nat := 118140960795 + 3067272 * 2 ^ 59
def prefixEnd_3067272 : Nat := 4983230072969 + 3 ^ 40 * 3067272 * 2
def baseEnd_3067272 : Nat := 12962838140556613315999

theorem tailTrace_3067272 : CollatzResearch.WordTrace tailWord_3067272 prefixEnd_3067272 12962838140556613315999 := by
  unfold tailWord_3067272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55936300271902433598506035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74581733695869911464674713 55936300271902433598506035)
  ·
    refine ⟨83904450407853650397759053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55936300271902433598506035 83904450407853650397759053)
    ·
      refine ⟨31464168902945118899159645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83904450407853650397759053 31464168902945118899159645)
      ·
        refine ⟨11799063338604419587184867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31464168902945118899159645 11799063338604419587184867)
        ·
          refine ⟨17698595007906629380777301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799063338604419587184867 17698595007906629380777301)
          ·
            refine ⟨12962838140556613315999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17698595007906629380777301 12962838140556613315999)
            ·
              rfl

theorem cell22_3067272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 12].length) (baseStart_3067272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067272 prefixEnd_3067272 := by exact prefixLift 3067272
  have htrace : WordTrace (prefixWord ++ tailWord_3067272) baseStart_3067272 baseEnd_3067272 := by
    simpa [prefixWord, tailWord_3067272, baseEnd_3067272] using wordTrace_append hprefix tailTrace_3067272
  have hstable : (prefixWord ++ tailWord_3067272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067272).length < 2 ^ (prefixWord ++ tailWord_3067272).sum := by decide
  have hdescent : baseEnd_3067272 < baseStart_3067272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067276 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_3067276 : Nat := 118140960795 + 3067276 * 2 ^ 59
def prefixEnd_3067276 : Nat := 4983230072969 + 3 ^ 40 * 3067276 * 2
def baseEnd_3067276 : Nat := 1049991258666831001495907

theorem tailTrace_3067276 : CollatzResearch.WordTrace tailWord_3067276 prefixEnd_3067276 1049991258666831001495907 := by
  unfold tailWord_3067276
  simp only [CollatzResearch.WordTrace]
  refine ⟨55936373217895187940078841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74581830957193583920105121 55936373217895187940078841)
  ·
    refine ⟨41952279913421390955059131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55936373217895187940078841 41952279913421390955059131)
    ·
      refine ⟨62928419870132086432588697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41952279913421390955059131 62928419870132086432588697)
      ·
        refine ⟨47196314902599064824441523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62928419870132086432588697 47196314902599064824441523)
        ·
          refine ⟨70794472353898597236662285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47196314902599064824441523 70794472353898597236662285)
          ·
            refine ⟨26547927132711973963748357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70794472353898597236662285 26547927132711973963748357)
            ·
              refine ⟨4977736337383495118202817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26547927132711973963748357 4977736337383495118202817)
              ·
                refine ⟨3733302253037621338652113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977736337383495118202817 3733302253037621338652113)
                ·
                  refine ⟨2799976689778216003989085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733302253037621338652113 2799976689778216003989085)
                  ·
                    refine ⟨1049991258666831001495907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799976689778216003989085 1049991258666831001495907)
                    ·
                      rfl

theorem cell22_3067276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_3067276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067276 prefixEnd_3067276 := by exact prefixLift 3067276
  have htrace : WordTrace (prefixWord ++ tailWord_3067276) baseStart_3067276 baseEnd_3067276 := by
    simpa [prefixWord, tailWord_3067276, baseEnd_3067276] using wordTrace_append hprefix tailTrace_3067276
  have hstable : (prefixWord ++ tailWord_3067276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067276).length < 2 ^ (prefixWord ++ tailWord_3067276).sum := by decide
  have hdescent : baseEnd_3067276 < baseStart_3067276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067278 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_3067278 : Nat := 118140960795 + 3067278 * 2 ^ 59
def prefixEnd_3067278 : Nat := 4983230072969 + 3 ^ 40 * 3067278 * 2
def baseEnd_3067278 : Nat := 349997314435901220981967

theorem tailTrace_3067278 : CollatzResearch.WordTrace tailWord_3067278 prefixEnd_3067278 349997314435901220981967 := by
  unfold tailWord_3067278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984102422722891277716311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74581879587855420147820325 13984102422722891277716311)
  ·
    refine ⟨20976153634084336916574467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13984102422722891277716311 20976153634084336916574467)
    ·
      refine ⟨31464230451126505374861701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20976153634084336916574467 31464230451126505374861701)
      ·
        refine ⟨5899543209586219757786569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31464230451126505374861701 5899543209586219757786569)
        ·
          refine ⟨4424657407189664818339927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899543209586219757786569 4424657407189664818339927)
          ·
            refine ⟨6636986110784497227509891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424657407189664818339927 6636986110784497227509891)
            ·
              refine ⟨9955479166176745841264837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636986110784497227509891 9955479166176745841264837)
              ·
                refine ⟨1866652343658139845237157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9955479166176745841264837 1866652343658139845237157)
                ·
                  refine ⟨349997314435901220981967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866652343658139845237157 349997314435901220981967)
                  ·
                    rfl

theorem cell22_3067278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_3067278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067278 prefixEnd_3067278 := by exact prefixLift 3067278
  have htrace : WordTrace (prefixWord ++ tailWord_3067278) baseStart_3067278 baseEnd_3067278 := by
    simpa [prefixWord, tailWord_3067278, baseEnd_3067278] using wordTrace_append hprefix tailTrace_3067278
  have hstable : (prefixWord ++ tailWord_3067278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067278).length < 2 ^ (prefixWord ++ tailWord_3067278).sum := by decide
  have hdescent : baseEnd_3067278 < baseStart_3067278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067287 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3067287 : Nat := 118140960795 + 3067287 * 2 ^ 59
def prefixEnd_3067287 : Nat := 4983230072969 + 3 ^ 40 * 3067287 * 2
def baseEnd_3067287 : Nat := 1049995024191630639470873

theorem tailTrace_3067287 : CollatzResearch.WordTrace tailWord_3067287 prefixEnd_3067287 1049995024191630639470873 := by
  unfold tailWord_3067287
  simp only [CollatzResearch.WordTrace]
  refine ⟨111873147638750524758808115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74582098425833683172538743 111873147638750524758808115)
  ·
    refine ⟨167809721458125787138212173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111873147638750524758808115 167809721458125787138212173)
    ·
      refine ⟨62928645546797170176829565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167809721458125787138212173 62928645546797170176829565)
      ·
        refine ⟨23598242080048938816311087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62928645546797170176829565 23598242080048938816311087)
        ·
          refine ⟨35397363120073408224466631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23598242080048938816311087 35397363120073408224466631)
          ·
            refine ⟨53096044680110112336699947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35397363120073408224466631 53096044680110112336699947)
            ·
              refine ⟨79644067020165168505049921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53096044680110112336699947 79644067020165168505049921)
              ·
                refine ⟨59733050265123876378787441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79644067020165168505049921 59733050265123876378787441)
                ·
                  refine ⟨44799787698842907284090581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59733050265123876378787441 44799787698842907284090581)
                  ·
                    refine ⟨1049995024191630639470873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44799787698842907284090581 1049995024191630639470873)
                    ·
                      rfl

theorem cell22_3067287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3067287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067287 prefixEnd_3067287 := by exact prefixLift 3067287
  have htrace : WordTrace (prefixWord ++ tailWord_3067287) baseStart_3067287 baseEnd_3067287 := by
    simpa [prefixWord, tailWord_3067287, baseEnd_3067287] using wordTrace_append hprefix tailTrace_3067287
  have hstable : (prefixWord ++ tailWord_3067287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067287).length < 2 ^ (prefixWord ++ tailWord_3067287).sum := by decide
  have hdescent : baseEnd_3067287 < baseStart_3067287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067289 : List Nat := [1, 2, 1, 2, 1, 7, 1, 7]
def baseStart_3067289 : Nat := 118140960795 + 3067289 * 2 ^ 59
def prefixEnd_3067289 : Nat := 4983230072969 + 3 ^ 40 * 3067289 * 2
def baseEnd_3067289 : Nat := 116666189870278144546763

theorem tailTrace_3067289 : CollatzResearch.WordTrace tailWord_3067289 prefixEnd_3067289 116666189870278144546763 := by
  unfold tailWord_3067289
  simp only [CollatzResearch.WordTrace]
  refine ⟨111873220584743279100380921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74582147056495519400253947 111873220584743279100380921)
  ·
    refine ⟨83904915438557459325285691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111873220584743279100380921 83904915438557459325285691)
    ·
      refine ⟨125857373157836188987928537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83904915438557459325285691 125857373157836188987928537)
      ·
        refine ⟨94393029868377141740946403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125857373157836188987928537 94393029868377141740946403)
        ·
          refine ⟨141589544802565712611419605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94393029868377141740946403 141589544802565712611419605)
          ·
            refine ⟨3318504956310133889330147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 141589544802565712611419605 3318504956310133889330147)
            ·
              refine ⟨4977757434465200833995221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318504956310133889330147 4977757434465200833995221)
              ·
                refine ⟨116666189870278144546763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4977757434465200833995221 116666189870278144546763)
                ·
                  rfl

theorem cell22_3067289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 7].length) (baseStart_3067289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067289 prefixEnd_3067289 := by exact prefixLift 3067289
  have htrace : WordTrace (prefixWord ++ tailWord_3067289) baseStart_3067289 baseEnd_3067289 := by
    simpa [prefixWord, tailWord_3067289, baseEnd_3067289] using wordTrace_append hprefix tailTrace_3067289
  have hstable : (prefixWord ++ tailWord_3067289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067289).length < 2 ^ (prefixWord ++ tailWord_3067289).sum := by decide
  have hdescent : baseEnd_3067289 < baseStart_3067289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067338 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_3067338 : Nat := 118140960795 + 3067338 * 2 ^ 59
def prefixEnd_3067338 : Nat := 4983230072969 + 3 ^ 40 * 3067338 * 2
def baseEnd_3067338 : Nat := 1050012482533883506445717

theorem tailTrace_3067338 : CollatzResearch.WordTrace tailWord_3067338 prefixEnd_3067338 1050012482533883506445717 := by
  unfold tailWord_3067338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27968751940391440117228667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74583338507710506979276445 27968751940391440117228667)
  ·
    refine ⟨41953127910587160175843001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27968751940391440117228667 41953127910587160175843001)
    ·
      refine ⟨31464845932940370131882251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41953127910587160175843001 31464845932940370131882251)
      ·
        refine ⟨47197268899410555197823377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31464845932940370131882251 47197268899410555197823377)
        ·
          refine ⟨35397951674557916398367533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47197268899410555197823377 35397951674557916398367533)
          ·
            refine ⟨13274231877959218649387825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35397951674557916398367533 13274231877959218649387825)
            ·
              refine ⟨9955673908469413987040869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13274231877959218649387825 9955673908469413987040869)
              ·
                refine ⟨1866688857838015122570163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9955673908469413987040869 1866688857838015122570163)
                ·
                  refine ⟨2800033286757022683855245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866688857838015122570163 2800033286757022683855245)
                  ·
                    refine ⟨1050012482533883506445717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2800033286757022683855245 1050012482533883506445717)
                    ·
                      rfl

theorem cell22_3067338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_3067338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067338 prefixEnd_3067338 := by exact prefixLift 3067338
  have htrace : WordTrace (prefixWord ++ tailWord_3067338) baseStart_3067338 baseEnd_3067338 := by
    simpa [prefixWord, tailWord_3067338, baseEnd_3067338] using wordTrace_append hprefix tailTrace_3067338
  have hstable : (prefixWord ++ tailWord_3067338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067338).length < 2 ^ (prefixWord ++ tailWord_3067338).sum := by decide
  have hdescent : baseEnd_3067338 < baseStart_3067338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067349 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3067349 : Nat := 118140960795 + 3067349 * 2 ^ 59
def prefixEnd_3067349 : Nat := 4983230072969 + 3 ^ 40 * 3067349 * 2
def baseEnd_3067349 : Nat := 1050016248058683144420683

theorem tailTrace_3067349 : CollatzResearch.WordTrace tailWord_3067349 prefixEnd_3067349 1050016248058683144420683 := by
  unfold tailWord_3067349
  simp only [CollatzResearch.WordTrace]
  refine ⟨111875408964525909347565101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74583605976350606231710067 111875408964525909347565101)
  ·
    refine ⟨41953278361697216005336913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111875408964525909347565101 41953278361697216005336913)
    ·
      refine ⟨31464958771272912004002685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41953278361697216005336913 31464958771272912004002685)
      ·
        refine ⟨11799359539227342001501007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31464958771272912004002685 11799359539227342001501007)
        ·
          refine ⟨17699039308841013002251511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799359539227342001501007 17699039308841013002251511)
          ·
            refine ⟨26548558963261519503377267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17699039308841013002251511 26548558963261519503377267)
            ·
              refine ⟨39822838444892279255065901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26548558963261519503377267 39822838444892279255065901)
              ·
                refine ⟨14933564416834604720649713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39822838444892279255065901 14933564416834604720649713)
                ·
                  refine ⟨11200173312625953540487285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14933564416834604720649713 11200173312625953540487285)
                  ·
                    refine ⟨1050016248058683144420683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11200173312625953540487285 1050016248058683144420683)
                    ·
                      rfl

theorem cell22_3067349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3067349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067349 prefixEnd_3067349 := by exact prefixLift 3067349
  have htrace : WordTrace (prefixWord ++ tailWord_3067349) baseStart_3067349 baseEnd_3067349 := by
    simpa [prefixWord, tailWord_3067349, baseEnd_3067349] using wordTrace_append hprefix tailTrace_3067349
  have hstable : (prefixWord ++ tailWord_3067349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067349).length < 2 ^ (prefixWord ++ tailWord_3067349).sum := by decide
  have hdescent : baseEnd_3067349 < baseStart_3067349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067364 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_3067364 : Nat := 118140960795 + 3067364 * 2 ^ 59
def prefixEnd_3067364 : Nat := 4983230072969 + 3 ^ 40 * 3067364 * 2
def baseEnd_3067364 : Nat := 1050021382865228105295637

theorem tailTrace_3067364 : CollatzResearch.WordTrace tailWord_3067364 prefixEnd_3067364 1050021382865228105295637 := by
  unfold tailWord_3067364
  simp only [CollatzResearch.WordTrace]
  refine ⟨55937978029735783454680573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74583970706314377939574097 55937978029735783454680573)
  ·
    refine ⟨20976741761150918795505215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55937978029735783454680573 20976741761150918795505215)
    ·
      refine ⟨31465112641726378193257823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20976741761150918795505215 31465112641726378193257823)
      ·
        refine ⟨47197668962589567289886735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31465112641726378193257823 47197668962589567289886735)
        ·
          refine ⟨70796503443884350934830103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47197668962589567289886735 70796503443884350934830103)
          ·
            refine ⟨106194755165826526402245155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70796503443884350934830103 106194755165826526402245155)
            ·
              refine ⟨159292132748739789603367733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106194755165826526402245155 159292132748739789603367733)
              ·
                refine ⟨14933637445194355275315725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159292132748739789603367733 14933637445194355275315725)
                ·
                  refine ⟨5600114041947883228243397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14933637445194355275315725 5600114041947883228243397)
                  ·
                    refine ⟨1050021382865228105295637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600114041947883228243397 1050021382865228105295637)
                    ·
                      rfl

theorem cell22_3067364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_3067364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067364 prefixEnd_3067364 := by exact prefixLift 3067364
  have htrace : WordTrace (prefixWord ++ tailWord_3067364) baseStart_3067364 baseEnd_3067364 := by
    simpa [prefixWord, tailWord_3067364, baseEnd_3067364] using wordTrace_append hprefix tailTrace_3067364
  have hstable : (prefixWord ++ tailWord_3067364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067364).length < 2 ^ (prefixWord ++ tailWord_3067364).sum := by decide
  have hdescent : baseEnd_3067364 < baseStart_3067364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067409 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3067409 : Nat := 118140960795 + 3067409 * 2 ^ 59
def prefixEnd_3067409 : Nat := 4983230072969 + 3 ^ 40 * 3067409 * 2
def baseEnd_3067409 : Nat := 1050036787284862987920499

theorem tailTrace_3067409 : CollatzResearch.WordTrace tailWord_3067409 prefixEnd_3067409 1050036787284862987920499 := by
  unfold tailWord_3067409
  simp only [CollatzResearch.WordTrace]
  refine ⟨111877597344308539594749281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74585064896205693063166187 111877597344308539594749281)
  ·
    refine ⟨83908198008231404696061961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111877597344308539594749281 83908198008231404696061961)
    ·
      refine ⟨62931148506173553522046471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83908198008231404696061961 62931148506173553522046471)
      ·
        refine ⟨94396722759260330283069707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62931148506173553522046471 94396722759260330283069707)
        ·
          refine ⟨141595084138890495424604561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94396722759260330283069707 141595084138890495424604561)
          ·
            refine ⟨106196313104167871568453421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141595084138890495424604561 106196313104167871568453421)
            ·
              refine ⟨39823617414062951838170033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106196313104167871568453421 39823617414062951838170033)
              ·
                refine ⟨29867713060547213878627525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39823617414062951838170033 29867713060547213878627525)
                ·
                  refine ⟨5600196198852602602242661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29867713060547213878627525 5600196198852602602242661)
                  ·
                    refine ⟨1050036787284862987920499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600196198852602602242661 1050036787284862987920499)
                    ·
                      rfl

theorem cell22_3067409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3067409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067409 prefixEnd_3067409 := by exact prefixLift 3067409
  have htrace : WordTrace (prefixWord ++ tailWord_3067409) baseStart_3067409 baseEnd_3067409 := by
    simpa [prefixWord, tailWord_3067409, baseEnd_3067409] using wordTrace_append hprefix tailTrace_3067409
  have hstable : (prefixWord ++ tailWord_3067409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067409).length < 2 ^ (prefixWord ++ tailWord_3067409).sum := by decide
  have hdescent : baseEnd_3067409 < baseStart_3067409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067426 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3067426 : Nat := 118140960795 + 3067426 * 2 ^ 59
def prefixEnd_3067426 : Nat := 4983230072969 + 3 ^ 40 * 3067426 * 2
def baseEnd_3067426 : Nat := 1050042606732280610245447

theorem tailTrace_3067426 : CollatzResearch.WordTrace tailWord_3067426 prefixEnd_3067426 1050042606732280610245447 := by
  unfold tailWord_3067426
  simp only [CollatzResearch.WordTrace]
  refine ⟨27969554346311737874529533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74585478256831300998745421 27969554346311737874529533)
  ·
    refine ⟨10488582879866901702948575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27969554346311737874529533 10488582879866901702948575)
    ·
      refine ⟨15732874319800352554422863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10488582879866901702948575 15732874319800352554422863)
      ·
        refine ⟨23599311479700528831634295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15732874319800352554422863 23599311479700528831634295)
        ·
          refine ⟨35398967219550793247451443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23599311479700528831634295 35398967219550793247451443)
          ·
            refine ⟨53098450829326189871177165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35398967219550793247451443 53098450829326189871177165)
            ·
              refine ⟨19911919060997321201691437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53098450829326189871177165 19911919060997321201691437)
              ·
                refine ⟨7466969647873995450634289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19911919060997321201691437 7466969647873995450634289)
                ·
                  refine ⟨5600227235905496587975717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466969647873995450634289 5600227235905496587975717)
                  ·
                    refine ⟨1050042606732280610245447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600227235905496587975717 1050042606732280610245447)
                    ·
                      rfl

theorem cell22_3067426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3067426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067426 prefixEnd_3067426 := by exact prefixLift 3067426
  have htrace : WordTrace (prefixWord ++ tailWord_3067426) baseStart_3067426 baseEnd_3067426 := by
    simpa [prefixWord, tailWord_3067426, baseEnd_3067426] using wordTrace_append hprefix tailTrace_3067426
  have hstable : (prefixWord ++ tailWord_3067426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067426).length < 2 ^ (prefixWord ++ tailWord_3067426).sum := by decide
  have hdescent : baseEnd_3067426 < baseStart_3067426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067456 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_3067456 : Nat := 118140960795 + 3067456 * 2 ^ 59
def prefixEnd_3067456 : Nat := 4983230072969 + 3 ^ 40 * 3067456 * 2
def baseEnd_3067456 : Nat := 1050052876345370531995355

theorem tailTrace_3067456 : CollatzResearch.WordTrace tailWord_3067456 prefixEnd_3067456 1050052876345370531995355 := by
  unfold tailWord_3067456
  simp only [CollatzResearch.WordTrace]
  refine ⟨55939655787569133310855111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74586207716758844414473481 55939655787569133310855111)
  ·
    refine ⟨83909483681353699966282667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55939655787569133310855111 83909483681353699966282667)
    ·
      refine ⟨125864225522030549949424001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83909483681353699966282667 125864225522030549949424001)
      ·
        refine ⟨94398169141522912462068001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125864225522030549949424001 94398169141522912462068001)
        ·
          refine ⟨70798626856142184346551001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94398169141522912462068001 70798626856142184346551001)
          ·
            refine ⟨53098970142106638259913251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70798626856142184346551001 53098970142106638259913251)
            ·
              refine ⟨79648455213159957389869877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53098970142106638259913251 79648455213159957389869877)
              ·
                refine ⟨7467042676233746005300301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79648455213159957389869877 7467042676233746005300301)
                ·
                  refine ⟨2800141003587654751987613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7467042676233746005300301 2800141003587654751987613)
                  ·
                    refine ⟨1050052876345370531995355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2800141003587654751987613 1050052876345370531995355)
                    ·
                      rfl

theorem cell22_3067456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_3067456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067456 prefixEnd_3067456 := by exact prefixLift 3067456
  have htrace : WordTrace (prefixWord ++ tailWord_3067456) baseStart_3067456 baseEnd_3067456 := by
    simpa [prefixWord, tailWord_3067456, baseEnd_3067456] using wordTrace_append hprefix tailTrace_3067456
  have hstable : (prefixWord ++ tailWord_3067456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067456).length < 2 ^ (prefixWord ++ tailWord_3067456).sum := by decide
  have hdescent : baseEnd_3067456 < baseStart_3067456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067550 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3067550 : Nat := 118140960795 + 3067550 * 2 ^ 59
def prefixEnd_3067550 : Nat := 4983230072969 + 3 ^ 40 * 3067550 * 2
def baseEnd_3067550 : Nat := 1050085054466385620145067

theorem tailTrace_3067550 : CollatzResearch.WordTrace tailWord_3067550 prefixEnd_3067550 1050085054466385620145067 := by
  unfold tailWord_3067550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985342504599715084454013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74588493357865147117088069 13985342504599715084454013)
  ·
    refine ⟨5244503439224893156670255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13985342504599715084454013 5244503439224893156670255)
    ·
      refine ⟨7866755158837339735005383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244503439224893156670255 7866755158837339735005383)
      ·
        refine ⟨11800132738256009602508075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7866755158837339735005383 11800132738256009602508075)
        ·
          refine ⟨17700199107384014403762113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11800132738256009602508075 17700199107384014403762113)
          ·
            refine ⟨13275149330538010802821585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17700199107384014403762113 13275149330538010802821585)
            ·
              refine ⟨9956361997903508102116189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13275149330538010802821585 9956361997903508102116189)
              ·
                refine ⟨3733635749213815538293571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9956361997903508102116189 3733635749213815538293571)
                ·
                  refine ⟨5600453623820723307440357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733635749213815538293571 5600453623820723307440357)
                  ·
                    refine ⟨1050085054466385620145067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600453623820723307440357 1050085054466385620145067)
                    ·
                      rfl

theorem cell22_3067550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3067550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067550 prefixEnd_3067550 := by exact prefixLift 3067550
  have htrace : WordTrace (prefixWord ++ tailWord_3067550) baseStart_3067550 baseEnd_3067550 := by
    simpa [prefixWord, tailWord_3067550, baseEnd_3067550] using wordTrace_append hprefix tailTrace_3067550
  have hstable : (prefixWord ++ tailWord_3067550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067550).length < 2 ^ (prefixWord ++ tailWord_3067550).sum := by decide
  have hdescent : baseEnd_3067550 < baseStart_3067550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067580 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3067580 : Nat := 118140960795 + 3067580 * 2 ^ 59
def prefixEnd_3067580 : Nat := 4983230072969 + 3 ^ 40 * 3067580 * 2
def baseEnd_3067580 : Nat := 1050095324079475541894975

theorem tailTrace_3067580 : CollatzResearch.WordTrace tailWord_3067580 prefixEnd_3067580 1050095324079475541894975 := by
  unfold tailWord_3067580
  simp only [CollatzResearch.WordTrace]
  refine ⟨55941917113344517899612097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74589222817792690532816129 55941917113344517899612097)
  ·
    refine ⟨41956437835008388424709073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55941917113344517899612097 41956437835008388424709073)
    ·
      refine ⟨31467328376256291318531805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41956437835008388424709073 31467328376256291318531805)
      ·
        refine ⟨11800248141096109244449427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31467328376256291318531805 11800248141096109244449427)
        ·
          refine ⟨17700372211644163866674141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11800248141096109244449427 17700372211644163866674141)
          ·
            refine ⟨6637639579366561450002803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17700372211644163866674141 6637639579366561450002803)
            ·
              refine ⟨9956459369049842175004205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637639579366561450002803 9956459369049842175004205)
              ·
                refine ⟨3733672263393690815626577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9956459369049842175004205 3733672263393690815626577)
                ·
                  refine ⟨2800254197545268111719933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733672263393690815626577 2800254197545268111719933)
                  ·
                    refine ⟨1050095324079475541894975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2800254197545268111719933 1050095324079475541894975)
                    ·
                      rfl

theorem cell22_3067580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3067580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067580 prefixEnd_3067580 := by exact prefixLift 3067580
  have htrace : WordTrace (prefixWord ++ tailWord_3067580) baseStart_3067580 baseEnd_3067580 := by
    simpa [prefixWord, tailWord_3067580, baseEnd_3067580] using wordTrace_append hprefix tailTrace_3067580
  have hstable : (prefixWord ++ tailWord_3067580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067580).length < 2 ^ (prefixWord ++ tailWord_3067580).sum := by decide
  have hdescent : baseEnd_3067580 < baseStart_3067580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067700 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3067700 : Nat := 118140960795 + 3067700 * 2 ^ 59
def prefixEnd_3067700 : Nat := 4983230072969 + 3 ^ 40 * 3067700 * 2
def baseEnd_3067700 : Nat := 350045467510611742964869

theorem tailTrace_3067700 : CollatzResearch.WordTrace tailWord_3067700 prefixEnd_3067700 350045467510611742964869 := by
  unfold tailWord_3067700
  simp only [CollatzResearch.WordTrace]
  refine ⟨55944105493127148146796277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74592140657502864195728369 55944105493127148146796277)
  ·
    refine ⟨5244759889980670138762151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55944105493127148146796277 5244759889980670138762151)
    ·
      refine ⟨7867139834971005208143227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244759889980670138762151 7867139834971005208143227)
      ·
        refine ⟨11800709752456507812214841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7867139834971005208143227 11800709752456507812214841)
        ·
          refine ⟨8850532314342380859161131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11800709752456507812214841 8850532314342380859161131)
          ·
            refine ⟨13275798471513571288741697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850532314342380859161131 13275798471513571288741697)
            ·
              refine ⟨9956848853635178466556273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13275798471513571288741697 9956848853635178466556273)
              ·
                refine ⟨7467636640226383849917205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9956848853635178466556273 7467636640226383849917205)
                ·
                  refine ⟨350045467510611742964869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7467636640226383849917205 350045467510611742964869)
                  ·
                    rfl

theorem cell22_3067700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3067700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067700 prefixEnd_3067700 := by exact prefixLift 3067700
  have htrace : WordTrace (prefixWord ++ tailWord_3067700) baseStart_3067700 baseEnd_3067700 := by
    simpa [prefixWord, tailWord_3067700, baseEnd_3067700] using wordTrace_append hprefix tailTrace_3067700
  have hstable : (prefixWord ++ tailWord_3067700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067700).length < 2 ^ (prefixWord ++ tailWord_3067700).sum := by decide
  have hdescent : baseEnd_3067700 < baseStart_3067700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067702 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3067702 : Nat := 118140960795 + 3067702 * 2 ^ 59
def prefixEnd_3067702 : Nat := 4983230072969 + 3 ^ 40 * 3067702 * 2
def baseEnd_3067702 : Nat := 1050137087172707890344601

theorem tailTrace_3067702 : CollatzResearch.WordTrace tailWord_3067702 prefixEnd_3067702 1050137087172707890344601 := by
  unfold tailWord_3067702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993017745765440664697835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74592189288164700423443573 6993017745765440664697835)
  ·
    refine ⟨10489526618648160997046753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993017745765440664697835 10489526618648160997046753)
    ·
      refine ⟨7867144963986120747785065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10489526618648160997046753 7867144963986120747785065)
      ·
        refine ⟨5900358722989590560838799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7867144963986120747785065 5900358722989590560838799)
        ·
          refine ⟨8850538084484385841258199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900358722989590560838799 8850538084484385841258199)
          ·
            refine ⟨13275807126726578761887299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850538084484385841258199 13275807126726578761887299)
            ·
              refine ⟨19913710690089868142830949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13275807126726578761887299 19913710690089868142830949)
              ·
                refine ⟨3733820754391850276780803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19913710690089868142830949 3733820754391850276780803)
                ·
                  refine ⟨5600731131587775415171205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733820754391850276780803 5600731131587775415171205)
                  ·
                    refine ⟨1050137087172707890344601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600731131587775415171205 1050137087172707890344601)
                    ·
                      rfl

theorem cell22_3067702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3067702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067702 prefixEnd_3067702 := by exact prefixLift 3067702
  have htrace : WordTrace (prefixWord ++ tailWord_3067702) baseStart_3067702 baseEnd_3067702 := by
    simpa [prefixWord, tailWord_3067702, baseEnd_3067702] using wordTrace_append hprefix tailTrace_3067702
  have hstable : (prefixWord ++ tailWord_3067702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067702).length < 2 ^ (prefixWord ++ tailWord_3067702).sum := by decide
  have hdescent : baseEnd_3067702 < baseStart_3067702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067730 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3067730 : Nat := 118140960795 + 3067730 * 2 ^ 59
def prefixEnd_3067730 : Nat := 4983230072969 + 3 ^ 40 * 3067730 * 2
def baseEnd_3067730 : Nat := 1050146672144925150644515

theorem tailTrace_3067730 : CollatzResearch.WordTrace tailWord_3067730 prefixEnd_3067730 1050146672144925150644515 := by
  unfold tailWord_3067730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27972326294036402854296161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74592870117430407611456429 27972326294036402854296161)
  ·
    refine ⟨20979244720527302140722121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27972326294036402854296161 20979244720527302140722121)
    ·
      refine ⟨15734433540395476605541591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20979244720527302140722121 15734433540395476605541591)
      ·
        refine ⟨23601650310593214908312387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15734433540395476605541591 23601650310593214908312387)
        ·
          refine ⟨35402475465889822362468581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23601650310593214908312387 35402475465889822362468581)
          ·
            refine ⟨6637964149854341692962859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35402475465889822362468581 6637964149854341692962859)
            ·
              refine ⟨9956946224781512539444289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637964149854341692962859 9956946224781512539444289)
              ·
                refine ⟨7467709668586134404583217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9956946224781512539444289 7467709668586134404583217)
                ·
                  refine ⟨5600782251439600803437413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7467709668586134404583217 5600782251439600803437413)
                  ·
                    refine ⟨1050146672144925150644515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600782251439600803437413 1050146672144925150644515)
                    ·
                      rfl

theorem cell22_3067730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3067730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067730 prefixEnd_3067730 := by exact prefixLift 3067730
  have htrace : WordTrace (prefixWord ++ tailWord_3067730) baseStart_3067730 baseEnd_3067730 := by
    simpa [prefixWord, tailWord_3067730, baseEnd_3067730] using wordTrace_append hprefix tailTrace_3067730
  have hstable : (prefixWord ++ tailWord_3067730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067730).length < 2 ^ (prefixWord ++ tailWord_3067730).sum := by decide
  have hdescent : baseEnd_3067730 < baseStart_3067730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067788 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_3067788 : Nat := 118140960795 + 3067788 * 2 ^ 59
def prefixEnd_3067788 : Nat := 4983230072969 + 3 ^ 40 * 3067788 * 2
def baseEnd_3067788 : Nat := 1050166526730232332694337

theorem tailTrace_3067788 : CollatzResearch.WordTrace tailWord_3067788 prefixEnd_3067788 1050166526730232332694337 := by
  unfold tailWord_3067788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55945710304967743661398009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74594280406623658215197345 55945710304967743661398009)
  ·
    refine ⟨41959282728725807746048507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55945710304967743661398009 41959282728725807746048507)
    ·
      refine ⟨62938924093088711619072761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41959282728725807746048507 62938924093088711619072761)
      ·
        refine ⟨47204193069816533714304571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62938924093088711619072761 47204193069816533714304571)
        ·
          refine ⟨70806289604724800571456857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47204193069816533714304571 70806289604724800571456857)
          ·
            refine ⟨53104717203543600428592643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70806289604724800571456857 53104717203543600428592643)
            ·
              refine ⟨79657075805315400642888965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53104717203543600428592643 79657075805315400642888965)
              ·
                refine ⟨14935701713496637620541681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79657075805315400642888965 14935701713496637620541681)
                ·
                  refine ⟨11201776285122478215406261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14935701713496637620541681 11201776285122478215406261)
                  ·
                    refine ⟨1050166526730232332694337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11201776285122478215406261 1050166526730232332694337)
                    ·
                      rfl

theorem cell22_3067788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_3067788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067788 prefixEnd_3067788 := by exact prefixLift 3067788
  have htrace : WordTrace (prefixWord ++ tailWord_3067788) baseStart_3067788 baseEnd_3067788 := by
    simpa [prefixWord, tailWord_3067788, baseEnd_3067788] using wordTrace_append hprefix tailTrace_3067788
  have hstable : (prefixWord ++ tailWord_3067788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067788).length < 2 ^ (prefixWord ++ tailWord_3067788).sum := by decide
  have hdescent : baseEnd_3067788 < baseStart_3067788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067805 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3067805 : Nat := 118140960795 + 3067805 * 2 ^ 59
def prefixEnd_3067805 : Nat := 4983230072969 + 3 ^ 40 * 3067805 * 2
def baseEnd_3067805 : Nat := 1050172346177649955019285

theorem tailTrace_3067805 : CollatzResearch.WordTrace tailWord_3067805 prefixEnd_3067805 1050172346177649955019285 := by
  unfold tailWord_3067805
  simp only [CollatzResearch.WordTrace]
  refine ⟨111892040650873899226164869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74594693767249266150776579 111892040650873899226164869)
  ·
    refine ⟨20979757622038856104905913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111892040650873899226164869 20979757622038856104905913)
    ·
      refine ⟨15734818216529142078679435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20979757622038856104905913 15734818216529142078679435)
      ·
        refine ⟨23602227324793713118019153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15734818216529142078679435 23602227324793713118019153)
        ·
          refine ⟨17701670493595284838514365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23602227324793713118019153 17701670493595284838514365)
          ·
            refine ⟨6638126435098231814442887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17701670493595284838514365 6638126435098231814442887)
            ·
              refine ⟨9957189652647347721664331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638126435098231814442887 9957189652647347721664331)
              ·
                refine ⟨14935784478971021582496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957189652647347721664331 14935784478971021582496497)
                ·
                  refine ⟨11201838359228266186872373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14935784478971021582496497 11201838359228266186872373)
                  ·
                    refine ⟨1050172346177649955019285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11201838359228266186872373 1050172346177649955019285)
                    ·
                      rfl

theorem cell22_3067805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3067805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067805 prefixEnd_3067805 := by exact prefixLift 3067805
  have htrace : WordTrace (prefixWord ++ tailWord_3067805) baseStart_3067805 baseEnd_3067805 := by
    simpa [prefixWord, tailWord_3067805, baseEnd_3067805] using wordTrace_append hprefix tailTrace_3067805
  have hstable : (prefixWord ++ tailWord_3067805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067805).length < 2 ^ (prefixWord ++ tailWord_3067805).sum := by decide
  have hdescent : baseEnd_3067805 < baseStart_3067805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067828 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3067828 : Nat := 118140960795 + 3067828 * 2 ^ 59
def prefixEnd_3067828 : Nat := 4983230072969 + 3 ^ 40 * 3067828 * 2
def baseEnd_3067828 : Nat := 1050180219547685561694215

theorem tailTrace_3067828 : CollatzResearch.WordTrace tailWord_3067828 prefixEnd_3067828 1050180219547685561694215 := by
  unfold tailWord_3067828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55946439764895287077126069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74595253019860382769501425 55946439764895287077126069)
  ·
    refine ⟨5244978727958933163480569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55946439764895287077126069 5244978727958933163480569)
    ·
      refine ⟨3933734045969199872610427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5244978727958933163480569 3933734045969199872610427)
      ·
        refine ⟨5900601068953799808915641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933734045969199872610427 5900601068953799808915641)
        ·
          refine ⟨4425450801715349856686731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900601068953799808915641 4425450801715349856686731)
          ·
            refine ⟨6638176202573024785030097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425450801715349856686731 6638176202573024785030097)
            ·
              refine ⟨4978632151929768588772573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6638176202573024785030097 4978632151929768588772573)
              ·
                refine ⟨1866987056973663220789715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4978632151929768588772573 1866987056973663220789715)
                ·
                  refine ⟨2800480585460494831184573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866987056973663220789715 2800480585460494831184573)
                  ·
                    refine ⟨1050180219547685561694215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2800480585460494831184573 1050180219547685561694215)
                    ·
                      rfl

theorem cell22_3067828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3067828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067828 prefixEnd_3067828 := by exact prefixLift 3067828
  have htrace : WordTrace (prefixWord ++ tailWord_3067828) baseStart_3067828 baseEnd_3067828 := by
    simpa [prefixWord, tailWord_3067828, baseEnd_3067828] using wordTrace_append hprefix tailTrace_3067828
  have hstable : (prefixWord ++ tailWord_3067828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067828).length < 2 ^ (prefixWord ++ tailWord_3067828).sum := by decide
  have hdescent : baseEnd_3067828 < baseStart_3067828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067835 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 4]
def baseStart_3067835 : Nat := 118140960795 + 3067835 * 2 ^ 59
def prefixEnd_3067835 : Nat := 4983230072969 + 3 ^ 40 * 3067835 * 2
def baseEnd_3067835 : Nat := 350060871930246625589731

theorem tailTrace_3067835 : CollatzResearch.WordTrace tailWord_3067835 prefixEnd_3067835 350060871930246625589731 := by
  unfold tailWord_3067835
  simp only [CollatzResearch.WordTrace]
  refine ⟨111893134840765214349756959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74595423227176809566504639 111893134840765214349756959)
  ·
    refine ⟨167839702261147821524635439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111893134840765214349756959 167839702261147821524635439)
    ·
      refine ⟨251759553391721732286953159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167839702261147821524635439 251759553391721732286953159)
      ·
        refine ⟨377639330087582598430429739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251759553391721732286953159 377639330087582598430429739)
        ·
          refine ⟨566458995131373897645644609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377639330087582598430429739 566458995131373897645644609)
          ·
            refine ⟨424844246348530423234233457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566458995131373897645644609 424844246348530423234233457)
            ·
              refine ⟨318633184761397817425675093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424844246348530423234233457 318633184761397817425675093)
              ·
                refine ⟨1866991316961315336478565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 318633184761397817425675093 1866991316961315336478565)
                ·
                  refine ⟨350060871930246625589731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866991316961315336478565 350060871930246625589731)
                  ·
                    rfl

theorem cell22_3067835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 4].length) (baseStart_3067835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067835 prefixEnd_3067835 := by exact prefixLift 3067835
  have htrace : WordTrace (prefixWord ++ tailWord_3067835) baseStart_3067835 baseEnd_3067835 := by
    simpa [prefixWord, tailWord_3067835, baseEnd_3067835] using wordTrace_append hprefix tailTrace_3067835
  have hstable : (prefixWord ++ tailWord_3067835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067835).length < 2 ^ (prefixWord ++ tailWord_3067835).sum := by decide
  have hdescent : baseEnd_3067835 < baseStart_3067835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067837 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_3067837 : Nat := 118140960795 + 3067837 * 2 ^ 59
def prefixEnd_3067837 : Nat := 4983230072969 + 3 ^ 40 * 3067837 * 2
def baseEnd_3067837 : Nat := 1050183300431612538219187

theorem tailTrace_3067837 : CollatzResearch.WordTrace tailWord_3067837 prefixEnd_3067837 1050183300431612538219187 := by
  unfold tailWord_3067837
  simp only [CollatzResearch.WordTrace]
  refine ⟨111893207786757968691329765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74595471857838645794219843 111893207786757968691329765)
  ·
    refine ⟨20979976460017119129624331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111893207786757968691329765 20979976460017119129624331)
    ·
      refine ⟨31469964690025678694436497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20979976460017119129624331 31469964690025678694436497)
      ·
        refine ⟨23602473517519259020827373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31469964690025678694436497 23602473517519259020827373)
        ·
          refine ⟨8850927569069722132810265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23602473517519259020827373 8850927569069722132810265)
          ·
            refine ⟨6638195676802291599607699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8850927569069722132810265 6638195676802291599607699)
            ·
              refine ⟨9957293515203437399411549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638195676802291599607699 9957293515203437399411549)
              ·
                refine ⟨3733985068201289024779331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9957293515203437399411549 3733985068201289024779331)
                ·
                  refine ⟨5600977602301933537168997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733985068201289024779331 5600977602301933537168997)
                  ·
                    refine ⟨1050183300431612538219187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600977602301933537168997 1050183300431612538219187)
                    ·
                      rfl

theorem cell22_3067837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_3067837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067837 prefixEnd_3067837 := by exact prefixLift 3067837
  have htrace : WordTrace (prefixWord ++ tailWord_3067837) baseStart_3067837 baseEnd_3067837 := by
    simpa [prefixWord, tailWord_3067837, baseEnd_3067837] using wordTrace_append hprefix tailTrace_3067837
  have hstable : (prefixWord ++ tailWord_3067837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067837).length < 2 ^ (prefixWord ++ tailWord_3067837).sum := by decide
  have hdescent : baseEnd_3067837 < baseStart_3067837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067852 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_3067852 : Nat := 118140960795 + 3067852 * 2 ^ 59
def prefixEnd_3067852 : Nat := 4983230072969 + 3 ^ 40 * 3067852 * 2
def baseEnd_3067852 : Nat := 350062811746052499698047

theorem tailTrace_3067852 : CollatzResearch.WordTrace tailWord_3067852 prefixEnd_3067852 350062811746052499698047 := by
  unfold tailWord_3067852
  simp only [CollatzResearch.WordTrace]
  refine ⟨55946877440851813126562905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74595836587802417502083873 55946877440851813126562905)
  ·
    refine ⟨41960158080638859844922179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55946877440851813126562905 41960158080638859844922179)
    ·
      refine ⟨62940237120958289767383269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41960158080638859844922179 62940237120958289767383269)
      ·
        refine ⟨11801294460179679331384363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62940237120958289767383269 11801294460179679331384363)
        ·
          refine ⟨17701941690269518997076545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11801294460179679331384363 17701941690269518997076545)
          ·
            refine ⟨13276456267702139247807409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17701941690269518997076545 13276456267702139247807409)
            ·
              refine ⟨9957342200776604435855557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13276456267702139247807409 9957342200776604435855557)
              ·
                refine ⟨1867001662645613331722917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9957342200776604435855557 1867001662645613331722917)
                ·
                  refine ⟨350062811746052499698047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867001662645613331722917 350062811746052499698047)
                  ·
                    rfl

theorem cell22_3067852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_3067852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067852 prefixEnd_3067852 := by exact prefixLift 3067852
  have htrace : WordTrace (prefixWord ++ tailWord_3067852) baseStart_3067852 baseEnd_3067852 := by
    simpa [prefixWord, tailWord_3067852, baseEnd_3067852] using wordTrace_append hprefix tailTrace_3067852
  have hstable : (prefixWord ++ tailWord_3067852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067852).length < 2 ^ (prefixWord ++ tailWord_3067852).sum := by decide
  have hdescent : baseEnd_3067852 < baseStart_3067852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067863 : List Nat := [1, 1, 3, 2, 1, 1, 4, 9]
def baseStart_3067863 : Nat := 118140960795 + 3067863 * 2 ^ 59
def prefixEnd_3067863 : Nat := 4983230072969 + 3 ^ 40 * 3067863 * 2
def baseEnd_3067863 : Nat := 116688022306995237452123

theorem tailTrace_3067863 : CollatzResearch.WordTrace tailWord_3067863 prefixEnd_3067863 116688022306995237452123 := by
  unfold tailWord_3067863
  simp only [CollatzResearch.WordTrace]
  refine ⟨111894156084663775131776243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74596104056442516754517495 111894156084663775131776243)
  ·
    refine ⟨167841234126995662697664365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111894156084663775131776243 167841234126995662697664365)
    ·
      refine ⟨62940462797623373511624137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167841234126995662697664365 62940462797623373511624137)
      ·
        refine ⟨47205347098217530133718103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62940462797623373511624137 47205347098217530133718103)
        ·
          refine ⟨70808020647326295200577155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47205347098217530133718103 70808020647326295200577155)
          ·
            refine ⟨106212030970989442800865733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70808020647326295200577155 106212030970989442800865733)
            ·
              refine ⟨19914755807060520525162325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106212030970989442800865733 19914755807060520525162325)
              ·
                refine ⟨116688022306995237452123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19914755807060520525162325 116688022306995237452123)
                ·
                  rfl

theorem cell22_3067863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 9].length) (baseStart_3067863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067863 prefixEnd_3067863 := by exact prefixLift 3067863
  have htrace : WordTrace (prefixWord ++ tailWord_3067863) baseStart_3067863 baseEnd_3067863 := by
    simpa [prefixWord, tailWord_3067863, baseEnd_3067863] using wordTrace_append hprefix tailTrace_3067863
  have hstable : (prefixWord ++ tailWord_3067863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067863).length < 2 ^ (prefixWord ++ tailWord_3067863).sum := by decide
  have hdescent : baseEnd_3067863 < baseStart_3067863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067974 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3067974 : Nat := 118140960795 + 3067974 * 2 ^ 59
def prefixEnd_3067974 : Nat := 4983230072969 + 3 ^ 40 * 3067974 * 2
def baseEnd_3067974 : Nat := 1050230198331389847543767

theorem tailTrace_3067974 : CollatzResearch.WordTrace tailWord_3067974 prefixEnd_3067974 1050230198331389847543767 := by
  unfold tailWord_3067974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496818893351926284033343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74598803058174427392711317 3496818893351926284033343)
  ·
    refine ⟨5245228340027889426050015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3496818893351926284033343 5245228340027889426050015)
    ·
      refine ⟨7867842510041834139075023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245228340027889426050015 7867842510041834139075023)
      ·
        refine ⟨11801763765062751208612535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7867842510041834139075023 11801763765062751208612535)
        ·
          refine ⟨17702645647594126812918803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11801763765062751208612535 17702645647594126812918803)
          ·
            refine ⟨26553968471391190219378205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17702645647594126812918803 26553968471391190219378205)
            ·
              refine ⟨9957738176771696332266827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26553968471391190219378205 9957738176771696332266827)
              ·
                refine ⟨14936607265157544498400241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957738176771696332266827 14936607265157544498400241)
                ·
                  refine ⟨11202455448868158373800181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14936607265157544498400241 11202455448868158373800181)
                  ·
                    refine ⟨1050230198331389847543767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11202455448868158373800181 1050230198331389847543767)
                    ·
                      rfl

theorem cell22_3067974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3067974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3067974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3067974 prefixEnd_3067974 := by exact prefixLift 3067974
  have htrace : WordTrace (prefixWord ++ tailWord_3067974) baseStart_3067974 baseEnd_3067974 := by
    simpa [prefixWord, tailWord_3067974, baseEnd_3067974] using wordTrace_append hprefix tailTrace_3067974
  have hstable : (prefixWord ++ tailWord_3067974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067974).length < 2 ^ (prefixWord ++ tailWord_3067974).sum := by decide
  have hdescent : baseEnd_3067974 < baseStart_3067974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068015 : List Nat := [1, 1, 2, 1, 3, 5, 9]
def baseStart_3068015 : Nat := 118140960795 + 3068015 * 2 ^ 59
def prefixEnd_3068015 : Nat := 4983230072969 + 3 ^ 40 * 3068015 * 2
def baseEnd_3068015 : Nat := 38897934572936274343283

theorem tailTrace_3068015 : CollatzResearch.WordTrace tailWord_3068015 prefixEnd_3068015 38897934572936274343283 := by
  unfold tailWord_3068015
  simp only [CollatzResearch.WordTrace]
  refine ⟨111899699980113105091309499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74599799986742070060872999 111899699980113105091309499)
  ·
    refine ⟨167849549970169657636964249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111899699980113105091309499 167849549970169657636964249)
    ·
      refine ⟨125887162477627243227723187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167849549970169657636964249 125887162477627243227723187)
      ·
        refine ⟨188830743716440864841584781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125887162477627243227723187 188830743716440864841584781)
        ·
          refine ⟨70811528893665324315594293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188830743716440864841584781 70811528893665324315594293)
          ·
            refine ⟨6638580833781124154586965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70811528893665324315594293 6638580833781124154586965)
            ·
              refine ⟨38897934572936274343283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6638580833781124154586965 38897934572936274343283)
              ·
                rfl

theorem cell22_3068015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 9].length) (baseStart_3068015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068015 prefixEnd_3068015 := by exact prefixLift 3068015
  have htrace : WordTrace (prefixWord ++ tailWord_3068015) baseStart_3068015 baseEnd_3068015 := by
    simpa [prefixWord, tailWord_3068015, baseEnd_3068015] using wordTrace_append hprefix tailTrace_3068015
  have hstable : (prefixWord ++ tailWord_3068015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068015).length < 2 ^ (prefixWord ++ tailWord_3068015).sum := by decide
  have hdescent : baseEnd_3068015 < baseStart_3068015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068036 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3068036 : Nat := 118140960795 + 3068036 * 2 ^ 59
def prefixEnd_3068036 : Nat := 4983230072969 + 3 ^ 40 * 3068036 * 2
def baseEnd_3068036 : Nat := 1050251422198442352493577

theorem tailTrace_3068036 : CollatzResearch.WordTrace tailWord_3068036 prefixEnd_3068036 1050251422198442352493577 := by
  unfold tailWord_3068036
  simp only [CollatzResearch.WordTrace]
  refine ⟨55950232956518512838911981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74600310608691350451882641 55950232956518512838911981)
  ·
    refine ⟨20981337358694442314591993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55950232956518512838911981 20981337358694442314591993)
    ·
      refine ⟨15736003019020831735943995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20981337358694442314591993 15736003019020831735943995)
      ·
        refine ⟨23604004528531247603915993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736003019020831735943995 23604004528531247603915993)
        ·
          refine ⟨17703003396398435702936995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23604004528531247603915993 17703003396398435702936995)
          ·
            refine ⟨26554505094597653554405493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17703003396398435702936995 26554505094597653554405493)
            ·
              refine ⟨2489484852618530020725515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26554505094597653554405493 2489484852618530020725515)
              ·
                refine ⟨3734227278927795031088273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489484852618530020725515 3734227278927795031088273)
                ·
                  refine ⟨2800670459195846273316205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734227278927795031088273 2800670459195846273316205)
                  ·
                    refine ⟨1050251422198442352493577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2800670459195846273316205 1050251422198442352493577)
                    ·
                      rfl

theorem cell22_3068036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3068036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068036 prefixEnd_3068036 := by exact prefixLift 3068036
  have htrace : WordTrace (prefixWord ++ tailWord_3068036) baseStart_3068036 baseEnd_3068036 := by
    simpa [prefixWord, tailWord_3068036, baseEnd_3068036] using wordTrace_append hprefix tailTrace_3068036
  have hstable : (prefixWord ++ tailWord_3068036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068036).length < 2 ^ (prefixWord ++ tailWord_3068036).sum := by decide
  have hdescent : baseEnd_3068036 < baseStart_3068036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068107 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_3068107 : Nat := 118140960795 + 3068107 * 2 ^ 59
def prefixEnd_3068107 : Nat := 4983230072969 + 3 ^ 40 * 3068107 * 2
def baseEnd_3068107 : Nat := 1050275726949421833968359

theorem tailTrace_3068107 : CollatzResearch.WordTrace tailWord_3068107 prefixEnd_3068107 1050275726949421833968359 := by
  unfold tailWord_3068107
  simp only [CollatzResearch.WordTrace]
  refine ⟨111903055495779804803658575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74602036997186536535772383 111903055495779804803658575)
  ·
    refine ⟨167854583243669707205487863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111903055495779804803658575 167854583243669707205487863)
    ·
      refine ⟨251781874865504560808231795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167854583243669707205487863 251781874865504560808231795)
      ·
        refine ⟨377672812298256841212347693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251781874865504560808231795 377672812298256841212347693)
        ·
          refine ⟨141627304611846315454630385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377672812298256841212347693 141627304611846315454630385)
          ·
            refine ⟨106220478458884736590972789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141627304611846315454630385 106220478458884736590972789)
            ·
              refine ⟨9958169855520444055403699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106220478458884736590972789 9958169855520444055403699)
              ·
                refine ⟨14937254783280666083105549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9958169855520444055403699 14937254783280666083105549)
                ·
                  refine ⟨5601470543730249781164581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14937254783280666083105549 5601470543730249781164581)
                  ·
                    refine ⟨1050275726949421833968359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601470543730249781164581 1050275726949421833968359)
                    ·
                      rfl

theorem cell22_3068107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_3068107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068107 prefixEnd_3068107 := by exact prefixLift 3068107
  have htrace : WordTrace (prefixWord ++ tailWord_3068107) baseStart_3068107 baseEnd_3068107 := by
    simpa [prefixWord, tailWord_3068107, baseEnd_3068107] using wordTrace_append hprefix tailTrace_3068107
  have hstable : (prefixWord ++ tailWord_3068107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068107).length < 2 ^ (prefixWord ++ tailWord_3068107).sum := by decide
  have hdescent : baseEnd_3068107 < baseStart_3068107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068139 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 4]
def baseStart_3068139 : Nat := 118140960795 + 3068139 * 2 ^ 59
def prefixEnd_3068139 : Nat := 4983230072969 + 3 ^ 40 * 3068139 * 2
def baseEnd_3068139 : Nat := 350095560401128139056087

theorem tailTrace_3068139 : CollatzResearch.WordTrace tailWord_3068139 prefixEnd_3068139 350095560401128139056087 := by
  unfold tailWord_3068139
  simp only [CollatzResearch.WordTrace]
  refine ⟨111904222631663874268823471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74602815087775916179215647 111904222631663874268823471)
  ·
    refine ⟨167856333947495811403235207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111904222631663874268823471 167856333947495811403235207)
    ·
      refine ⟨251784500921243717104852811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167856333947495811403235207 251784500921243717104852811)
      ·
        refine ⟨377676751381865575657279217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251784500921243717104852811 377676751381865575657279217)
        ·
          refine ⟨283257563536399181742959413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377676751381865575657279217 283257563536399181742959413)
          ·
            refine ⟨26555396581537423288402445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283257563536399181742959413 26555396581537423288402445)
            ·
              refine ⟨9958273718076533733150917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26555396581537423288402445 9958273718076533733150917)
              ·
                refine ⟨1867176322139350074965797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9958273718076533733150917 1867176322139350074965797)
                ·
                  refine ⟨350095560401128139056087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867176322139350074965797 350095560401128139056087)
                  ·
                    rfl

theorem cell22_3068139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 4].length) (baseStart_3068139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068139 prefixEnd_3068139 := by exact prefixLift 3068139
  have htrace : WordTrace (prefixWord ++ tailWord_3068139) baseStart_3068139 baseEnd_3068139 := by
    simpa [prefixWord, tailWord_3068139, baseEnd_3068139] using wordTrace_append hprefix tailTrace_3068139
  have hstable : (prefixWord ++ tailWord_3068139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068139).length < 2 ^ (prefixWord ++ tailWord_3068139).sum := by decide
  have hdescent : baseEnd_3068139 < baseStart_3068139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068152 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_3068152 : Nat := 118140960795 + 3068152 * 2 ^ 59
def prefixEnd_3068152 : Nat := 4983230072969 + 3 ^ 40 * 3068152 * 2
def baseEnd_3068152 : Nat := 1050291131369056716593221

theorem tailTrace_3068152 : CollatzResearch.WordTrace tailWord_3068152 prefixEnd_3068152 1050291131369056716593221 := by
  unfold tailWord_3068152
  simp only [CollatzResearch.WordTrace]
  refine ⟨55952348390308388744523355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74603131187077851659364473 55952348390308388744523355)
  ·
    refine ⟨83928522585462583116785033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55952348390308388744523355 83928522585462583116785033)
    ·
      refine ⟨62946391939096937337588775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83928522585462583116785033 62946391939096937337588775)
      ·
        refine ⟨94419587908645406006383163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62946391939096937337588775 94419587908645406006383163)
        ·
          refine ⟨141629381862968109009574745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94419587908645406006383163 141629381862968109009574745)
          ·
            refine ⟨106222036397226081757181059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141629381862968109009574745 106222036397226081757181059)
            ·
              refine ⟨159333054595839122635771589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106222036397226081757181059 159333054595839122635771589)
              ·
                refine ⟨29874947736719835494207173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159333054595839122635771589 29874947736719835494207173)
                ·
                  refine ⟨5601552700634969155163845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29874947736719835494207173 5601552700634969155163845)
                  ·
                    refine ⟨1050291131369056716593221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601552700634969155163845 1050291131369056716593221)
                    ·
                      rfl

theorem cell22_3068152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_3068152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068152 prefixEnd_3068152 := by exact prefixLift 3068152
  have htrace : WordTrace (prefixWord ++ tailWord_3068152) baseStart_3068152 baseEnd_3068152 := by
    simpa [prefixWord, tailWord_3068152, baseEnd_3068152] using wordTrace_append hprefix tailTrace_3068152
  have hstable : (prefixWord ++ tailWord_3068152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068152).length < 2 ^ (prefixWord ++ tailWord_3068152).sum := by decide
  have hdescent : baseEnd_3068152 < baseStart_3068152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068154 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_3068154 : Nat := 118140960795 + 3068154 * 2 ^ 59
def prefixEnd_3068154 : Nat := 4983230072969 + 3 ^ 40 * 3068154 * 2
def baseEnd_3068154 : Nat := 1050291816009929378043215

theorem tailTrace_3068154 : CollatzResearch.WordTrace tailWord_3068154 prefixEnd_3068154 1050291816009929378043215 := by
  unfold tailWord_3068154
  simp only [CollatzResearch.WordTrace]
  refine ⟨27976192431652382957654879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74603179817739687887079677 27976192431652382957654879)
  ·
    refine ⟨41964288647478574436482319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27976192431652382957654879 41964288647478574436482319)
    ·
      refine ⟨62946432971217861654723479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41964288647478574436482319 62946432971217861654723479)
      ·
        refine ⟨94419649456826792482085219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62946432971217861654723479 94419649456826792482085219)
        ·
          refine ⟨141629474185240188723127829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94419649456826792482085219 141629474185240188723127829)
          ·
            refine ⟨6638881602433133846396617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141629474185240188723127829 6638881602433133846396617)
            ·
              refine ⟨4979161201824850384797463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6638881602433133846396617 4979161201824850384797463)
              ·
                refine ⟨7468741802737275577196195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979161201824850384797463 7468741802737275577196195)
                ·
                  refine ⟨11203112704105913365794293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468741802737275577196195 11203112704105913365794293)
                  ·
                    refine ⟨1050291816009929378043215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11203112704105913365794293 1050291816009929378043215)
                    ·
                      rfl

theorem cell22_3068154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_3068154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068154 prefixEnd_3068154 := by exact prefixLift 3068154
  have htrace : WordTrace (prefixWord ++ tailWord_3068154) baseStart_3068154 baseEnd_3068154 := by
    simpa [prefixWord, tailWord_3068154, baseEnd_3068154] using wordTrace_append hprefix tailTrace_3068154
  have hstable : (prefixWord ++ tailWord_3068154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068154).length < 2 ^ (prefixWord ++ tailWord_3068154).sum := by decide
  have hdescent : baseEnd_3068154 < baseStart_3068154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068169 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_3068169 : Nat := 118140960795 + 3068169 * 2 ^ 59
def prefixEnd_3068169 : Nat := 4983230072969 + 3 ^ 40 * 3068169 * 2
def baseEnd_3068169 : Nat := 1050296950816474338918169

theorem tailTrace_3068169 : CollatzResearch.WordTrace tailWord_3068169 prefixEnd_3068169 1050296950816474338918169 := by
  unfold tailWord_3068169
  simp only [CollatzResearch.WordTrace]
  refine ⟨111905316821555189392415561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74603544547703459594943707 111905316821555189392415561)
  ·
    refine ⟨83928987616166392044311671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111905316821555189392415561 83928987616166392044311671)
    ·
      refine ⟨125893481424249588066467507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83928987616166392044311671 125893481424249588066467507)
      ·
        refine ⟨188840222136374382099701261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125893481424249588066467507 188840222136374382099701261)
        ·
          refine ⟨70815083301140393287387973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188840222136374382099701261 70815083301140393287387973)
          ·
            refine ⟨13277828118963823741385245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70815083301140393287387973 13277828118963823741385245)
            ·
              refine ⟨4979185544611433903019467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13277828118963823741385245 4979185544611433903019467)
              ·
                refine ⟨7468778316917150854529201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979185544611433903019467 7468778316917150854529201)
                ·
                  refine ⟨5601583737687863140896901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468778316917150854529201 5601583737687863140896901)
                  ·
                    refine ⟨1050296950816474338918169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601583737687863140896901 1050296950816474338918169)
                    ·
                      rfl

theorem cell22_3068169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_3068169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068169 prefixEnd_3068169 := by exact prefixLift 3068169
  have htrace : WordTrace (prefixWord ++ tailWord_3068169) baseStart_3068169 baseEnd_3068169 := by
    simpa [prefixWord, tailWord_3068169, baseEnd_3068169] using wordTrace_append hprefix tailTrace_3068169
  have hstable : (prefixWord ++ tailWord_3068169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068169).length < 2 ^ (prefixWord ++ tailWord_3068169).sum := by decide
  have hdescent : baseEnd_3068169 < baseStart_3068169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068205 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3068205 : Nat := 118140960795 + 3068205 * 2 ^ 59
def prefixEnd_3068205 : Nat := 4983230072969 + 3 ^ 40 * 3068205 * 2
def baseEnd_3068205 : Nat := 1050309274352182245018059

theorem tailTrace_3068205 : CollatzResearch.WordTrace tailWord_3068205 prefixEnd_3068205 1050309274352182245018059 := by
  unfold tailWord_3068205
  simp only [CollatzResearch.WordTrace]
  refine ⟨111906629849424767540726069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74604419899616511693817379 111906629849424767540726069)
  ·
    refine ⟨10491246548383571956943069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111906629849424767540726069 10491246548383571956943069)
    ·
      refine ⟨3934217455643839483853651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10491246548383571956943069 3934217455643839483853651)
      ·
        refine ⟨5901326183465759225780477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934217455643839483853651 5901326183465759225780477)
        ·
          refine ⟨2212997318799659709667679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5901326183465759225780477 2212997318799659709667679)
          ·
            refine ⟨3319495978199489564501519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212997318799659709667679 3319495978199489564501519)
            ·
              refine ⟨4979243967299234346752279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319495978199489564501519 4979243967299234346752279)
              ·
                refine ⟨7468865950948851520128419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979243967299234346752279 7468865950948851520128419)
                ·
                  refine ⟨11203298926423277280192629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468865950948851520128419 11203298926423277280192629)
                  ·
                    refine ⟨1050309274352182245018059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11203298926423277280192629 1050309274352182245018059)
                    ·
                      rfl

theorem cell22_3068205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3068205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068205 prefixEnd_3068205 := by exact prefixLift 3068205
  have htrace : WordTrace (prefixWord ++ tailWord_3068205) baseStart_3068205 baseEnd_3068205 := by
    simpa [prefixWord, tailWord_3068205, baseEnd_3068205] using wordTrace_append hprefix tailTrace_3068205
  have hstable : (prefixWord ++ tailWord_3068205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068205).length < 2 ^ (prefixWord ++ tailWord_3068205).sum := by decide
  have hdescent : baseEnd_3068205 < baseStart_3068205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068227 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_3068227 : Nat := 118140960795 + 3068227 * 2 ^ 59
def prefixEnd_3068227 : Nat := 4983230072969 + 3 ^ 40 * 3068227 * 2
def baseEnd_3068227 : Nat := 1050316805401781520967991

theorem tailTrace_3068227 : CollatzResearch.WordTrace tailWord_3068227 prefixEnd_3068227 1050316805401781520967991 := by
  unfold tailWord_3068227
  simp only [CollatzResearch.WordTrace]
  refine ⟨111907432255345065298026935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74604954836896710198684623 111907432255345065298026935)
  ·
    refine ⟨167861148383017597947040403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111907432255345065298026935 167861148383017597947040403)
    ·
      refine ⟨251791722574526396920560605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167861148383017597947040403 251791722574526396920560605)
      ·
        refine ⟨94421895965447398845210227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251791722574526396920560605 94421895965447398845210227)
        ·
          refine ⟨141632843948171098267815341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94421895965447398845210227 141632843948171098267815341)
          ·
            refine ⟨53112316480564161850430753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141632843948171098267815341 53112316480564161850430753)
            ·
              refine ⟨39834237360423121387823065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53112316480564161850430753 39834237360423121387823065)
              ·
                refine ⟨29875678020317341040867299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39834237360423121387823065 29875678020317341040867299)
                ·
                  refine ⟨44813517030476011561300949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29875678020317341040867299 44813517030476011561300949)
                  ·
                    refine ⟨1050316805401781520967991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44813517030476011561300949 1050316805401781520967991)
                    ·
                      rfl

theorem cell22_3068227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_3068227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068227 prefixEnd_3068227 := by exact prefixLift 3068227
  have htrace : WordTrace (prefixWord ++ tailWord_3068227) baseStart_3068227 baseEnd_3068227 := by
    simpa [prefixWord, tailWord_3068227, baseEnd_3068227] using wordTrace_append hprefix tailTrace_3068227
  have hstable : (prefixWord ++ tailWord_3068227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068227).length < 2 ^ (prefixWord ++ tailWord_3068227).sum := by decide
  have hdescent : baseEnd_3068227 < baseStart_3068227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068259 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_3068259 : Nat := 118140960795 + 3068259 * 2 ^ 59
def prefixEnd_3068259 : Nat := 4983230072969 + 3 ^ 40 * 3068259 * 2
def baseEnd_3068259 : Nat := 1050327759655744104167893

theorem tailTrace_3068259 : CollatzResearch.WordTrace tailWord_3068259 prefixEnd_3068259 1050327759655744104167893 := by
  unfold tailWord_3068259
  simp only [CollatzResearch.WordTrace]
  refine ⟨111908599391229134763191831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74605732927486089842127887 111908599391229134763191831)
  ·
    refine ⟨167862899086843702144787747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111908599391229134763191831 167862899086843702144787747)
    ·
      refine ⟨251794348630265553217181621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167862899086843702144787747 251794348630265553217181621)
      ·
        refine ⟨23605720184087395614110777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251794348630265553217181621 23605720184087395614110777)
        ·
          refine ⟨17704290138065546710583083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23605720184087395614110777 17704290138065546710583083)
          ·
            refine ⟨26556435207098320065874625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17704290138065546710583083 26556435207098320065874625)
            ·
              refine ⟨19917326405323740049405969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26556435207098320065874625 19917326405323740049405969)
              ·
                refine ⟨14937994803992805037054477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19917326405323740049405969 14937994803992805037054477)
                ·
                  refine ⟨5601748051497301888895429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14937994803992805037054477 5601748051497301888895429)
                  ·
                    refine ⟨1050327759655744104167893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601748051497301888895429 1050327759655744104167893)
                    ·
                      rfl

theorem cell22_3068259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_3068259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068259 prefixEnd_3068259 := by exact prefixLift 3068259
  have htrace : WordTrace (prefixWord ++ tailWord_3068259) baseStart_3068259 baseEnd_3068259 := by
    simpa [prefixWord, tailWord_3068259, baseEnd_3068259] using wordTrace_append hprefix tailTrace_3068259
  have hstable : (prefixWord ++ tailWord_3068259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068259).length < 2 ^ (prefixWord ++ tailWord_3068259).sum := by decide
  have hdescent : baseEnd_3068259 < baseStart_3068259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068263 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 5]
def baseStart_3068263 : Nat := 118140960795 + 3068263 * 2 ^ 59
def prefixEnd_3068263 : Nat := 4983230072969 + 3 ^ 40 * 3068263 * 2
def baseEnd_3068263 : Nat := 350109709645829809022627

theorem tailTrace_3068263 : CollatzResearch.WordTrace tailWord_3068263 prefixEnd_3068263 350109709645829809022627 := by
  unfold tailWord_3068263
  simp only [CollatzResearch.WordTrace]
  refine ⟨111908745283214643446337443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74605830188809762297558295 111908745283214643446337443)
  ·
    refine ⟨167863117924821965169506165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111908745283214643446337443 167863117924821965169506165)
    ·
      refine ⟨15737167305452059234641203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167863117924821965169506165 15737167305452059234641203)
      ·
        refine ⟨23605750958178088851961805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15737167305452059234641203 23605750958178088851961805)
        ·
          refine ⟨8852156609316783319485677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23605750958178088851961805 8852156609316783319485677)
          ·
            refine ⟨3319558728493793744807129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8852156609316783319485677 3319558728493793744807129)
            ·
              refine ⟨2489669046370345308605347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319558728493793744807129 2489669046370345308605347)
              ·
                refine ⟨3734503569555517962908021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489669046370345308605347 3734503569555517962908021)
                ·
                  refine ⟨350109709645829809022627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3734503569555517962908021 350109709645829809022627)
                  ·
                    rfl

theorem cell22_3068263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 5].length) (baseStart_3068263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068263 prefixEnd_3068263 := by exact prefixLift 3068263
  have htrace : WordTrace (prefixWord ++ tailWord_3068263) baseStart_3068263 baseEnd_3068263 := by
    simpa [prefixWord, tailWord_3068263, baseEnd_3068263] using wordTrace_append hprefix tailTrace_3068263
  have hstable : (prefixWord ++ tailWord_3068263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068263).length < 2 ^ (prefixWord ++ tailWord_3068263).sum := by decide
  have hdescent : baseEnd_3068263 < baseStart_3068263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068409 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 8]
def baseStart_3068409 : Nat := 118140960795 + 3068409 * 2 ^ 59
def prefixEnd_3068409 : Nat := 4983230072969 + 3 ^ 40 * 3068409 * 2
def baseEnd_3068409 : Nat := 350126369240397904305811

theorem tailTrace_3068409 : CollatzResearch.WordTrace tailWord_3068409 prefixEnd_3068409 350126369240397904305811 := by
  unfold tailWord_3068409
  simp only [CollatzResearch.WordTrace]
  refine ⟨111914070340685710381152281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74609380227123806920768187 111914070340685710381152281)
  ·
    refine ⟨83935552755514282785864211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111914070340685710381152281 83935552755514282785864211)
    ·
      refine ⟨125903329133271424178796317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83935552755514282785864211 125903329133271424178796317)
      ·
        refine ⟨47213748424976784067048619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125903329133271424178796317 47213748424976784067048619)
        ·
          refine ⟨70820622637465176100572929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47213748424976784067048619 70820622637465176100572929)
          ·
            refine ⟨53115466978098882075429697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70820622637465176100572929 53115466978098882075429697)
            ·
              refine ⟨39836600233574161556572273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53115466978098882075429697 39836600233574161556572273)
              ·
                refine ⟨29877450175180621167429205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39836600233574161556572273 29877450175180621167429205)
                ·
                  refine ⟨350126369240397904305811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29877450175180621167429205 350126369240397904305811)
                  ·
                    rfl

theorem cell22_3068409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_3068409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068409 prefixEnd_3068409 := by exact prefixLift 3068409
  have htrace : WordTrace (prefixWord ++ tailWord_3068409) baseStart_3068409 baseEnd_3068409 := by
    simpa [prefixWord, tailWord_3068409, baseEnd_3068409] using wordTrace_append hprefix tailTrace_3068409
  have hstable : (prefixWord ++ tailWord_3068409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068409).length < 2 ^ (prefixWord ++ tailWord_3068409).sum := by decide
  have hdescent : baseEnd_3068409 < baseStart_3068409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068445 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3068445 : Nat := 118140960795 + 3068445 * 2 ^ 59
def prefixEnd_3068445 : Nat := 4983230072969 + 3 ^ 40 * 3068445 * 2
def baseEnd_3068445 : Nat := 1050391431256901619017323

theorem tailTrace_3068445 : CollatzResearch.WordTrace tailWord_3068445 prefixEnd_3068445 1050391431256901619017323 := by
  unfold tailWord_3068445
  simp only [CollatzResearch.WordTrace]
  refine ⟨111915383368555288529462789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74610255579036859019641859 111915383368555288529462789)
  ·
    refine ⟨20984134381604116599274273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111915383368555288529462789 20984134381604116599274273)
    ·
      refine ⟨15738100786203087449455705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20984134381604116599274273 15738100786203087449455705)
      ·
        refine ⟨11803575589652315587091779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15738100786203087449455705 11803575589652315587091779)
        ·
          refine ⟨17705363384478473380637669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11803575589652315587091779 17705363384478473380637669)
          ·
            refine ⟨3319755634589713758869563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17705363384478473380637669 3319755634589713758869563)
            ·
              refine ⟨4979633451884570638304345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319755634589713758869563 4979633451884570638304345)
              ·
                refine ⟨3734725088913427978728259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4979633451884570638304345 3734725088913427978728259)
                ·
                  refine ⟨5602087633370141968092389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734725088913427978728259 5602087633370141968092389)
                  ·
                    refine ⟨1050391431256901619017323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602087633370141968092389 1050391431256901619017323)
                    ·
                      rfl

theorem cell22_3068445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3068445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068445 prefixEnd_3068445 := by exact prefixLift 3068445
  have htrace : WordTrace (prefixWord ++ tailWord_3068445) baseStart_3068445 baseEnd_3068445 := by
    simpa [prefixWord, tailWord_3068445, baseEnd_3068445] using wordTrace_append hprefix tailTrace_3068445
  have hstable : (prefixWord ++ tailWord_3068445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068445).length < 2 ^ (prefixWord ++ tailWord_3068445).sum := by decide
  have hdescent : baseEnd_3068445 < baseStart_3068445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068458 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3068458 : Nat := 118140960795 + 3068458 * 2 ^ 59
def prefixEnd_3068458 : Nat := 4983230072969 + 3 ^ 40 * 3068458 * 2
def baseEnd_3068458 : Nat := 1050395881422573918442283

theorem tailTrace_3068458 : CollatzResearch.WordTrace tailWord_3068458 prefixEnd_3068458 1050395881422573918442283 := by
  unfold tailWord_3068458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27978964379377047937421507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74610571678338794499790685 27978964379377047937421507)
  ·
    refine ⟨41968446569065571906132261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27978964379377047937421507 41968446569065571906132261)
    ·
      refine ⟨7869083731699794732399799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41968446569065571906132261 7869083731699794732399799)
      ·
        refine ⟨11803625597549692098599699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869083731699794732399799 11803625597549692098599699)
        ·
          refine ⟨17705438396324538147899549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11803625597549692098599699 17705438396324538147899549)
          ·
            refine ⟨6639539398621701805462331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17705438396324538147899549 6639539398621701805462331)
            ·
              refine ⟨9959309097932552708193497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639539398621701805462331 9959309097932552708193497)
              ·
                refine ⟨7469481823449414531145123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9959309097932552708193497 7469481823449414531145123)
                ·
                  refine ⟨11204222735174121796717685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7469481823449414531145123 11204222735174121796717685)
                  ·
                    refine ⟨1050395881422573918442283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11204222735174121796717685 1050395881422573918442283)
                    ·
                      rfl

theorem cell22_3068458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3068458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068458 prefixEnd_3068458 := by exact prefixLift 3068458
  have htrace : WordTrace (prefixWord ++ tailWord_3068458) baseStart_3068458 baseEnd_3068458 := by
    simpa [prefixWord, tailWord_3068458, baseEnd_3068458] using wordTrace_append hprefix tailTrace_3068458
  have hstable : (prefixWord ++ tailWord_3068458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068458).length < 2 ^ (prefixWord ++ tailWord_3068458).sum := by decide
  have hdescent : baseEnd_3068458 < baseStart_3068458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068462 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3068462 : Nat := 118140960795 + 3068462 * 2 ^ 59
def prefixEnd_3068462 : Nat := 4983230072969 + 3 ^ 40 * 3068462 * 2
def baseEnd_3068462 : Nat := 1050397250704319241342271

theorem tailTrace_3068462 : CollatzResearch.WordTrace tailWord_3068462 prefixEnd_3068462 1050397250704319241342271 := by
  unfold tailWord_3068462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989500426186712554103955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74610668939662466955221093 13989500426186712554103955)
  ·
    refine ⟨20984250639280068831155933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13989500426186712554103955 20984250639280068831155933)
    ·
      refine ⟨7869093989730025811683475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20984250639280068831155933 7869093989730025811683475)
      ·
        refine ⟨11803640984595038717525213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869093989730025811683475 11803640984595038717525213)
        ·
          refine ⟨4426365369223139519071955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11803640984595038717525213 4426365369223139519071955)
          ·
            refine ⟨6639548053834709278607933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426365369223139519071955 6639548053834709278607933)
            ·
              refine ⟨2489830520188015979477975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6639548053834709278607933 2489830520188015979477975)
              ·
                refine ⟨3734745780282023969216963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489830520188015979477975 3734745780282023969216963)
                ·
                  refine ⟨5602118670423035953825445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734745780282023969216963 5602118670423035953825445)
                  ·
                    refine ⟨1050397250704319241342271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602118670423035953825445 1050397250704319241342271)
                    ·
                      rfl

theorem cell22_3068462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3068462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068462 prefixEnd_3068462 := by exact prefixLift 3068462
  have htrace : WordTrace (prefixWord ++ tailWord_3068462) baseStart_3068462 baseEnd_3068462 := by
    simpa [prefixWord, tailWord_3068462, baseEnd_3068462] using wordTrace_append hprefix tailTrace_3068462
  have hstable : (prefixWord ++ tailWord_3068462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068462).length < 2 ^ (prefixWord ++ tailWord_3068462).sum := by decide
  have hdescent : baseEnd_3068462 < baseStart_3068462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068477 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 4]
def baseStart_3068477 : Nat := 118140960795 + 3068477 * 2 ^ 59
def prefixEnd_3068477 : Nat := 4983230072969 + 3 ^ 40 * 3068477 * 2
def baseEnd_3068477 : Nat := 350134128503621400739075

theorem tailTrace_3068477 : CollatzResearch.WordTrace tailWord_3068477 prefixEnd_3068477 350134128503621400739075 := by
  unfold tailWord_3068477
  simp only [CollatzResearch.WordTrace]
  refine ⟨111916550504439357994627685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74611033669626238663085123 111916550504439357994627685)
  ·
    refine ⟨20984353219582379623992691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111916550504439357994627685 20984353219582379623992691)
    ·
      refine ⟨31476529829373569435989037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984353219582379623992691 31476529829373569435989037)
      ·
        refine ⟨11803698686015088538495889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31476529829373569435989037 11803698686015088538495889)
        ·
          refine ⟨8852774014511316403871917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11803698686015088538495889 8852774014511316403871917)
          ·
            refine ⟨3319790255441743651451969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8852774014511316403871917 3319790255441743651451969)
            ·
              refine ⟨2489842691581307738588977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319790255441743651451969 2489842691581307738588977)
              ·
                refine ⟨1867382018685980803941733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489842691581307738588977 1867382018685980803941733)
                ·
                  refine ⟨350134128503621400739075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867382018685980803941733 350134128503621400739075)
                  ·
                    rfl

theorem cell22_3068477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_3068477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068477 prefixEnd_3068477 := by exact prefixLift 3068477
  have htrace : WordTrace (prefixWord ++ tailWord_3068477) baseStart_3068477 baseEnd_3068477 := by
    simpa [prefixWord, tailWord_3068477, baseEnd_3068477] using wordTrace_append hprefix tailTrace_3068477
  have hstable : (prefixWord ++ tailWord_3068477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068477).length < 2 ^ (prefixWord ++ tailWord_3068477).sum := by decide
  have hdescent : baseEnd_3068477 < baseStart_3068477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068503 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 3, 3]
def baseStart_3068503 : Nat := 118140960795 + 3068503 * 2 ^ 59
def prefixEnd_3068503 : Nat := 4983230072969 + 3 ^ 40 * 3068503 * 2
def baseEnd_3068503 : Nat := 1050411285842208801067145

theorem tailTrace_3068503 : CollatzResearch.WordTrace tailWord_3068503 prefixEnd_3068503 1050411285842208801067145 := by
  unfold tailWord_3068503
  simp only [CollatzResearch.WordTrace]
  refine ⟨111917498802345164435074163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74611665868230109623382775 111917498802345164435074163)
  ·
    refine ⟨167876248203517746652611245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111917498802345164435074163 167876248203517746652611245)
    ·
      refine ⟨62953593076319154994729217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167876248203517746652611245 62953593076319154994729217)
      ·
        refine ⟨47215194807239366246046913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62953593076319154994729217 47215194807239366246046913)
        ·
          refine ⟨35411396105429524684535185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47215194807239366246046913 35411396105429524684535185)
          ·
            refine ⟨26558547079072143513401389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35411396105429524684535185 26558547079072143513401389)
            ·
              refine ⟨9959455154652053817525521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26558547079072143513401389 9959455154652053817525521)
              ·
                refine ⟨7469591365989040363144141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9959455154652053817525521 7469591365989040363144141)
                ·
                  refine ⟨2801096762245890136179053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7469591365989040363144141 2801096762245890136179053)
                  ·
                    refine ⟨1050411285842208801067145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801096762245890136179053 1050411285842208801067145)
                    ·
                      rfl

theorem cell22_3068503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_3068503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068503 prefixEnd_3068503 := by exact prefixLift 3068503
  have htrace : WordTrace (prefixWord ++ tailWord_3068503) baseStart_3068503 baseEnd_3068503 := by
    simpa [prefixWord, tailWord_3068503, baseEnd_3068503] using wordTrace_append hprefix tailTrace_3068503
  have hstable : (prefixWord ++ tailWord_3068503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068503).length < 2 ^ (prefixWord ++ tailWord_3068503).sum := by decide
  have hdescent : baseEnd_3068503 < baseStart_3068503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068516 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_3068516 : Nat := 118140960795 + 3068516 * 2 ^ 59
def prefixEnd_3068516 : Nat := 4983230072969 + 3 ^ 40 * 3068516 * 2
def baseEnd_3068516 : Nat := 350138578669293700164035

theorem tailTrace_3068516 : CollatzResearch.WordTrace tailWord_3068516 prefixEnd_3068516 350138578669293700164035 := by
  unfold tailWord_3068516
  simp only [CollatzResearch.WordTrace]
  refine ⟨55958986475649033827648701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74611981967532045103531601 55958986475649033827648701)
  ·
    refine ⟨20984619928368387685368263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55958986475649033827648701 20984619928368387685368263)
    ·
      refine ⟨31476929892552581528052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984619928368387685368263 31476929892552581528052395)
      ·
        refine ⟨47215394838828872292078593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31476929892552581528052395 47215394838828872292078593)
        ·
          refine ⟨35411546129121654219058945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47215394838828872292078593 35411546129121654219058945)
          ·
            refine ⟨26558659596841240664294209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35411546129121654219058945 26558659596841240664294209)
            ·
              refine ⟨19918994697630930498220657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26558659596841240664294209 19918994697630930498220657)
              ·
                refine ⟨14939246023223197873665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19918994697630930498220657 14939246023223197873665493)
                ·
                  refine ⟨350138578669293700164035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14939246023223197873665493 350138578669293700164035)
                  ·
                    rfl

theorem cell22_3068516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_3068516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068516 prefixEnd_3068516 := by exact prefixLift 3068516
  have htrace : WordTrace (prefixWord ++ tailWord_3068516) baseStart_3068516 baseEnd_3068516 := by
    simpa [prefixWord, tailWord_3068516, baseEnd_3068516] using wordTrace_append hprefix tailTrace_3068516
  have hstable : (prefixWord ++ tailWord_3068516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068516).length < 2 ^ (prefixWord ++ tailWord_3068516).sum := by decide
  have hdescent : baseEnd_3068516 < baseStart_3068516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068548 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3068548 : Nat := 118140960795 + 3068548 * 2 ^ 59
def prefixEnd_3068548 : Nat := 4983230072969 + 3 ^ 40 * 3068548 * 2
def baseEnd_3068548 : Nat := 1050426690261843683692007

theorem tailTrace_3068548 : CollatzResearch.WordTrace tailWord_3068548 prefixEnd_3068548 1050426690261843683692007 := by
  unfold tailWord_3068548
  simp only [CollatzResearch.WordTrace]
  refine ⟨55959570043591068560231149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74612760058121424746974865 55959570043591068560231149)
  ·
    refine ⟨20984838766346650710086681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55959570043591068560231149 20984838766346650710086681)
    ·
      refine ⟨15738629074759988032565011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20984838766346650710086681 15738629074759988032565011)
      ·
        refine ⟨23607943612139982048847517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15738629074759988032565011 23607943612139982048847517)
        ·
          refine ⟨8852978854552493268317819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23607943612139982048847517 8852978854552493268317819)
          ·
            refine ⟨13279468281828739902476729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852978854552493268317819 13279468281828739902476729)
            ·
              refine ⟨9959601211371554926857547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13279468281828739902476729 9959601211371554926857547)
              ·
                refine ⟨14939401817057332390286321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959601211371554926857547 14939401817057332390286321)
                ·
                  refine ⟨11204551362792999292714741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14939401817057332390286321 11204551362792999292714741)
                  ·
                    refine ⟨1050426690261843683692007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11204551362792999292714741 1050426690261843683692007)
                    ·
                      rfl

theorem cell22_3068548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3068548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068548 prefixEnd_3068548 := by exact prefixLift 3068548
  have htrace : WordTrace (prefixWord ++ tailWord_3068548) baseStart_3068548 baseEnd_3068548 := by
    simpa [prefixWord, tailWord_3068548, baseEnd_3068548] using wordTrace_append hprefix tailTrace_3068548
  have hstable : (prefixWord ++ tailWord_3068548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068548).length < 2 ^ (prefixWord ++ tailWord_3068548).sum := by decide
  have hdescent : baseEnd_3068548 < baseStart_3068548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068614 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3068614 : Nat := 118140960795 + 3068614 * 2 ^ 59
def prefixEnd_3068614 : Nat := 4983230072969 + 3 ^ 40 * 3068614 * 2
def baseEnd_3068614 : Nat := 1050449283410641511541805

theorem tailTrace_3068614 : CollatzResearch.WordTrace tailWord_3068614 prefixEnd_3068614 1050449283410641511541805 := by
  unfold tailWord_3068614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497548353279469699761403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74614364869962020261576597 3497548353279469699761403)
  ·
    refine ⟨5246322529919204549642105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497548353279469699761403 5246322529919204549642105)
    ·
      refine ⟨3934741897439403412231579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5246322529919204549642105 3934741897439403412231579)
      ·
        refine ⟨5902112846159105118347369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934741897439403412231579 5902112846159105118347369)
        ·
          refine ⟨4426584634619328838760527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5902112846159105118347369 4426584634619328838760527)
          ·
            refine ⟨6639876951928993258140791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426584634619328838760527 6639876951928993258140791)
            ·
              refine ⟨9959815427893489887211187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639876951928993258140791 9959815427893489887211187)
              ·
                refine ⟨14939723141840234830816781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959815427893489887211187 14939723141840234830816781)
                ·
                  refine ⟨5602396178190088061556293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14939723141840234830816781 5602396178190088061556293)
                  ·
                    refine ⟨1050449283410641511541805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602396178190088061556293 1050449283410641511541805)
                    ·
                      rfl

theorem cell22_3068614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3068614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068614 prefixEnd_3068614 := by exact prefixLift 3068614
  have htrace : WordTrace (prefixWord ++ tailWord_3068614) baseStart_3068614 baseEnd_3068614 := by
    simpa [prefixWord, tailWord_3068614, baseEnd_3068614] using wordTrace_append hprefix tailTrace_3068614
  have hstable : (prefixWord ++ tailWord_3068614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068614).length < 2 ^ (prefixWord ++ tailWord_3068614).sum := by decide
  have hdescent : baseEnd_3068614 < baseStart_3068614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068653 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3068653 : Nat := 118140960795 + 3068653 * 2 ^ 59
def prefixEnd_3068653 : Nat := 4983230072969 + 3 ^ 40 * 3068653 * 2
def baseEnd_3068653 : Nat := 1050462633907658409816685

theorem tailTrace_3068653 : CollatzResearch.WordTrace tailWord_3068653 prefixEnd_3068653 1050462633907658409816685 := by
  unfold tailWord_3068653
  simp only [CollatzResearch.WordTrace]
  refine ⟨111922969751801740053034613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74615313167867826702023075 111922969751801740053034613)
  ·
    refine ⟨10492778414231413129971995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111922969751801740053034613 10492778414231413129971995)
    ·
      refine ⟨15739167621347119694957993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10492778414231413129971995 15739167621347119694957993)
      ·
        refine ⟨11804375716010339771218495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15739167621347119694957993 11804375716010339771218495)
        ·
          refine ⟨17706563574015509656827743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11804375716010339771218495 17706563574015509656827743)
          ·
            refine ⟨26559845361023264485241615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706563574015509656827743 26559845361023264485241615)
            ·
              refine ⟨39839768041534896727862423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26559845361023264485241615 39839768041534896727862423)
              ·
                refine ⟨59759652062302345091793635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39839768041534896727862423 59759652062302345091793635)
                ·
                  refine ⟨89639478093453517637690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59759652062302345091793635 89639478093453517637690453)
                  ·
                    refine ⟨1050462633907658409816685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89639478093453517637690453 1050462633907658409816685)
                    ·
                      rfl

theorem cell22_3068653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3068653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068653 prefixEnd_3068653 := by exact prefixLift 3068653
  have htrace : WordTrace (prefixWord ++ tailWord_3068653) baseStart_3068653 baseEnd_3068653 := by
    simpa [prefixWord, tailWord_3068653, baseEnd_3068653] using wordTrace_append hprefix tailTrace_3068653
  have hstable : (prefixWord ++ tailWord_3068653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068653).length < 2 ^ (prefixWord ++ tailWord_3068653).sum := by decide
  have hdescent : baseEnd_3068653 < baseStart_3068653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068740 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3068740 : Nat := 118140960795 + 3068740 * 2 ^ 59
def prefixEnd_3068740 : Nat := 4983230072969 + 3 ^ 40 * 3068740 * 2
def baseEnd_3068740 : Nat := 1050492415785619182891419

theorem tailTrace_3068740 : CollatzResearch.WordTrace tailWord_3068740 prefixEnd_3068740 1050492415785619182891419 := by
  unfold tailWord_3068740
  simp only [CollatzResearch.WordTrace]
  refine ⟨55963071451243276955725837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74617428601657702607634449 55963071451243276955725837)
  ·
    refine ⟨20986151794216228858397189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55963071451243276955725837 20986151794216228858397189)
    ·
      refine ⟨3934903461415542910949473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20986151794216228858397189 3934903461415542910949473)
      ·
        refine ⟨2951177596061657183212105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3934903461415542910949473 2951177596061657183212105)
        ·
          refine ⟨2213383197046242887409079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2951177596061657183212105 2213383197046242887409079)
          ·
            refine ⟨3320074795569364331113619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213383197046242887409079 3320074795569364331113619)
            ·
              refine ⟨4980112193354046496670429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320074795569364331113619 4980112193354046496670429)
              ·
                refine ⟨1867542072507767436251411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4980112193354046496670429 1867542072507767436251411)
                ·
                  refine ⟨2801313108761651154377117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867542072507767436251411 2801313108761651154377117)
                  ·
                    refine ⟨1050492415785619182891419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801313108761651154377117 1050492415785619182891419)
                    ·
                      rfl

theorem cell22_3068740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3068740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068740 prefixEnd_3068740 := by exact prefixLift 3068740
  have htrace : WordTrace (prefixWord ++ tailWord_3068740) baseStart_3068740 baseEnd_3068740 := by
    simpa [prefixWord, tailWord_3068740, baseEnd_3068740] using wordTrace_append hprefix tailTrace_3068740
  have hstable : (prefixWord ++ tailWord_3068740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068740).length < 2 ^ (prefixWord ++ tailWord_3068740).sum := by decide
  have hdescent : baseEnd_3068740 < baseStart_3068740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068745 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_3068745 : Nat := 118140960795 + 3068745 * 2 ^ 59
def prefixEnd_3068745 : Nat := 4983230072969 + 3 ^ 40 * 3068745 * 2
def baseEnd_3068745 : Nat := 1050494127387800836516403

theorem tailTrace_3068745 : CollatzResearch.WordTrace tailWord_3068745 prefixEnd_3068745 1050494127387800836516403 := by
  unfold tailWord_3068745
  simp only [CollatzResearch.WordTrace]
  refine ⟨111926325267468439765383689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74617550178312293176922459 111926325267468439765383689)
  ·
    refine ⟨83944743950601329824037767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111926325267468439765383689 83944743950601329824037767)
    ·
      refine ⟨125917115925901994736056651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83944743950601329824037767 125917115925901994736056651)
      ·
        refine ⟨188875673888852992104084977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125917115925901994736056651 188875673888852992104084977)
        ·
          refine ⟨141656755416639744078063733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188875673888852992104084977 141656755416639744078063733)
          ·
            refine ⟨13280320820309976007318475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141656755416639744078063733 13280320820309976007318475)
            ·
              refine ⟨19920481230464964010977713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280320820309976007318475 19920481230464964010977713)
              ·
                refine ⟨14940360922848723008233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19920481230464964010977713 14940360922848723008233285)
                ·
                  refine ⟨2801317673034135564043741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14940360922848723008233285 2801317673034135564043741)
                  ·
                    refine ⟨1050494127387800836516403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801317673034135564043741 1050494127387800836516403)
                    ·
                      rfl

theorem cell22_3068745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_3068745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068745 prefixEnd_3068745 := by exact prefixLift 3068745
  have htrace : WordTrace (prefixWord ++ tailWord_3068745) baseStart_3068745 baseEnd_3068745 := by
    simpa [prefixWord, tailWord_3068745, baseEnd_3068745] using wordTrace_append hprefix tailTrace_3068745
  have hstable : (prefixWord ++ tailWord_3068745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068745).length < 2 ^ (prefixWord ++ tailWord_3068745).sum := by decide
  have hdescent : baseEnd_3068745 < baseStart_3068745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068775 : List Nat := [1, 1, 5, 1, 2, 3, 2, 7]
def baseStart_3068775 : Nat := 118140960795 + 3068775 * 2 ^ 59
def prefixEnd_3068775 : Nat := 4983230072969 + 3 ^ 40 * 3068775 * 2
def baseEnd_3068775 : Nat := 116722710777876750918479

theorem tailTrace_3068775 : CollatzResearch.WordTrace tailWord_3068775 prefixEnd_3068775 116722710777876750918479 := by
  unfold tailWord_3068775
  simp only [CollatzResearch.WordTrace]
  refine ⟨111927419457359754888975779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74618279638239836592650519 111927419457359754888975779)
  ·
    refine ⟨167891129186039632333463669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111927419457359754888975779 167891129186039632333463669)
    ·
      refine ⟨15739793361191215531262219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167891129186039632333463669 15739793361191215531262219)
      ·
        refine ⟨23609690041786823296893329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15739793361191215531262219 23609690041786823296893329)
        ·
          refine ⟨17707267531340117472669997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23609690041786823296893329 17707267531340117472669997)
          ·
            refine ⟨6640225324252544052251249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17707267531340117472669997 6640225324252544052251249)
            ·
              refine ⟨4980168993189408039188437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6640225324252544052251249 4980168993189408039188437)
              ·
                refine ⟨116722710777876750918479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4980168993189408039188437 116722710777876750918479)
                ·
                  rfl

theorem cell22_3068775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 7].length) (baseStart_3068775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068775 prefixEnd_3068775 := by exact prefixLift 3068775
  have htrace : WordTrace (prefixWord ++ tailWord_3068775) baseStart_3068775 baseEnd_3068775 := by
    simpa [prefixWord, tailWord_3068775, baseEnd_3068775] using wordTrace_append hprefix tailTrace_3068775
  have hstable : (prefixWord ++ tailWord_3068775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068775).length < 2 ^ (prefixWord ++ tailWord_3068775).sum := by decide
  have hdescent : baseEnd_3068775 < baseStart_3068775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068882 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_3068882 : Nat := 118140960795 + 3068882 * 2 ^ 59
def prefixEnd_3068882 : Nat := 4983230072969 + 3 ^ 40 * 3068882 * 2
def baseEnd_3068882 : Nat := 350180341762526048613661

theorem tailTrace_3068882 : CollatzResearch.WordTrace tailWord_3068882 prefixEnd_3068882 350180341762526048613661 := by
  unfold tailWord_3068882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982830516993028040780225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74620881378648074775413933 27982830516993028040780225)
  ·
    refine ⟨20987122887744771030585169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27982830516993028040780225 20987122887744771030585169)
    ·
      refine ⟨15740342165808578272938877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20987122887744771030585169 15740342165808578272938877)
      ·
        refine ⟨5902628312178216852352079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15740342165808578272938877 5902628312178216852352079)
        ·
          refine ⟨8853942468267325278528119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902628312178216852352079 8853942468267325278528119)
          ·
            refine ⟨13280913702400987917792179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853942468267325278528119 13280913702400987917792179)
            ·
              refine ⟨19921370553601481876688269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280913702400987917792179 19921370553601481876688269)
              ·
                refine ⟨7470513957600555703758101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19921370553601481876688269 7470513957600555703758101)
                ·
                  refine ⟨350180341762526048613661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7470513957600555703758101 350180341762526048613661)
                  ·
                    rfl

theorem cell22_3068882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_3068882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068882 prefixEnd_3068882 := by exact prefixLift 3068882
  have htrace : WordTrace (prefixWord ++ tailWord_3068882) baseStart_3068882 baseEnd_3068882 := by
    simpa [prefixWord, tailWord_3068882, baseEnd_3068882] using wordTrace_append hprefix tailTrace_3068882
  have hstable : (prefixWord ++ tailWord_3068882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068882).length < 2 ^ (prefixWord ++ tailWord_3068882).sum := by decide
  have hdescent : baseEnd_3068882 < baseStart_3068882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068901 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_3068901 : Nat := 118140960795 + 3068901 * 2 ^ 59
def prefixEnd_3068901 : Nat := 4983230072969 + 3 ^ 40 * 3068901 * 2
def baseEnd_3068901 : Nat := 1050547529375868429615925

theorem tailTrace_3068901 : CollatzResearch.WordTrace tailWord_3068901 prefixEnd_3068901 1050547529375868429615925 := by
  unfold tailWord_3068901
  simp only [CollatzResearch.WordTrace]
  refine ⟨111932015054903278408062557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74621343369935518938708371 111932015054903278408062557)
  ·
    refine ⟨41974505645588729403023459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111932015054903278408062557 41974505645588729403023459)
    ·
      refine ⟨62961758468383094104535189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41974505645588729403023459 62961758468383094104535189)
      ·
        refine ⟨2951332428205457536150087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62961758468383094104535189 2951332428205457536150087)
        ·
          refine ⟨4426998642308186304225131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951332428205457536150087 4426998642308186304225131)
          ·
            refine ⟨6640497963462279456337697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426998642308186304225131 6640497963462279456337697)
            ·
              refine ⟨4980373472596709592253273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6640497963462279456337697 4980373472596709592253273)
              ·
                refine ⟨3735280104447532194189955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980373472596709592253273 3735280104447532194189955)
                ·
                  refine ⟨5602920156671298291284933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735280104447532194189955 5602920156671298291284933)
                  ·
                    refine ⟨1050547529375868429615925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602920156671298291284933 1050547529375868429615925)
                    ·
                      rfl

theorem cell22_3068901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_3068901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068901 prefixEnd_3068901 := by exact prefixLift 3068901
  have htrace : WordTrace (prefixWord ++ tailWord_3068901) baseStart_3068901 baseEnd_3068901 := by
    simpa [prefixWord, tailWord_3068901, baseEnd_3068901] using wordTrace_append hprefix tailTrace_3068901
  have hstable : (prefixWord ++ tailWord_3068901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068901).length < 2 ^ (prefixWord ++ tailWord_3068901).sum := by decide
  have hdescent : baseEnd_3068901 < baseStart_3068901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068989 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3068989 : Nat := 118140960795 + 3068989 * 2 ^ 59
def prefixEnd_3068989 : Nat := 4983230072969 + 3 ^ 40 * 3068989 * 2
def baseEnd_3068989 : Nat := 350192551191421844471885

theorem tailTrace_3068989 : CollatzResearch.WordTrace tailWord_3068989 prefixEnd_3068989 350192551191421844471885 := by
  unfold tailWord_3068989
  simp only [CollatzResearch.WordTrace]
  refine ⟨111935224678584469437266021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74623483119056312958177347 111935224678584469437266021)
  ·
    refine ⟨20987854627234588019487379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111935224678584469437266021 20987854627234588019487379)
    ·
      refine ⟨31481781940851882029231069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20987854627234588019487379 31481781940851882029231069)
      ·
        refine ⟨11805668227819455760961651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31481781940851882029231069 11805668227819455760961651)
        ·
          refine ⟨17708502341729183641442477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11805668227819455760961651 17708502341729183641442477)
          ·
            refine ⟨6640688378148443865540929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17708502341729183641442477 6640688378148443865540929)
            ·
              refine ⟨4980516283611332899155697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6640688378148443865540929 4980516283611332899155697)
              ·
                refine ⟨3735387212708499674366773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980516283611332899155697 3735387212708499674366773)
                ·
                  refine ⟨350192551191421844471885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3735387212708499674366773 350192551191421844471885)
                  ·
                    rfl

theorem cell22_3068989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3068989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068989 prefixEnd_3068989 := by exact prefixLift 3068989
  have htrace : WordTrace (prefixWord ++ tailWord_3068989) baseStart_3068989 baseEnd_3068989 := by
    simpa [prefixWord, tailWord_3068989, baseEnd_3068989] using wordTrace_append hprefix tailTrace_3068989
  have hstable : (prefixWord ++ tailWord_3068989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068989).length < 2 ^ (prefixWord ++ tailWord_3068989).sum := by decide
  have hdescent : baseEnd_3068989 < baseStart_3068989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068993 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3068993 : Nat := 118140960795 + 3068993 * 2 ^ 59
def prefixEnd_3068993 : Nat := 4983230072969 + 3 ^ 40 * 3068993 * 2
def baseEnd_3068993 : Nat := 1050579022856010856315643

theorem tailTrace_3068993 : CollatzResearch.WordTrace tailWord_3068993 prefixEnd_3068993 1050579022856010856315643 := by
  unfold tailWord_3068993
  simp only [CollatzResearch.WordTrace]
  refine ⟨111935370570569978120411633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74623580380379985413607755 111935370570569978120411633)
  ·
    refine ⟨83951527927927483590308725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111935370570569978120411633 83951527927927483590308725)
    ·
      refine ⟨7870455743243201586591443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83951527927927483590308725 7870455743243201586591443)
      ·
        refine ⟨11805683614864802379887165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870455743243201586591443 11805683614864802379887165)
        ·
          refine ⟨4427131355574300892457687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11805683614864802379887165 4427131355574300892457687)
          ·
            refine ⟨6640697033361451338686531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427131355574300892457687 6640697033361451338686531)
            ·
              refine ⟨9961045550042177008029797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640697033361451338686531 9961045550042177008029797)
              ·
                refine ⟨1867696040632908189005587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9961045550042177008029797 1867696040632908189005587)
                ·
                  refine ⟨2801544060949362283508381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867696040632908189005587 2801544060949362283508381)
                  ·
                    refine ⟨1050579022856010856315643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801544060949362283508381 1050579022856010856315643)
                    ·
                      rfl

theorem cell22_3068993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3068993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3068993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3068993 prefixEnd_3068993 := by exact prefixLift 3068993
  have htrace : WordTrace (prefixWord ++ tailWord_3068993) baseStart_3068993 baseEnd_3068993 := by
    simpa [prefixWord, tailWord_3068993, baseEnd_3068993] using wordTrace_append hprefix tailTrace_3068993
  have hstable : (prefixWord ++ tailWord_3068993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068993).length < 2 ^ (prefixWord ++ tailWord_3068993).sum := by decide
  have hdescent : baseEnd_3068993 < baseStart_3068993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069002 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3069002 : Nat := 118140960795 + 3069002 * 2 ^ 59
def prefixEnd_3069002 : Nat := 4983230072969 + 3 ^ 40 * 3069002 * 2
def baseEnd_3069002 : Nat := 1050582103739937832840615

theorem tailTrace_3069002 : CollatzResearch.WordTrace tailWord_3069002 prefixEnd_3069002 1050582103739937832840615 := by
  unfold tailWord_3069002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27983924706884343164372315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74623799218358248438326173 27983924706884343164372315)
  ·
    refine ⟨41975887060326514746558473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27983924706884343164372315 41975887060326514746558473)
    ·
      refine ⟨31481915295244886059918855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41975887060326514746558473 31481915295244886059918855)
      ·
        refine ⟨47222872942867329089878283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31481915295244886059918855 47222872942867329089878283)
        ·
          refine ⟨70834309414300993634817425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47222872942867329089878283 70834309414300993634817425)
          ·
            refine ⟨53125732060725745226113069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70834309414300993634817425 53125732060725745226113069)
            ·
              refine ⟨19922149522772154459792401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53125732060725745226113069 19922149522772154459792401)
              ·
                refine ⟨14941612142079115844844301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19922149522772154459792401 14941612142079115844844301)
                ·
                  refine ⟨5603104553279668441816613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14941612142079115844844301 5603104553279668441816613)
                  ·
                    refine ⟨1050582103739937832840615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5603104553279668441816613 1050582103739937832840615)
                    ·
                      rfl

theorem cell22_3069002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3069002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069002 prefixEnd_3069002 := by exact prefixLift 3069002
  have htrace : WordTrace (prefixWord ++ tailWord_3069002) baseStart_3069002 baseEnd_3069002 := by
    simpa [prefixWord, tailWord_3069002, baseEnd_3069002] using wordTrace_append hprefix tailTrace_3069002
  have hstable : (prefixWord ++ tailWord_3069002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069002).length < 2 ^ (prefixWord ++ tailWord_3069002).sum := by decide
  have hdescent : baseEnd_3069002 < baseStart_3069002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069047 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3069047 : Nat := 118140960795 + 3069047 * 2 ^ 59
def prefixEnd_3069047 : Nat := 4983230072969 + 3 ^ 40 * 3069047 * 2
def baseEnd_3069047 : Nat := 1050597508159572715465477

theorem tailTrace_3069047 : CollatzResearch.WordTrace tailWord_3069047 prefixEnd_3069047 1050597508159572715465477 := by
  unfold tailWord_3069047
  simp only [CollatzResearch.WordTrace]
  refine ⟨111937340112374345342877395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74624893408249563561918263 111937340112374345342877395)
  ·
    refine ⟨167906010168561518014316093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111937340112374345342877395 167906010168561518014316093)
    ·
      refine ⟨62964753813210569255368535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167906010168561518014316093 62964753813210569255368535)
      ·
        refine ⟨94447130719815853883052803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62964753813210569255368535 94447130719815853883052803)
        ·
          refine ⟨141670696079723780824579205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94447130719815853883052803 141670696079723780824579205)
          ·
            refine ⟨26563255514948208904608601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141670696079723780824579205 26563255514948208904608601)
            ·
              refine ⟨19922441636211156678456451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26563255514948208904608601 19922441636211156678456451)
              ·
                refine ⟨29883662454316735017684677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19922441636211156678456451 29883662454316735017684677)
                ·
                  refine ⟨5603186710184387815815877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29883662454316735017684677 5603186710184387815815877)
                  ·
                    refine ⟨1050597508159572715465477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5603186710184387815815877 1050597508159572715465477)
                    ·
                      rfl

theorem cell22_3069047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3069047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069047 prefixEnd_3069047 := by exact prefixLift 3069047
  have htrace : WordTrace (prefixWord ++ tailWord_3069047) baseStart_3069047 baseEnd_3069047 := by
    simpa [prefixWord, tailWord_3069047, baseEnd_3069047] using wordTrace_append hprefix tailTrace_3069047
  have hstable : (prefixWord ++ tailWord_3069047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069047).length < 2 ^ (prefixWord ++ tailWord_3069047).sum := by decide
  have hdescent : baseEnd_3069047 < baseStart_3069047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069079 : List Nat := [1, 1, 3, 3, 3, 1, 4, 6]
def baseStart_3069079 : Nat := 118140960795 + 3069079 * 2 ^ 59
def prefixEnd_3069079 : Nat := 4983230072969 + 3 ^ 40 * 3069079 * 2
def baseEnd_3069079 : Nat := 116734273601503922073931

theorem tailTrace_3069079 : CollatzResearch.WordTrace tailWord_3069079 prefixEnd_3069079 116734273601503922073931 := by
  unfold tailWord_3069079
  simp only [CollatzResearch.WordTrace]
  refine ⟨111938507248258414808042291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74625671498838943205361527 111938507248258414808042291)
  ·
    refine ⟨167907760872387622212063437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111938507248258414808042291 167907760872387622212063437)
    ·
      refine ⟨62965410327145358329523789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167907760872387622212063437 62965410327145358329523789)
      ·
        refine ⟨23612028872679509373571421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62965410327145358329523789 23612028872679509373571421)
        ·
          refine ⟨8854510827254816015089283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23612028872679509373571421 8854510827254816015089283)
          ·
            refine ⟨13281766240882224022633925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854510827254816015089283 13281766240882224022633925)
            ·
              refine ⟨2490331170165417004243861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13281766240882224022633925 2490331170165417004243861)
              ·
                refine ⟨116734273601503922073931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2490331170165417004243861 116734273601503922073931)
                ·
                  rfl

theorem cell22_3069079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 6].length) (baseStart_3069079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069079 prefixEnd_3069079 := by exact prefixLift 3069079
  have htrace : WordTrace (prefixWord ++ tailWord_3069079) baseStart_3069079 baseEnd_3069079 := by
    simpa [prefixWord, tailWord_3069079, baseEnd_3069079] using wordTrace_append hprefix tailTrace_3069079
  have hstable : (prefixWord ++ tailWord_3069079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069079).length < 2 ^ (prefixWord ++ tailWord_3069079).sum := by decide
  have hdescent : baseEnd_3069079 < baseStart_3069079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069107 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 7]
def baseStart_3069107 : Nat := 118140960795 + 3069107 * 2 ^ 59
def prefixEnd_3069107 : Nat := 4983230072969 + 3 ^ 40 * 3069107 * 2
def baseEnd_3069107 : Nat := 350206015795250852988431

theorem tailTrace_3069107 : CollatzResearch.WordTrace tailWord_3069107 prefixEnd_3069107 350206015795250852988431 := by
  unfold tailWord_3069107
  simp only [CollatzResearch.WordTrace]
  refine ⟨111939528492156975590061575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74626352328104650393374383 111939528492156975590061575)
  ·
    refine ⟨167909292738235463385092363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111939528492156975590061575 167909292738235463385092363)
    ·
      refine ⟨251863939107353195077638545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167909292738235463385092363 251863939107353195077638545)
      ·
        refine ⟨188897954330514896308228909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251863939107353195077638545 188897954330514896308228909)
        ·
          refine ⟨70836732873943086115585841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188897954330514896308228909 70836732873943086115585841)
          ·
            refine ⟨53127549655457314586689381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70836732873943086115585841 53127549655457314586689381)
            ·
              refine ⟨9961415560398246485004259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53127549655457314586689381 9961415560398246485004259)
              ·
                refine ⟨14942123340597369727506389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961415560398246485004259 14942123340597369727506389)
                ·
                  refine ⟨350206015795250852988431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14942123340597369727506389 350206015795250852988431)
                  ·
                    rfl

theorem cell22_3069107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_3069107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069107 prefixEnd_3069107 := by exact prefixLift 3069107
  have htrace : WordTrace (prefixWord ++ tailWord_3069107) baseStart_3069107 baseEnd_3069107 := by
    simpa [prefixWord, tailWord_3069107, baseEnd_3069107] using wordTrace_append hprefix tailTrace_3069107
  have hstable : (prefixWord ++ tailWord_3069107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069107).length < 2 ^ (prefixWord ++ tailWord_3069107).sum := by decide
  have hdescent : baseEnd_3069107 < baseStart_3069107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069184 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_3069184 : Nat := 118140960795 + 3069184 * 2 ^ 59
def prefixEnd_3069184 : Nat := 4983230072969 + 3 ^ 40 * 3069184 * 2
def baseEnd_3069184 : Nat := 1050644406059350024790057

theorem tailTrace_3069184 : CollatzResearch.WordTrace tailWord_3069184 prefixEnd_3069184 1050644406059350024790057 := by
  unfold tailWord_3069184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55971168456439008870307303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74628224608585345160409737 55971168456439008870307303)
  ·
    refine ⟨83956752684658513305460955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55971168456439008870307303 83956752684658513305460955)
    ·
      refine ⟨125935129026987769958191433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83956752684658513305460955 125935129026987769958191433)
      ·
        refine ⟨94451346770240827468643575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125935129026987769958191433 94451346770240827468643575)
        ·
          refine ⟨141677020155361241202965363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94451346770240827468643575 141677020155361241202965363)
          ·
            refine ⟨212515530233041861804448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141677020155361241202965363 212515530233041861804448045)
            ·
              refine ⟨79693323837390698176668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212515530233041861804448045 79693323837390698176668017)
              ·
                refine ⟨59769992878043023632501013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79693323837390698176668017 59769992878043023632501013)
                ·
                  refine ⟨2801718416158266732773485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59769992878043023632501013 2801718416158266732773485)
                  ·
                    refine ⟨1050644406059350024790057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801718416158266732773485 1050644406059350024790057)
                    ·
                      rfl

theorem cell22_3069184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_3069184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069184 prefixEnd_3069184 := by exact prefixLift 3069184
  have htrace : WordTrace (prefixWord ++ tailWord_3069184) baseStart_3069184 baseEnd_3069184 := by
    simpa [prefixWord, tailWord_3069184, baseEnd_3069184] using wordTrace_append hprefix tailTrace_3069184
  have hstable : (prefixWord ++ tailWord_3069184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069184).length < 2 ^ (prefixWord ++ tailWord_3069184).sum := by decide
  have hdescent : baseEnd_3069184 < baseStart_3069184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069218 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3069218 : Nat := 118140960795 + 3069218 * 2 ^ 59
def prefixEnd_3069218 : Nat := 4983230072969 + 3 ^ 40 * 3069218 * 2
def baseEnd_3069218 : Nat := 1050656044954185269439953

theorem tailTrace_3069218 : CollatzResearch.WordTrace tailWord_3069218 prefixEnd_3069218 1050656044954185269439953 := by
  unfold tailWord_3069218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27985894248688710386838077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74629051329836561031568205 27985894248688710386838077)
  ·
    refine ⟨10494710343258266395064279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27985894248688710386838077 10494710343258266395064279)
    ·
      refine ⟨15742065514887399592596419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10494710343258266395064279 15742065514887399592596419)
      ·
        refine ⟨23613098272331099388894629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15742065514887399592596419 23613098272331099388894629)
        ·
          refine ⟨4427455926062081135417743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23613098272331099388894629 4427455926062081135417743)
          ·
            refine ⟨6641183889093121703126615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427455926062081135417743 6641183889093121703126615)
            ·
              refine ⟨9961775833639682554689923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641183889093121703126615 9961775833639682554689923)
              ·
                refine ⟨14942663750459523832034885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961775833639682554689923 14942663750459523832034885)
                ·
                  refine ⟨2801749453211160718506541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14942663750459523832034885 2801749453211160718506541)
                  ·
                    refine ⟨1050656044954185269439953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801749453211160718506541 1050656044954185269439953)
                    ·
                      rfl

theorem cell22_3069218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3069218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069218 prefixEnd_3069218 := by exact prefixLift 3069218
  have htrace : WordTrace (prefixWord ++ tailWord_3069218) baseStart_3069218 baseEnd_3069218 := by
    simpa [prefixWord, tailWord_3069218, baseEnd_3069218] using wordTrace_append hprefix tailTrace_3069218
  have hstable : (prefixWord ++ tailWord_3069218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069218).length < 2 ^ (prefixWord ++ tailWord_3069218).sum := by decide
  have hdescent : baseEnd_3069218 < baseStart_3069218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069254 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3069254 : Nat := 118140960795 + 3069254 * 2 ^ 59
def prefixEnd_3069254 : Nat := 4983230072969 + 3 ^ 40 * 3069254 * 2
def baseEnd_3069254 : Nat := 350222789496631058513281

theorem tailTrace_3069254 : CollatzResearch.WordTrace tailWord_3069254 prefixEnd_3069254 350222789496631058513281 := by
  unfold tailWord_3069254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498277813207013115489463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74629926681749613130441877 3498277813207013115489463)
  ·
    refine ⟨5247416719810519673234195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498277813207013115489463 5247416719810519673234195)
    ·
      refine ⟨7871125079715779509851293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247416719810519673234195 7871125079715779509851293)
      ·
        refine ⟨2951671904893417316194235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7871125079715779509851293 2951671904893417316194235)
        ·
          refine ⟨4427507857340125974291353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951671904893417316194235 4427507857340125974291353)
          ·
            refine ⟨3320630893005094480718515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4427507857340125974291353 3320630893005094480718515)
            ·
              refine ⟨4980946339507641721077773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320630893005094480718515 4980946339507641721077773)
              ·
                refine ⟨1867854877315365645404165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4980946339507641721077773 1867854877315365645404165)
                ·
                  refine ⟨350222789496631058513281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867854877315365645404165 350222789496631058513281)
                  ·
                    rfl

theorem cell22_3069254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3069254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069254 prefixEnd_3069254 := by exact prefixLift 3069254
  have htrace : WordTrace (prefixWord ++ tailWord_3069254) baseStart_3069254 baseEnd_3069254 := by
    simpa [prefixWord, tailWord_3069254, baseEnd_3069254] using wordTrace_append hprefix tailTrace_3069254
  have hstable : (prefixWord ++ tailWord_3069254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069254).length < 2 ^ (prefixWord ++ tailWord_3069254).sum := by decide
  have hdescent : baseEnd_3069254 < baseStart_3069254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069274 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_3069274 : Nat := 118140960795 + 3069274 * 2 ^ 59
def prefixEnd_3069274 : Nat := 4983230072969 + 3 ^ 40 * 3069274 * 2
def baseEnd_3069274 : Nat := 1050675214898619790039781

theorem tailTrace_3069274 : CollatzResearch.WordTrace tailWord_3069274 prefixEnd_3069274 1050675214898619790039781 := by
  unfold tailWord_3069274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986404870637990777847719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74630412988367975407593917 27986404870637990777847719)
  ·
    refine ⟨41979607305956986166771579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986404870637990777847719 41979607305956986166771579)
    ·
      refine ⟨62969410958935479250157369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41979607305956986166771579 62969410958935479250157369)
      ·
        refine ⟨47227058219201609437618027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62969410958935479250157369 47227058219201609437618027)
        ·
          refine ⟨70840587328802414156427041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47227058219201609437618027 70840587328802414156427041)
          ·
            refine ⟨53130440496601810617320281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70840587328802414156427041 53130440496601810617320281)
            ·
              refine ⟨39847830372451357962990211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53130440496601810617320281 39847830372451357962990211)
              ·
                refine ⟨59771745558677036944485317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39847830372451357962990211 59771745558677036944485317)
                ·
                  refine ⟨11207202292251944427090997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59771745558677036944485317 11207202292251944427090997)
                  ·
                    refine ⟨1050675214898619790039781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11207202292251944427090997 1050675214898619790039781)
                    ·
                      rfl

theorem cell22_3069274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_3069274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069274 prefixEnd_3069274 := by exact prefixLift 3069274
  have htrace : WordTrace (prefixWord ++ tailWord_3069274) baseStart_3069274 baseEnd_3069274 := by
    simpa [prefixWord, tailWord_3069274, baseEnd_3069274] using wordTrace_append hprefix tailTrace_3069274
  have hstable : (prefixWord ++ tailWord_3069274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069274).length < 2 ^ (prefixWord ++ tailWord_3069274).sum := by decide
  have hdescent : baseEnd_3069274 < baseStart_3069274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069293 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3069293 : Nat := 118140960795 + 3069293 * 2 ^ 59
def prefixEnd_3069293 : Nat := 4983230072969 + 3 ^ 40 * 3069293 * 2
def baseEnd_3069293 : Nat := 350227239662303357938241

theorem tailTrace_3069293 : CollatzResearch.WordTrace tailWord_3069293 prefixEnd_3069293 350227239662303357938241 := by
  unfold tailWord_3069293
  simp only [CollatzResearch.WordTrace]
  refine ⟨111946312469483129356332533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74630874979655419570888355 111946312469483129356332533)
  ·
    refine ⟨10494966794014043377156175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111946312469483129356332533 10494966794014043377156175)
    ·
      refine ⟨15742450191021065065734263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10494966794014043377156175 15742450191021065065734263)
      ·
        refine ⟨23613675286531597598601395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15742450191021065065734263 23613675286531597598601395)
        ·
          refine ⟨35420512929797396397902093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23613675286531597598601395 35420512929797396397902093)
          ·
            refine ⟨13282692348674023649213285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35420512929797396397902093 13282692348674023649213285)
            ·
              refine ⟨2490504815376379434227491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13282692348674023649213285 2490504815376379434227491)
              ·
                refine ⟨3735757223064569151341237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490504815376379434227491 3735757223064569151341237)
                ·
                  refine ⟨350227239662303357938241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3735757223064569151341237 350227239662303357938241)
                  ·
                    rfl

theorem cell22_3069293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3069293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069293 prefixEnd_3069293 := by exact prefixLift 3069293
  have htrace : WordTrace (prefixWord ++ tailWord_3069293) baseStart_3069293 baseEnd_3069293 := by
    simpa [prefixWord, tailWord_3069293, baseEnd_3069293] using wordTrace_append hprefix tailTrace_3069293
  have hstable : (prefixWord ++ tailWord_3069293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069293).length < 2 ^ (prefixWord ++ tailWord_3069293).sum := by decide
  have hdescent : baseEnd_3069293 < baseStart_3069293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069323 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 1, 4]
def baseStart_3069323 : Nat := 118140960795 + 3069323 * 2 ^ 59
def prefixEnd_3069323 : Nat := 4983230072969 + 3 ^ 40 * 3069323 * 2
def baseEnd_3069323 : Nat := 1050691988599999995564631

theorem tailTrace_3069323 : CollatzResearch.WordTrace tailWord_3069323 prefixEnd_3069323 1050691988599999995564631 := by
  unfold tailWord_3069323
  simp only [CollatzResearch.WordTrace]
  refine ⟨111947406659374444479924623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74631604439582962986616415 111947406659374444479924623)
  ·
    refine ⟨167921109989061666719886935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111947406659374444479924623 167921109989061666719886935)
    ·
      refine ⟨251881664983592500079830403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167921109989061666719886935 251881664983592500079830403)
      ·
        refine ⟨377822497475388750119745605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251881664983592500079830403 377822497475388750119745605)
        ·
          refine ⟨70841718276635390647452301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377822497475388750119745605 70841718276635390647452301)
          ·
            refine ⟨26565644353738271492794613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70841718276635390647452301 26565644353738271492794613)
            ·
              refine ⟨2490529158162962952449495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26565644353738271492794613 2490529158162962952449495)
              ·
                refine ⟨3735793737244444428674243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490529158162962952449495 3735793737244444428674243)
                ·
                  refine ⟨5603690605866666643011365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735793737244444428674243 5603690605866666643011365)
                  ·
                    refine ⟨1050691988599999995564631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5603690605866666643011365 1050691988599999995564631)
                    ·
                      rfl

theorem cell22_3069323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 4].length) (baseStart_3069323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069323 prefixEnd_3069323 := by exact prefixLift 3069323
  have htrace : WordTrace (prefixWord ++ tailWord_3069323) baseStart_3069323 baseEnd_3069323 := by
    simpa [prefixWord, tailWord_3069323, baseEnd_3069323] using wordTrace_append hprefix tailTrace_3069323
  have hstable : (prefixWord ++ tailWord_3069323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069323).length < 2 ^ (prefixWord ++ tailWord_3069323).sum := by decide
  have hdescent : baseEnd_3069323 < baseStart_3069323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069338 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_3069338 : Nat := 118140960795 + 3069338 * 2 ^ 59
def prefixEnd_3069338 : Nat := 4983230072969 + 3 ^ 40 * 3069338 * 2
def baseEnd_3069338 : Nat := 350232374468848318813195

theorem tailTrace_3069338 : CollatzResearch.WordTrace tailWord_3069338 prefixEnd_3069338 350232374468848318813195 := by
  unfold tailWord_3069338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986988438580025510430167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74631969169546734694480445 27986988438580025510430167)
  ·
    refine ⟨41980482657870038265645251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986988438580025510430167 41980482657870038265645251)
    ·
      refine ⟨62970723986805057398467877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41980482657870038265645251 62970723986805057398467877)
      ·
        refine ⟨11807010747525948262212727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62970723986805057398467877 11807010747525948262212727)
        ·
          refine ⟨17710516121288922393319091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807010747525948262212727 17710516121288922393319091)
          ·
            refine ⟨26565774181933383589978637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17710516121288922393319091 26565774181933383589978637)
            ·
              refine ⟨9962165318225018846241989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26565774181933383589978637 9962165318225018846241989)
              ·
                refine ⟨1867905997167191033670373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9962165318225018846241989 1867905997167191033670373)
                ·
                  refine ⟨350232374468848318813195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867905997167191033670373 350232374468848318813195)
                  ·
                    rfl

theorem cell22_3069338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_3069338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069338 prefixEnd_3069338 := by exact prefixLift 3069338
  have htrace : WordTrace (prefixWord ++ tailWord_3069338) baseStart_3069338 baseEnd_3069338 := by
    simpa [prefixWord, tailWord_3069338, baseEnd_3069338] using wordTrace_append hprefix tailTrace_3069338
  have hstable : (prefixWord ++ tailWord_3069338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069338).length < 2 ^ (prefixWord ++ tailWord_3069338).sum := by decide
  have hdescent : baseEnd_3069338 < baseStart_3069338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069349 : List Nat := [1, 3, 1, 2, 1, 1, 2, 11]
def baseStart_3069349 : Nat := 118140960795 + 3069349 * 2 ^ 59
def prefixEnd_3069349 : Nat := 4983230072969 + 3 ^ 40 * 3069349 * 2
def baseEnd_3069349 : Nat := 116744543214593843823839

theorem tailTrace_3069349 : CollatzResearch.WordTrace tailWord_3069349 prefixEnd_3069349 116744543214593843823839 := by
  unfold tailWord_3069349
  simp only [CollatzResearch.WordTrace]
  refine ⟨111948354957280250920371101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74632236638186833946914067 111948354957280250920371101)
  ·
    refine ⟨41980633108980094095139163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111948354957280250920371101 41980633108980094095139163)
    ·
      refine ⟨62970949663470141142708745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41980633108980094095139163 62970949663470141142708745)
      ·
        refine ⟨47228212247602605857031559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62970949663470141142708745 47228212247602605857031559)
        ·
          refine ⟨70842318371403908785547339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47228212247602605857031559 70842318371403908785547339)
          ·
            refine ⟨106263477557105863178321009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70842318371403908785547339 106263477557105863178321009)
            ·
              refine ⟨79697608167829397383740757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106263477557105863178321009 79697608167829397383740757)
              ·
                refine ⟨116744543214593843823839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79697608167829397383740757 116744543214593843823839)
                ·
                  rfl

theorem cell22_3069349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 11].length) (baseStart_3069349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069349 prefixEnd_3069349 := by exact prefixLift 3069349
  have htrace : WordTrace (prefixWord ++ tailWord_3069349) baseStart_3069349 baseEnd_3069349 := by
    simpa [prefixWord, tailWord_3069349, baseEnd_3069349] using wordTrace_append hprefix tailTrace_3069349
  have hstable : (prefixWord ++ tailWord_3069349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069349).length < 2 ^ (prefixWord ++ tailWord_3069349).sum := by decide
  have hdescent : baseEnd_3069349 < baseStart_3069349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069351 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3069351 : Nat := 118140960795 + 3069351 * 2 ^ 59
def prefixEnd_3069351 : Nat := 4983230072969 + 3 ^ 40 * 3069351 * 2
def baseEnd_3069351 : Nat := 1050701573572217255864545

theorem tailTrace_3069351 : CollatzResearch.WordTrace tailWord_3069351 prefixEnd_3069351 1050701573572217255864545 := by
  unfold tailWord_3069351
  simp only [CollatzResearch.WordTrace]
  refine ⟨111948427903273005261943907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74632285268848670174629271 111948427903273005261943907)
  ·
    refine ⟨167922641854909507892915861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111948427903273005261943907 167922641854909507892915861)
    ·
      refine ⟨7871373836948883182480431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167922641854909507892915861 7871373836948883182480431)
      ·
        refine ⟨11807060755423324773720647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7871373836948883182480431 11807060755423324773720647)
        ·
          refine ⟨17710591133134987160580971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807060755423324773720647 17710591133134987160580971)
          ·
            refine ⟨26565886699702480740871457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17710591133134987160580971 26565886699702480740871457)
            ·
              refine ⟨19924415024776860555653593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26565886699702480740871457 19924415024776860555653593)
              ·
                refine ⟨14943311268582645416740195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19924415024776860555653593 14943311268582645416740195)
                ·
                  refine ⟨22414966902873968125110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14943311268582645416740195 22414966902873968125110293)
                  ·
                    refine ⟨1050701573572217255864545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22414966902873968125110293 1050701573572217255864545)
                    ·
                      rfl

theorem cell22_3069351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3069351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069351 prefixEnd_3069351 := by exact prefixLift 3069351
  have htrace : WordTrace (prefixWord ++ tailWord_3069351) baseStart_3069351 baseEnd_3069351 := by
    simpa [prefixWord, tailWord_3069351, baseEnd_3069351] using wordTrace_append hprefix tailTrace_3069351
  have hstable : (prefixWord ++ tailWord_3069351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069351).length < 2 ^ (prefixWord ++ tailWord_3069351).sum := by decide
  have hdescent : baseEnd_3069351 < baseStart_3069351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069432 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 1, 3]
def baseStart_3069432 : Nat := 118140960795 + 3069432 * 2 ^ 59
def prefixEnd_3069432 : Nat := 4983230072969 + 3 ^ 40 * 3069432 * 2
def baseEnd_3069432 : Nat := 1050729301527560044589297

theorem tailTrace_3069432 : CollatzResearch.WordTrace tailWord_3069432 prefixEnd_3069432 1050729301527560044589297 := by
  unfold tailWord_3069432
  simp only [CollatzResearch.WordTrace]
  refine ⟨55975691107989778047821275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74634254810653037397095033 55975691107989778047821275)
  ·
    refine ⟨83963536661984667071731913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55975691107989778047821275 83963536661984667071731913)
    ·
      refine ⟨62972652496488500303798935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83963536661984667071731913 62972652496488500303798935)
      ·
        refine ⟨94458978744732750455698403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62972652496488500303798935 94458978744732750455698403)
        ·
          refine ⟨141688468117099125683547605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94458978744732750455698403 141688468117099125683547605)
          ·
            refine ⟨3320823471494510758208147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 141688468117099125683547605 3320823471494510758208147)
            ·
              refine ⟨4981235207241766137312221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320823471494510758208147 4981235207241766137312221)
              ·
                refine ⟨1867963202715662301492083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4981235207241766137312221 1867963202715662301492083)
                ·
                  refine ⟨2801944804073493452238125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867963202715662301492083 2801944804073493452238125)
                  ·
                    refine ⟨1050729301527560044589297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801944804073493452238125 1050729301527560044589297)
                    ·
                      rfl

theorem cell22_3069432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_3069432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069432 prefixEnd_3069432 := by exact prefixLift 3069432
  have htrace : WordTrace (prefixWord ++ tailWord_3069432) baseStart_3069432 baseEnd_3069432 := by
    simpa [prefixWord, tailWord_3069432, baseEnd_3069432] using wordTrace_append hprefix tailTrace_3069432
  have hstable : (prefixWord ++ tailWord_3069432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069432).length < 2 ^ (prefixWord ++ tailWord_3069432).sum := by decide
  have hdescent : baseEnd_3069432 < baseStart_3069432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069501 : List Nat := [1, 4, 1, 3, 13]
def baseStart_3069501 : Nat := 118140960795 + 3069501 * 2 ^ 59
def prefixEnd_3069501 : Nat := 4983230072969 + 3 ^ 40 * 3069501 * 2
def baseEnd_3069501 : Nat := 4324086097274349237095

theorem tailTrace_3069501 : CollatzResearch.WordTrace tailWord_3069501 prefixEnd_3069501 4324086097274349237095 := by
  unfold tailWord_3069501
  simp only [CollatzResearch.WordTrace]
  refine ⟨111953898852729580879904357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74635932568486387253269571 111953898852729580879904357)
  ·
    refine ⟨20991356034886796414982067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111953898852729580879904357 20991356034886796414982067)
    ·
      refine ⟨31487034052330194622473101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20991356034886796414982067 31487034052330194622473101)
      ·
        refine ⟨11807637769623822983427413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31487034052330194622473101 11807637769623822983427413)
        ·
          refine ⟨4324086097274349237095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11807637769623822983427413 4324086097274349237095)
          ·
            rfl

theorem cell22_3069501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 13].length) (baseStart_3069501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069501 prefixEnd_3069501 := by exact prefixLift 3069501
  have htrace : WordTrace (prefixWord ++ tailWord_3069501) baseStart_3069501 baseEnd_3069501 := by
    simpa [prefixWord, tailWord_3069501, baseEnd_3069501] using wordTrace_append hprefix tailTrace_3069501
  have hstable : (prefixWord ++ tailWord_3069501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069501).length < 2 ^ (prefixWord ++ tailWord_3069501).sum := by decide
  have hdescent : baseEnd_3069501 < baseStart_3069501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069503 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_3069503 : Nat := 118140960795 + 3069503 * 2 ^ 59
def prefixEnd_3069503 : Nat := 4983230072969 + 3 ^ 40 * 3069503 * 2
def baseEnd_3069503 : Nat := 1050753606278539526064079

theorem tailTrace_3069503 : CollatzResearch.WordTrace tailWord_3069503 prefixEnd_3069503 1050753606278539526064079 := by
  unfold tailWord_3069503
  simp only [CollatzResearch.WordTrace]
  refine ⟨111953971798722335221477163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74635981199148223480984775 111953971798722335221477163)
  ·
    refine ⟨167930957698083502832215745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111953971798722335221477163 167930957698083502832215745)
    ·
      refine ⟨125948218273562627124161809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167930957698083502832215745 125948218273562627124161809)
      ·
        refine ⟨94461163705171970343121357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125948218273562627124161809 94461163705171970343121357)
        ·
          refine ⟨35422936389439488878670509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94461163705171970343121357 35422936389439488878670509)
          ·
            refine ⟨13283601146039808329501441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35422936389439488878670509 13283601146039808329501441)
            ·
              refine ⟨9962700859529856247126081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13283601146039808329501441 9962700859529856247126081)
              ·
                refine ⟨7472025644647392185344561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9962700859529856247126081 7472025644647392185344561)
                ·
                  refine ⟨5604019233485544139008421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472025644647392185344561 5604019233485544139008421)
                  ·
                    refine ⟨1050753606278539526064079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604019233485544139008421 1050753606278539526064079)
                    ·
                      rfl

theorem cell22_3069503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_3069503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069503 prefixEnd_3069503 := by exact prefixLift 3069503
  have htrace : WordTrace (prefixWord ++ tailWord_3069503) baseStart_3069503 baseEnd_3069503 := by
    simpa [prefixWord, tailWord_3069503, baseEnd_3069503] using wordTrace_append hprefix tailTrace_3069503
  have hstable : (prefixWord ++ tailWord_3069503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069503).length < 2 ^ (prefixWord ++ tailWord_3069503).sum := by decide
  have hdescent : baseEnd_3069503 < baseStart_3069503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069580 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_3069580 : Nat := 118140960795 + 3069580 * 2 ^ 59
def prefixEnd_3069580 : Nat := 4983230072969 + 3 ^ 40 * 3069580 * 2
def baseEnd_3069580 : Nat := 350259988317378997296281

theorem tailTrace_3069580 : CollatzResearch.WordTrace tailWord_3069580 prefixEnd_3069580 350259988317378997296281 := by
  unfold tailWord_3069580
  simp only [CollatzResearch.WordTrace]
  refine ⟨55978390109721688686015097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74637853479628918248020129 55978390109721688686015097)
  ·
    refine ⟨41983792582291266514511323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55978390109721688686015097 41983792582291266514511323)
    ·
      refine ⟨62975688873436899771766985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41983792582291266514511323 62975688873436899771766985)
      ·
        refine ⟨47231766655077674828825239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62975688873436899771766985 47231766655077674828825239)
        ·
          refine ⟨70847649982616512243237859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47231766655077674828825239 70847649982616512243237859)
          ·
            refine ⟨106271474973924768364856789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70847649982616512243237859 106271474973924768364856789)
            ·
              refine ⟨2490737694701361758551331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 106271474973924768364856789 2490737694701361758551331)
              ·
                refine ⟨3736106542052042637826997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490737694701361758551331 3736106542052042637826997)
                ·
                  refine ⟨350259988317378997296281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736106542052042637826997 350259988317378997296281)
                  ·
                    rfl

theorem cell22_3069580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_3069580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069580 prefixEnd_3069580 := by exact prefixLift 3069580
  have htrace : WordTrace (prefixWord ++ tailWord_3069580) baseStart_3069580 baseEnd_3069580 := by
    simpa [prefixWord, tailWord_3069580, baseEnd_3069580] using wordTrace_append hprefix tailTrace_3069580
  have hstable : (prefixWord ++ tailWord_3069580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069580).length < 2 ^ (prefixWord ++ tailWord_3069580).sum := by decide
  have hdescent : baseEnd_3069580 < baseStart_3069580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069625 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 4]
def baseStart_3069625 : Nat := 118140960795 + 3069625 * 2 ^ 59
def prefixEnd_3069625 : Nat := 4983230072969 + 3 ^ 40 * 3069625 * 2
def baseEnd_3069625 : Nat := 350265123123923958171235

theorem tailTrace_3069625 : CollatzResearch.WordTrace tailWord_3069625 prefixEnd_3069625 350265123123923958171235 := by
  unfold tailWord_3069625
  simp only [CollatzResearch.WordTrace]
  refine ⟨111958421504280350057418329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74638947669520233371612219 111958421504280350057418329)
  ·
    refine ⟨83968816128210262543063747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111958421504280350057418329 83968816128210262543063747)
    ·
      refine ⟨125953224192315393814595621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83968816128210262543063747 125953224192315393814595621)
      ·
        refine ⟨23616229536059136340236679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125953224192315393814595621 23616229536059136340236679)
        ·
          refine ⟨35424344304088704510355019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23616229536059136340236679 35424344304088704510355019)
          ·
            refine ⟨53136516456133056765532529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35424344304088704510355019 53136516456133056765532529)
            ·
              refine ⟨39852387342099792574149397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53136516456133056765532529 39852387342099792574149397)
              ·
                refine ⟨1868080656660927776913253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39852387342099792574149397 1868080656660927776913253)
                ·
                  refine ⟨350265123123923958171235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868080656660927776913253 350265123123923958171235)
                  ·
                    rfl

theorem cell22_3069625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_3069625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069625 prefixEnd_3069625 := by exact prefixLift 3069625
  have htrace : WordTrace (prefixWord ++ tailWord_3069625) baseStart_3069625 baseEnd_3069625 := by
    simpa [prefixWord, tailWord_3069625, baseEnd_3069625] using wordTrace_append hprefix tailTrace_3069625
  have hstable : (prefixWord ++ tailWord_3069625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069625).length < 2 ^ (prefixWord ++ tailWord_3069625).sum := by decide
  have hdescent : baseEnd_3069625 < baseStart_3069625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069644 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_3069644 : Nat := 118140960795 + 3069644 * 2 ^ 59
def prefixEnd_3069644 : Nat := 4983230072969 + 3 ^ 40 * 3069644 * 2
def baseEnd_3069644 : Nat := 1050801873460062158288647

theorem tailTrace_3069644 : CollatzResearch.WordTrace tailWord_3069644 prefixEnd_3069644 1050801873460062158288647 := by
  unfold tailWord_3069644
  simp only [CollatzResearch.WordTrace]
  refine ⟨55979557245605758151179993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74639409660807677534906657 55979557245605758151179993)
  ·
    refine ⟨41984667934204318613384995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55979557245605758151179993 41984667934204318613384995)
    ·
      refine ⟨62977001901306477920077493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41984667934204318613384995 62977001901306477920077493)
      ·
        refine ⟨5904093928247482305007265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62977001901306477920077493 5904093928247482305007265)
        ·
          refine ⟨4428070446185611728755449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904093928247482305007265 4428070446185611728755449)
          ·
            refine ⟨3321052834639208796566587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428070446185611728755449 3321052834639208796566587)
            ·
              refine ⟨4981579251958813194849881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321052834639208796566587 4981579251958813194849881)
              ·
                refine ⟨3736184438969109896137411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981579251958813194849881 3736184438969109896137411)
                ·
                  refine ⟨5604276658453664844206117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736184438969109896137411 5604276658453664844206117)
                  ·
                    refine ⟨1050801873460062158288647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604276658453664844206117 1050801873460062158288647)
                    ·
                      rfl

theorem cell22_3069644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_3069644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069644 prefixEnd_3069644 := by exact prefixLift 3069644
  have htrace : WordTrace (prefixWord ++ tailWord_3069644) baseStart_3069644 baseEnd_3069644 := by
    simpa [prefixWord, tailWord_3069644, baseEnd_3069644] using wordTrace_append hprefix tailTrace_3069644
  have hstable : (prefixWord ++ tailWord_3069644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069644).length < 2 ^ (prefixWord ++ tailWord_3069644).sum := by decide
  have hdescent : baseEnd_3069644 < baseStart_3069644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069655 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3069655 : Nat := 118140960795 + 3069655 * 2 ^ 59
def prefixEnd_3069655 : Nat := 4983230072969 + 3 ^ 40 * 3069655 * 2
def baseEnd_3069655 : Nat := 1050805638984861796263613

theorem tailTrace_3069655 : CollatzResearch.WordTrace tailWord_3069655 prefixEnd_3069655 1050805638984861796263613 := by
  unfold tailWord_3069655
  simp only [CollatzResearch.WordTrace]
  refine ⟨111959515694171665181010419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74639677129447776787340279 111959515694171665181010419)
  ·
    refine ⟨167939273541257497771515629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111959515694171665181010419 167939273541257497771515629)
    ·
      refine ⟨62977227577971561664318361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167939273541257497771515629 62977227577971561664318361)
      ·
        refine ⟨47232920683478671248238771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62977227577971561664318361 47232920683478671248238771)
        ·
          refine ⟨70849381025218006872358157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47232920683478671248238771 70849381025218006872358157)
          ·
            refine ⟨26568517884456752577134309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70849381025218006872358157 26568517884456752577134309)
            ·
              refine ⟨4981597103335641108212683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26568517884456752577134309 4981597103335641108212683)
              ·
                refine ⟨7472395655003461662319025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981597103335641108212683 7472395655003461662319025)
                ·
                  refine ⟨5604296741252596246739269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472395655003461662319025 5604296741252596246739269)
                  ·
                    refine ⟨1050805638984861796263613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604296741252596246739269 1050805638984861796263613)
                    ·
                      rfl

theorem cell22_3069655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3069655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069655 prefixEnd_3069655 := by exact prefixLift 3069655
  have htrace : WordTrace (prefixWord ++ tailWord_3069655) baseStart_3069655 baseEnd_3069655 := by
    simpa [prefixWord, tailWord_3069655, baseEnd_3069655] using wordTrace_append hprefix tailTrace_3069655
  have hstable : (prefixWord ++ tailWord_3069655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069655).length < 2 ^ (prefixWord ++ tailWord_3069655).sum := by decide
  have hdescent : baseEnd_3069655 < baseStart_3069655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069661 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3069661 : Nat := 118140960795 + 3069661 * 2 ^ 59
def prefixEnd_3069661 : Nat := 4983230072969 + 3 ^ 40 * 3069661 * 2
def baseEnd_3069661 : Nat := 1050807692907479780613595

theorem tailTrace_3069661 : CollatzResearch.WordTrace tailWord_3069661 prefixEnd_3069661 1050807692907479780613595 := by
  unfold tailWord_3069661
  simp only [CollatzResearch.WordTrace]
  refine ⟨111959734532149928205728837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74639823021433285470485891 111959734532149928205728837)
  ·
    refine ⟨20992450224778111538574157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111959734532149928205728837 20992450224778111538574157)
    ·
      refine ⟨7872168834291791826965309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20992450224778111538574157 7872168834291791826965309)
      ·
        refine ⟨2952063312859421935111991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7872168834291791826965309 2952063312859421935111991)
        ·
          refine ⟨4428094969289132902667987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952063312859421935111991 4428094969289132902667987)
          ·
            refine ⟨6642142453933699354001981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428094969289132902667987 6642142453933699354001981)
            ·
              refine ⟨2490803420225137257750743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6642142453933699354001981 2490803420225137257750743)
              ·
                refine ⟨3736205130337705886626115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490803420225137257750743 3736205130337705886626115)
                ·
                  refine ⟨5604307695506558829939173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736205130337705886626115 5604307695506558829939173)
                  ·
                    refine ⟨1050807692907479780613595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604307695506558829939173 1050807692907479780613595)
                    ·
                      rfl

theorem cell22_3069661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3069661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069661 prefixEnd_3069661 := by exact prefixLift 3069661
  have htrace : WordTrace (prefixWord ++ tailWord_3069661) baseStart_3069661 baseEnd_3069661 := by
    simpa [prefixWord, tailWord_3069661, baseEnd_3069661] using wordTrace_append hprefix tailTrace_3069661
  have hstable : (prefixWord ++ tailWord_3069661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069661).length < 2 ^ (prefixWord ++ tailWord_3069661).sum := by decide
  have hdescent : baseEnd_3069661 < baseStart_3069661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069683 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_3069683 : Nat := 118140960795 + 3069683 * 2 ^ 59
def prefixEnd_3069683 : Nat := 4983230072969 + 3 ^ 40 * 3069683 * 2
def baseEnd_3069683 : Nat := 1050815223957079056563527

theorem tailTrace_3069683 : CollatzResearch.WordTrace tailWord_3069683 prefixEnd_3069683 1050815223957079056563527 := by
  unfold tailWord_3069683
  simp only [CollatzResearch.WordTrace]
  refine ⟨111960536938070225963029703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74640357958713483975353135 111960536938070225963029703)
  ·
    refine ⟨167940805407105338944544555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111960536938070225963029703 167940805407105338944544555)
    ·
      refine ⟨251911208110658008416816833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167940805407105338944544555 251911208110658008416816833)
      ·
        refine ⟨188933406082993506312612625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251911208110658008416816833 188933406082993506312612625)
        ·
          refine ⟨141700054562245129734459469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188933406082993506312612625 141700054562245129734459469)
          ·
            refine ⟨53137520460841923650422301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141700054562245129734459469 53137520460841923650422301)
            ·
              refine ⟨19926570172815721368908363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53137520460841923650422301 19926570172815721368908363)
              ·
                refine ⟨29889855259223582053362545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19926570172815721368908363 29889855259223582053362545)
                ·
                  refine ⟨22417391444417686540021909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29889855259223582053362545 22417391444417686540021909)
                  ·
                    refine ⟨1050815223957079056563527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22417391444417686540021909 1050815223957079056563527)
                    ·
                      rfl

theorem cell22_3069683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_3069683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069683 prefixEnd_3069683 := by exact prefixLift 3069683
  have htrace : WordTrace (prefixWord ++ tailWord_3069683) baseStart_3069683 baseEnd_3069683 := by
    simpa [prefixWord, tailWord_3069683, baseEnd_3069683] using wordTrace_append hprefix tailTrace_3069683
  have hstable : (prefixWord ++ tailWord_3069683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069683).length < 2 ^ (prefixWord ++ tailWord_3069683).sum := by decide
  have hdescent : baseEnd_3069683 < baseStart_3069683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069713 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3069713 : Nat := 118140960795 + 3069713 * 2 ^ 59
def prefixEnd_3069713 : Nat := 4983230072969 + 3 ^ 40 * 3069713 * 2
def baseEnd_3069713 : Nat := 1050825493570168978313435

theorem tailTrace_3069713 : CollatzResearch.WordTrace tailWord_3069713 prefixEnd_3069713 1050825493570168978313435 := by
  unfold tailWord_3069713
  simp only [CollatzResearch.WordTrace]
  refine ⟨111961631127961541086621793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74641087418641027391081195 111961631127961541086621793)
  ·
    refine ⟨83971223345971155814966345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111961631127961541086621793 83971223345971155814966345)
    ·
      refine ⟨62978417509478366861224759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83971223345971155814966345 62978417509478366861224759)
      ·
        refine ⟨94467626264217550291837139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62978417509478366861224759 94467626264217550291837139)
        ·
          refine ⟨141701439396326325437755709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94467626264217550291837139 141701439396326325437755709)
          ·
            refine ⟨53138039773622372039158391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141701439396326325437755709 53138039773622372039158391)
            ·
              refine ⟨79707059660433558058737587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53138039773622372039158391 79707059660433558058737587)
              ·
                refine ⟨119560589490650337088106381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79707059660433558058737587 119560589490650337088106381)
                ·
                  refine ⟨44835221058993876408039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119560589490650337088106381 44835221058993876408039893)
                  ·
                    refine ⟨1050825493570168978313435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44835221058993876408039893 1050825493570168978313435)
                    ·
                      rfl

theorem cell22_3069713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3069713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069713 prefixEnd_3069713 := by exact prefixLift 3069713
  have htrace : WordTrace (prefixWord ++ tailWord_3069713) baseStart_3069713 baseEnd_3069713 := by
    simpa [prefixWord, tailWord_3069713, baseEnd_3069713] using wordTrace_append hprefix tailTrace_3069713
  have hstable : (prefixWord ++ tailWord_3069713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069713).length < 2 ^ (prefixWord ++ tailWord_3069713).sum := by decide
  have hdescent : baseEnd_3069713 < baseStart_3069713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069719 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 1, 3]
def baseStart_3069719 : Nat := 118140960795 + 3069719 * 2 ^ 59
def prefixEnd_3069719 : Nat := 4983230072969 + 3 ^ 40 * 3069719 * 2
def baseEnd_3069719 : Nat := 1050827547492786962663417

theorem tailTrace_3069719 : CollatzResearch.WordTrace tailWord_3069719 prefixEnd_3069719 1050827547492786962663417 := by
  unfold tailWord_3069719
  simp only [CollatzResearch.WordTrace]
  refine ⟨111961849965939804111340211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74641233310626536074226807 111961849965939804111340211)
  ·
    refine ⟨167942774948909706167010317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111961849965939804111340211 167942774948909706167010317)
    ·
      refine ⟨62978540605841139812628869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167942774948909706167010317 62978540605841139812628869)
      ·
        refine ⟨11808476363595213714867913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62978540605841139812628869 11808476363595213714867913)
        ·
          refine ⟨8856357272696410286150935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11808476363595213714867913 8856357272696410286150935)
          ·
            refine ⟨13284535909044615429226403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856357272696410286150935 13284535909044615429226403)
            ·
              refine ⟨19926803863566923143839605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284535909044615429226403 19926803863566923143839605)
              ·
                refine ⟨1868137862209399044734963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19926803863566923143839605 1868137862209399044734963)
                ·
                  refine ⟨2802206793314098567102445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868137862209399044734963 2802206793314098567102445)
                  ·
                    refine ⟨1050827547492786962663417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2802206793314098567102445 1050827547492786962663417)
                    ·
                      rfl

theorem cell22_3069719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_3069719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069719 prefixEnd_3069719 := by exact prefixLift 3069719
  have htrace : WordTrace (prefixWord ++ tailWord_3069719) baseStart_3069719 baseEnd_3069719 := by
    simpa [prefixWord, tailWord_3069719, baseEnd_3069719] using wordTrace_append hprefix tailTrace_3069719
  have hstable : (prefixWord ++ tailWord_3069719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069719).length < 2 ^ (prefixWord ++ tailWord_3069719).sum := by decide
  have hdescent : baseEnd_3069719 < baseStart_3069719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069730 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3069730 : Nat := 118140960795 + 3069730 * 2 ^ 59
def prefixEnd_3069730 : Nat := 4983230072969 + 3 ^ 40 * 3069730 * 2
def baseEnd_3069730 : Nat := 1050831313017586600638383

theorem tailTrace_3069730 : CollatzResearch.WordTrace tailWord_3069730 prefixEnd_3069730 1050831313017586600638383 := by
  unfold tailWord_3069730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27990562792224988247497661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74641500779266635326660429 27990562792224988247497661)
  ·
    refine ⟨10496461047084370592811623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27990562792224988247497661 10496461047084370592811623)
    ·
      refine ⟨15744691570626555889217435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496461047084370592811623 15744691570626555889217435)
      ·
        refine ⟨23617037355939833833826153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15744691570626555889217435 23617037355939833833826153)
        ·
          refine ⟨17712778016954875375369615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23617037355939833833826153 17712778016954875375369615)
          ·
            refine ⟨26569167025432313063054423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17712778016954875375369615 26569167025432313063054423)
            ·
              refine ⟨39853750538148469594581635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26569167025432313063054423 39853750538148469594581635)
              ·
                refine ⟨59780625807222704391872453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39853750538148469594581635 59780625807222704391872453)
                ·
                  refine ⟨11208867338854257073476085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59780625807222704391872453 11208867338854257073476085)
                  ·
                    refine ⟨1050831313017586600638383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11208867338854257073476085 1050831313017586600638383)
                    ·
                      rfl

theorem cell22_3069730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3069730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069730 prefixEnd_3069730 := by exact prefixLift 3069730
  have htrace : WordTrace (prefixWord ++ tailWord_3069730) baseStart_3069730 baseEnd_3069730 := by
    simpa [prefixWord, tailWord_3069730, baseEnd_3069730] using wordTrace_append hprefix tailTrace_3069730
  have hstable : (prefixWord ++ tailWord_3069730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069730).length < 2 ^ (prefixWord ++ tailWord_3069730).sum := by decide
  have hdescent : baseEnd_3069730 < baseStart_3069730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069732 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_3069732 : Nat := 118140960795 + 3069732 * 2 ^ 59
def prefixEnd_3069732 : Nat := 4983230072969 + 3 ^ 40 * 3069732 * 2
def baseEnd_3069732 : Nat := 350277332552819754029459

theorem tailTrace_3069732 : CollatzResearch.WordTrace tailWord_3069732 prefixEnd_3069732 350277332552819754029459 := by
  unfold tailWord_3069732
  simp only [CollatzResearch.WordTrace]
  refine ⟨55981162057446353665781725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74641549409928471554375633 55981162057446353665781725)
  ·
    refine ⟨20992935771542382624668147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55981162057446353665781725 20992935771542382624668147)
    ·
      refine ⟨31489403657313573937002221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20992935771542382624668147 31489403657313573937002221)
      ·
        refine ⟨11808526371492590226375833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31489403657313573937002221 11808526371492590226375833)
        ·
          refine ⟨8856394778619442669781875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11808526371492590226375833 8856394778619442669781875)
          ·
            refine ⟨13284592167929164004672813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856394778619442669781875 13284592167929164004672813)
            ·
              refine ⟨4981722062973436501752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13284592167929164004672813 4981722062973436501752305)
              ·
                refine ⟨3736291547230077376314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981722062973436501752305 3736291547230077376314229)
                ·
                  refine ⟨350277332552819754029459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736291547230077376314229 350277332552819754029459)
                  ·
                    rfl

theorem cell22_3069732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_3069732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069732 prefixEnd_3069732 := by exact prefixLift 3069732
  have htrace : WordTrace (prefixWord ++ tailWord_3069732) baseStart_3069732 baseEnd_3069732 := by
    simpa [prefixWord, tailWord_3069732, baseEnd_3069732] using wordTrace_append hprefix tailTrace_3069732
  have hstable : (prefixWord ++ tailWord_3069732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069732).length < 2 ^ (prefixWord ++ tailWord_3069732).sum := by decide
  have hdescent : baseEnd_3069732 < baseStart_3069732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069743 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 10]
def baseStart_3069743 : Nat := 118140960795 + 3069743 * 2 ^ 59
def prefixEnd_3069743 : Nat := 4983230072969 + 3 ^ 40 * 3069743 * 2
def baseEnd_3069743 : Nat := 350278587727752966687781

theorem tailTrace_3069743 : CollatzResearch.WordTrace tailWord_3069743 prefixEnd_3069743 350278587727752966687781 := by
  unfold tailWord_3069743
  simp only [CollatzResearch.WordTrace]
  refine ⟨111962725317852856210213883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74641816878568570806809255 111962725317852856210213883)
  ·
    refine ⟨167944087976779284315320825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111962725317852856210213883 167944087976779284315320825)
    ·
      refine ⟨125958065982584463236490619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167944087976779284315320825 125958065982584463236490619)
      ·
        refine ⟨188937098973876694854735929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125958065982584463236490619 188937098973876694854735929)
        ·
          refine ⟨141702824230407521141051947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188937098973876694854735929 141702824230407521141051947)
          ·
            refine ⟨212554236345611281711577921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141702824230407521141051947 212554236345611281711577921)
            ·
              refine ⟨159415677259208461283683441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212554236345611281711577921 159415677259208461283683441)
              ·
                refine ⟨119561757944406345962762581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159415677259208461283683441 119561757944406345962762581)
                ·
                  refine ⟨350278587727752966687781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119561757944406345962762581 350278587727752966687781)
                  ·
                    rfl

theorem cell22_3069743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_3069743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069743 prefixEnd_3069743 := by exact prefixLift 3069743
  have htrace : WordTrace (prefixWord ++ tailWord_3069743) baseStart_3069743 baseEnd_3069743 := by
    simpa [prefixWord, tailWord_3069743, baseEnd_3069743] using wordTrace_append hprefix tailTrace_3069743
  have hstable : (prefixWord ++ tailWord_3069743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069743).length < 2 ^ (prefixWord ++ tailWord_3069743).sum := by decide
  have hdescent : baseEnd_3069743 < baseStart_3069743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069749 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 5]
def baseStart_3069749 : Nat := 118140960795 + 3069749 * 2 ^ 59
def prefixEnd_3069749 : Nat := 4983230072969 + 3 ^ 40 * 3069749 * 2
def baseEnd_3069749 : Nat := 350279272368625628137775

theorem tailTrace_3069749 : CollatzResearch.WordTrace tailWord_3069749 prefixEnd_3069749 350279272368625628137775 := by
  unfold tailWord_3069749
  simp only [CollatzResearch.WordTrace]
  refine ⟨111962944155831119234932301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74641962770554079489954867 111962944155831119234932301)
  ·
    refine ⟨41986104058436669713099613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111962944155831119234932301 41986104058436669713099613)
    ·
      refine ⟨15744789021913751142412355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41986104058436669713099613 15744789021913751142412355)
      ·
        refine ⟨23617183532870626713618533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15744789021913751142412355 23617183532870626713618533)
        ·
          refine ⟨4428221912413242508803475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23617183532870626713618533 4428221912413242508803475)
          ·
            refine ⟨6642332868619863763205213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428221912413242508803475 6642332868619863763205213)
            ·
              refine ⟨2490874825732448911201955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6642332868619863763205213 2490874825732448911201955)
              ·
                refine ⟨3736312238598673366802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490874825732448911201955 3736312238598673366802933)
                ·
                  refine ⟨350279272368625628137775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736312238598673366802933 350279272368625628137775)
                  ·
                    rfl

theorem cell22_3069749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_3069749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069749 prefixEnd_3069749 := by exact prefixLift 3069749
  have htrace : WordTrace (prefixWord ++ tailWord_3069749) baseStart_3069749 baseEnd_3069749 := by
    simpa [prefixWord, tailWord_3069749, baseEnd_3069749] using wordTrace_append hprefix tailTrace_3069749
  have hstable : (prefixWord ++ tailWord_3069749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069749).length < 2 ^ (prefixWord ++ tailWord_3069749).sum := by decide
  have hdescent : baseEnd_3069749 < baseStart_3069749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
