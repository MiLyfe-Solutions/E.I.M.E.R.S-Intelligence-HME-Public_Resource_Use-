import V185TrunkScan23Chunk0723

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4281989 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_4281989 : Nat := 118140960795 + 4281989 * 2 ^ 59
def prefixEnd_4281989 : Nat := 4983230072969 + 3 ^ 40 * 4281989 * 2
def baseEnd_4281989 : Nat := 2198718514265152432044997

theorem tailTrace_4281989 : CollatzResearch.WordTrace tailWord_4281989 prefixEnd_4281989 2198718514265152432044997 := by
  unfold tailWord_4281989
  simp only [CollatzResearch.WordTrace]
  refine ⟨156176969284092633344105021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104117979522728422229403347 156176969284092633344105021)
  ·
    refine ⟨58566363481534737504039383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156176969284092633344105021 58566363481534737504039383)
    ·
      refine ⟨87849545222302106256059075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58566363481534737504039383 87849545222302106256059075)
      ·
        refine ⟨131774317833453159384088613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87849545222302106256059075 131774317833453159384088613)
        ·
          refine ⟨24707684593772467384516615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131774317833453159384088613 24707684593772467384516615)
          ·
            refine ⟨37061526890658701076774923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24707684593772467384516615 37061526890658701076774923)
            ·
              refine ⟨55592290335988051615162385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37061526890658701076774923 55592290335988051615162385)
              ·
                refine ⟨41694217751991038711371789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55592290335988051615162385 41694217751991038711371789)
                ·
                  refine ⟨15635331656996639516764421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41694217751991038711371789 15635331656996639516764421)
                  ·
                    refine ⟨2931624685686869909393329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15635331656996639516764421 2931624685686869909393329)
                    ·
                      refine ⟨2198718514265152432044997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931624685686869909393329 2198718514265152432044997)
                      ·
                        rfl

theorem cell23_4281989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_4281989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4281989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4281989 prefixEnd_4281989 := by exact prefixLift 4281989
  have htrace : WordTrace (prefixWord ++ tailWord_4281989) baseStart_4281989 baseEnd_4281989 := by
    simpa [prefixWord, tailWord_4281989, baseEnd_4281989] using wordTrace_append hprefix tailTrace_4281989
  have hstable : (prefixWord ++ tailWord_4281989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4281989).length < 2 ^ (prefixWord ++ tailWord_4281989).sum := by decide
  have hdescent : baseEnd_4281989 < baseStart_4281989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4281989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282039 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_4282039 : Nat := 118140960795 + 4282039 * 2 ^ 59
def prefixEnd_4282039 : Nat := 4983230072969 + 3 ^ 40 * 4282039 * 2
def baseEnd_4282039 : Nat := 2198744188297877236419767

theorem tailTrace_4282039 : CollatzResearch.WordTrace tailWord_4282039 prefixEnd_4282039 2198744188297877236419767 := by
  unfold tailWord_4282039
  simp only [CollatzResearch.WordTrace]
  refine ⟨156178792933911491883425171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104119195289274327922283447 156178792933911491883425171)
  ·
    refine ⟨234268189400867237825137757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156178792933911491883425171 234268189400867237825137757)
    ·
      refine ⟨87850571025325214184426659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234268189400867237825137757 87850571025325214184426659)
      ·
        refine ⟨131775856537987821276639989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87850571025325214184426659 131775856537987821276639989)
        ·
          refine ⟨12353986550436358244684999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131775856537987821276639989 12353986550436358244684999)
          ·
            refine ⟨18530979825654537367027499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12353986550436358244684999 18530979825654537367027499)
            ·
              refine ⟨27796469738481806050541249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18530979825654537367027499 27796469738481806050541249)
              ·
                refine ⟨20847352303861354537905937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27796469738481806050541249 20847352303861354537905937)
                ·
                  refine ⟨15635514227896015903429453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20847352303861354537905937 15635514227896015903429453)
                  ·
                    refine ⟨5863317835461005963786045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15635514227896015903429453 5863317835461005963786045)
                    ·
                      refine ⟨2198744188297877236419767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5863317835461005963786045 2198744188297877236419767)
                      ·
                        rfl

theorem cell23_4282039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_4282039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282039 prefixEnd_4282039 := by exact prefixLift 4282039
  have htrace : WordTrace (prefixWord ++ tailWord_4282039) baseStart_4282039 baseEnd_4282039 := by
    simpa [prefixWord, tailWord_4282039, baseEnd_4282039] using wordTrace_append hprefix tailTrace_4282039
  have hstable : (prefixWord ++ tailWord_4282039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282039).length < 2 ^ (prefixWord ++ tailWord_4282039).sum := by decide
  have hdescent : baseEnd_4282039 < baseStart_4282039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282046 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_4282046 : Nat := 118140960795 + 4282046 * 2 ^ 59
def prefixEnd_4282046 : Nat := 4983230072969 + 3 ^ 40 * 4282046 * 2
def baseEnd_4282046 : Nat := 244305309184717634336915

theorem tailTrace_4282046 : CollatzResearch.WordTrace tailWord_4282046 prefixEnd_4282046 244305309184717634336915 := by
  unfold tailWord_4282046
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522381030610766509866249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104119365496590754719286661 19522381030610766509866249)
  ·
    refine ⟨14641785772958074882399687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19522381030610766509866249 14641785772958074882399687)
    ·
      refine ⟨21962678659437112323599531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14641785772958074882399687 21962678659437112323599531)
      ·
        refine ⟨32944017989155668485399297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21962678659437112323599531 32944017989155668485399297)
        ·
          refine ⟨24708013491866751364049473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32944017989155668485399297 24708013491866751364049473)
          ·
            refine ⟨18531010118900063523037105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24708013491866751364049473 18531010118900063523037105)
            ·
              refine ⟨13898257589175047642277829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18531010118900063523037105 13898257589175047642277829)
              ·
                refine ⟨2605923297970321432927093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13898257589175047642277829 2605923297970321432927093)
                ·
                  refine ⟨244305309184717634336915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2605923297970321432927093 244305309184717634336915)
                  ·
                    rfl

theorem cell23_4282046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_4282046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282046 prefixEnd_4282046 := by exact prefixLift 4282046
  have htrace : WordTrace (prefixWord ++ tailWord_4282046) baseStart_4282046 baseEnd_4282046 := by
    simpa [prefixWord, tailWord_4282046, baseEnd_4282046] using wordTrace_append hprefix tailTrace_4282046
  have hstable : (prefixWord ++ tailWord_4282046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282046).length < 2 ^ (prefixWord ++ tailWord_4282046).sum := by decide
  have hdescent : baseEnd_4282046 < baseStart_4282046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282072 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_4282072 : Nat := 118140960795 + 4282072 * 2 ^ 59
def prefixEnd_4282072 : Nat := 4983230072969 + 3 ^ 40 * 4282072 * 2
def baseEnd_4282072 : Nat := 732920377719825202435705

theorem tailTrace_4282072 : CollatzResearch.WordTrace tailWord_4282072 prefixEnd_4282072 732920377719825202435705 := by
  unfold tailWord_4282072
  simp only [CollatzResearch.WordTrace]
  refine ⟨78089998271395969259688235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104119997695194625679584313 78089998271395969259688235)
  ·
    refine ⟨117134997407093953889532353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78089998271395969259688235 117134997407093953889532353)
    ·
      refine ⟨87851248055320465417149265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117134997407093953889532353 87851248055320465417149265)
      ·
        refine ⟨65888436041490349062861949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87851248055320465417149265 65888436041490349062861949)
        ·
          refine ⟨24708163515558880898573231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65888436041490349062861949 24708163515558880898573231)
          ·
            refine ⟨37062245273338321347859847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24708163515558880898573231 37062245273338321347859847)
            ·
              refine ⟨55593367910007482021789771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37062245273338321347859847 55593367910007482021789771)
              ·
                refine ⟨83390051865011223032684657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55593367910007482021789771 83390051865011223032684657)
                ·
                  refine ⟨62542538898758417274513493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83390051865011223032684657 62542538898758417274513493)
                  ·
                    refine ⟨732920377719825202435705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62542538898758417274513493 732920377719825202435705)
                    ·
                      rfl

theorem cell23_4282072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_4282072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282072 prefixEnd_4282072 := by exact prefixLift 4282072
  have htrace : WordTrace (prefixWord ++ tailWord_4282072) baseStart_4282072 baseEnd_4282072 := by
    simpa [prefixWord, tailWord_4282072, baseEnd_4282072] using wordTrace_append hprefix tailTrace_4282072
  have hstable : (prefixWord ++ tailWord_4282072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282072).length < 2 ^ (prefixWord ++ tailWord_4282072).sum := by decide
  have hdescent : baseEnd_4282072 < baseStart_4282072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282079 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_4282079 : Nat := 118140960795 + 4282079 * 2 ^ 59
def prefixEnd_4282079 : Nat := 4983230072969 + 3 ^ 40 * 4282079 * 2
def baseEnd_4282079 : Nat := 2198764727524057079919583

theorem tailTrace_4282079 : CollatzResearch.WordTrace tailWord_4282079 prefixEnd_4282079 2198764727524057079919583 := by
  unfold tailWord_4282079
  simp only [CollatzResearch.WordTrace]
  refine ⟨156180251853766578714881291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104120167902511052476587527 156180251853766578714881291)
  ·
    refine ⟨234270377780649868072321937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156180251853766578714881291 234270377780649868072321937)
    ·
      refine ⟨175702783335487401054241453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234270377780649868072321937 175702783335487401054241453)
      ·
        refine ⟨65888543750807775395340545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175702783335487401054241453 65888543750807775395340545)
        ·
          refine ⟨49416407813105831546505409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65888543750807775395340545 49416407813105831546505409)
          ·
            refine ⟨37062305859829373659879057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49416407813105831546505409 37062305859829373659879057)
            ·
              refine ⟨27796729394872030244909293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37062305859829373659879057 27796729394872030244909293)
              ·
                refine ⟨10423773523077011341840985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27796729394872030244909293 10423773523077011341840985)
                ·
                  refine ⟨7817830142307758506380739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10423773523077011341840985 7817830142307758506380739)
                  ·
                    refine ⟨11726745213461637759571109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7817830142307758506380739 11726745213461637759571109)
                    ·
                      refine ⟨2198764727524057079919583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11726745213461637759571109 2198764727524057079919583)
                      ·
                        rfl

theorem cell23_4282079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_4282079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282079 prefixEnd_4282079 := by exact prefixLift 4282079
  have htrace : WordTrace (prefixWord ++ tailWord_4282079) baseStart_4282079 baseEnd_4282079 := by
    simpa [prefixWord, tailWord_4282079, baseEnd_4282079] using wordTrace_append hprefix tailTrace_4282079
  have hstable : (prefixWord ++ tailWord_4282079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282079).length < 2 ^ (prefixWord ++ tailWord_4282079).sum := by decide
  have hdescent : baseEnd_4282079 < baseStart_4282079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282092 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_4282092 : Nat := 118140960795 + 4282092 * 2 ^ 59
def prefixEnd_4282092 : Nat := 4983230072969 + 3 ^ 40 * 4282092 * 2
def baseEnd_4282092 : Nat := 2198771402772565529057023

theorem tailTrace_4282092 : CollatzResearch.WordTrace tailWord_4282092 prefixEnd_4282092 2198771402772565529057023 := by
  unfold tailWord_4282092
  simp only [CollatzResearch.WordTrace]
  refine ⟨78090363001359740967552265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104120484001812987956736353 78090363001359740967552265)
  ·
    refine ⟨58567772251019805725664199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78090363001359740967552265 58567772251019805725664199)
    ·
      refine ⟨87851658376529708588496299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58567772251019805725664199 87851658376529708588496299)
      ·
        refine ⟨131777487564794562882744449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87851658376529708588496299 131777487564794562882744449)
        ·
          refine ⟨98833115673595922162058337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131777487564794562882744449 98833115673595922162058337)
          ·
            refine ⟨74124836755196941621543753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98833115673595922162058337 74124836755196941621543753)
            ·
              refine ⟨55593627566397706216157815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74124836755196941621543753 55593627566397706216157815)
              ·
                refine ⟨83390441349596559324236723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55593627566397706216157815 83390441349596559324236723)
                ·
                  refine ⟨125085662024394838986355085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83390441349596559324236723 125085662024394838986355085)
                  ·
                    refine ⟨46907123259148064619883157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125085662024394838986355085 46907123259148064619883157)
                    ·
                      refine ⟨2198771402772565529057023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46907123259148064619883157 2198771402772565529057023)
                      ·
                        rfl

theorem cell23_4282092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_4282092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282092 prefixEnd_4282092 := by exact prefixLift 4282092
  have htrace : WordTrace (prefixWord ++ tailWord_4282092) baseStart_4282092 baseEnd_4282092 := by
    simpa [prefixWord, tailWord_4282092, baseEnd_4282092] using wordTrace_append hprefix tailTrace_4282092
  have hstable : (prefixWord ++ tailWord_4282092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282092).length < 2 ^ (prefixWord ++ tailWord_4282092).sum := by decide
  have hdescent : baseEnd_4282092 < baseStart_4282092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282099 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3]
def baseStart_4282099 : Nat := 118140960795 + 4282099 * 2 ^ 59
def prefixEnd_4282099 : Nat := 4983230072969 + 3 ^ 40 * 4282099 * 2
def baseEnd_4282099 : Nat := 2198774997137147001669491

theorem tailTrace_4282099 : CollatzResearch.WordTrace tailWord_4282099 prefixEnd_4282099 2198774997137147001669491 := by
  unfold tailWord_4282099
  simp only [CollatzResearch.WordTrace]
  refine ⟨156180981313694122130609351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104120654209129414753739567 156180981313694122130609351)
  ·
    refine ⟨234271471970541183195914027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156180981313694122130609351 234271471970541183195914027)
    ·
      refine ⟨351407207955811774793871041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234271471970541183195914027 351407207955811774793871041)
      ·
        refine ⟨263555405966858831095403281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351407207955811774793871041 263555405966858831095403281)
        ·
          refine ⟨197666554475144123321552461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263555405966858831095403281 197666554475144123321552461)
          ·
            refine ⟨74124957928179046245582173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197666554475144123321552461 74124957928179046245582173)
            ·
              refine ⟨27796859223067142342093315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74124957928179046245582173 27796859223067142342093315)
              ·
                refine ⟨41695288834600713513139973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27796859223067142342093315 41695288834600713513139973)
                ·
                  refine ⟨7817866656487633783713745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41695288834600713513139973 7817866656487633783713745)
                  ·
                    refine ⟨5863399992365725337785309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7817866656487633783713745 5863399992365725337785309)
                    ·
                      refine ⟨2198774997137147001669491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5863399992365725337785309 2198774997137147001669491)
                      ·
                        rfl

theorem cell23_4282099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_4282099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282099 prefixEnd_4282099 := by exact prefixLift 4282099
  have htrace : WordTrace (prefixWord ++ tailWord_4282099) baseStart_4282099 baseEnd_4282099 := by
    simpa [prefixWord, tailWord_4282099, baseEnd_4282099] using wordTrace_append hprefix tailTrace_4282099
  have hstable : (prefixWord ++ tailWord_4282099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282099).length < 2 ^ (prefixWord ++ tailWord_4282099).sum := by decide
  have hdescent : baseEnd_4282099 < baseStart_4282099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282179 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 1, 6]
def baseStart_4282179 : Nat := 118140960795 + 4282179 * 2 ^ 59
def prefixEnd_4282179 : Nat := 4983230072969 + 3 ^ 40 * 4282179 * 2
def baseEnd_4282179 : Nat := 732938691863168896223041

theorem tailTrace_4282179 : CollatzResearch.WordTrace tailWord_4282179 prefixEnd_4282179 732938691863168896223041 := by
  unfold tailWord_4282179
  simp only [CollatzResearch.WordTrace]
  refine ⟨156183899153404295793521591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104122599435602863862347727 156183899153404295793521591)
  ·
    refine ⟨234275848730106443690282387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156183899153404295793521591 234275848730106443690282387)
    ·
      refine ⟨351413773095159665535423581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234275848730106443690282387 351413773095159665535423581)
      ·
        refine ⟨131780164910684874575783843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351413773095159665535423581 131780164910684874575783843)
        ·
          refine ⟨197670247366027311863675765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131780164910684874575783843 197670247366027311863675765)
          ·
            refine ⟨18531585690565060487219603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197670247366027311863675765 18531585690565060487219603)
            ·
              refine ⟨27797378535847590730829405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18531585690565060487219603 27797378535847590730829405)
              ·
                refine ⟨10424016950942846524061027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27797378535847590730829405 10424016950942846524061027)
                ·
                  refine ⟨15636025426414269786091541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10424016950942846524061027 15636025426414269786091541)
                  ·
                    refine ⟨732938691863168896223041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15636025426414269786091541 732938691863168896223041)
                    ·
                      rfl

theorem cell23_4282179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 6].length) (baseStart_4282179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282179 prefixEnd_4282179 := by exact prefixLift 4282179
  have htrace : WordTrace (prefixWord ++ tailWord_4282179) baseStart_4282179 baseEnd_4282179 := by
    simpa [prefixWord, tailWord_4282179, baseEnd_4282179] using wordTrace_append hprefix tailTrace_4282179
  have hstable : (prefixWord ++ tailWord_4282179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282179).length < 2 ^ (prefixWord ++ tailWord_4282179).sum := by decide
  have hdescent : baseEnd_4282179 < baseStart_4282179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282186 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_4282186 : Nat := 118140960795 + 4282186 * 2 ^ 59
def prefixEnd_4282186 : Nat := 4983230072969 + 3 ^ 40 * 4282186 * 2
def baseEnd_4282186 : Nat := 2198819669954088161281591

theorem tailTrace_4282186 : CollatzResearch.WordTrace tailWord_4282186 prefixEnd_4282186 2198819669954088161281591 := by
  unfold tailWord_4282186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39046038616094733997256603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104122769642919290659350941 39046038616094733997256603)
  ·
    refine ⟨58569057924142100995884905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39046038616094733997256603 58569057924142100995884905)
    ·
      refine ⟨43926793443106575746913679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58569057924142100995884905 43926793443106575746913679)
      ·
        refine ⟨65890190164659863620370519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43926793443106575746913679 65890190164659863620370519)
        ·
          refine ⟨98835285246989795430555779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65890190164659863620370519 98835285246989795430555779)
          ·
            refine ⟨148252927870484693145833669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98835285246989795430555779 148252927870484693145833669)
            ·
              refine ⟨27797423975715879964843813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148252927870484693145833669 27797423975715879964843813)
              ·
                refine ⟨5212016995446727493408215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27797423975715879964843813 5212016995446727493408215)
                ·
                  refine ⟨7818025493170091240112323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212016995446727493408215 7818025493170091240112323)
                  ·
                    refine ⟨11727038239755136860168485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7818025493170091240112323 11727038239755136860168485)
                    ·
                      refine ⟨2198819669954088161281591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11727038239755136860168485 2198819669954088161281591)
                      ·
                        rfl

theorem cell23_4282186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_4282186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282186 prefixEnd_4282186 := by exact prefixLift 4282186
  have htrace : WordTrace (prefixWord ++ tailWord_4282186) baseStart_4282186 baseEnd_4282186 := by
    simpa [prefixWord, tailWord_4282186, baseEnd_4282186] using wordTrace_append hprefix tailTrace_4282186
  have hstable : (prefixWord ++ tailWord_4282186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282186).length < 2 ^ (prefixWord ++ tailWord_4282186).sum := by decide
  have hdescent : baseEnd_4282186 < baseStart_4282186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282196 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_4282196 : Nat := 118140960795 + 4282196 * 2 ^ 59
def prefixEnd_4282196 : Nat := 4983230072969 + 3 ^ 40 * 4282196 * 2
def baseEnd_4282196 : Nat := 732941601586877707385515

theorem tailTrace_4282196 : CollatzResearch.WordTrace tailWord_4282196 prefixEnd_4282196 732941601586877707385515 := by
  unfold tailWord_4282196
  simp only [CollatzResearch.WordTrace]
  refine ⟨78092259597171353848445221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104123012796228471797926961 78092259597171353848445221)
  ·
    refine ⟨14642298674469628846583479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78092259597171353848445221 14642298674469628846583479)
    ·
      refine ⟨21963448011704443269875219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14642298674469628846583479 21963448011704443269875219)
      ·
        refine ⟨32945172017556664904812829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21963448011704443269875219 32945172017556664904812829)
        ·
          refine ⟨12354439506583749339304811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32945172017556664904812829 12354439506583749339304811)
          ·
            refine ⟨18531659259875624008957217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12354439506583749339304811 18531659259875624008957217)
            ·
              refine ⟨13898744444906718006717913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18531659259875624008957217 13898744444906718006717913)
              ·
                refine ⟨10424058333680038505038435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13898744444906718006717913 10424058333680038505038435)
                ·
                  refine ⟨15636087500520057757557653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10424058333680038505038435 15636087500520057757557653)
                  ·
                    refine ⟨732941601586877707385515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15636087500520057757557653 732941601586877707385515)
                    ·
                      rfl

theorem cell23_4282196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_4282196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282196 prefixEnd_4282196 := by exact prefixLift 4282196
  have htrace : WordTrace (prefixWord ++ tailWord_4282196) baseStart_4282196 baseEnd_4282196 := by
    simpa [prefixWord, tailWord_4282196, baseEnd_4282196] using wordTrace_append hprefix tailTrace_4282196
  have hstable : (prefixWord ++ tailWord_4282196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282196).length < 2 ^ (prefixWord ++ tailWord_4282196).sum := by decide
  have hdescent : baseEnd_4282196 < baseStart_4282196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282220 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_4282220 : Nat := 118140960795 + 4282220 * 2 ^ 59
def prefixEnd_4282220 : Nat := 4983230072969 + 3 ^ 40 * 4282220 * 2
def baseEnd_4282220 : Nat := 2198837128296341028256435

theorem tailTrace_4282220 : CollatzResearch.WordTrace tailWord_4282220 prefixEnd_4282220 2198837128296341028256435 := by
  unfold tailWord_4282220
  simp only [CollatzResearch.WordTrace]
  refine ⟨78092697273127879897882057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104123596364170506530509409 78092697273127879897882057)
  ·
    refine ⟨58569522954845909923411543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78092697273127879897882057 58569522954845909923411543)
    ·
      refine ⟨87854284432268864885117315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58569522954845909923411543 87854284432268864885117315)
      ·
        refine ⟨131781426648403297327675973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87854284432268864885117315 131781426648403297327675973)
        ·
          refine ⟨24709017496575618248939245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131781426648403297327675973 24709017496575618248939245)
          ·
            refine ⟨9265881561215856843352217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24709017496575618248939245 9265881561215856843352217)
            ·
              refine ⟨6949411170911892632514163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9265881561215856843352217 6949411170911892632514163)
              ·
                refine ⟨10424116756367838948771245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949411170911892632514163 10424116756367838948771245)
                ·
                  refine ⟨3909043783637939605789217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10424116756367838948771245 3909043783637939605789217)
                  ·
                    refine ⟨2931782837728454704341913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909043783637939605789217 2931782837728454704341913)
                    ·
                      refine ⟨2198837128296341028256435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931782837728454704341913 2198837128296341028256435)
                      ·
                        rfl

theorem cell23_4282220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_4282220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282220 prefixEnd_4282220 := by exact prefixLift 4282220
  have htrace : WordTrace (prefixWord ++ tailWord_4282220) baseStart_4282220 baseEnd_4282220 := by
    simpa [prefixWord, tailWord_4282220, baseEnd_4282220] using wordTrace_append hprefix tailTrace_4282220
  have hstable : (prefixWord ++ tailWord_4282220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282220).length < 2 ^ (prefixWord ++ tailWord_4282220).sum := by decide
  have hdescent : baseEnd_4282220 < baseStart_4282220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282230 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_4282230 : Nat := 118140960795 + 4282230 * 2 ^ 59
def prefixEnd_4282230 : Nat := 4983230072969 + 3 ^ 40 * 4282230 * 2
def baseEnd_4282230 : Nat := 732947421034295329710463

theorem tailTrace_4282230 : CollatzResearch.WordTrace tailWord_4282230 prefixEnd_4282230 732947421034295329710463 := by
  unfold tailWord_4282230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9761609954763720718976759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104123839517479687669085429 9761609954763720718976759)
  ·
    refine ⟨14642414932145581078465139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9761609954763720718976759 14642414932145581078465139)
    ·
      refine ⟨21963622398218371617697709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14642414932145581078465139 21963622398218371617697709)
      ·
        refine ⟨8236358399331889356636641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21963622398218371617697709 8236358399331889356636641)
        ·
          refine ⟨6177268799498917017477481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8236358399331889356636641 6177268799498917017477481)
          ·
            refine ⟨4632951599624187763108111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6177268799498917017477481 4632951599624187763108111)
            ·
              refine ⟨6949427399436281644662167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632951599624187763108111 6949427399436281644662167)
              ·
                refine ⟨10424141099154422466993251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949427399436281644662167 10424141099154422466993251)
                ·
                  refine ⟨15636211648731633700489877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10424141099154422466993251 15636211648731633700489877)
                  ·
                    refine ⟨732947421034295329710463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15636211648731633700489877 732947421034295329710463)
                    ·
                      rfl

theorem cell23_4282230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_4282230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282230 prefixEnd_4282230 := by exact prefixLift 4282230
  have htrace : WordTrace (prefixWord ++ tailWord_4282230) baseStart_4282230 baseEnd_4282230 := by
    simpa [prefixWord, tailWord_4282230, baseEnd_4282230] using wordTrace_append hprefix tailTrace_4282230
  have hstable : (prefixWord ++ tailWord_4282230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282230).length < 2 ^ (prefixWord ++ tailWord_4282230).sum := by decide
  have hdescent : baseEnd_4282230 < baseStart_4282230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282249 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_4282249 : Nat := 118140960795 + 4282249 * 2 ^ 59
def prefixEnd_4282249 : Nat := 4983230072969 + 3 ^ 40 * 4282249 * 2
def baseEnd_4282249 : Nat := 2198852019235321414793801

theorem tailTrace_4282249 : CollatzResearch.WordTrace tailWord_4282249 prefixEnd_4282249 2198852019235321414793801 := by
  unfold tailWord_4282249
  simp only [CollatzResearch.WordTrace]
  refine ⟨156186452263150697748569801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104124301508767131832379867 156186452263150697748569801)
  ·
    refine ⟨117139839197363023311427351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156186452263150697748569801 117139839197363023311427351)
    ·
      refine ⟨175709758796044534967141027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117139839197363023311427351 175709758796044534967141027)
      ·
        refine ⟨263564638194066802450711541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175709758796044534967141027 263564638194066802450711541)
        ·
          refine ⟨24709184830693762729754207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263564638194066802450711541 24709184830693762729754207)
          ·
            refine ⟨37063777246040644094631311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24709184830693762729754207 37063777246040644094631311)
            ·
              refine ⟨55595665869060966141946967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37063777246040644094631311 55595665869060966141946967)
              ·
                refine ⟨83393498803591449212920451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55595665869060966141946967 83393498803591449212920451)
                ·
                  refine ⟨125090248205387173819380677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83393498803591449212920451 125090248205387173819380677)
                  ·
                    refine ⟨23454421538510095091133877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125090248205387173819380677 23454421538510095091133877)
                    ·
                      refine ⟨2198852019235321414793801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23454421538510095091133877 2198852019235321414793801)
                      ·
                        rfl

theorem cell23_4282249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_4282249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282249 prefixEnd_4282249 := by exact prefixLift 4282249
  have htrace : WordTrace (prefixWord ++ tailWord_4282249) baseStart_4282249 baseEnd_4282249 := by
    simpa [prefixWord, tailWord_4282249, baseEnd_4282249] using wordTrace_append hprefix tailTrace_4282249
  have hstable : (prefixWord ++ tailWord_4282249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282249).length < 2 ^ (prefixWord ++ tailWord_4282249).sum := by decide
  have hdescent : baseEnd_4282249 < baseStart_4282249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282309 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_4282309 : Nat := 118140960795 + 4282309 * 2 ^ 59
def prefixEnd_4282309 : Nat := 4983230072969 + 3 ^ 40 * 4282309 * 2
def baseEnd_4282309 : Nat := 2198882828074591180043525

theorem tailTrace_4282309 : CollatzResearch.WordTrace tailWord_4282309 prefixEnd_4282309 2198882828074591180043525 := by
  unfold tailWord_4282309
  simp only [CollatzResearch.WordTrace]
  refine ⟨156188640642933327995753981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104125760428622218663835987 156188640642933327995753981)
  ·
    refine ⟨58570740241099997998407743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156188640642933327995753981 58570740241099997998407743)
    ·
      refine ⟨87856110361649996997611615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58570740241099997998407743 87856110361649996997611615)
      ·
        refine ⟨131784165542474995496417423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87856110361649996997611615 131784165542474995496417423)
        ·
          refine ⟨197676248313712493244626135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131784165542474995496417423 197676248313712493244626135)
          ·
            refine ⟨296514372470568739866939203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197676248313712493244626135 296514372470568739866939203)
            ·
              refine ⟨444771558705853109800408805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296514372470568739866939203 444771558705853109800408805)
              ·
                refine ⟨83394667257347458087576651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 444771558705853109800408805 83394667257347458087576651)
                ·
                  refine ⟨125092000886021187131364977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83394667257347458087576651 125092000886021187131364977)
                  ·
                    refine ⟨93819000664515890348523733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125092000886021187131364977 93819000664515890348523733)
                    ·
                      refine ⟨2198882828074591180043525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93819000664515890348523733 2198882828074591180043525)
                      ·
                        rfl

theorem cell23_4282309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_4282309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282309 prefixEnd_4282309 := by exact prefixLift 4282309
  have htrace : WordTrace (prefixWord ++ tailWord_4282309) baseStart_4282309 baseEnd_4282309 := by
    simpa [prefixWord, tailWord_4282309, baseEnd_4282309] using wordTrace_append hprefix tailTrace_4282309
  have hstable : (prefixWord ++ tailWord_4282309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282309).length < 2 ^ (prefixWord ++ tailWord_4282309).sum := by decide
  have hdescent : baseEnd_4282309 < baseStart_4282309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282346 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_4282346 : Nat := 118140960795 + 4282346 * 2 ^ 59
def prefixEnd_4282346 : Nat := 4983230072969 + 3 ^ 40 * 4282346 * 2
def baseEnd_4282346 : Nat := 732967275619602511760285

theorem tailTrace_4282346 : CollatzResearch.WordTrace tailWord_4282346 prefixEnd_4282346 732967275619602511760285 := by
  unfold tailWord_4282346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39047497535949820828712723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104126660095866188876567261 39047497535949820828712723)
  ·
    refine ⟨58571246303924731243069085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39047497535949820828712723 58571246303924731243069085)
    ·
      refine ⟨21964217363971774216150907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58571246303924731243069085 21964217363971774216150907)
      ·
        refine ⟨32946326045957661324226361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21964217363971774216150907 32946326045957661324226361)
        ·
          refine ⟨24709744534468245993169771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32946326045957661324226361 24709744534468245993169771)
          ·
            refine ⟨37064616801702368989754657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24709744534468245993169771 37064616801702368989754657)
            ·
              refine ⟨27798462601276776742315993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37064616801702368989754657 27798462601276776742315993)
              ·
                refine ⟨20848846950957582556736995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27798462601276776742315993 20848846950957582556736995)
                ·
                  refine ⟨31273270426436373835105493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20848846950957582556736995 31273270426436373835105493)
                  ·
                    refine ⟨732967275619602511760285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31273270426436373835105493 732967275619602511760285)
                    ·
                      rfl

theorem cell23_4282346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_4282346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282346 prefixEnd_4282346 := by exact prefixLift 4282346
  have htrace : WordTrace (prefixWord ++ tailWord_4282346) baseStart_4282346 baseEnd_4282346 := by
    simpa [prefixWord, tailWord_4282346, baseEnd_4282346] using wordTrace_append hprefix tailTrace_4282346
  have hstable : (prefixWord ++ tailWord_4282346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282346).length < 2 ^ (prefixWord ++ tailWord_4282346).sum := by decide
  have hdescent : baseEnd_4282346 < baseStart_4282346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282410 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_4282410 : Nat := 118140960795 + 4282410 * 2 ^ 59
def prefixEnd_4282410 : Nat := 4983230072969 + 3 ^ 40 * 4282410 * 2
def baseEnd_4282410 : Nat := 732978229873565094960187

theorem tailTrace_4282410 : CollatzResearch.WordTrace tailWord_4282410 prefixEnd_4282410 732978229873565094960187 := by
  unfold tailWord_4282410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39048081103891855561295171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104128216277044948163453789 39048081103891855561295171)
  ·
    refine ⟨58572121655837783341942757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39048081103891855561295171 58572121655837783341942757)
    ·
      refine ⟨10982272810469584376614267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58572121655837783341942757 10982272810469584376614267)
      ·
        refine ⟨16473409215704376564921401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10982272810469584376614267 16473409215704376564921401)
        ·
          refine ⟨12355056911778282423691051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16473409215704376564921401 12355056911778282423691051)
          ·
            refine ⟨18532585367667423635536577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12355056911778282423691051 18532585367667423635536577)
            ·
              refine ⟨13899439025750567726652433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18532585367667423635536577 13899439025750567726652433)
              ·
                refine ⟨10424579269312925794989325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13899439025750567726652433 10424579269312925794989325)
                ·
                  refine ⟨3909217225992347173120997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10424579269312925794989325 3909217225992347173120997)
                  ·
                    refine ⟨732978229873565094960187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3909217225992347173120997 732978229873565094960187)
                    ·
                      rfl

theorem cell23_4282410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_4282410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282410 prefixEnd_4282410 := by exact prefixLift 4282410
  have htrace : WordTrace (prefixWord ++ tailWord_4282410) baseStart_4282410 baseEnd_4282410 := by
    simpa [prefixWord, tailWord_4282410, baseEnd_4282410] using wordTrace_append hprefix tailTrace_4282410
  have hstable : (prefixWord ++ tailWord_4282410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282410).length < 2 ^ (prefixWord ++ tailWord_4282410).sum := by decide
  have hdescent : baseEnd_4282410 < baseStart_4282410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282473 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_4282473 : Nat := 118140960795 + 4282473 * 2 ^ 59
def prefixEnd_4282473 : Nat := 4983230072969 + 3 ^ 40 * 4282473 * 2
def baseEnd_4282473 : Nat := 2198967038901928538392771

theorem tailTrace_4282473 : CollatzResearch.WordTrace tailWord_4282473 prefixEnd_4282473 2198967038901928538392771 := by
  unfold tailWord_4282473
  simp only [CollatzResearch.WordTrace]
  refine ⟨156194622214339184004724073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104129748142892789336482715 156194622214339184004724073)
  ·
    refine ⟨117145966660754388003543055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156194622214339184004724073 117145966660754388003543055)
    ·
      refine ⟨175718949991131582005314583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117145966660754388003543055 175718949991131582005314583)
      ·
        refine ⟨263578424986697373007971875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175718949991131582005314583 263578424986697373007971875)
        ·
          refine ⟨395367637480046059511957813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263578424986697373007971875 395367637480046059511957813)
          ·
            refine ⟨37065716013754318079246045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 395367637480046059511957813 37065716013754318079246045)
            ·
              refine ⟨13899643505157869279717267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37065716013754318079246045 13899643505157869279717267)
              ·
                refine ⟨20849465257736803919575901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13899643505157869279717267 20849465257736803919575901)
                ·
                  refine ⟨7818549471651301469840963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20849465257736803919575901 7818549471651301469840963)
                  ·
                    refine ⟨11727824207476952204761445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7818549471651301469840963 11727824207476952204761445)
                    ·
                      refine ⟨2198967038901928538392771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11727824207476952204761445 2198967038901928538392771)
                      ·
                        rfl

theorem cell23_4282473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_4282473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282473 prefixEnd_4282473 := by exact prefixLift 4282473
  have htrace : WordTrace (prefixWord ++ tailWord_4282473) baseStart_4282473 baseEnd_4282473 := by
    simpa [prefixWord, tailWord_4282473, baseEnd_4282473] using wordTrace_append hprefix tailTrace_4282473
  have hstable : (prefixWord ++ tailWord_4282473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282473).length < 2 ^ (prefixWord ++ tailWord_4282473).sum := by decide
  have hdescent : baseEnd_4282473 < baseStart_4282473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282477 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4282477 : Nat := 118140960795 + 4282477 * 2 ^ 59
def prefixEnd_4282477 : Nat := 4983230072969 + 3 ^ 40 * 4282477 * 2
def baseEnd_4282477 : Nat := 2198969092824546522742753

theorem tailTrace_4282477 : CollatzResearch.WordTrace tailWord_4282477 prefixEnd_4282477 2198969092824546522742753 := by
  unfold tailWord_4282477
  simp only [CollatzResearch.WordTrace]
  refine ⟨156194768106324692687869685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104129845404216461791913123 156194768106324692687869685)
  ·
    refine ⟨14643259509967939939487783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156194768106324692687869685 14643259509967939939487783)
    ·
      refine ⟨21964889264951909909231675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643259509967939939487783 21964889264951909909231675)
      ·
        refine ⟨32947333897427864863847513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21964889264951909909231675 32947333897427864863847513)
        ·
          refine ⟨24710500423070898647885635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32947333897427864863847513 24710500423070898647885635)
          ·
            refine ⟨37065750634606347971828453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24710500423070898647885635 37065750634606347971828453)
            ·
              refine ⟨6949828243988690244717835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37065750634606347971828453 6949828243988690244717835)
              ·
                refine ⟨10424742365983035367076753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949828243988690244717835 10424742365983035367076753)
                ·
                  refine ⟨7818556774487276525307565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10424742365983035367076753 7818556774487276525307565)
                  ·
                    refine ⟨2931958790432728696990337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7818556774487276525307565 2931958790432728696990337)
                    ·
                      refine ⟨2198969092824546522742753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2931958790432728696990337 2198969092824546522742753)
                      ·
                        rfl

theorem cell23_4282477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4282477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282477 prefixEnd_4282477 := by exact prefixLift 4282477
  have htrace : WordTrace (prefixWord ++ tailWord_4282477) baseStart_4282477 baseEnd_4282477 := by
    simpa [prefixWord, tailWord_4282477, baseEnd_4282477] using wordTrace_append hprefix tailTrace_4282477
  have hstable : (prefixWord ++ tailWord_4282477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282477).length < 2 ^ (prefixWord ++ tailWord_4282477).sum := by decide
  have hdescent : baseEnd_4282477 < baseStart_4282477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282501 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 1, 1, 3]
def baseStart_4282501 : Nat := 118140960795 + 4282501 * 2 ^ 59
def prefixEnd_4282501 : Nat := 4983230072969 + 3 ^ 40 * 4282501 * 2
def baseEnd_4282501 : Nat := 2198981416360254428842643

theorem tailTrace_4282501 : CollatzResearch.WordTrace tailWord_4282501 prefixEnd_4282501 2198981416360254428842643 := by
  unfold tailWord_4282501
  simp only [CollatzResearch.WordTrace]
  refine ⟨156195643458237744786743357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104130428972158496524495571 156195643458237744786743357)
  ·
    refine ⟨58573366296839154295028759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156195643458237744786743357 58573366296839154295028759)
    ·
      refine ⟨87860049445258731442543139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58573366296839154295028759 87860049445258731442543139)
      ·
        refine ⟨131790074167888097163814709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87860049445258731442543139 131790074167888097163814709)
        ·
          refine ⟨12355319453239509109107629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131790074167888097163814709 12355319453239509109107629)
          ·
            refine ⟨4633244794964815915915361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12355319453239509109107629 4633244794964815915915361)
            ·
              refine ⟨3474933596223611936936521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633244794964815915915361 3474933596223611936936521)
              ·
                refine ⟨2606200197167708952702391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474933596223611936936521 2606200197167708952702391)
                ·
                  refine ⟨3909300295751563429053587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606200197167708952702391 3909300295751563429053587)
                  ·
                    refine ⟨5863950443627345143580381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3909300295751563429053587 5863950443627345143580381)
                    ·
                      refine ⟨2198981416360254428842643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5863950443627345143580381 2198981416360254428842643)
                      ·
                        rfl

theorem cell23_4282501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_4282501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282501 prefixEnd_4282501 := by exact prefixLift 4282501
  have htrace : WordTrace (prefixWord ++ tailWord_4282501) baseStart_4282501 baseEnd_4282501 := by
    simpa [prefixWord, tailWord_4282501, baseEnd_4282501] using wordTrace_append hprefix tailTrace_4282501
  have hstable : (prefixWord ++ tailWord_4282501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282501).length < 2 ^ (prefixWord ++ tailWord_4282501).sum := by decide
  have hdescent : baseEnd_4282501 < baseStart_4282501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282541 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_4282541 : Nat := 118140960795 + 4282541 * 2 ^ 59
def prefixEnd_4282541 : Nat := 4983230072969 + 3 ^ 40 * 4282541 * 2
def baseEnd_4282541 : Nat := 2199001955586434272342459

theorem tailTrace_4282541 : CollatzResearch.WordTrace tailWord_4282541 prefixEnd_4282541 2199001955586434272342459 := by
  unfold tailWord_4282541
  simp only [CollatzResearch.WordTrace]
  refine ⟨156197102378092831618199477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104131401585395221078799651 156197102378092831618199477)
  ·
    refine ⟨14643478347946202964206201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156197102378092831618199477 14643478347946202964206201)
    ·
      refine ⟨10982608760959652223154651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14643478347946202964206201 10982608760959652223154651)
      ·
        refine ⟨16473913141439478334731977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10982608760959652223154651 16473913141439478334731977)
        ·
          refine ⟨12355434856079608751048983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16473913141439478334731977 12355434856079608751048983)
          ·
            refine ⟨18533152284119413126573475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12355434856079608751048983 18533152284119413126573475)
            ·
              refine ⟨27799728426179119689860213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18533152284119413126573475 27799728426179119689860213)
              ·
                refine ⟨2606224539954292470924395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27799728426179119689860213 2606224539954292470924395)
                ·
                  refine ⟨3909336809931438706386593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606224539954292470924395 3909336809931438706386593)
                  ·
                    refine ⟨2932002607448579029789945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909336809931438706386593 2932002607448579029789945)
                    ·
                      refine ⟨2199001955586434272342459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932002607448579029789945 2199001955586434272342459)
                      ·
                        rfl

theorem cell23_4282541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_4282541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282541 prefixEnd_4282541 := by exact prefixLift 4282541
  have htrace : WordTrace (prefixWord ++ tailWord_4282541) baseStart_4282541 baseEnd_4282541 := by
    simpa [prefixWord, tailWord_4282541, baseEnd_4282541] using wordTrace_append hprefix tailTrace_4282541
  have hstable : (prefixWord ++ tailWord_4282541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282541).length < 2 ^ (prefixWord ++ tailWord_4282541).sum := by decide
  have hdescent : baseEnd_4282541 < baseStart_4282541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282583 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_4282583 : Nat := 118140960795 + 4282583 * 2 ^ 59
def prefixEnd_4282583 : Nat := 4983230072969 + 3 ^ 40 * 4282583 * 2
def baseEnd_4282583 : Nat := 2199023521773923108017265

theorem tailTrace_4282583 : CollatzResearch.WordTrace tailWord_4282583 prefixEnd_4282583 2199023521773923108017265 := by
  unfold tailWord_4282583
  simp only [CollatzResearch.WordTrace]
  refine ⟨156198634243940672791228403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104132422829293781860818935 156198634243940672791228403)
  ·
    refine ⟨234297951365911009186842605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156198634243940672791228403 234297951365911009186842605)
    ·
      refine ⟨87861731762216628445065977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234297951365911009186842605 87861731762216628445065977)
      ·
        refine ⟨65896298821662471333799483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87861731762216628445065977 65896298821662471333799483)
        ·
          refine ⟨98844448232493707000699225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65896298821662471333799483 98844448232493707000699225)
          ·
            refine ⟨74133336174370280250524419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98844448232493707000699225 74133336174370280250524419)
            ·
              refine ⟨111200004261555420375786629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74133336174370280250524419 111200004261555420375786629)
              ·
                refine ⟨20850000799041641320459993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111200004261555420375786629 20850000799041641320459993)
                ·
                  refine ⟨15637500599281230990344995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20850000799041641320459993 15637500599281230990344995)
                  ·
                    refine ⟨23456250898921846485517493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15637500599281230990344995 23456250898921846485517493)
                    ·
                      refine ⟨2199023521773923108017265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23456250898921846485517493 2199023521773923108017265)
                      ·
                        rfl

theorem cell23_4282583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_4282583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282583 prefixEnd_4282583 := by exact prefixLift 4282583
  have htrace : WordTrace (prefixWord ++ tailWord_4282583) baseStart_4282583 baseEnd_4282583 := by
    simpa [prefixWord, tailWord_4282583, baseEnd_4282583] using wordTrace_append hprefix tailTrace_4282583
  have hstable : (prefixWord ++ tailWord_4282583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282583).length < 2 ^ (prefixWord ++ tailWord_4282583).sum := by decide
  have hdescent : baseEnd_4282583 < baseStart_4282583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282584 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_4282584 : Nat := 118140960795 + 4282584 * 2 ^ 59
def prefixEnd_4282584 : Nat := 4983230072969 + 3 ^ 40 * 4282584 * 2
def baseEnd_4282584 : Nat := 2199024035254577604104761

theorem tailTrace_4282584 : CollatzResearch.WordTrace tailWord_4282584 prefixEnd_4282584 2199024035254577604104761 := by
  unfold tailWord_4282584
  simp only [CollatzResearch.WordTrace]
  refine ⟨78099335358468524981007403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104132447144624699974676537 78099335358468524981007403)
  ·
    refine ⟨117149003037702787471511105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78099335358468524981007403 117149003037702787471511105)
    ·
      refine ⟨87861752278277090603633329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117149003037702787471511105 87861752278277090603633329)
      ·
        refine ⟨65896314208707817952724997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87861752278277090603633329 65896314208707817952724997)
        ·
          refine ⟨12355558914132715866135937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65896314208707817952724997 12355558914132715866135937)
          ·
            refine ⟨9266669185599536899601953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12355558914132715866135937 9266669185599536899601953)
            ·
              refine ⟨6950001889199652674701465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9266669185599536899601953 6950001889199652674701465)
              ·
                refine ⟨5212501416899739506026099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6950001889199652674701465 5212501416899739506026099)
                ·
                  refine ⟨7818752125349609259039149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212501416899739506026099 7818752125349609259039149)
                  ·
                    refine ⟨2932032047006103472139681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7818752125349609259039149 2932032047006103472139681)
                    ·
                      refine ⟨2199024035254577604104761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932032047006103472139681 2199024035254577604104761)
                      ·
                        rfl

theorem cell23_4282584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_4282584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282584 prefixEnd_4282584 := by exact prefixLift 4282584
  have htrace : WordTrace (prefixWord ++ tailWord_4282584) baseStart_4282584 baseEnd_4282584 := by
    simpa [prefixWord, tailWord_4282584, baseEnd_4282584] using wordTrace_append hprefix tailTrace_4282584
  have hstable : (prefixWord ++ tailWord_4282584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282584).length < 2 ^ (prefixWord ++ tailWord_4282584).sum := by decide
  have hdescent : baseEnd_4282584 < baseStart_4282584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282600 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4282600 : Nat := 118140960795 + 4282600 * 2 ^ 59
def prefixEnd_4282600 : Nat := 4983230072969 + 3 ^ 40 * 4282600 * 2
def baseEnd_4282600 : Nat := 2199032250945049541504687

theorem tailTrace_4282600 : CollatzResearch.WordTrace tailWord_4282600 prefixEnd_4282600 2199032250945049541504687 := by
  unfold tailWord_4282600
  simp only [CollatzResearch.WordTrace]
  refine ⟨78099627142439542347298627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104132836189919389796398169 78099627142439542347298627)
  ·
    refine ⟨117149440713659313520947941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78099627142439542347298627 117149440713659313520947941)
    ·
      refine ⟨21965520133811121285177739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117149440713659313520947941 21965520133811121285177739)
      ·
        refine ⟨32948280200716681927766609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21965520133811121285177739 32948280200716681927766609)
        ·
          refine ⟨24711210150537511445824957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32948280200716681927766609 24711210150537511445824957)
          ·
            refine ⟨9266703806451566792184359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24711210150537511445824957 9266703806451566792184359)
            ·
              refine ⟨13900055709677350188276539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9266703806451566792184359 13900055709677350188276539)
              ·
                refine ⟨20850083564516025282414809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13900055709677350188276539 20850083564516025282414809)
                ·
                  refine ⟨15637562673387018961811107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20850083564516025282414809 15637562673387018961811107)
                  ·
                    refine ⟨23456344010080528442716661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15637562673387018961811107 23456344010080528442716661)
                    ·
                      refine ⟨2199032250945049541504687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23456344010080528442716661 2199032250945049541504687)
                      ·
                        rfl

theorem cell23_4282600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4282600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282600 prefixEnd_4282600 := by exact prefixLift 4282600
  have htrace : WordTrace (prefixWord ++ tailWord_4282600) baseStart_4282600 baseEnd_4282600 := by
    simpa [prefixWord, tailWord_4282600, baseEnd_4282600] using wordTrace_append hprefix tailTrace_4282600
  have hstable : (prefixWord ++ tailWord_4282600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282600).length < 2 ^ (prefixWord ++ tailWord_4282600).sum := by decide
  have hdescent : baseEnd_4282600 < baseStart_4282600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282614 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4282614 : Nat := 118140960795 + 4282614 * 2 ^ 59
def prefixEnd_4282614 : Nat := 4983230072969 + 3 ^ 40 * 4282614 * 2
def baseEnd_4282614 : Nat := 2199039439674212486729623

theorem tailTrace_4282614 : CollatzResearch.WordTrace tailWord_4282614 prefixEnd_4282614 2199039439674212486729623 := by
  unfold tailWord_4282614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762485306676772817850431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104133176604552243390404597 9762485306676772817850431)
  ·
    refine ⟨14643727960015159226775647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762485306676772817850431 14643727960015159226775647)
    ·
      refine ⟨21965591940022738840163471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643727960015159226775647 21965591940022738840163471)
      ·
        refine ⟨32948387910034108260245207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21965591940022738840163471 32948387910034108260245207)
        ·
          refine ⟨49422581865051162390367811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32948387910034108260245207 49422581865051162390367811)
          ·
            refine ⟨74133872797576743585551717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49422581865051162390367811 74133872797576743585551717)
            ·
              refine ⟨13900101149545639422290947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74133872797576743585551717 13900101149545639422290947)
              ·
                refine ⟨20850151724318459133436421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13900101149545639422290947 20850151724318459133436421)
                ·
                  refine ⟨3909403448309711087519329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20850151724318459133436421 3909403448309711087519329)
                  ·
                    refine ⟨2932052586232283315639497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909403448309711087519329 2932052586232283315639497)
                    ·
                      refine ⟨2199039439674212486729623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932052586232283315639497 2199039439674212486729623)
                      ·
                        rfl

theorem cell23_4282614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4282614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282614 prefixEnd_4282614 := by exact prefixLift 4282614
  have htrace : WordTrace (prefixWord ++ tailWord_4282614) baseStart_4282614 baseEnd_4282614 := by
    simpa [prefixWord, tailWord_4282614, baseEnd_4282614] using wordTrace_append hprefix tailTrace_4282614
  have hstable : (prefixWord ++ tailWord_4282614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282614).length < 2 ^ (prefixWord ++ tailWord_4282614).sum := by decide
  have hdescent : baseEnd_4282614 < baseStart_4282614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282620 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 7]
def baseStart_4282620 : Nat := 118140960795 + 4282620 * 2 ^ 59
def prefixEnd_4282620 : Nat := 4983230072969 + 3 ^ 40 * 4282620 * 2
def baseEnd_4282620 : Nat := 244338057839793273694955

theorem tailTrace_4282620 : CollatzResearch.WordTrace tailWord_4282620 prefixEnd_4282620 244338057839793273694955 := by
  unfold tailWord_4282620
  simp only [CollatzResearch.WordTrace]
  refine ⟨78099991872403314055162657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104133322496537752073550209 78099991872403314055162657)
  ·
    refine ⟨58574993904302485541371993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78099991872403314055162657 58574993904302485541371993)
    ·
      refine ⟨43931245428226864156028995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58574993904302485541371993 43931245428226864156028995)
      ·
        refine ⟨65896868142340296234043493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43931245428226864156028995 65896868142340296234043493)
        ·
          refine ⟨12355662776688805543883155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65896868142340296234043493 12355662776688805543883155)
          ·
            refine ⟨18533494165033208315824733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12355662776688805543883155 18533494165033208315824733)
            ·
              refine ⟨6950060311887453118434275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18533494165033208315824733 6950060311887453118434275)
              ·
                refine ⟨10425090467831179677651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6950060311887453118434275 10425090467831179677651413)
                ·
                  refine ⟨244338057839793273694955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10425090467831179677651413 244338057839793273694955)
                  ·
                    rfl

theorem cell23_4282620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_4282620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282620 prefixEnd_4282620 := by exact prefixLift 4282620
  have htrace : WordTrace (prefixWord ++ tailWord_4282620) baseStart_4282620 baseEnd_4282620 := by
    simpa [prefixWord, tailWord_4282620, baseEnd_4282620] using wordTrace_append hprefix tailTrace_4282620
  have hstable : (prefixWord ++ tailWord_4282620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282620).length < 2 ^ (prefixWord ++ tailWord_4282620).sum := by decide
  have hdescent : baseEnd_4282620 < baseStart_4282620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282660 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4282660 : Nat := 118140960795 + 4282660 * 2 ^ 59
def prefixEnd_4282660 : Nat := 4983230072969 + 3 ^ 40 * 4282660 * 2
def baseEnd_4282660 : Nat := 2199063059784319306754411

theorem tailTrace_4282660 : CollatzResearch.WordTrace tailWord_4282660 prefixEnd_4282660 2199063059784319306754411 := by
  unfold tailWord_4282660
  simp only [CollatzResearch.WordTrace]
  refine ⟨78100721332330857470890717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104134295109774476627854289 78100721332330857470890717)
  ·
    refine ⟨29287770499624071551584019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78100721332330857470890717 29287770499624071551584019)
    ·
      refine ⟨43931655749436107327376029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29287770499624071551584019 43931655749436107327376029)
      ·
        refine ⟨16474370906038540247766011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43931655749436107327376029 16474370906038540247766011)
        ·
          refine ⟨24711556359057810371649017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16474370906038540247766011 24711556359057810371649017)
          ·
            refine ⟨18533667269293357778736763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24711556359057810371649017 18533667269293357778736763)
            ·
              refine ⟨27800500903940036668105145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18533667269293357778736763 27800500903940036668105145)
              ·
                refine ⟨20850375677955027501078859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27800500903940036668105145 20850375677955027501078859)
                ·
                  refine ⟨31275563516932541251618289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20850375677955027501078859 31275563516932541251618289)
                  ·
                    refine ⟨23456672637699405938713717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31275563516932541251618289 23456672637699405938713717)
                    ·
                      refine ⟨2199063059784319306754411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23456672637699405938713717 2199063059784319306754411)
                      ·
                        rfl

theorem cell23_4282660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4282660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282660 prefixEnd_4282660 := by exact prefixLift 4282660
  have htrace : WordTrace (prefixWord ++ tailWord_4282660) baseStart_4282660 baseEnd_4282660 := by
    simpa [prefixWord, tailWord_4282660, baseEnd_4282660] using wordTrace_append hprefix tailTrace_4282660
  have hstable : (prefixWord ++ tailWord_4282660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282660).length < 2 ^ (prefixWord ++ tailWord_4282660).sum := by decide
  have hdescent : baseEnd_4282660 < baseStart_4282660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282687 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 2, 4, 2]
def baseStart_4282687 : Nat := 118140960795 + 4282687 * 2 ^ 59
def prefixEnd_4282687 : Nat := 4983230072969 + 3 ^ 40 * 4282687 * 2
def baseEnd_4282687 : Nat := 2199076923761990701116787

theorem tailTrace_4282687 : CollatzResearch.WordTrace tailWord_4282687 prefixEnd_4282687 2199076923761990701116787 := by
  unfold tailWord_4282687
  simp only [CollatzResearch.WordTrace]
  refine ⟨156202427435563898553014315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104134951623709265702009543 156202427435563898553014315)
  ·
    refine ⟨234303641153345847829521473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156202427435563898553014315 234303641153345847829521473)
    ·
      refine ⟨175727730865009385872141105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234303641153345847829521473 175727730865009385872141105)
      ·
        refine ⟨131795798148757039404105829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175727730865009385872141105 131795798148757039404105829)
        ·
          refine ⟨24711712152891944888269843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131795798148757039404105829 24711712152891944888269843)
          ·
            refine ⟨37067568229337917332404765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24711712152891944888269843 37067568229337917332404765)
            ·
              refine ⟨13900338086001718999651787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37067568229337917332404765 13900338086001718999651787)
              ·
                refine ⟨20850507129002578499477681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13900338086001718999651787 20850507129002578499477681)
                ·
                  refine ⟨15637880346751933874608261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20850507129002578499477681 15637880346751933874608261)
                  ·
                    refine ⟨2932102565015987601489049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15637880346751933874608261 2932102565015987601489049)
                    ·
                      refine ⟨2199076923761990701116787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932102565015987601489049 2199076923761990701116787)
                      ·
                        rfl

theorem cell23_4282687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_4282687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282687 prefixEnd_4282687 := by exact prefixLift 4282687
  have htrace : WordTrace (prefixWord ++ tailWord_4282687) baseStart_4282687 baseEnd_4282687 := by
    simpa [prefixWord, tailWord_4282687, baseEnd_4282687] using wordTrace_append hprefix tailTrace_4282687
  have hstable : (prefixWord ++ tailWord_4282687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282687).length < 2 ^ (prefixWord ++ tailWord_4282687).sum := by decide
  have hdescent : baseEnd_4282687 < baseStart_4282687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282693 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 12]
def baseStart_4282693 : Nat := 118140960795 + 4282693 * 2 ^ 59
def prefixEnd_4282693 : Nat := 4983230072969 + 3 ^ 40 * 4282693 * 2
def baseEnd_4282693 : Nat := 244342222738435297515751

theorem tailTrace_4282693 : CollatzResearch.WordTrace tailWord_4282693 prefixEnd_4282693 244342222738435297515751 := by
  unfold tailWord_4282693
  simp only [CollatzResearch.WordTrace]
  refine ⟨156202646273542161577732733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104135097515694774385155155 156202646273542161577732733)
  ·
    refine ⟨58575992352578310591649775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156202646273542161577732733 58575992352578310591649775)
    ·
      refine ⟨87863988528867465887474663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58575992352578310591649775 87863988528867465887474663)
      ·
        refine ⟨131795982793301198831211995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87863988528867465887474663 131795982793301198831211995)
        ·
          refine ⟨197693974189951798246817993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131795982793301198831211995 197693974189951798246817993)
          ·
            refine ⟨148270480642463848685113495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197693974189951798246817993 148270480642463848685113495)
            ·
              refine ⟨222405720963695773027670243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148270480642463848685113495 222405720963695773027670243)
              ·
                refine ⟨333608581445543659541505365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222405720963695773027670243 333608581445543659541505365)
                ·
                  refine ⟨244342222738435297515751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 333608581445543659541505365 244342222738435297515751)
                  ·
                    rfl

theorem cell23_4282693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_4282693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282693 prefixEnd_4282693 := by exact prefixLift 4282693
  have htrace : WordTrace (prefixWord ++ tailWord_4282693) baseStart_4282693 baseEnd_4282693 := by
    simpa [prefixWord, tailWord_4282693, baseEnd_4282693] using wordTrace_append hprefix tailTrace_4282693
  have hstable : (prefixWord ++ tailWord_4282693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282693).length < 2 ^ (prefixWord ++ tailWord_4282693).sum := by decide
  have hdescent : baseEnd_4282693 < baseStart_4282693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282727 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 6]
def baseStart_4282727 : Nat := 118140960795 + 4282727 * 2 ^ 59
def prefixEnd_4282727 : Nat := 4983230072969 + 3 ^ 40 * 4282727 * 2
def baseEnd_4282727 : Nat := 244344162554241171624067

theorem tailTrace_4282727 : CollatzResearch.WordTrace tailWord_4282727 prefixEnd_4282727 244344162554241171624067 := by
  unfold tailWord_4282727
  simp only [CollatzResearch.WordTrace]
  refine ⟨156203886355418985384470435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104135924236945990256313623 156203886355418985384470435)
  ·
    refine ⟨234305829533128478076705653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156203886355418985384470435 234305829533128478076705653)
    ·
      refine ⟨21966171518730794819691155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 234305829533128478076705653 21966171518730794819691155)
      ·
        refine ⟨32949257278096192229536733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21966171518730794819691155 32949257278096192229536733)
        ·
          refine ⟨12355971479286072086076275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32949257278096192229536733 12355971479286072086076275)
          ·
            refine ⟨18533957218929108129114413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12355971479286072086076275 18533957218929108129114413)
            ·
              refine ⟨6950233957098415548417905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18533957218929108129114413 6950233957098415548417905)
              ·
                refine ⟨5212675467823811661313429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6950233957098415548417905 5212675467823811661313429)
                ·
                  refine ⟨244344162554241171624067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5212675467823811661313429 244344162554241171624067)
                  ·
                    rfl

theorem cell23_4282727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 6].length) (baseStart_4282727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282727 prefixEnd_4282727 := by exact prefixLift 4282727
  have htrace : WordTrace (prefixWord ++ tailWord_4282727) baseStart_4282727 baseEnd_4282727 := by
    simpa [prefixWord, tailWord_4282727, baseEnd_4282727] using wordTrace_append hprefix tailTrace_4282727
  have hstable : (prefixWord ++ tailWord_4282727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282727).length < 2 ^ (prefixWord ++ tailWord_4282727).sum := by decide
  have hdescent : baseEnd_4282727 < baseStart_4282727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282747 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 5, 2]
def baseStart_4282747 : Nat := 118140960795 + 4282747 * 2 ^ 59
def prefixEnd_4282747 : Nat := 4983230072969 + 3 ^ 40 * 4282747 * 2
def baseEnd_4282747 : Nat := 2199107732601260466366511

theorem tailTrace_4282747 : CollatzResearch.WordTrace tailWord_4282747 prefixEnd_4282747 2199107732601260466366511 := by
  unfold tailWord_4282747
  simp only [CollatzResearch.WordTrace]
  refine ⟨156204615815346528800198495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104136410543564352533465663 156204615815346528800198495)
  ·
    refine ⟨234306923723019793200297743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156204615815346528800198495 234306923723019793200297743)
    ·
      refine ⟨351460385584529689800446615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234306923723019793200297743 351460385584529689800446615)
      ·
        refine ⟨527190578376794534700669923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351460385584529689800446615 527190578376794534700669923)
        ·
          refine ⟨790785867565191802051004885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527190578376794534700669923 790785867565191802051004885)
          ·
            refine ⟨18534043771059182860570427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 790785867565191802051004885 18534043771059182860570427)
            ·
              refine ⟨27801065656588774290855641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18534043771059182860570427 27801065656588774290855641)
              ·
                refine ⟨20850799242441580718141731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27801065656588774290855641 20850799242441580718141731)
                ·
                  refine ⟨31276198863662371077212597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20850799242441580718141731 31276198863662371077212597)
                  ·
                    refine ⟨2932143643468347288488681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31276198863662371077212597 2932143643468347288488681)
                    ·
                      refine ⟨2199107732601260466366511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932143643468347288488681 2199107732601260466366511)
                      ·
                        rfl

theorem cell23_4282747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5, 2].length) (baseStart_4282747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282747 prefixEnd_4282747 := by exact prefixLift 4282747
  have htrace : WordTrace (prefixWord ++ tailWord_4282747) baseStart_4282747 baseEnd_4282747 := by
    simpa [prefixWord, tailWord_4282747, baseEnd_4282747] using wordTrace_append hprefix tailTrace_4282747
  have hstable : (prefixWord ++ tailWord_4282747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282747).length < 2 ^ (prefixWord ++ tailWord_4282747).sum := by decide
  have hdescent : baseEnd_4282747 < baseStart_4282747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282777 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_4282777 : Nat := 118140960795 + 4282777 * 2 ^ 59
def prefixEnd_4282777 : Nat := 4983230072969 + 3 ^ 40 * 4282777 * 2
def baseEnd_4282777 : Nat := 2199123137020895348991373

theorem tailTrace_4282777 : CollatzResearch.WordTrace tailWord_4282777 prefixEnd_4282777 2199123137020895348991373 := by
  unfold tailWord_4282777
  simp only [CollatzResearch.WordTrace]
  refine ⟨156205710005237843923790585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104137140003491895949193723 156205710005237843923790585)
  ·
    refine ⟨117154282503928382942842939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156205710005237843923790585 117154282503928382942842939)
    ·
      refine ⟨175731423755892574414264409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117154282503928382942842939 175731423755892574414264409)
      ·
        refine ⟨131798567816919430810698307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175731423755892574414264409 131798567816919430810698307)
        ·
          refine ⟨197697851725379146216047461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131798567816919430810698307 197697851725379146216047461)
          ·
            refine ⟨37068347198508589915508899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197697851725379146216047461 37068347198508589915508899)
            ·
              refine ⟨55602520797762884873263349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37068347198508589915508899 55602520797762884873263349)
              ·
                refine ⟨5212736324790270456868439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55602520797762884873263349 5212736324790270456868439)
                ·
                  refine ⟨7819104487185405685302659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212736324790270456868439 7819104487185405685302659)
                  ·
                    refine ⟨11728656730778108527953989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7819104487185405685302659 11728656730778108527953989)
                    ·
                      refine ⟨2199123137020895348991373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11728656730778108527953989 2199123137020895348991373)
                      ·
                        rfl

theorem cell23_4282777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_4282777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282777 prefixEnd_4282777 := by exact prefixLift 4282777
  have htrace : WordTrace (prefixWord ++ tailWord_4282777) baseStart_4282777 baseEnd_4282777 := by
    simpa [prefixWord, tailWord_4282777, baseEnd_4282777] using wordTrace_append hprefix tailTrace_4282777
  have hstable : (prefixWord ++ tailWord_4282777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282777).length < 2 ^ (prefixWord ++ tailWord_4282777).sum := by decide
  have hdescent : baseEnd_4282777 < baseStart_4282777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282781 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_4282781 : Nat := 118140960795 + 4282781 * 2 ^ 59
def prefixEnd_4282781 : Nat := 4983230072969 + 3 ^ 40 * 4282781 * 2
def baseEnd_4282781 : Nat := 2199125190943513333341355

theorem tailTrace_4282781 : CollatzResearch.WordTrace tailWord_4282781 prefixEnd_4282781 2199125190943513333341355 := by
  unfold tailWord_4282781
  simp only [CollatzResearch.WordTrace]
  refine ⟨156205855897223352606936197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104137237264815568404624131 156205855897223352606936197)
  ·
    refine ⟨29288597980729378613800537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156205855897223352606936197 29288597980729378613800537)
    ·
      refine ⟨21966448485547033960350403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29288597980729378613800537 21966448485547033960350403)
      ·
        refine ⟨32949672728320550940525605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21966448485547033960350403 32949672728320550940525605)
        ·
          refine ⟨6178063636560103301348551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32949672728320550940525605 6178063636560103301348551)
          ·
            refine ⟨9267095454840154952022827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178063636560103301348551 9267095454840154952022827)
            ·
              refine ⟨13900643182260232428034241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267095454840154952022827 13900643182260232428034241)
              ·
                refine ⟨10425482386695174321025681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13900643182260232428034241 10425482386695174321025681)
                ·
                  refine ⟨7819111790021380740769261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10425482386695174321025681 7819111790021380740769261)
                  ·
                    refine ⟨2932166921258017777788473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7819111790021380740769261 2932166921258017777788473)
                    ·
                      refine ⟨2199125190943513333341355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932166921258017777788473 2199125190943513333341355)
                      ·
                        rfl

theorem cell23_4282781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_4282781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282781 prefixEnd_4282781 := by exact prefixLift 4282781
  have htrace : WordTrace (prefixWord ++ tailWord_4282781) baseStart_4282781 baseEnd_4282781 := by
    simpa [prefixWord, tailWord_4282781, baseEnd_4282781] using wordTrace_append hprefix tailTrace_4282781
  have hstable : (prefixWord ++ tailWord_4282781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282781).length < 2 ^ (prefixWord ++ tailWord_4282781).sum := by decide
  have hdescent : baseEnd_4282781 < baseStart_4282781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282787 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 4, 4]
def baseStart_4282787 : Nat := 118140960795 + 4282787 * 2 ^ 59
def prefixEnd_4282787 : Nat := 4983230072969 + 3 ^ 40 * 4282787 * 2
def baseEnd_4282787 : Nat := 733042757275813436622109

theorem tailTrace_4282787 : CollatzResearch.WordTrace tailWord_4282787 prefixEnd_4282787 733042757275813436622109 := by
  unfold tailWord_4282787
  simp only [CollatzResearch.WordTrace]
  refine ⟨156206074735201615631654615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104137383156801077087769743 156206074735201615631654615)
  ·
    refine ⟨234309112102802423447481923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156206074735201615631654615 234309112102802423447481923)
    ·
      refine ⟨351463668154203635171222885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234309112102802423447481923 351463668154203635171222885)
      ·
        refine ⟨65899437778913181594604291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 351463668154203635171222885 65899437778913181594604291)
        ·
          refine ⟨98849156668369772391906437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65899437778913181594604291 98849156668369772391906437)
          ·
            refine ⟨18534216875319332323482457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98849156668369772391906437 18534216875319332323482457)
            ·
              refine ⟨13900662656489499242611843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18534216875319332323482457 13900662656489499242611843)
              ·
                refine ⟨20850993984734248863917765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13900662656489499242611843 20850993984734248863917765)
                ·
                  refine ⟨3909561372137671661984581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20850993984734248863917765 3909561372137671661984581)
                  ·
                    refine ⟨733042757275813436622109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3909561372137671661984581 733042757275813436622109)
                    ·
                      rfl

theorem cell23_4282787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 4].length) (baseStart_4282787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282787 prefixEnd_4282787 := by exact prefixLift 4282787
  have htrace : WordTrace (prefixWord ++ tailWord_4282787) baseStart_4282787 baseEnd_4282787 := by
    simpa [prefixWord, tailWord_4282787, baseEnd_4282787] using wordTrace_append hprefix tailTrace_4282787
  have hstable : (prefixWord ++ tailWord_4282787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282787).length < 2 ^ (prefixWord ++ tailWord_4282787).sum := by decide
  have hdescent : baseEnd_4282787 < baseStart_4282787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282834 : List Nat := [3, 2, 2, 4, 2, 10]
def baseStart_4282834 : Nat := 118140960795 + 4282834 * 2 ^ 59
def prefixEnd_4282834 : Nat := 4983230072969 + 3 ^ 40 * 4282834 * 2
def baseEnd_4282834 : Nat := 9050009898840335909377

theorem tailTrace_4282834 : CollatzResearch.WordTrace tailWord_4282834 prefixEnd_4282834 9050009898840335909377 := by
  unfold tailWord_4282834
  simp only [CollatzResearch.WordTrace]
  refine ⟨39051947241507835664653889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104138525977354228439077037 39051947241507835664653889)
  ·
    refine ⟨29288960431130876748490417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39051947241507835664653889 29288960431130876748490417)
    ·
      refine ⟨21966720323348157561367813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29288960431130876748490417 21966720323348157561367813)
      ·
        refine ⟨4118760060627779542756465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21966720323348157561367813 4118760060627779542756465)
        ·
          refine ⟨3089070045470834657067349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118760060627779542756465 3089070045470834657067349)
          ·
            refine ⟨9050009898840335909377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3089070045470834657067349 9050009898840335909377)
            ·
              rfl

theorem cell23_4282834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 10].length) (baseStart_4282834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282834 prefixEnd_4282834 := by exact prefixLift 4282834
  have htrace : WordTrace (prefixWord ++ tailWord_4282834) baseStart_4282834 baseEnd_4282834 := by
    simpa [prefixWord, tailWord_4282834, baseEnd_4282834] using wordTrace_append hprefix tailTrace_4282834
  have hstable : (prefixWord ++ tailWord_4282834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282834).length < 2 ^ (prefixWord ++ tailWord_4282834).sum := by decide
  have hdescent : baseEnd_4282834 < baseStart_4282834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282861 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4282861 : Nat := 118140960795 + 4282861 * 2 ^ 59
def prefixEnd_4282861 : Nat := 4983230072969 + 3 ^ 40 * 4282861 * 2
def baseEnd_4282861 : Nat := 2199166269395873020340987

theorem tailTrace_4282861 : CollatzResearch.WordTrace tailWord_4282861 prefixEnd_4282861 2199166269395873020340987 := by
  unfold tailWord_4282861
  simp only [CollatzResearch.WordTrace]
  refine ⟨156208773736933526269848437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104139182491289017513232291 156208773736933526269848437)
  ·
    refine ⟨14644572537837518087798291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156208773736933526269848437 14644572537837518087798291)
    ·
      refine ⟨21966858806756277131697437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14644572537837518087798291 21966858806756277131697437)
      ·
        refine ⟨8237572052533603924386539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21966858806756277131697437 8237572052533603924386539)
        ·
          refine ⟨12356358078800405886579809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237572052533603924386539 12356358078800405886579809)
          ·
            refine ⟨9267268559100304414934857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12356358078800405886579809 9267268559100304414934857)
            ·
              refine ⟨6950451419325228311201143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9267268559100304414934857 6950451419325228311201143)
              ·
                refine ⟨10425677128987842466801715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6950451419325228311201143 10425677128987842466801715)
                ·
                  refine ⟨15638515693481763700202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10425677128987842466801715 15638515693481763700202573)
                  ·
                    refine ⟨5864443385055661387575965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15638515693481763700202573 5864443385055661387575965)
                    ·
                      refine ⟨2199166269395873020340987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5864443385055661387575965 2199166269395873020340987)
                      ·
                        rfl

theorem cell23_4282861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4282861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282861 prefixEnd_4282861 := by exact prefixLift 4282861
  have htrace : WordTrace (prefixWord ++ tailWord_4282861) baseStart_4282861 baseEnd_4282861 := by
    simpa [prefixWord, tailWord_4282861, baseEnd_4282861] using wordTrace_append hprefix tailTrace_4282861
  have hstable : (prefixWord ++ tailWord_4282861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282861).length < 2 ^ (prefixWord ++ tailWord_4282861).sum := by decide
  have hdescent : baseEnd_4282861 < baseStart_4282861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282882 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4282882 : Nat := 118140960795 + 4282882 * 2 ^ 59
def prefixEnd_4282882 : Nat := 4983230072969 + 3 ^ 40 * 4282882 * 2
def baseEnd_4282882 : Nat := 2199177052489617438178391

theorem tailTrace_4282882 : CollatzResearch.WordTrace tailWord_4282882 prefixEnd_4282882 2199177052489617438178391 := by
  unfold tailWord_4282882
  simp only [CollatzResearch.WordTrace]
  refine ⟨39052384917464361714090725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104139693113238297904241933 39052384917464361714090725)
  ·
    refine ⟨7322322172024567821392011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39052384917464361714090725 7322322172024567821392011)
    ·
      refine ⟨10983483258036851732088017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7322322172024567821392011 10983483258036851732088017)
      ·
        refine ⟨8237612443527638799066013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10983483258036851732088017 8237612443527638799066013)
        ·
          refine ⟨3089104666322864549649755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8237612443527638799066013 3089104666322864549649755)
          ·
            refine ⟨4633656999484296824474633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089104666322864549649755 4633656999484296824474633)
            ·
              refine ⟨3475242749613222618355975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633656999484296824474633 3475242749613222618355975)
              ·
                refine ⟨5212864124419833927533963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475242749613222618355975 5212864124419833927533963)
                ·
                  refine ⟨7819296186629750891300945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212864124419833927533963 7819296186629750891300945)
                  ·
                    refine ⟨5864472139972313168475709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7819296186629750891300945 5864472139972313168475709)
                    ·
                      refine ⟨2199177052489617438178391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5864472139972313168475709 2199177052489617438178391)
                      ·
                        rfl

theorem cell23_4282882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4282882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282882 prefixEnd_4282882 := by exact prefixLift 4282882
  have htrace : WordTrace (prefixWord ++ tailWord_4282882) baseStart_4282882 baseEnd_4282882 := by
    simpa [prefixWord, tailWord_4282882, baseEnd_4282882] using wordTrace_append hprefix tailTrace_4282882
  have hstable : (prefixWord ++ tailWord_4282882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282882).length < 2 ^ (prefixWord ++ tailWord_4282882).sum := by decide
  have hdescent : baseEnd_4282882 < baseStart_4282882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282901 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_4282901 : Nat := 118140960795 + 4282901 * 2 ^ 59
def prefixEnd_4282901 : Nat := 4983230072969 + 3 ^ 40 * 4282901 * 2
def baseEnd_4282901 : Nat := 2199186808622052863840803

theorem tailTrace_4282901 : CollatzResearch.WordTrace tailWord_4282901 prefixEnd_4282901 2199186808622052863840803 := by
  unfold tailWord_4282901
  simp only [CollatzResearch.WordTrace]
  refine ⟨156210232656788613101304557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104140155104525742067536371 156210232656788613101304557)
  ·
    refine ⟨58578837246295729912989209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156210232656788613101304557 58578837246295729912989209)
    ·
      refine ⟨43934127934721797434741907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58578837246295729912989209 43934127934721797434741907)
      ·
        refine ⟨65901191902082696152112861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43934127934721797434741907 65901191902082696152112861)
        ·
          refine ⟨24712946963281011057042323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65901191902082696152112861 24712946963281011057042323)
          ·
            refine ⟨37069420444921516585563485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24712946963281011057042323 37069420444921516585563485)
            ·
              refine ⟨13901032666845568719586307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37069420444921516585563485 13901032666845568719586307)
              ·
                refine ⟨20851549000268353079379461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13901032666845568719586307 20851549000268353079379461)
                ·
                  refine ⟨3909665437550316202383649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20851549000268353079379461 3909665437550316202383649)
                  ·
                    refine ⟨2932249078162737151787737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909665437550316202383649 2932249078162737151787737)
                    ·
                      refine ⟨2199186808622052863840803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932249078162737151787737 2199186808622052863840803)
                      ·
                        rfl

theorem cell23_4282901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_4282901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282901 prefixEnd_4282901 := by exact prefixLift 4282901
  have htrace : WordTrace (prefixWord ++ tailWord_4282901) baseStart_4282901 baseEnd_4282901 := by
    simpa [prefixWord, tailWord_4282901, baseEnd_4282901] using wordTrace_append hprefix tailTrace_4282901
  have hstable : (prefixWord ++ tailWord_4282901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282901).length < 2 ^ (prefixWord ++ tailWord_4282901).sum := by decide
  have hdescent : baseEnd_4282901 < baseStart_4282901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282937 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_4282937 : Nat := 118140960795 + 4282937 * 2 ^ 59
def prefixEnd_4282937 : Nat := 4983230072969 + 3 ^ 40 * 4282937 * 2
def baseEnd_4282937 : Nat := 733068431308538240996879

theorem tailTrace_4282937 : CollatzResearch.WordTrace tailWord_4282937 prefixEnd_4282937 733068431308538240996879 := by
  unfold tailWord_4282937
  simp only [CollatzResearch.WordTrace]
  refine ⟨156211545684658191249615065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104141030456438794166410043 156211545684658191249615065)
  ·
    refine ⟨117158659263493643437211299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156211545684658191249615065 117158659263493643437211299)
    ·
      refine ⟨175737988895240465155816949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117158659263493643437211299 175737988895240465155816949)
      ·
        refine ⟨16475436458928793608357839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175737988895240465155816949 16475436458928793608357839)
        ·
          refine ⟨24713154688393190412536759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16475436458928793608357839 24713154688393190412536759)
          ·
            refine ⟨37069732032589785618805139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24713154688393190412536759 37069732032589785618805139)
            ·
              refine ⟨55604598048884678428207709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37069732032589785618805139 55604598048884678428207709)
              ·
                refine ⟨20851724268331754410577891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55604598048884678428207709 20851724268331754410577891)
                ·
                  refine ⟨31277586402497631615866837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20851724268331754410577891 31277586402497631615866837)
                  ·
                    refine ⟨733068431308538240996879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31277586402497631615866837 733068431308538240996879)
                    ·
                      rfl

theorem cell23_4282937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_4282937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282937 prefixEnd_4282937 := by exact prefixLift 4282937
  have htrace : WordTrace (prefixWord ++ tailWord_4282937) baseStart_4282937 baseEnd_4282937 := by
    simpa [prefixWord, tailWord_4282937, baseEnd_4282937] using wordTrace_append hprefix tailTrace_4282937
  have hstable : (prefixWord ++ tailWord_4282937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282937).length < 2 ^ (prefixWord ++ tailWord_4282937).sum := by decide
  have hdescent : baseEnd_4282937 < baseStart_4282937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282941 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 5]
def baseStart_4282941 : Nat := 118140960795 + 4282941 * 2 ^ 59
def prefixEnd_4282941 : Nat := 4983230072969 + 3 ^ 40 * 4282941 * 2
def baseEnd_4282941 : Nat := 244356371983136967482291

theorem tailTrace_4282941 : CollatzResearch.WordTrace tailWord_4282941 prefixEnd_4282941 244356371983136967482291 := by
  unfold tailWord_4282941
  simp only [CollatzResearch.WordTrace]
  refine ⟨156211691576643699932760677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104141127717762466621840451 156211691576643699932760677)
  ·
    refine ⟨29289692170620693737392627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156211691576643699932760677 29289692170620693737392627)
    ·
      refine ⟨43934538255931040606088941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29289692170620693737392627 43934538255931040606088941)
      ·
        refine ⟨16475451845974140227283353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43934538255931040606088941 16475451845974140227283353)
        ·
          refine ⟨12356588884480605170462515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16475451845974140227283353 12356588884480605170462515)
          ·
            refine ⟨18534883326720907755693773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12356588884480605170462515 18534883326720907755693773)
            ·
              refine ⟨6950581247520340408385165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18534883326720907755693773 6950581247520340408385165)
              ·
                refine ⟨2606467967820127653144437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6950581247520340408385165 2606467967820127653144437)
                ·
                  refine ⟨244356371983136967482291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606467967820127653144437 244356371983136967482291)
                  ·
                    rfl

theorem cell23_4282941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_4282941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282941 prefixEnd_4282941 := by exact prefixLift 4282941
  have htrace : WordTrace (prefixWord ++ tailWord_4282941) baseStart_4282941 baseEnd_4282941 := by
    simpa [prefixWord, tailWord_4282941, baseEnd_4282941] using wordTrace_append hprefix tailTrace_4282941
  have hstable : (prefixWord ++ tailWord_4282941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282941).length < 2 ^ (prefixWord ++ tailWord_4282941).sum := by decide
  have hdescent : baseEnd_4282941 < baseStart_4282941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282954 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_4282954 : Nat := 118140960795 + 4282954 * 2 ^ 59
def prefixEnd_4282954 : Nat := 4983230072969 + 3 ^ 40 * 4282954 * 2
def baseEnd_4282954 : Nat := 733071341032247052159353

theorem tailTrace_4282954 : CollatzResearch.WordTrace tailWord_4282954 prefixEnd_4282954 733071341032247052159353 := by
  unfold tailWord_4282954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39053041431399150788245979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104141443817064402101989277 39053041431399150788245979)
  ·
    refine ⟨58579562147098726182368969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39053041431399150788245979 58579562147098726182368969)
    ·
      refine ⟨43934671610324044636776727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58579562147098726182368969 43934671610324044636776727)
      ·
        refine ⟨65902007415486066955165091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43934671610324044636776727 65902007415486066955165091)
        ·
          refine ⟨98853011123229100432747637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65902007415486066955165091 98853011123229100432747637)
          ·
            refine ⟨9267469792802728165570091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98853011123229100432747637 9267469792802728165570091)
            ·
              refine ⟨13901204689204092248355137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267469792802728165570091 13901204689204092248355137)
              ·
                refine ⟨10425903516903069186266353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13901204689204092248355137 10425903516903069186266353)
                ·
                  refine ⟨7819427637677301889699765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10425903516903069186266353 7819427637677301889699765)
                  ·
                    refine ⟨733071341032247052159353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7819427637677301889699765 733071341032247052159353)
                    ·
                      rfl

theorem cell23_4282954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_4282954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282954 prefixEnd_4282954 := by exact prefixLift 4282954
  have htrace : WordTrace (prefixWord ++ tailWord_4282954) baseStart_4282954 baseEnd_4282954 := by
    simpa [prefixWord, tailWord_4282954, baseEnd_4282954] using wordTrace_append hprefix tailTrace_4282954
  have hstable : (prefixWord ++ tailWord_4282954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282954).length < 2 ^ (prefixWord ++ tailWord_4282954).sum := by decide
  have hdescent : baseEnd_4282954 < baseStart_4282954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4282964 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4282964 : Nat := 118140960795 + 4282964 * 2 ^ 59
def prefixEnd_4282964 : Nat := 4983230072969 + 3 ^ 40 * 4282964 * 2
def baseEnd_4282964 : Nat := 2199219157903286117353013

theorem tailTrace_4282964 : CollatzResearch.WordTrace tailWord_4282964 prefixEnd_4282964 2199219157903286117353013 := by
  unfold tailWord_4282964
  simp only [CollatzResearch.WordTrace]
  refine ⟨78106265227780187430423973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104141686970373583240565297 78106265227780187430423973)
  ·
    refine ⟨14644924730208785143204495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78106265227780187430423973 14644924730208785143204495)
    ·
      refine ⟨21967387095313177714806743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14644924730208785143204495 21967387095313177714806743)
      ·
        refine ⟨32951080642969766572210115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21967387095313177714806743 32951080642969766572210115)
        ·
          refine ⟨49426620964454649858315173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32951080642969766572210115 49426620964454649858315173)
          ·
            refine ⟨9267491430835246848434095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49426620964454649858315173 9267491430835246848434095)
            ·
              refine ⟨13901237146252870272651143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267491430835246848434095 13901237146252870272651143)
              ·
                refine ⟨20851855719379305408976715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13901237146252870272651143 20851855719379305408976715)
                ·
                  refine ⟨31277783579068958113465073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20851855719379305408976715 31277783579068958113465073)
                  ·
                    refine ⟨23458337684301718585098805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31277783579068958113465073 23458337684301718585098805)
                    ·
                      refine ⟨2199219157903286117353013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23458337684301718585098805 2199219157903286117353013)
                      ·
                        rfl

theorem cell23_4282964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4282964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4282964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4282964 prefixEnd_4282964 := by exact prefixLift 4282964
  have htrace : WordTrace (prefixWord ++ tailWord_4282964) baseStart_4282964 baseEnd_4282964 := by
    simpa [prefixWord, tailWord_4282964, baseEnd_4282964] using wordTrace_append hprefix tailTrace_4282964
  have hstable : (prefixWord ++ tailWord_4282964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4282964).length < 2 ^ (prefixWord ++ tailWord_4282964).sum := by decide
  have hdescent : baseEnd_4282964 < baseStart_4282964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4282964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283017 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_4283017 : Nat := 118140960795 + 4283017 * 2 ^ 59
def prefixEnd_4283017 : Nat := 4983230072969 + 3 ^ 40 * 4283017 * 2
def baseEnd_4283017 : Nat := 2199246372377974409990269

theorem tailTrace_4283017 : CollatzResearch.WordTrace tailWord_4283017 prefixEnd_4283017 2199246372377974409990269 := by
  unfold tailWord_4283017
  simp only [CollatzResearch.WordTrace]
  refine ⟨156214463524368364912527305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104142975682912243275018203 156214463524368364912527305)
  ·
    refine ⟨117160847643276273684395479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156214463524368364912527305 117160847643276273684395479)
    ·
      refine ⟨175741271464914410526593219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117160847643276273684395479 175741271464914410526593219)
      ·
        refine ⟨263611907197371615789889829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175741271464914410526593219 263611907197371615789889829)
        ·
          refine ⟨49427232599507177960604343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263611907197371615789889829 49427232599507177960604343)
          ·
            refine ⟨74140848899260766940906515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49427232599507177960604343 74140848899260766940906515)
            ·
              refine ⟨111211273348891150411359773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74140848899260766940906515 111211273348891150411359773)
              ·
                refine ⟨41704227505834181404259915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111211273348891150411359773 41704227505834181404259915)
                ·
                  refine ⟨62556341258751272106389873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41704227505834181404259915 62556341258751272106389873)
                  ·
                    refine ⟨46917255944063454079792405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62556341258751272106389873 46917255944063454079792405)
                    ·
                      refine ⟨2199246372377974409990269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46917255944063454079792405 2199246372377974409990269)
                      ·
                        rfl

theorem cell23_4283017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_4283017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283017 prefixEnd_4283017 := by exact prefixLift 4283017
  have htrace : WordTrace (prefixWord ++ tailWord_4283017) baseStart_4283017 baseEnd_4283017 := by
    simpa [prefixWord, tailWord_4283017, baseEnd_4283017] using wordTrace_append hprefix tailTrace_4283017
  have hstable : (prefixWord ++ tailWord_4283017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283017).length < 2 ^ (prefixWord ++ tailWord_4283017).sum := by decide
  have hdescent : baseEnd_4283017 < baseStart_4283017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283044 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_4283044 : Nat := 118140960795 + 4283044 * 2 ^ 59
def prefixEnd_4283044 : Nat := 4983230072969 + 3 ^ 40 * 4283044 * 2
def baseEnd_4283044 : Nat := 733086745451881934784215

theorem tailTrace_4283044 : CollatzResearch.WordTrace tailWord_4283044 prefixEnd_4283044 733086745451881934784215 := by
  unfold tailWord_4283044
  simp only [CollatzResearch.WordTrace]
  refine ⟨78107724147635274261880093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104143632196847032349173457 78107724147635274261880093)
  ·
    refine ⟨29290396555363227848205035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78107724147635274261880093 29290396555363227848205035)
    ·
      refine ⟨43935594833044841772307553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29290396555363227848205035 43935594833044841772307553)
      ·
        refine ⟨32951696124783631329230665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43935594833044841772307553 32951696124783631329230665)
        ·
          refine ⟨24713772093587723496922999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32951696124783631329230665 24713772093587723496922999)
          ·
            refine ⟨37070658140381585245384499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24713772093587723496922999 37070658140381585245384499)
            ·
              refine ⟨55605987210572377868076749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37070658140381585245384499 55605987210572377868076749)
              ·
                refine ⟨20852245203964641700528781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55605987210572377868076749 20852245203964641700528781)
                ·
                  refine ⟨7819591951486740637698293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20852245203964641700528781 7819591951486740637698293)
                  ·
                    refine ⟨733086745451881934784215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7819591951486740637698293 733086745451881934784215)
                    ·
                      rfl

theorem cell23_4283044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_4283044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283044 prefixEnd_4283044 := by exact prefixLift 4283044
  have htrace : WordTrace (prefixWord ++ tailWord_4283044) baseStart_4283044 baseEnd_4283044 := by
    simpa [prefixWord, tailWord_4283044, baseEnd_4283044] using wordTrace_append hprefix tailTrace_4283044
  have hstable : (prefixWord ++ tailWord_4283044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283044).length < 2 ^ (prefixWord ++ tailWord_4283044).sum := by decide
  have hdescent : baseEnd_4283044 < baseStart_4283044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283098 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_4283098 : Nat := 118140960795 + 4283098 * 2 ^ 59
def prefixEnd_4283098 : Nat := 4983230072969 + 3 ^ 40 * 4283098 * 2
def baseEnd_4283098 : Nat := 2199287964310988593077397

theorem tailTrace_4283098 : CollatzResearch.WordTrace tailWord_4283098 prefixEnd_4283098 2199287964310988593077397 := by
  unfold tailWord_4283098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39054354459268728936556487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104144945224716610497483965 39054354459268728936556487)
  ·
    refine ⟨58581531688903093404834731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39054354459268728936556487 58581531688903093404834731)
    ·
      refine ⟨87872297533354640107252097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58581531688903093404834731 87872297533354640107252097)
      ·
        refine ⟨65904223150015980080439073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87872297533354640107252097 65904223150015980080439073)
        ·
          refine ⟨49428167362511985060329305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65904223150015980080439073 49428167362511985060329305)
          ·
            refine ⟨37071125521883988795246979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49428167362511985060329305 37071125521883988795246979)
            ·
              refine ⟨55606688282825983192870469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37071125521883988795246979 55606688282825983192870469)
              ·
                refine ⟨10426254053029871848663213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55606688282825983192870469 10426254053029871848663213)
                ·
                  refine ⟨3909845269886201943248705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10426254053029871848663213 3909845269886201943248705)
                  ·
                    refine ⟨2932383952414651457436529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909845269886201943248705 2932383952414651457436529)
                    ·
                      refine ⟨2199287964310988593077397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932383952414651457436529 2199287964310988593077397)
                      ·
                        rfl

theorem cell23_4283098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_4283098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283098 prefixEnd_4283098 := by exact prefixLift 4283098
  have htrace : WordTrace (prefixWord ++ tailWord_4283098) baseStart_4283098 baseEnd_4283098 := by
    simpa [prefixWord, tailWord_4283098, baseEnd_4283098] using wordTrace_append hprefix tailTrace_4283098
  have hstable : (prefixWord ++ tailWord_4283098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283098).length < 2 ^ (prefixWord ++ tailWord_4283098).sum := by decide
  have hdescent : baseEnd_4283098 < baseStart_4283098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283118 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_4283118 : Nat := 118140960795 + 4283118 * 2 ^ 59
def prefixEnd_4283118 : Nat := 4983230072969 + 3 ^ 40 * 4283118 * 2
def baseEnd_4283118 : Nat := 2199298233924078514827305

theorem tailTrace_4283118 : CollatzResearch.WordTrace tailWord_4283118 prefixEnd_4283118 2199298233924078514827305 := by
  unfold tailWord_4283118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527268412125307395244251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104145431531334972774636005 19527268412125307395244251)
  ·
    refine ⟨29290902618187961092866377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19527268412125307395244251 29290902618187961092866377)
    ·
      refine ⟨21968176963640970819649783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29290902618187961092866377 21968176963640970819649783)
      ·
        refine ⟨32952265445461456229474675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21968176963640970819649783 32952265445461456229474675)
        ·
          refine ⟨49428398168192184344212013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32952265445461456229474675 49428398168192184344212013)
          ·
            refine ⟨18535649313072069129079505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49428398168192184344212013 18535649313072069129079505)
            ·
              refine ⟨13901736984804051846809629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18535649313072069129079505 13901736984804051846809629)
              ·
                refine ⟨5213151369301519442553611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13901736984804051846809629 5213151369301519442553611)
                ·
                  refine ⟨7819727053952279163830417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5213151369301519442553611 7819727053952279163830417)
                  ·
                    refine ⟨5864795290464209372872813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7819727053952279163830417 5864795290464209372872813)
                    ·
                      refine ⟨2199298233924078514827305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5864795290464209372872813 2199298233924078514827305)
                      ·
                        rfl

theorem cell23_4283118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_4283118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283118 prefixEnd_4283118 := by exact prefixLift 4283118
  have htrace : WordTrace (prefixWord ++ tailWord_4283118) baseStart_4283118 baseEnd_4283118 := by
    simpa [prefixWord, tailWord_4283118, baseEnd_4283118] using wordTrace_append hprefix tailTrace_4283118
  have hstable : (prefixWord ++ tailWord_4283118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283118).length < 2 ^ (prefixWord ++ tailWord_4283118).sum := by decide
  have hdescent : baseEnd_4283118 < baseStart_4283118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283165 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4283165 : Nat := 118140960795 + 4283165 * 2 ^ 59
def prefixEnd_4283165 : Nat := 4983230072969 + 3 ^ 40 * 4283165 * 2
def baseEnd_4283165 : Nat := 2199322367514839830939589

theorem tailTrace_4283165 : CollatzResearch.WordTrace tailWord_4283165 prefixEnd_4283165 2199322367514839830939589 := by
  unfold tailWord_4283165
  simp only [CollatzResearch.WordTrace]
  refine ⟨156219861527832186188914949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104146574351888124125943299 156219861527832186188914949)
  ·
    refine ⟨29291224036468534910421553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156219861527832186188914949 29291224036468534910421553)
    ·
      refine ⟨21968418027351401182816165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29291224036468534910421553 21968418027351401182816165)
      ·
        refine ⟨4119078380128387721778031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21968418027351401182816165 4119078380128387721778031)
        ·
          refine ⟨6178617570192581582667047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119078380128387721778031 6178617570192581582667047)
          ·
            refine ⟨9267926355288872374000571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178617570192581582667047 9267926355288872374000571)
            ·
              refine ⟨13901889532933308561000857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267926355288872374000571 13901889532933308561000857)
              ·
                refine ⟨10426417149699981420750643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13901889532933308561000857 10426417149699981420750643)
                ·
                  refine ⟨15639625724549972131125965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10426417149699981420750643 15639625724549972131125965)
                  ·
                    refine ⟨5864859646706239549172237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15639625724549972131125965 5864859646706239549172237)
                    ·
                      refine ⟨2199322367514839830939589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5864859646706239549172237 2199322367514839830939589)
                      ·
                        rfl

theorem cell23_4283165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4283165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283165 prefixEnd_4283165 := by exact prefixLift 4283165
  have htrace : WordTrace (prefixWord ++ tailWord_4283165) baseStart_4283165 baseEnd_4283165 := by
    simpa [prefixWord, tailWord_4283165, baseEnd_4283165] using wordTrace_append hprefix tailTrace_4283165
  have hstable : (prefixWord ++ tailWord_4283165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283165).length < 2 ^ (prefixWord ++ tailWord_4283165).sum := by decide
  have hdescent : baseEnd_4283165 < baseStart_4283165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283182 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4283182 : Nat := 118140960795 + 4283182 * 2 ^ 59
def prefixEnd_4283182 : Nat := 4983230072969 + 3 ^ 40 * 4283182 * 2
def baseEnd_4283182 : Nat := 2199331096685966264427011

theorem tailTrace_4283182 : CollatzResearch.WordTrace tailWord_4283182 prefixEnd_4283182 2199331096685966264427011 := by
  unfold tailWord_4283182
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527560196096324761535475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104146987712513732061522533 19527560196096324761535475)
  ·
    refine ⟨29291340294144487142303213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19527560196096324761535475 29291340294144487142303213)
    ·
      refine ⟨10984252610304182678363705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29291340294144487142303213 10984252610304182678363705)
      ·
        refine ⟨8238189457728137008772779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10984252610304182678363705 8238189457728137008772779)
        ·
          refine ⟨12357284186592205513159169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238189457728137008772779 12357284186592205513159169)
          ·
            refine ⟨9267963139944154134869377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12357284186592205513159169 9267963139944154134869377)
            ·
              refine ⟨6950972354958115601152033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9267963139944154134869377 6950972354958115601152033)
              ·
                refine ⟨5213229266218586700864025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6950972354958115601152033 5213229266218586700864025)
                ·
                  refine ⟨3909921949663940025648019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213229266218586700864025 3909921949663940025648019)
                  ·
                    refine ⟨5864882924495910038472029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3909921949663940025648019 5864882924495910038472029)
                    ·
                      refine ⟨2199331096685966264427011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5864882924495910038472029 2199331096685966264427011)
                      ·
                        rfl

theorem cell23_4283182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4283182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283182 prefixEnd_4283182 := by exact prefixLift 4283182
  have htrace : WordTrace (prefixWord ++ tailWord_4283182) baseStart_4283182 baseEnd_4283182 := by
    simpa [prefixWord, tailWord_4283182, baseEnd_4283182] using wordTrace_append hprefix tailTrace_4283182
  have hstable : (prefixWord ++ tailWord_4283182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283182).length < 2 ^ (prefixWord ++ tailWord_4283182).sum := by decide
  have hdescent : baseEnd_4283182 < baseStart_4283182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283184 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_4283184 : Nat := 118140960795 + 4283184 * 2 ^ 59
def prefixEnd_4283184 : Nat := 4983230072969 + 3 ^ 40 * 4283184 * 2
def baseEnd_4283184 : Nat := 2199332123647275256602001

theorem tailTrace_4283184 : CollatzResearch.WordTrace tailWord_4283184 prefixEnd_4283184 2199332123647275256602001 := by
  unfold tailWord_4283184
  simp only [CollatzResearch.WordTrace]
  refine ⟨78110277257381676216928303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104147036343175568289237737 78110277257381676216928303)
  ·
    refine ⟨117165415886072514325392455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78110277257381676216928303 117165415886072514325392455)
    ·
      refine ⟨175748123829108771488088683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117165415886072514325392455 175748123829108771488088683)
      ·
        refine ⟨263622185743663157232133025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175748123829108771488088683 263622185743663157232133025)
        ·
          refine ⟨197716639307747367924099769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263622185743663157232133025 197716639307747367924099769)
          ·
            refine ⟨148287479480810525943074827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197716639307747367924099769 148287479480810525943074827)
            ·
              refine ⟨222431219221215788914612241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148287479480810525943074827 222431219221215788914612241)
              ·
                refine ⟨166823414415911841685959181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222431219221215788914612241 166823414415911841685959181)
                ·
                  refine ⟨62558780405966940632234693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166823414415911841685959181 62558780405966940632234693)
                  ·
                    refine ⟨11729771326118801368544005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62558780405966940632234693 11729771326118801368544005)
                    ·
                      refine ⟨2199332123647275256602001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11729771326118801368544005 2199332123647275256602001)
                      ·
                        rfl

theorem cell23_4283184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_4283184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283184 prefixEnd_4283184 := by exact prefixLift 4283184
  have htrace : WordTrace (prefixWord ++ tailWord_4283184) baseStart_4283184 baseEnd_4283184 := by
    simpa [prefixWord, tailWord_4283184, baseEnd_4283184] using wordTrace_append hprefix tailTrace_4283184
  have hstable : (prefixWord ++ tailWord_4283184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283184).length < 2 ^ (prefixWord ++ tailWord_4283184).sum := by decide
  have hdescent : baseEnd_4283184 < baseStart_4283184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283198 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_4283198 : Nat := 118140960795 + 4283198 * 2 ^ 59
def prefixEnd_4283198 : Nat := 4983230072969 + 3 ^ 40 * 4283198 * 2
def baseEnd_4283198 : Nat := 733113104125479400608979

theorem tailTrace_4283198 : CollatzResearch.WordTrace tailWord_4283198 prefixEnd_4283198 733113104125479400608979 := by
  unfold tailWord_4283198
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527633142089079103108281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104147376757808421883244165 19527633142089079103108281)
  ·
    refine ⟨14645724856566809327331211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19527633142089079103108281 14645724856566809327331211)
    ·
      refine ⟨21968587284850213990996817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14645724856566809327331211 21968587284850213990996817)
      ·
        refine ⟨16476440463637660493247613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21968587284850213990996817 16476440463637660493247613)
        ·
          refine ⟨6178665173864122684967855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16476440463637660493247613 6178665173864122684967855)
          ·
            refine ⟨9267997760796184027451783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178665173864122684967855 9267997760796184027451783)
            ·
              refine ⟨13901996641194276041177675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267997760796184027451783 13901996641194276041177675)
              ·
                refine ⟨20852994961791414061766513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13901996641194276041177675 20852994961791414061766513)
                ·
                  refine ⟨15639746221343560546324885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20852994961791414061766513 15639746221343560546324885)
                  ·
                    refine ⟨733113104125479400608979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15639746221343560546324885 733113104125479400608979)
                    ·
                      rfl

theorem cell23_4283198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_4283198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283198 prefixEnd_4283198 := by exact prefixLift 4283198
  have htrace : WordTrace (prefixWord ++ tailWord_4283198) baseStart_4283198 baseEnd_4283198 := by
    simpa [prefixWord, tailWord_4283198, baseEnd_4283198] using wordTrace_append hprefix tailTrace_4283198
  have hstable : (prefixWord ++ tailWord_4283198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283198).length < 2 ^ (prefixWord ++ tailWord_4283198).sum := by decide
  have hdescent : baseEnd_4283198 < baseStart_4283198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283221 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4283221 : Nat := 118140960795 + 4283221 * 2 ^ 59
def prefixEnd_4283221 : Nat := 4983230072969 + 3 ^ 40 * 4283221 * 2
def baseEnd_4283221 : Nat := 2199351122431491611839331

theorem tailTrace_4283221 : CollatzResearch.WordTrace tailWord_4283221 prefixEnd_4283221 2199351122431491611839331 := by
  unfold tailWord_4283221
  simp only [CollatzResearch.WordTrace]
  refine ⟨156221904015629307752953517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104147936010419538501969011 156221904015629307752953517)
  ·
    refine ⟨58583214005860990407357569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156221904015629307752953517 58583214005860990407357569)
    ·
      refine ⟨43937410504395742805518177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58583214005860990407357569 43937410504395742805518177)
      ·
        refine ⟨32953057878296807104138633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43937410504395742805518177 32953057878296807104138633)
        ·
          refine ⟨24714793408722605328103975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32953057878296807104138633 24714793408722605328103975)
          ·
            refine ⟨37072190113083907992155963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24714793408722605328103975 37072190113083907992155963)
            ·
              refine ⟨55608285169625861988233945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37072190113083907992155963 55608285169625861988233945)
              ·
                refine ⟨41706213877219396491175459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55608285169625861988233945 41706213877219396491175459)
                ·
                  refine ⟨62559320815829094736763189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41706213877219396491175459 62559320815829094736763189)
                  ·
                    refine ⟨5864936326483977631571549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62559320815829094736763189 5864936326483977631571549)
                    ·
                      refine ⟨2199351122431491611839331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5864936326483977631571549 2199351122431491611839331)
                      ·
                        rfl

theorem cell23_4283221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4283221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283221 prefixEnd_4283221 := by exact prefixLift 4283221
  have htrace : WordTrace (prefixWord ++ tailWord_4283221) baseStart_4283221 baseEnd_4283221 := by
    simpa [prefixWord, tailWord_4283221, baseEnd_4283221] using wordTrace_append hprefix tailTrace_4283221
  have hstable : (prefixWord ++ tailWord_4283221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283221).length < 2 ^ (prefixWord ++ tailWord_4283221).sum := by decide
  have hdescent : baseEnd_4283221 < baseStart_4283221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283261 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_4283261 : Nat := 118140960795 + 4283261 * 2 ^ 59
def prefixEnd_4283261 : Nat := 4983230072969 + 3 ^ 40 * 4283261 * 2
def baseEnd_4283261 : Nat := 2199371661657671455339147

theorem tailTrace_4283261 : CollatzResearch.WordTrace tailWord_4283261 prefixEnd_4283261 2199371661657671455339147 := by
  unfold tailWord_4283261
  simp only [CollatzResearch.WordTrace]
  refine ⟨156223362935484394584409637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104148908623656263056273091 156223362935484394584409637)
  ·
    refine ⟨29291880550403323984576807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156223362935484394584409637 29291880550403323984576807)
    ·
      refine ⟨43937820825604985976865211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29291880550403323984576807 43937820825604985976865211)
      ·
        refine ⟨65906731238407478965297817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43937820825604985976865211 65906731238407478965297817)
        ·
          refine ⟨49430048428805609223973363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65906731238407478965297817 49430048428805609223973363)
          ·
            refine ⟨74145072643208413835960045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49430048428805609223973363 74145072643208413835960045)
            ·
              refine ⟨27804402241203155188485017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74145072643208413835960045 27804402241203155188485017)
              ·
                refine ⟨20853301680902366391363763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27804402241203155188485017 20853301680902366391363763)
                ·
                  refine ⟨31279952521353549587045645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20853301680902366391363763 31279952521353549587045645)
                  ·
                    refine ⟨11729982195507581095142117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31279952521353549587045645 11729982195507581095142117)
                    ·
                      refine ⟨2199371661657671455339147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11729982195507581095142117 2199371661657671455339147)
                      ·
                        rfl

theorem cell23_4283261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_4283261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283261 prefixEnd_4283261 := by exact prefixLift 4283261
  have htrace : WordTrace (prefixWord ++ tailWord_4283261) baseStart_4283261 baseEnd_4283261 := by
    simpa [prefixWord, tailWord_4283261, baseEnd_4283261] using wordTrace_append hprefix tailTrace_4283261
  have hstable : (prefixWord ++ tailWord_4283261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283261).length < 2 ^ (prefixWord ++ tailWord_4283261).sum := by decide
  have hdescent : baseEnd_4283261 < baseStart_4283261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283311 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_4283311 : Nat := 118140960795 + 4283311 * 2 ^ 59
def prefixEnd_4283311 : Nat := 4983230072969 + 3 ^ 40 * 4283311 * 2
def baseEnd_4283311 : Nat := 2199397335690396259713917

theorem tailTrace_4283311 : CollatzResearch.WordTrace tailWord_4283311 prefixEnd_4283311 2199397335690396259713917 := by
  unfold tailWord_4283311
  simp only [CollatzResearch.WordTrace]
  refine ⟨156225186585303253123729787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104150124390202168749153191 156225186585303253123729787)
  ·
    refine ⟨234337779877954879685594681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156225186585303253123729787 234337779877954879685594681)
    ·
      refine ⟨175753334908466159764196011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234337779877954879685594681 175753334908466159764196011)
      ·
        refine ⟨263630002362699239646294017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175753334908466159764196011 263630002362699239646294017)
        ·
          refine ⟨197722501772024429734720513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263630002362699239646294017 197722501772024429734720513)
          ·
            refine ⟨148291876329018322301040385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197722501772024429734720513 148291876329018322301040385)
            ·
              refine ⟨111218907246763741725780289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148291876329018322301040385 111218907246763741725780289)
              ·
                refine ⟨83414180435072806294335217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111218907246763741725780289 83414180435072806294335217)
                ·
                  refine ⟨62560635326304604720751413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83414180435072806294335217 62560635326304604720751413)
                  ·
                    refine ⟨5865059561841056692570445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62560635326304604720751413 5865059561841056692570445)
                    ·
                      refine ⟨2199397335690396259713917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5865059561841056692570445 2199397335690396259713917)
                      ·
                        rfl

theorem cell23_4283311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_4283311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283311 prefixEnd_4283311 := by exact prefixLift 4283311
  have htrace : WordTrace (prefixWord ++ tailWord_4283311) baseStart_4283311 baseEnd_4283311 := by
    simpa [prefixWord, tailWord_4283311, baseEnd_4283311] using wordTrace_append hprefix tailTrace_4283311
  have hstable : (prefixWord ++ tailWord_4283311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283311).length < 2 ^ (prefixWord ++ tailWord_4283311).sum := by decide
  have hdescent : baseEnd_4283311 < baseStart_4283311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283331 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 3, 5]
def baseStart_4283331 : Nat := 118140960795 + 4283331 * 2 ^ 59
def prefixEnd_4283331 : Nat := 4983230072969 + 3 ^ 40 * 4283331 * 2
def baseEnd_4283331 : Nat := 733135868434495393821275

theorem tailTrace_4283331 : CollatzResearch.WordTrace tailWord_4283331 prefixEnd_4283331 733135868434495393821275 := by
  unfold tailWord_4283331
  simp only [CollatzResearch.WordTrace]
  refine ⟨156225916045230796539457847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104150610696820531026305231 156225916045230796539457847)
  ·
    refine ⟨234338874067846194809186771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156225916045230796539457847 234338874067846194809186771)
    ·
      refine ⟨351508311101769292213780157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234338874067846194809186771 351508311101769292213780157)
      ·
        refine ⟨131815616663163484580167559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351508311101769292213780157 131815616663163484580167559)
        ·
          refine ⟨197723424994745226870251339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131815616663163484580167559 197723424994745226870251339)
          ·
            refine ⟨296585137492117840305377009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197723424994745226870251339 296585137492117840305377009)
            ·
              refine ⟨222438853119088380229032757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296585137492117840305377009 222438853119088380229032757)
              ·
                refine ⟨20853642479914535646471821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222438853119088380229032757 20853642479914535646471821)
                ·
                  refine ⟨7820115929967950867426933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20853642479914535646471821 7820115929967950867426933)
                  ·
                    refine ⟨733135868434495393821275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7820115929967950867426933 733135868434495393821275)
                    ·
                      rfl

theorem cell23_4283331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 5].length) (baseStart_4283331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283331 prefixEnd_4283331 := by exact prefixLift 4283331
  have htrace : WordTrace (prefixWord ++ tailWord_4283331) baseStart_4283331 baseEnd_4283331 := by
    simpa [prefixWord, tailWord_4283331, baseEnd_4283331] using wordTrace_append hprefix tailTrace_4283331
  have hstable : (prefixWord ++ tailWord_4283331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283331).length < 2 ^ (prefixWord ++ tailWord_4283331).sum := by decide
  have hdescent : baseEnd_4283331 < baseStart_4283331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283361 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_4283361 : Nat := 118140960795 + 4283361 * 2 ^ 59
def prefixEnd_4283361 : Nat := 4983230072969 + 3 ^ 40 * 4283361 * 2
def baseEnd_4283361 : Nat := 733141003241040354696229

theorem tailTrace_4283361 : CollatzResearch.WordTrace tailWord_4283361 prefixEnd_4283361 733141003241040354696229 := by
  unfold tailWord_4283361
  simp only [CollatzResearch.WordTrace]
  refine ⟨156227010235122111663049937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104151340156748074442033291 156227010235122111663049937)
  ·
    refine ⟨117170257676341583747287453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156227010235122111663049937 117170257676341583747287453)
    ·
      refine ⟨43938846628628093905232795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117170257676341583747287453 43938846628628093905232795)
      ·
        refine ⟨65908269942942140857849193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43938846628628093905232795 65908269942942140857849193)
        ·
          refine ⟨49431202457206605643386895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65908269942942140857849193 49431202457206605643386895)
          ·
            refine ⟨74146803685809908465080343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49431202457206605643386895 74146803685809908465080343)
            ·
              refine ⟨111220205528714862697620515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74146803685809908465080343 111220205528714862697620515)
              ·
                refine ⟨166830308293072294046430773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111220205528714862697620515 166830308293072294046430773)
                ·
                  refine ⟨15640341402475527566852885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166830308293072294046430773 15640341402475527566852885)
                  ·
                    refine ⟨733141003241040354696229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15640341402475527566852885 733141003241040354696229)
                    ·
                      rfl

theorem cell23_4283361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_4283361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283361 prefixEnd_4283361 := by exact prefixLift 4283361
  have htrace : WordTrace (prefixWord ++ tailWord_4283361) baseStart_4283361 baseEnd_4283361 := by
    simpa [prefixWord, tailWord_4283361, baseEnd_4283361] using wordTrace_append hprefix tailTrace_4283361
  have hstable : (prefixWord ++ tailWord_4283361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283361).length < 2 ^ (prefixWord ++ tailWord_4283361).sum := by decide
  have hdescent : baseEnd_4283361 < baseStart_4283361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283368 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4283368 : Nat := 118140960795 + 4283368 * 2 ^ 59
def prefixEnd_4283368 : Nat := 4983230072969 + 3 ^ 40 * 4283368 * 2
def baseEnd_4283368 : Nat := 2199426604087702536701155

theorem tailTrace_4283368 : CollatzResearch.WordTrace tailWord_4283368 prefixEnd_4283368 2199426604087702536701155 := by
  unfold tailWord_4283368
  simp only [CollatzResearch.WordTrace]
  refine ⟨78113632773048375929277379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104151510364064501239036505 78113632773048375929277379)
  ·
    refine ⟨117170449159572563893916069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78113632773048375929277379 117170449159572563893916069)
    ·
      refine ⟨21969459217419855730109263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117170449159572563893916069 21969459217419855730109263)
      ·
        refine ⟨32954188826129783595163895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21969459217419855730109263 32954188826129783595163895)
        ·
          refine ⟨49431283239194675392745843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32954188826129783595163895 49431283239194675392745843)
          ·
            refine ⟨74146924858792013089118765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49431283239194675392745843 74146924858792013089118765)
            ·
              refine ⟨27805096822047004908419537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74146924858792013089118765 27805096822047004908419537)
              ·
                refine ⟨20853822616535253681314653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27805096822047004908419537 20853822616535253681314653)
                ·
                  refine ⟨7820183481200720130492995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20853822616535253681314653 7820183481200720130492995)
                  ·
                    refine ⟨11730275221801080195739493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7820183481200720130492995 11730275221801080195739493)
                    ·
                      refine ⟨2199426604087702536701155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11730275221801080195739493 2199426604087702536701155)
                      ·
                        rfl

theorem cell23_4283368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4283368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283368 prefixEnd_4283368 := by exact prefixLift 4283368
  have htrace : WordTrace (prefixWord ++ tailWord_4283368) baseStart_4283368 baseEnd_4283368 := by
    simpa [prefixWord, tailWord_4283368, baseEnd_4283368] using wordTrace_append hprefix tailTrace_4283368
  have hstable : (prefixWord ++ tailWord_4283368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283368).length < 2 ^ (prefixWord ++ tailWord_4283368).sum := by decide
  have hdescent : baseEnd_4283368 < baseStart_4283368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283402 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_4283402 : Nat := 118140960795 + 4283402 * 2 ^ 59
def prefixEnd_4283402 : Nat := 4983230072969 + 3 ^ 40 * 4283402 * 2
def baseEnd_4283402 : Nat := 2199444062429955403675999

theorem tailTrace_4283402 : CollatzResearch.WordTrace tailWord_4283402 prefixEnd_4283402 2199444062429955403675999 := by
  unfold tailWord_4283402
  simp only [CollatzResearch.WordTrace]
  refine ⟨39057126406993393916323115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104152337085315717110194973 39057126406993393916323115)
  ·
    refine ⟨58585689610490090874484673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39057126406993393916323115 58585689610490090874484673)
    ·
      refine ⟨43939267207867568155863505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58585689610490090874484673 43939267207867568155863505)
      ·
        refine ⟨32954450405900676116897629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43939267207867568155863505 32954450405900676116897629)
        ·
          refine ⟨12357918902212753543836611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32954450405900676116897629 12357918902212753543836611)
          ·
            refine ⟨18536878353319130315754917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12357918902212753543836611 18536878353319130315754917)
            ·
              refine ⟨3475664691247336934204047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18536878353319130315754917 3475664691247336934204047)
              ·
                refine ⟨5213497036871005401306071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475664691247336934204047 5213497036871005401306071)
                ·
                  refine ⟨7820245555306508101959107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5213497036871005401306071 7820245555306508101959107)
                  ·
                    refine ⟨11730368332959762152938661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7820245555306508101959107 11730368332959762152938661)
                    ·
                      refine ⟨2199444062429955403675999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11730368332959762152938661 2199444062429955403675999)
                      ·
                        rfl

theorem cell23_4283402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_4283402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283402 prefixEnd_4283402 := by exact prefixLift 4283402
  have htrace : WordTrace (prefixWord ++ tailWord_4283402) baseStart_4283402 baseEnd_4283402 := by
    simpa [prefixWord, tailWord_4283402, baseEnd_4283402] using wordTrace_append hprefix tailTrace_4283402
  have hstable : (prefixWord ++ tailWord_4283402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283402).length < 2 ^ (prefixWord ++ tailWord_4283402).sum := by decide
  have hdescent : baseEnd_4283402 < baseStart_4283402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283411 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_4283411 : Nat := 118140960795 + 4283411 * 2 ^ 59
def prefixEnd_4283411 : Nat := 4983230072969 + 3 ^ 40 * 4283411 * 2
def baseEnd_4283411 : Nat := 2199448683755845868463457

theorem tailTrace_4283411 : CollatzResearch.WordTrace tailWord_4283411 prefixEnd_4283411 2199448683755845868463457 := by
  unfold tailWord_4283411
  simp only [CollatzResearch.WordTrace]
  refine ⟨156228833884940970202370087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104152555923293980134913391 156228833884940970202370087)
  ·
    refine ⟨234343250827411455303555131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156228833884940970202370087 234343250827411455303555131)
    ·
      refine ⟨351514876241117182955332697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234343250827411455303555131 351514876241117182955332697)
      ·
        refine ⟨263636157180837887216499523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351514876241117182955332697 263636157180837887216499523)
        ·
          refine ⟨395454235771256830824749285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263636157180837887216499523 395454235771256830824749285)
          ·
            refine ⟨74147669207110655779640491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 395454235771256830824749285 74147669207110655779640491)
            ·
              refine ⟨111221503810665983669460737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74147669207110655779640491 111221503810665983669460737)
              ·
                refine ⟨83416127857999487752095553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111221503810665983669460737 83416127857999487752095553)
                ·
                  refine ⟨62562095893499615814071665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83416127857999487752095553 62562095893499615814071665)
                  ·
                    refine ⟨46921571920124711860553749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62562095893499615814071665 46921571920124711860553749)
                    ·
                      refine ⟨2199448683755845868463457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46921571920124711860553749 2199448683755845868463457)
                      ·
                        rfl

theorem cell23_4283411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_4283411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283411 prefixEnd_4283411 := by exact prefixLift 4283411
  have htrace : WordTrace (prefixWord ++ tailWord_4283411) baseStart_4283411 baseEnd_4283411 := by
    simpa [prefixWord, tailWord_4283411, baseEnd_4283411] using wordTrace_append hprefix tailTrace_4283411
  have hstable : (prefixWord ++ tailWord_4283411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283411).length < 2 ^ (prefixWord ++ tailWord_4283411).sum := by decide
  have hdescent : baseEnd_4283411 < baseStart_4283411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283448 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_4283448 : Nat := 118140960795 + 4283448 * 2 ^ 59
def prefixEnd_4283448 : Nat := 4983230072969 + 3 ^ 40 * 4283448 * 2
def baseEnd_4283448 : Nat := 2199467682540062223700787

theorem tailTrace_4283448 : CollatzResearch.WordTrace tailWord_4283448 prefixEnd_4283448 2199467682540062223700787 := by
  unfold tailWord_4283448
  simp only [CollatzResearch.WordTrace]
  refine ⟨78115091692903462760733499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104153455590537950347644665 78115091692903462760733499)
  ·
    refine ⟨117172637539355194141100249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78115091692903462760733499 117172637539355194141100249)
    ·
      refine ⟨87879478154516395605825187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117172637539355194141100249 87879478154516395605825187)
      ·
        refine ⟨131819217231774593408737781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87879478154516395605825187 131819217231774593408737781)
        ·
          refine ⟨12358051615478868132069167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131819217231774593408737781 12358051615478868132069167)
          ·
            refine ⟨18537077423218302198103751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12358051615478868132069167 18537077423218302198103751)
            ·
              refine ⟨27805616134827453297155627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18537077423218302198103751 27805616134827453297155627)
              ·
                refine ⟨41708424202241179945733441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27805616134827453297155627 41708424202241179945733441)
                ·
                  refine ⟨31281318151680884959300081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41708424202241179945733441 31281318151680884959300081)
                  ·
                    refine ⟨23460988613760663719475061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31281318151680884959300081 23460988613760663719475061)
                    ·
                      refine ⟨2199467682540062223700787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23460988613760663719475061 2199467682540062223700787)
                      ·
                        rfl

theorem cell23_4283448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_4283448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283448 prefixEnd_4283448 := by exact prefixLift 4283448
  have htrace : WordTrace (prefixWord ++ tailWord_4283448) baseStart_4283448 baseEnd_4283448 := by
    simpa [prefixWord, tailWord_4283448, baseEnd_4283448] using wordTrace_append hprefix tailTrace_4283448
  have hstable : (prefixWord ++ tailWord_4283448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283448).length < 2 ^ (prefixWord ++ tailWord_4283448).sum := by decide
  have hdescent : baseEnd_4283448 < baseStart_4283448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283488 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_4283488 : Nat := 118140960795 + 4283488 * 2 ^ 59
def prefixEnd_4283488 : Nat := 4983230072969 + 3 ^ 40 * 4283488 * 2
def baseEnd_4283488 : Nat := 2199488221766242067200603

theorem tailTrace_4283488 : CollatzResearch.WordTrace tailWord_4283488 prefixEnd_4283488 2199488221766242067200603 := by
  unfold tailWord_4283488
  simp only [CollatzResearch.WordTrace]
  refine ⟨78115821152831006176461559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104154428203774674901948745 78115821152831006176461559)
  ·
    refine ⟨117173731729246509264692339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78115821152831006176461559 117173731729246509264692339)
    ·
      refine ⟨175760597593869763897038509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117173731729246509264692339 175760597593869763897038509)
      ·
        refine ⟨65910224097701161461389441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175760597593869763897038509 65910224097701161461389441)
        ·
          refine ⟨49432668073275871096042081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65910224097701161461389441 49432668073275871096042081)
          ·
            refine ⟨37074501054956903322031561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49432668073275871096042081 37074501054956903322031561)
            ·
              refine ⟨27805875791217677491523671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37074501054956903322031561 27805875791217677491523671)
              ·
                refine ⟨41708813686826516237285507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27805875791217677491523671 41708813686826516237285507)
                ·
                  refine ⟨62563220530239774355928261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41708813686826516237285507 62563220530239774355928261)
                  ·
                    refine ⟨11730603849419957691736549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62563220530239774355928261 11730603849419957691736549)
                    ·
                      refine ⟨2199488221766242067200603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11730603849419957691736549 2199488221766242067200603)
                      ·
                        rfl

theorem cell23_4283488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_4283488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283488 prefixEnd_4283488 := by exact prefixLift 4283488
  have htrace : WordTrace (prefixWord ++ tailWord_4283488) baseStart_4283488 baseEnd_4283488 := by
    simpa [prefixWord, tailWord_4283488, baseEnd_4283488] using wordTrace_append hprefix tailTrace_4283488
  have hstable : (prefixWord ++ tailWord_4283488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283488).length < 2 ^ (prefixWord ++ tailWord_4283488).sum := by decide
  have hdescent : baseEnd_4283488 < baseStart_4283488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283562 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4283562 : Nat := 118140960795 + 4283562 * 2 ^ 59
def prefixEnd_4283562 : Nat := 4983230072969 + 3 ^ 40 * 4283562 * 2
def baseEnd_4283562 : Nat := 733175406444891592558421

theorem tailTrace_4283562 : CollatzResearch.WordTrace tailWord_4283562 prefixEnd_4283562 733175406444891592558421 := by
  unfold tailWord_4283562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39058585326848480747779235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104156227538262615327411293 39058585326848480747779235)
  ·
    refine ⟨58587877990272721121668853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39058585326848480747779235 58587877990272721121668853)
    ·
      refine ⟨5492613561588067605156455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58587877990272721121668853 5492613561588067605156455)
      ·
        refine ⟨8238920342382101407734683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5492613561588067605156455 8238920342382101407734683)
        ·
          refine ⟨12358380513573152111602025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238920342382101407734683 12358380513573152111602025)
          ·
            refine ⟨9268785385179864083701519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12358380513573152111602025 9268785385179864083701519)
            ·
              refine ⟨13903178077769796125552279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9268785385179864083701519 13903178077769796125552279)
              ·
                refine ⟨20854767116654694188328419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13903178077769796125552279 20854767116654694188328419)
                ·
                  refine ⟨31282150674982041282492629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20854767116654694188328419 31282150674982041282492629)
                  ·
                    refine ⟨733175406444891592558421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31282150674982041282492629 733175406444891592558421)
                    ·
                      rfl

theorem cell23_4283562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4283562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283562 prefixEnd_4283562 := by exact prefixLift 4283562
  have htrace : WordTrace (prefixWord ++ tailWord_4283562) baseStart_4283562 baseEnd_4283562 := by
    simpa [prefixWord, tailWord_4283562, baseEnd_4283562] using wordTrace_append hprefix tailTrace_4283562
  have hstable : (prefixWord ++ tailWord_4283562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283562).length < 2 ^ (prefixWord ++ tailWord_4283562).sum := by decide
  have hdescent : baseEnd_4283562 < baseStart_4283562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283575 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 5, 4]
def baseStart_4283575 : Nat := 118140960795 + 4283575 * 2 ^ 59
def prefixEnd_4283575 : Nat := 4983230072969 + 3 ^ 40 * 4283575 * 2
def baseEnd_4283575 : Nat := 733177631527727742270901

theorem tailTrace_4283575 : CollatzResearch.WordTrace tailWord_4283575 prefixEnd_4283575 733177631527727742270901 := by
  unfold tailWord_4283575
  simp only [CollatzResearch.WordTrace]
  refine ⟨156234815456346826211340179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104156543637564550807560119 156234815456346826211340179)
  ·
    refine ⟨234352223184520239317010269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156234815456346826211340179 234352223184520239317010269)
    ·
      refine ⟨87882083694195089743878851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234352223184520239317010269 87882083694195089743878851)
      ·
        refine ⟨131823125541292634615818277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87882083694195089743878851 131823125541292634615818277)
        ·
          refine ⟨24716836038992368990465927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131823125541292634615818277 24716836038992368990465927)
          ·
            refine ⟨37075254058488553485698891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24716836038992368990465927 37075254058488553485698891)
            ·
              refine ⟨55612881087732830228548337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37075254058488553485698891 55612881087732830228548337)
              ·
                refine ⟨41709660815799622671411253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55612881087732830228548337 41709660815799622671411253)
                ·
                  refine ⟨3910280701481214625444805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41709660815799622671411253 3910280701481214625444805)
                  ·
                    refine ⟨733177631527727742270901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910280701481214625444805 733177631527727742270901)
                    ·
                      rfl

theorem cell23_4283575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_4283575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283575 prefixEnd_4283575 := by exact prefixLift 4283575
  have htrace : WordTrace (prefixWord ++ tailWord_4283575) baseStart_4283575 baseEnd_4283575 := by
    simpa [prefixWord, tailWord_4283575, baseEnd_4283575] using wordTrace_append hprefix tailTrace_4283575
  have hstable : (prefixWord ++ tailWord_4283575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283575).length < 2 ^ (prefixWord ++ tailWord_4283575).sum := by decide
  have hdescent : baseEnd_4283575 < baseStart_4283575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283626 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_4283626 : Nat := 118140960795 + 4283626 * 2 ^ 59
def prefixEnd_4283626 : Nat := 4983230072969 + 3 ^ 40 * 4283626 * 2
def baseEnd_4283626 : Nat := 733186360698854175758323

theorem tailTrace_4283626 : CollatzResearch.WordTrace tailWord_4283626 prefixEnd_4283626 733186360698854175758323 := by
  unfold tailWord_4283626
  simp only [CollatzResearch.WordTrace]
  refine ⟨39059168894790515480361683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104157783719441374614297821 39059168894790515480361683)
  ·
    refine ⟨58588753342185773220542525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39059168894790515480361683 58588753342185773220542525)
    ·
      refine ⟨21970782503319664957703447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58588753342185773220542525 21970782503319664957703447)
      ·
        refine ⟨32956173754979497436555171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21970782503319664957703447 32956173754979497436555171)
        ·
          refine ⟨49434260632469246154832757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32956173754979497436555171 49434260632469246154832757)
          ·
            refine ⟨4634461934293991827015571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49434260632469246154832757 4634461934293991827015571)
            ·
              refine ⟨6951692901440987740523357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4634461934293991827015571 6951692901440987740523357)
              ·
                refine ⟨2606884838040370402696259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6951692901440987740523357 2606884838040370402696259)
                ·
                  refine ⟨3910327257060555604044389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606884838040370402696259 3910327257060555604044389)
                  ·
                    refine ⟨733186360698854175758323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910327257060555604044389 733186360698854175758323)
                    ·
                      rfl

theorem cell23_4283626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_4283626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283626 prefixEnd_4283626 := by exact prefixLift 4283626
  have htrace : WordTrace (prefixWord ++ tailWord_4283626) baseStart_4283626 baseEnd_4283626 := by
    simpa [prefixWord, tailWord_4283626, baseEnd_4283626] using wordTrace_append hprefix tailTrace_4283626
  have hstable : (prefixWord ++ tailWord_4283626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283626).length < 2 ^ (prefixWord ++ tailWord_4283626).sum := by decide
  have hdescent : baseEnd_4283626 < baseStart_4283626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283649 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_4283649 : Nat := 118140960795 + 4283649 * 2 ^ 59
def prefixEnd_4283649 : Nat := 4983230072969 + 3 ^ 40 * 4283649 * 2
def baseEnd_4283649 : Nat := 2199570892151615937287363

theorem tailTrace_4283649 : CollatzResearch.WordTrace tailWord_4283649 prefixEnd_4283649 2199570892151615937287363 := by
  unfold tailWord_4283649
  simp only [CollatzResearch.WordTrace]
  refine ⟨156237514458078736849534001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104158342972052491233022667 156237514458078736849534001)
  ·
    refine ⟨117178135843559052637150501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156237514458078736849534001 117178135843559052637150501)
    ·
      refine ⟨21970900470667322369465719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117178135843559052637150501 21970900470667322369465719)
      ·
        refine ⟨32956350706000983554198579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21970900470667322369465719 32956350706000983554198579)
        ·
          refine ⟨49434526059001475331297869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32956350706000983554198579 49434526059001475331297869)
          ·
            refine ⟨18537947272125553249236701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49434526059001475331297869 18537947272125553249236701)
            ·
              refine ⟨6951730227047082468463763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18537947272125553249236701 6951730227047082468463763)
              ·
                refine ⟨10427595340570623702695645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6951730227047082468463763 10427595340570623702695645)
                ·
                  refine ⟨3910348252713983888510867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10427595340570623702695645 3910348252713983888510867)
                  ·
                    refine ⟨5865522379070975832766301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910348252713983888510867 5865522379070975832766301)
                    ·
                      refine ⟨2199570892151615937287363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5865522379070975832766301 2199570892151615937287363)
                      ·
                        rfl

theorem cell23_4283649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_4283649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283649 prefixEnd_4283649 := by exact prefixLift 4283649
  have htrace : WordTrace (prefixWord ++ tailWord_4283649) baseStart_4283649 baseEnd_4283649 := by
    simpa [prefixWord, tailWord_4283649, baseEnd_4283649] using wordTrace_append hprefix tailTrace_4283649
  have hstable : (prefixWord ++ tailWord_4283649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283649).length < 2 ^ (prefixWord ++ tailWord_4283649).sum := by decide
  have hdescent : baseEnd_4283649 < baseStart_4283649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283656 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 6]
def baseStart_4283656 : Nat := 118140960795 + 4283656 * 2 ^ 59
def prefixEnd_4283656 : Nat := 4983230072969 + 3 ^ 40 * 4283656 * 2
def baseEnd_4283656 : Nat := 244397165168466378877759

theorem tailTrace_4283656 : CollatzResearch.WordTrace tailWord_4283656 prefixEnd_4283656 244397165168466378877759 := by
  unfold tailWord_4283656
  simp only [CollatzResearch.WordTrace]
  refine ⟨78118884884526688522519411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104158513179368918030025881 78118884884526688522519411)
  ·
    refine ⟨117178327326790032783779117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78118884884526688522519411 117178327326790032783779117)
    ·
      refine ⟨43941872747546262293917169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117178327326790032783779117 43941872747546262293917169)
      ·
        refine ⟨32956404560659696720437877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43941872747546262293917169 32956404560659696720437877)
        ·
          refine ⟨3089662927561846567541051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32956404560659696720437877 3089662927561846567541051)
          ·
            refine ⟨4634494391342769851311577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089662927561846567541051 4634494391342769851311577)
            ·
              refine ⟨3475870793507077388483683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634494391342769851311577 3475870793507077388483683)
              ·
                refine ⟨5213806190260616082725525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475870793507077388483683 5213806190260616082725525)
                ·
                  refine ⟨244397165168466378877759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5213806190260616082725525 244397165168466378877759)
                  ·
                    rfl

theorem cell23_4283656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 6].length) (baseStart_4283656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283656 prefixEnd_4283656 := by exact prefixLift 4283656
  have htrace : WordTrace (prefixWord ++ tailWord_4283656) baseStart_4283656 baseEnd_4283656 := by
    simpa [prefixWord, tailWord_4283656, baseEnd_4283656] using wordTrace_append hprefix tailTrace_4283656
  have hstable : (prefixWord ++ tailWord_4283656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283656).length < 2 ^ (prefixWord ++ tailWord_4283656).sum := by decide
  have hdescent : baseEnd_4283656 < baseStart_4283656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283665 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_4283665 : Nat := 118140960795 + 4283665 * 2 ^ 59
def prefixEnd_4283665 : Nat := 4983230072969 + 3 ^ 40 * 4283665 * 2
def baseEnd_4283665 : Nat := 733193035947362624895763

theorem tailTrace_4283665 : CollatzResearch.WordTrace tailWord_4283665 prefixEnd_4283665 733193035947362624895763 := by
  unfold tailWord_4283665
  simp only [CollatzResearch.WordTrace]
  refine ⟨156238098026020771582116449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104158732017347181054744299 156238098026020771582116449)
  ·
    refine ⟨117178573519515578686587337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156238098026020771582116449 117178573519515578686587337)
    ·
      refine ⟨87883930139636684014940503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117178573519515578686587337 87883930139636684014940503)
      ·
        refine ⟨131825895209455026022410755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87883930139636684014940503 131825895209455026022410755)
        ·
          refine ⟨197738842814182539033616133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131825895209455026022410755 197738842814182539033616133)
          ·
            refine ⟨37076033027659226068803025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197738842814182539033616133 37076033027659226068803025)
            ·
              refine ⟨27807024770744419551602269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37076033027659226068803025 27807024770744419551602269)
              ·
                refine ⟨10427634289029157331850851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27807024770744419551602269 10427634289029157331850851)
                ·
                  refine ⟨15641451433543735997776277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10427634289029157331850851 15641451433543735997776277)
                  ·
                    refine ⟨733193035947362624895763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15641451433543735997776277 733193035947362624895763)
                    ·
                      rfl

theorem cell23_4283665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_4283665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283665 prefixEnd_4283665 := by exact prefixLift 4283665
  have htrace : WordTrace (prefixWord ++ tailWord_4283665) baseStart_4283665 baseEnd_4283665 := by
    simpa [prefixWord, tailWord_4283665, baseEnd_4283665] using wordTrace_append hprefix tailTrace_4283665
  have hstable : (prefixWord ++ tailWord_4283665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283665).length < 2 ^ (prefixWord ++ tailWord_4283665).sum := by decide
  have hdescent : baseEnd_4283665 < baseStart_4283665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283672 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4283672 : Nat := 118140960795 + 4283672 * 2 ^ 59
def prefixEnd_4283672 : Nat := 4983230072969 + 3 ^ 40 * 4283672 * 2
def baseEnd_4283672 : Nat := 2199582702206669347299757

theorem tailTrace_4283672 : CollatzResearch.WordTrace tailWord_4283672 prefixEnd_4283672 2199582702206669347299757 := by
  unfold tailWord_4283672
  simp only [CollatzResearch.WordTrace]
  refine ⟨78119176668497705888810635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104158902224663607851747513 78119176668497705888810635)
  ·
    refine ⟨117178765002746558833215953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78119176668497705888810635 117178765002746558833215953)
    ·
      refine ⟨87884073752059919124911965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117178765002746558833215953 87884073752059919124911965)
      ·
        refine ⟨32956527657022469671841987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87884073752059919124911965 32956527657022469671841987)
        ·
          refine ⟨49434791485533704507762981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32956527657022469671841987 49434791485533704507762981)
          ·
            refine ⟨9269023403537569595205559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49434791485533704507762981 9269023403537569595205559)
            ·
              refine ⟨13903535105306354392808339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9269023403537569595205559 13903535105306354392808339)
              ·
                refine ⟨20855302657959531589212509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13903535105306354392808339 20855302657959531589212509)
                ·
                  refine ⟨7820738496734824345954691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20855302657959531589212509 7820738496734824345954691)
                  ·
                    refine ⟨11731107745102236518932037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7820738496734824345954691 11731107745102236518932037)
                    ·
                      refine ⟨2199582702206669347299757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11731107745102236518932037 2199582702206669347299757)
                      ·
                        rfl

theorem cell23_4283672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4283672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283672 prefixEnd_4283672 := by exact prefixLift 4283672
  have htrace : WordTrace (prefixWord ++ tailWord_4283672) baseStart_4283672 baseEnd_4283672 := by
    simpa [prefixWord, tailWord_4283672, baseEnd_4283672] using wordTrace_append hprefix tailTrace_4283672
  have hstable : (prefixWord ++ tailWord_4283672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283672).length < 2 ^ (prefixWord ++ tailWord_4283672).sum := by decide
  have hdescent : baseEnd_4283672 < baseStart_4283672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283699 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 2, 4]
def baseStart_4283699 : Nat := 118140960795 + 4283699 * 2 ^ 59
def prefixEnd_4283699 : Nat := 4983230072969 + 3 ^ 40 * 4283699 * 2
def baseEnd_4283699 : Nat := 733198855394780247220711

theorem tailTrace_4283699 : CollatzResearch.WordTrace tailWord_4283699 prefixEnd_4283699 733198855394780247220711 := by
  unfold tailWord_4283699
  simp only [CollatzResearch.WordTrace]
  refine ⟨156239338107897595388854151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104159558738598396925902767 156239338107897595388854151)
  ·
    refine ⟨234359007161846393083281227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156239338107897595388854151 234359007161846393083281227)
    ·
      refine ⟨351538510742769589624921841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234359007161846393083281227 351538510742769589624921841)
      ·
        refine ⟨263653883057077192218691381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351538510742769589624921841 263653883057077192218691381)
        ·
          refine ⟨24717551536600986770502317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263653883057077192218691381 24717551536600986770502317)
          ·
            refine ⟨9269081826225370038938369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24717551536600986770502317 9269081826225370038938369)
            ·
              refine ⟨6951811369669027529203777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9269081826225370038938369 6951811369669027529203777)
              ·
                refine ⟨5213858527251770646902833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6951811369669027529203777 5213858527251770646902833)
                ·
                  refine ⟨3910393895438827985177125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213858527251770646902833 3910393895438827985177125)
                  ·
                    refine ⟨733198855394780247220711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910393895438827985177125 733198855394780247220711)
                    ·
                      rfl

theorem cell23_4283699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 4].length) (baseStart_4283699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283699 prefixEnd_4283699 := by exact prefixLift 4283699
  have htrace : WordTrace (prefixWord ++ tailWord_4283699) baseStart_4283699 baseEnd_4283699 := by
    simpa [prefixWord, tailWord_4283699, baseEnd_4283699] using wordTrace_append hprefix tailTrace_4283699
  have hstable : (prefixWord ++ tailWord_4283699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283699).length < 2 ^ (prefixWord ++ tailWord_4283699).sum := by decide
  have hdescent : baseEnd_4283699 < baseStart_4283699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283716 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4283716 : Nat := 118140960795 + 4283716 * 2 ^ 59
def prefixEnd_4283716 : Nat := 4983230072969 + 3 ^ 40 * 4283716 * 2
def baseEnd_4283716 : Nat := 733201765118489058383185

theorem tailTrace_4283716 : CollatzResearch.WordTrace tailWord_4283716 prefixEnd_4283716 733201765118489058383185 := by
  unfold tailWord_4283716
  simp only [CollatzResearch.WordTrace]
  refine ⟨78119979074418003646111501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104159972099224004861482001 78119979074418003646111501)
  ·
    refine ⟨29294992152906751367291813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78119979074418003646111501 29294992152906751367291813)
    ·
      refine ⟨5492811028670015881367215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29294992152906751367291813 5492811028670015881367215)
      ·
        refine ⟨8239216543005023822050823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5492811028670015881367215 8239216543005023822050823)
        ·
          refine ⟨12358824814507535733076235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8239216543005023822050823 12358824814507535733076235)
          ·
            refine ⟨18538237221761303599614353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12358824814507535733076235 18538237221761303599614353)
            ·
              refine ⟨13903677916320977699710765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18538237221761303599614353 13903677916320977699710765)
              ·
                refine ⟨5213879218620366637391537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13903677916320977699710765 5213879218620366637391537)
                ·
                  refine ⟨3910409413965274978043653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213879218620366637391537 3910409413965274978043653)
                  ·
                    refine ⟨733201765118489058383185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910409413965274978043653 733201765118489058383185)
                    ·
                      rfl

theorem cell23_4283716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4283716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283716 prefixEnd_4283716 := by exact prefixLift 4283716
  have htrace : WordTrace (prefixWord ++ tailWord_4283716) baseStart_4283716 baseEnd_4283716 := by
    simpa [prefixWord, tailWord_4283716, baseEnd_4283716] using wordTrace_append hprefix tailTrace_4283716
  have hstable : (prefixWord ++ tailWord_4283716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283716).length < 2 ^ (prefixWord ++ tailWord_4283716).sum := by decide
  have hdescent : baseEnd_4283716 < baseStart_4283716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283734 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4283734 : Nat := 118140960795 + 4283734 * 2 ^ 59
def prefixEnd_4283734 : Nat := 4983230072969 + 3 ^ 40 * 4283734 * 2
def baseEnd_4283734 : Nat := 2199614538007248104724473

theorem tailTrace_4283734 : CollatzResearch.WordTrace tailWord_4283734 prefixEnd_4283734 2199614538007248104724473 := by
  unfold tailWord_4283734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765038416423174772898641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104160409775180530910918837 9765038416423174772898641)
  ·
    refine ⟨7323778812317381079673981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9765038416423174772898641 7323778812317381079673981)
    ·
      refine ⟨2746417054619017904877743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7323778812317381079673981 2746417054619017904877743)
      ·
        refine ⟨4119625581928526857316615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746417054619017904877743 4119625581928526857316615)
        ·
          refine ⟨6179438372892790285974923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119625581928526857316615 6179438372892790285974923)
          ·
            refine ⟨9269157559339185428962385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179438372892790285974923 9269157559339185428962385)
            ·
              refine ⟨6951868169504389071721789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9269157559339185428962385 6951868169504389071721789)
              ·
                refine ⟨2606950563564145901895671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6951868169504389071721789 2606950563564145901895671)
                ·
                  refine ⟨3910425845346218852843507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606950563564145901895671 3910425845346218852843507)
                  ·
                    refine ⟨5865638768019328279265261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910425845346218852843507 5865638768019328279265261)
                    ·
                      refine ⟨2199614538007248104724473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5865638768019328279265261 2199614538007248104724473)
                      ·
                        rfl

theorem cell23_4283734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4283734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283734 prefixEnd_4283734 := by exact prefixLift 4283734
  have htrace : WordTrace (prefixWord ++ tailWord_4283734) baseStart_4283734 baseEnd_4283734 := by
    simpa [prefixWord, tailWord_4283734, baseEnd_4283734] using wordTrace_append hprefix tailTrace_4283734
  have hstable : (prefixWord ++ tailWord_4283734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283734).length < 2 ^ (prefixWord ++ tailWord_4283734).sum := by decide
  have hdescent : baseEnd_4283734 < baseStart_4283734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283756 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_4283756 : Nat := 118140960795 + 4283756 * 2 ^ 59
def prefixEnd_4283756 : Nat := 4983230072969 + 3 ^ 40 * 4283756 * 2
def baseEnd_4283756 : Nat := 2199625834581647018649371

theorem tailTrace_4283756 : CollatzResearch.WordTrace tailWord_4283756 prefixEnd_4283756 2199625834581647018649371 := by
  unfold tailWord_4283756
  simp only [CollatzResearch.WordTrace]
  refine ⟨78120708534345547061839561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104160944712460729415786081 78120708534345547061839561)
  ·
    refine ⟨58590531400759160296379671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78120708534345547061839561 58590531400759160296379671)
    ·
      refine ⟨87885797101138740444569507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58590531400759160296379671 87885797101138740444569507)
      ·
        refine ⟨131828695651708110666854261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87885797101138740444569507 131828695651708110666854261)
        ·
          refine ⟨12358940217347635375017587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131828695651708110666854261 12358940217347635375017587)
          ·
            refine ⟨18538410326021453062526381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12358940217347635375017587 18538410326021453062526381)
            ·
              refine ⟨6951903872258044898447393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18538410326021453062526381 6951903872258044898447393)
              ·
                refine ⟨5213927904193533673835545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6951903872258044898447393 5213927904193533673835545)
                ·
                  refine ⟨3910445928145150255376659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213927904193533673835545 3910445928145150255376659)
                  ·
                    refine ⟨5865668892217725383064989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910445928145150255376659 5865668892217725383064989)
                    ·
                      refine ⟨2199625834581647018649371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5865668892217725383064989 2199625834581647018649371)
                      ·
                        rfl

theorem cell23_4283756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_4283756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283756 prefixEnd_4283756 := by exact prefixLift 4283756
  have htrace : WordTrace (prefixWord ++ tailWord_4283756) baseStart_4283756 baseEnd_4283756 := by
    simpa [prefixWord, tailWord_4283756, baseEnd_4283756] using wordTrace_append hprefix tailTrace_4283756
  have hstable : (prefixWord ++ tailWord_4283756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283756).length < 2 ^ (prefixWord ++ tailWord_4283756).sum := by decide
  have hdescent : baseEnd_4283756 < baseStart_4283756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283886 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_4283886 : Nat := 118140960795 + 4283886 * 2 ^ 59
def prefixEnd_4283886 : Nat := 4983230072969 + 3 ^ 40 * 4283886 * 2
def baseEnd_4283886 : Nat := 2199692587066731510023773

theorem tailTrace_4283886 : CollatzResearch.WordTrace tailWord_4283886 prefixEnd_4283886 2199692587066731510023773 := by
  unfold tailWord_4283886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19530769819777515790738939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104164105705480084217274341 19530769819777515790738939)
  ·
    refine ⟨29296154729666273686108409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19530769819777515790738939 29296154729666273686108409)
    ·
      refine ⟨21972116047249705264581307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29296154729666273686108409 21972116047249705264581307)
      ·
        refine ⟨32958174070874557896871961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21972116047249705264581307 32958174070874557896871961)
        ·
          refine ⟨24718630553155918422653971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32958174070874557896871961 24718630553155918422653971)
          ·
            refine ⟨37077945829733877633980957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24718630553155918422653971 37077945829733877633980957)
            ·
              refine ⟨13904229686150204112742859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37077945829733877633980957 13904229686150204112742859)
              ·
                refine ⟨20856344529225306169114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13904229686150204112742859 20856344529225306169114289)
                ·
                  refine ⟨15642258396918979626835717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20856344529225306169114289 15642258396918979626835717)
                  ·
                    refine ⟨2932923449422308680031697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15642258396918979626835717 2932923449422308680031697)
                    ·
                      refine ⟨2199692587066731510023773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932923449422308680031697 2199692587066731510023773)
                      ·
                        rfl

theorem cell23_4283886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_4283886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283886 prefixEnd_4283886 := by exact prefixLift 4283886
  have htrace : WordTrace (prefixWord ++ tailWord_4283886) baseStart_4283886 baseEnd_4283886 := by
    simpa [prefixWord, tailWord_4283886, baseEnd_4283886] using wordTrace_append hprefix tailTrace_4283886
  have hstable : (prefixWord ++ tailWord_4283886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283886).length < 2 ^ (prefixWord ++ tailWord_4283886).sum := by decide
  have hdescent : baseEnd_4283886 < baseStart_4283886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283929 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 5, 2]
def baseStart_4283929 : Nat := 118140960795 + 4283929 * 2 ^ 59
def prefixEnd_4283929 : Nat := 4983230072969 + 3 ^ 40 * 4283929 * 2
def baseEnd_4283929 : Nat := 2199714666734874841786075

theorem tailTrace_4283929 : CollatzResearch.WordTrace tailWord_4283929 prefixEnd_4283929 2199714666734874841786075 := by
  unfold tailWord_4283929
  simp only [CollatzResearch.WordTrace]
  refine ⟨156247726897064344669726841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104165151264709563113151227 156247726897064344669726841)
  ·
    refine ⟨117185795172798258502295131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156247726897064344669726841 117185795172798258502295131)
    ·
      refine ⟨175778692759197387753442697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117185795172798258502295131 175778692759197387753442697)
      ·
        refine ⟨131834019569398040815082023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175778692759197387753442697 131834019569398040815082023)
        ·
          refine ⟨197751029354097061222623035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131834019569398040815082023 197751029354097061222623035)
          ·
            refine ⟨296626544031145591833934553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197751029354097061222623035 296626544031145591833934553)
            ·
              refine ⟨222469908023359193875450915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296626544031145591833934553 222469908023359193875450915)
              ·
                refine ⟨333704862035038790813176373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222469908023359193875450915 333704862035038790813176373)
                ·
                  refine ⟨31284830815784886638735285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333704862035038790813176373 31284830815784886638735285)
                  ·
                    refine ⟨2932952888979833122381433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31284830815784886638735285 2932952888979833122381433)
                    ·
                      refine ⟨2199714666734874841786075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932952888979833122381433 2199714666734874841786075)
                      ·
                        rfl

theorem cell23_4283929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_4283929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283929 prefixEnd_4283929 := by exact prefixLift 4283929
  have htrace : WordTrace (prefixWord ++ tailWord_4283929) baseStart_4283929 baseEnd_4283929 := by
    simpa [prefixWord, tailWord_4283929, baseEnd_4283929] using wordTrace_append hprefix tailTrace_4283929
  have hstable : (prefixWord ++ tailWord_4283929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283929).length < 2 ^ (prefixWord ++ tailWord_4283929).sum := by decide
  have hdescent : baseEnd_4283929 < baseStart_4283929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283946 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4283946 : Nat := 118140960795 + 4283946 * 2 ^ 59
def prefixEnd_4283946 : Nat := 4983230072969 + 3 ^ 40 * 4283946 * 2
def baseEnd_4283946 : Nat := 2199723395906001275273497

theorem tailTrace_4283946 : CollatzResearch.WordTrace tailWord_4283946 prefixEnd_4283946 2199723395906001275273497 := by
  unfold tailWord_4283946
  simp only [CollatzResearch.WordTrace]
  refine ⟨39062086734500689143273923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104165564625335171048730461 39062086734500689143273923)
  ·
    refine ⟨58593130101751033714910885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39062086734500689143273923 58593130101751033714910885)
    ·
      refine ⟨10986211894078318821545791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58593130101751033714910885 10986211894078318821545791)
      ·
        refine ⟨16479317841117478232318687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10986211894078318821545791 16479317841117478232318687)
        ·
          refine ⟨24718976761676217348478031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16479317841117478232318687 24718976761676217348478031)
          ·
            refine ⟨37078465142514326022717047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24718976761676217348478031 37078465142514326022717047)
            ·
              refine ⟨55617697713771489034075571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37078465142514326022717047 55617697713771489034075571)
              ·
                refine ⟨83426546570657233551113357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55617697713771489034075571 83426546570657233551113357)
                ·
                  refine ⟨31284954963996462581667509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83426546570657233551113357 31284954963996462581667509)
                  ·
                    refine ⟨2932964527874668367031329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31284954963996462581667509 2932964527874668367031329)
                    ·
                      refine ⟨2199723395906001275273497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2932964527874668367031329 2199723395906001275273497)
                      ·
                        rfl

theorem cell23_4283946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4283946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283946 prefixEnd_4283946 := by exact prefixLift 4283946
  have htrace : WordTrace (prefixWord ++ tailWord_4283946) baseStart_4283946 baseEnd_4283946 := by
    simpa [prefixWord, tailWord_4283946, baseEnd_4283946] using wordTrace_append hprefix tailTrace_4283946
  have hstable : (prefixWord ++ tailWord_4283946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283946).length < 2 ^ (prefixWord ++ tailWord_4283946).sum := by decide
  have hdescent : baseEnd_4283946 < baseStart_4283946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283969 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4283969 : Nat := 118140960795 + 4283969 * 2 ^ 59
def prefixEnd_4283969 : Nat := 4983230072969 + 3 ^ 40 * 4283969 * 2
def baseEnd_4283969 : Nat := 733245068653684895095297

theorem tailTrace_4283969 : CollatzResearch.WordTrace tailWord_4283969 prefixEnd_4283969 733245068653684895095297 := by
  unfold tailWord_4283969
  simp only [CollatzResearch.WordTrace]
  refine ⟨156249185816919431501182961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104166123877946287667455307 156249185816919431501182961)
  ·
    refine ⟨117186889362689573625887221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156249185816919431501182961 117186889362689573625887221)
    ·
      refine ⟨10986270877752147527426927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117186889362689573625887221 10986270877752147527426927)
      ·
        refine ⟨16479406316628221291140391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10986270877752147527426927 16479406316628221291140391)
        ·
          refine ⟨24719109474942331936710587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16479406316628221291140391 24719109474942331936710587)
          ·
            refine ⟨37078664212413497905065881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24719109474942331936710587 37078664212413497905065881)
            ·
              refine ⟨27808998159310123428799411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37078664212413497905065881 27808998159310123428799411)
              ·
                refine ⟨41713497238965185143199117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27808998159310123428799411 41713497238965185143199117)
                ·
                  refine ⟨15642561464611944428699669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41713497238965185143199117 15642561464611944428699669)
                  ·
                    refine ⟨733245068653684895095297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15642561464611944428699669 733245068653684895095297)
                    ·
                      rfl

theorem cell23_4283969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4283969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283969 prefixEnd_4283969 := by exact prefixLift 4283969
  have htrace : WordTrace (prefixWord ++ tailWord_4283969) baseStart_4283969 baseEnd_4283969 := by
    simpa [prefixWord, tailWord_4283969, baseEnd_4283969] using wordTrace_append hprefix tailTrace_4283969
  have hstable : (prefixWord ++ tailWord_4283969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283969).length < 2 ^ (prefixWord ++ tailWord_4283969).sum := by decide
  have hdescent : baseEnd_4283969 < baseStart_4283969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283979 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3]
def baseStart_4283979 : Nat := 118140960795 + 4283979 * 2 ^ 59
def prefixEnd_4283979 : Nat := 4983230072969 + 3 ^ 40 * 4283979 * 2
def baseEnd_4283979 : Nat := 2199740340767599646160845

theorem tailTrace_4283979 : CollatzResearch.WordTrace tailWord_4283979 prefixEnd_4283979 2199740340767599646160845 := by
  unfold tailWord_4283979
  simp only [CollatzResearch.WordTrace]
  refine ⟨156249550546883203209046991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104166367031255468806031327 156249550546883203209046991)
  ·
    refine ⟨234374325820324804813570487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156249550546883203209046991 234374325820324804813570487)
    ·
      refine ⟨351561488730487207220355731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234374325820324804813570487 351561488730487207220355731)
      ·
        refine ⟨527342233095730810830533597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351561488730487207220355731 527342233095730810830533597)
        ·
          refine ⟨197753337410899054061450099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527342233095730810830533597 197753337410899054061450099)
          ·
            refine ⟨296630006116348581092175149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197753337410899054061450099 296630006116348581092175149)
            ·
              refine ⟨111236252293630717909565681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296630006116348581092175149 111236252293630717909565681)
              ·
                refine ⟨83427189220223038432174261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111236252293630717909565681 83427189220223038432174261)
                ·
                  refine ⟨7821298989395909853016337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83427189220223038432174261 7821298989395909853016337)
                  ·
                    refine ⟨5865974242046932389762253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7821298989395909853016337 5865974242046932389762253)
                    ·
                      refine ⟨2199740340767599646160845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5865974242046932389762253 2199740340767599646160845)
                      ·
                        rfl

theorem cell23_4283979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3].length) (baseStart_4283979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283979 prefixEnd_4283979 := by exact prefixLift 4283979
  have htrace : WordTrace (prefixWord ++ tailWord_4283979) baseStart_4283979 baseEnd_4283979 := by
    simpa [prefixWord, tailWord_4283979, baseEnd_4283979] using wordTrace_append hprefix tailTrace_4283979
  have hstable : (prefixWord ++ tailWord_4283979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283979).length < 2 ^ (prefixWord ++ tailWord_4283979).sum := by decide
  have hdescent : baseEnd_4283979 < baseStart_4283979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283986 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_4283986 : Nat := 118140960795 + 4283986 * 2 ^ 59
def prefixEnd_4283986 : Nat := 4983230072969 + 3 ^ 40 * 4283986 * 2
def baseEnd_4283986 : Nat := 733247978377393706257771

theorem tailTrace_4283986 : CollatzResearch.WordTrace tailWord_4283986 prefixEnd_4283986 733247978377393706257771 := by
  unfold tailWord_4283986
  simp only [CollatzResearch.WordTrace]
  refine ⟨39062451464464460851137953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104166537238571895603034541 39062451464464460851137953)
  ·
    refine ⟨29296838598348345638353465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39062451464464460851137953 29296838598348345638353465)
    ·
      refine ⟨21972628948761259228765099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29296838598348345638353465 21972628948761259228765099)
      ·
        refine ⟨32958943423141888843147649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21972628948761259228765099 32958943423141888843147649)
        ·
          refine ⟨24719207567356416632360737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32958943423141888843147649 24719207567356416632360737)
          ·
            refine ⟨18539405675517312474270553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24719207567356416632360737 18539405675517312474270553)
            ·
              refine ⟨13904554256637984355702915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18539405675517312474270553 13904554256637984355702915)
              ·
                refine ⟨20856831384956976533554373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13904554256637984355702915 20856831384956976533554373)
                ·
                  refine ⟨3910655884679433100041445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20856831384956976533554373 3910655884679433100041445)
                  ·
                    refine ⟨733247978377393706257771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910655884679433100041445 733247978377393706257771)
                    ·
                      rfl

theorem cell23_4283986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_4283986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283986 prefixEnd_4283986 := by exact prefixLift 4283986
  have htrace : WordTrace (prefixWord ++ tailWord_4283986) baseStart_4283986 baseEnd_4283986 := by
    simpa [prefixWord, tailWord_4283986, baseEnd_4283986] using wordTrace_append hprefix tailTrace_4283986
  have hstable : (prefixWord ++ tailWord_4283986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283986).length < 2 ^ (prefixWord ++ tailWord_4283986).sum := by decide
  have hdescent : baseEnd_4283986 < baseStart_4283986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4283996 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4283996 : Nat := 118140960795 + 4283996 * 2 ^ 59
def prefixEnd_4283996 : Nat := 4983230072969 + 3 ^ 40 * 4283996 * 2
def baseEnd_4283996 : Nat := 2199749069938726079648267

theorem tailTrace_4283996 : CollatzResearch.WordTrace tailWord_4283996 prefixEnd_4283996 2199749069938726079648267 := by
  unfold tailWord_4283996
  simp only [CollatzResearch.WordTrace]
  refine ⟨78125085293910807556207921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104166780391881076741610561 78125085293910807556207921)
  ·
    refine ⟨58593813970433105667155941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78125085293910807556207921 58593813970433105667155941)
    ·
      refine ⟨10986340119456207312591739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58593813970433105667155941 10986340119456207312591739)
      ·
        refine ⟨16479510179184310968887609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10986340119456207312591739 16479510179184310968887609)
        ·
          refine ⟨12359632634388233226665707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16479510179184310968887609 12359632634388233226665707)
          ·
            refine ⟨18539448951582349839998561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12359632634388233226665707 18539448951582349839998561)
            ·
              refine ⟨13904586713686762379998921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18539448951582349839998561 13904586713686762379998921)
              ·
                refine ⟨10428440035265071784999191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13904586713686762379998921 10428440035265071784999191)
                ·
                  refine ⟨15642660052897607677498787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10428440035265071784999191 15642660052897607677498787)
                  ·
                    refine ⟨23463990079346411516248181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15642660052897607677498787 23463990079346411516248181)
                    ·
                      refine ⟨2199749069938726079648267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23463990079346411516248181 2199749069938726079648267)
                      ·
                        rfl

theorem cell23_4283996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4283996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4283996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4283996 prefixEnd_4283996 := by exact prefixLift 4283996
  have htrace : WordTrace (prefixWord ++ tailWord_4283996) baseStart_4283996 baseEnd_4283996 := by
    simpa [prefixWord, tailWord_4283996, baseEnd_4283996] using wordTrace_append hprefix tailTrace_4283996
  have hstable : (prefixWord ++ tailWord_4283996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4283996).length < 2 ^ (prefixWord ++ tailWord_4283996).sum := by decide
  have hdescent : baseEnd_4283996 < baseStart_4283996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4283996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284003 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 2, 4]
def baseStart_4284003 : Nat := 118140960795 + 4284003 * 2 ^ 59
def prefixEnd_4284003 : Nat := 4983230072969 + 3 ^ 40 * 4284003 * 2
def baseEnd_4284003 : Nat := 733250888101102517420245

theorem tailTrace_4284003 : CollatzResearch.WordTrace tailWord_4284003 prefixEnd_4284003 733250888101102517420245 := by
  unfold tailWord_4284003
  simp only [CollatzResearch.WordTrace]
  refine ⟨156250425898796255307920663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104166950599197503538613775 156250425898796255307920663)
  ·
    refine ⟨234375638848194382961880995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156250425898796255307920663 234375638848194382961880995)
    ·
      refine ⟨351563458272291574442821493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234375638848194382961880995 351563458272291574442821493)
      ·
        refine ⟨32959074213027335104014515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 351563458272291574442821493 32959074213027335104014515)
        ·
          refine ⟨49438611319541002656021773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32959074213027335104014515 49438611319541002656021773)
          ·
            refine ⟨18539479244827875996008165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49438611319541002656021773 18539479244827875996008165)
            ·
              refine ⟨3476152358405226749251531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18539479244827875996008165 3476152358405226749251531)
              ·
                refine ⟨5214228537607840123877297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476152358405226749251531 5214228537607840123877297)
                ·
                  refine ⟨3910671403205880092907973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5214228537607840123877297 3910671403205880092907973)
                  ·
                    refine ⟨733250888101102517420245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910671403205880092907973 733250888101102517420245)
                    ·
                      rfl

theorem cell23_4284003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 4].length) (baseStart_4284003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284003 prefixEnd_4284003 := by exact prefixLift 4284003
  have htrace : WordTrace (prefixWord ++ tailWord_4284003) baseStart_4284003 baseEnd_4284003 := by
    simpa [prefixWord, tailWord_4284003, baseEnd_4284003] using wordTrace_append hprefix tailTrace_4284003
  have hstable : (prefixWord ++ tailWord_4284003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284003).length < 2 ^ (prefixWord ++ tailWord_4284003).sum := by decide
  have hdescent : baseEnd_4284003 < baseStart_4284003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284013 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4284013 : Nat := 118140960795 + 4284013 * 2 ^ 59
def prefixEnd_4284013 : Nat := 4983230072969 + 3 ^ 40 * 4284013 * 2
def baseEnd_4284013 : Nat := 2199757799109852513135689

theorem tailTrace_4284013 : CollatzResearch.WordTrace tailWord_4284013 prefixEnd_4284013 2199757799109852513135689 := by
  unfold tailWord_4284013
  simp only [CollatzResearch.WordTrace]
  refine ⟨156250790628760027015784693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104167193752506684677189795 156250790628760027015784693)
  ·
    refine ⟨14648511621446252532729815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156250790628760027015784693 14648511621446252532729815)
    ·
      refine ⟨21972767432169378799094723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14648511621446252532729815 21972767432169378799094723)
      ·
        refine ⟨32959151148254068198642085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21972767432169378799094723 32959151148254068198642085)
        ·
          refine ⟨6179840840297637787245391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32959151148254068198642085 6179840840297637787245391)
          ·
            refine ⟨9269761260446456680868087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179840840297637787245391 9269761260446456680868087)
            ·
              refine ⟨13904641890669685021302131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9269761260446456680868087 13904641890669685021302131)
              ·
                refine ⟨20856962836004527531953197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13904641890669685021302131 20856962836004527531953197)
                ·
                  refine ⟨7821361063501697824482449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20856962836004527531953197 7821361063501697824482449)
                  ·
                    refine ⟨5866020797626273368361837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7821361063501697824482449 5866020797626273368361837)
                    ·
                      refine ⟨2199757799109852513135689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866020797626273368361837 2199757799109852513135689)
                      ·
                        rfl

theorem cell23_4284013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4284013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284013 prefixEnd_4284013 := by exact prefixLift 4284013
  have htrace : WordTrace (prefixWord ++ tailWord_4284013) baseStart_4284013 baseEnd_4284013 := by
    simpa [prefixWord, tailWord_4284013, baseEnd_4284013] using wordTrace_append hprefix tailTrace_4284013
  have hstable : (prefixWord ++ tailWord_4284013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284013).length < 2 ^ (prefixWord ++ tailWord_4284013).sum := by decide
  have hdescent : baseEnd_4284013 < baseStart_4284013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284026 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_4284026 : Nat := 118140960795 + 4284026 * 2 ^ 59
def prefixEnd_4284026 : Nat := 4983230072969 + 3 ^ 40 * 4284026 * 2
def baseEnd_4284026 : Nat := 2199764474358360962273129

theorem tailTrace_4284026 : CollatzResearch.WordTrace tailWord_4284026 prefixEnd_4284026 2199764474358360962273129 := by
  unfold tailWord_4284026
  simp only [CollatzResearch.WordTrace]
  refine ⟨39062816194428232559001983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104167509851808620157338621 39062816194428232559001983)
  ·
    refine ⟨58594224291642348838502975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39062816194428232559001983 58594224291642348838502975)
    ·
      refine ⟨87891336437463523257754463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58594224291642348838502975 87891336437463523257754463)
      ·
        refine ⟨131837004656195284886631695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87891336437463523257754463 131837004656195284886631695)
        ·
          refine ⟨197755506984292927329947543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131837004656195284886631695 197755506984292927329947543)
          ·
            refine ⟨296633260476439390994921315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197755506984292927329947543 296633260476439390994921315)
            ·
              refine ⟨444949890714659086492381973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296633260476439390994921315 444949890714659086492381973)
              ·
                refine ⟨20857026127249644679330405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 444949890714659086492381973 20857026127249644679330405)
                ·
                  refine ⟨3910692398859308377374451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20857026127249644679330405 3910692398859308377374451)
                  ·
                    refine ⟨5866038598288962566061677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910692398859308377374451 5866038598288962566061677)
                    ·
                      refine ⟨2199764474358360962273129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866038598288962566061677 2199764474358360962273129)
                      ·
                        rfl

theorem cell23_4284026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_4284026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284026 prefixEnd_4284026 := by exact prefixLift 4284026
  have htrace : WordTrace (prefixWord ++ tailWord_4284026) baseStart_4284026 baseEnd_4284026 := by
    simpa [prefixWord, tailWord_4284026, baseEnd_4284026] using wordTrace_append hprefix tailTrace_4284026
  have hstable : (prefixWord ++ tailWord_4284026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284026).length < 2 ^ (prefixWord ++ tailWord_4284026).sum := by decide
  have hdescent : baseEnd_4284026 < baseStart_4284026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284043 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 3]
def baseStart_4284043 : Nat := 118140960795 + 4284043 * 2 ^ 59
def prefixEnd_4284043 : Nat := 4983230072969 + 3 ^ 40 * 4284043 * 2
def baseEnd_4284043 : Nat := 2199773203529487395760551

theorem tailTrace_4284043 : CollatzResearch.WordTrace tailWord_4284043 prefixEnd_4284043 2199773203529487395760551 := by
  unfold tailWord_4284043
  simp only [CollatzResearch.WordTrace]
  refine ⟨156251884818651342139376783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104167923212434228092917855 156251884818651342139376783)
  ·
    refine ⟨234377827227977013209065175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156251884818651342139376783 234377827227977013209065175)
    ·
      refine ⟨351566740841965519813597763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234377827227977013209065175 351566740841965519813597763)
      ·
        refine ⟨527350111262948279720396645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351566740841965519813597763 527350111262948279720396645)
        ·
          refine ⟨98878145861802802447574371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 527350111262948279720396645 98878145861802802447574371)
          ·
            refine ⟨148317218792704203671361557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98878145861802802447574371 148317218792704203671361557)
            ·
              refine ⟨6952369630908009547095073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148317218792704203671361557 6952369630908009547095073)
              ·
                refine ⟨5214277223181007160321305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6952369630908009547095073 5214277223181007160321305)
                ·
                  refine ⟨3910707917385755370240979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5214277223181007160321305 3910707917385755370240979)
                  ·
                    refine ⟨5866061876078633055361469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910707917385755370240979 5866061876078633055361469)
                    ·
                      refine ⟨2199773203529487395760551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866061876078633055361469 2199773203529487395760551)
                      ·
                        rfl

theorem cell23_4284043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 3].length) (baseStart_4284043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284043 prefixEnd_4284043 := by exact prefixLift 4284043
  have htrace : WordTrace (prefixWord ++ tailWord_4284043) baseStart_4284043 baseEnd_4284043 := by
    simpa [prefixWord, tailWord_4284043, baseEnd_4284043] using wordTrace_append hprefix tailTrace_4284043
  have hstable : (prefixWord ++ tailWord_4284043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284043).length < 2 ^ (prefixWord ++ tailWord_4284043).sum := by decide
  have hdescent : baseEnd_4284043 < baseStart_4284043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284069 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_4284069 : Nat := 118140960795 + 4284069 * 2 ^ 59
def prefixEnd_4284069 : Nat := 4983230072969 + 3 ^ 40 * 4284069 * 2
def baseEnd_4284069 : Nat := 2199786554026504294035431

theorem tailTrace_4284069 : CollatzResearch.WordTrace tailWord_4284069 prefixEnd_4284069 2199786554026504294035431 := by
  unfold tailWord_4284069
  simp only [CollatzResearch.WordTrace]
  refine ⟨156252833116557148579823261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104168555411038099053215507 156252833116557148579823261)
  ·
    refine ⟨58594812418708930717433723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156252833116557148579823261 58594812418708930717433723)
    ·
      refine ⟨87892218628063396076150585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58594812418708930717433723 87892218628063396076150585)
      ·
        refine ⟨65919163971047547057112939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87892218628063396076150585 65919163971047547057112939)
        ·
          refine ⟨98878745956571320585669409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65919163971047547057112939 98878745956571320585669409)
          ·
            refine ⟨74159059467428490439252057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98878745956571320585669409 74159059467428490439252057)
            ·
              refine ⟨55619294600571367829439043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74159059467428490439252057 55619294600571367829439043)
              ·
                refine ⟨83428941900857051744158565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55619294600571367829439043 83428941900857051744158565)
                ·
                  refine ⟨15642926606410697202029731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83428941900857051744158565 15642926606410697202029731)
                  ·
                    refine ⟨23464389909616045803044597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15642926606410697202029731 23464389909616045803044597)
                    ·
                      refine ⟨2199786554026504294035431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23464389909616045803044597 2199786554026504294035431)
                      ·
                        rfl

theorem cell23_4284069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_4284069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284069 prefixEnd_4284069 := by exact prefixLift 4284069
  have htrace : WordTrace (prefixWord ++ tailWord_4284069) baseStart_4284069 baseEnd_4284069 := by
    simpa [prefixWord, tailWord_4284069, baseEnd_4284069] using wordTrace_append hprefix tailTrace_4284069
  have hstable : (prefixWord ++ tailWord_4284069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284069).length < 2 ^ (prefixWord ++ tailWord_4284069).sum := by decide
  have hdescent : baseEnd_4284069 < baseStart_4284069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284079 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_4284079 : Nat := 118140960795 + 4284079 * 2 ^ 59
def prefixEnd_4284079 : Nat := 4983230072969 + 3 ^ 40 * 4284079 * 2
def baseEnd_4284079 : Nat := 2199791688833049254910385

theorem tailTrace_4284079 : CollatzResearch.WordTrace tailWord_4284079 prefixEnd_4284079 2199791688833049254910385 := by
  unfold tailWord_4284079
  simp only [CollatzResearch.WordTrace]
  refine ⟨156253197846520920287687291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104168798564347280191791527 156253197846520920287687291)
  ·
    refine ⟨234379796769781380431530937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156253197846520920287687291 234379796769781380431530937)
    ·
      refine ⟨175784847577336035323648203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234379796769781380431530937 175784847577336035323648203)
      ·
        refine ⟨263677271366004052985472305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175784847577336035323648203 263677271366004052985472305)
        ·
          refine ⟨197757953524503039739104229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263677271366004052985472305 197757953524503039739104229)
          ·
            refine ⟨37079616285844319951082043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197757953524503039739104229 37079616285844319951082043)
            ·
              refine ⟨55619424428766479926623065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37079616285844319951082043 55619424428766479926623065)
              ·
                refine ⟨41714568321574859944967299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55619424428766479926623065 41714568321574859944967299)
                ·
                  refine ⟨62571852482362289917450949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41714568321574859944967299 62571852482362289917450949)
                  ·
                    refine ⟨11732222340442929359522053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62571852482362289917450949 11732222340442929359522053)
                    ·
                      refine ⟨2199791688833049254910385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11732222340442929359522053 2199791688833049254910385)
                      ·
                        rfl

theorem cell23_4284079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_4284079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284079 prefixEnd_4284079 := by exact prefixLift 4284079
  have htrace : WordTrace (prefixWord ++ tailWord_4284079) baseStart_4284079 baseEnd_4284079 := by
    simpa [prefixWord, tailWord_4284079, baseEnd_4284079] using wordTrace_append hprefix tailTrace_4284079
  have hstable : (prefixWord ++ tailWord_4284079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284079).length < 2 ^ (prefixWord ++ tailWord_4284079).sum := by decide
  have hdescent : baseEnd_4284079 < baseStart_4284079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284083 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 4, 2, 2]
def baseStart_4284083 : Nat := 118140960795 + 4284083 * 2 ^ 59
def prefixEnd_4284083 : Nat := 4983230072969 + 3 ^ 40 * 4284083 * 2
def baseEnd_4284083 : Nat := 2199793742755667239260367

theorem tailTrace_4284083 : CollatzResearch.WordTrace tailWord_4284083 prefixEnd_4284083 2199793742755667239260367 := by
  unfold tailWord_4284083
  simp only [CollatzResearch.WordTrace]
  refine ⟨156253343738506428970832903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104168895825670952647221935 156253343738506428970832903)
  ·
    refine ⟨234380015607759643456249355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156253343738506428970832903 234380015607759643456249355)
    ·
      refine ⟨351570023411639465184374033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234380015607759643456249355 351570023411639465184374033)
      ·
        refine ⟨263677517558729598888280525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351570023411639465184374033 263677517558729598888280525)
        ·
          refine ⟨98879069084523599583105197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263677517558729598888280525 98879069084523599583105197)
          ·
            refine ⟨37079650906696349843664449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98879069084523599583105197 37079650906696349843664449)
            ·
              refine ⟨27809738180022262382748337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37079650906696349843664449 27809738180022262382748337)
              ·
                refine ⟨20857303635016696787061253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27809738180022262382748337 20857303635016696787061253)
                ·
                  refine ⟨3910744431565630647573985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20857303635016696787061253 3910744431565630647573985)
                  ·
                    refine ⟨2933058323674222985680489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3910744431565630647573985 2933058323674222985680489)
                    ·
                      refine ⟨2199793742755667239260367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933058323674222985680489 2199793742755667239260367)
                      ·
                        rfl

theorem cell23_4284083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2, 2].length) (baseStart_4284083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284083 prefixEnd_4284083 := by exact prefixLift 4284083
  have htrace : WordTrace (prefixWord ++ tailWord_4284083) baseStart_4284083 baseEnd_4284083 := by
    simpa [prefixWord, tailWord_4284083, baseEnd_4284083] using wordTrace_append hprefix tailTrace_4284083
  have hstable : (prefixWord ++ tailWord_4284083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284083).length < 2 ^ (prefixWord ++ tailWord_4284083).sum := by decide
  have hdescent : baseEnd_4284083 < baseStart_4284083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284087 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_4284087 : Nat := 118140960795 + 4284087 * 2 ^ 59
def prefixEnd_4284087 : Nat := 4983230072969 + 3 ^ 40 * 4284087 * 2
def baseEnd_4284087 : Nat := 2199795796678285223610349

theorem tailTrace_4284087 : CollatzResearch.WordTrace tailWord_4284087 prefixEnd_4284087 2199795796678285223610349 := by
  unfold tailWord_4284087
  simp only [CollatzResearch.WordTrace]
  refine ⟨156253489630491937653978515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104168993086994625102652343 156253489630491937653978515)
  ·
    refine ⟨234380234445737906480967773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156253489630491937653978515 234380234445737906480967773)
    ·
      refine ⟨87892587917151714930362915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234380234445737906480967773 87892587917151714930362915)
      ·
        refine ⟨131838881875727572395544373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87892587917151714930362915 131838881875727572395544373)
        ·
          refine ⟨12359895175849459912082285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131838881875727572395544373 12359895175849459912082285)
          ·
            refine ⟨4634960690943547467030857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12359895175849459912082285 4634960690943547467030857)
            ·
              refine ⟨3476220518207660600273143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634960690943547467030857 3476220518207660600273143)
              ·
                refine ⟨5214330777311490900409715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476220518207660600273143 5214330777311490900409715)
                ·
                  refine ⟨7821496165967236350614573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5214330777311490900409715 7821496165967236350614573)
                  ·
                    refine ⟨2933061062237713631480465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7821496165967236350614573 2933061062237713631480465)
                    ·
                      refine ⟨2199795796678285223610349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933061062237713631480465 2199795796678285223610349)
                      ·
                        rfl

theorem cell23_4284087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_4284087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284087 prefixEnd_4284087 := by exact prefixLift 4284087
  have htrace : WordTrace (prefixWord ++ tailWord_4284087) baseStart_4284087 baseEnd_4284087 := by
    simpa [prefixWord, tailWord_4284087, baseEnd_4284087] using wordTrace_append hprefix tailTrace_4284087
  have hstable : (prefixWord ++ tailWord_4284087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284087).length < 2 ^ (prefixWord ++ tailWord_4284087).sum := by decide
  have hdescent : baseEnd_4284087 < baseStart_4284087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284100 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_4284100 : Nat := 118140960795 + 4284100 * 2 ^ 59
def prefixEnd_4284100 : Nat := 4983230072969 + 3 ^ 40 * 4284100 * 2
def baseEnd_4284100 : Nat := 2199802471926793672747789

theorem tailTrace_4284100 : CollatzResearch.WordTrace tailWord_4284100 prefixEnd_4284100 2199802471926793672747789 := by
  unfold tailWord_4284100
  simp only [CollatzResearch.WordTrace]
  refine ⟨78126981889722420437100877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104169309186296560582801169 78126981889722420437100877)
  ·
    refine ⟨29297618208645907663912829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78126981889722420437100877 29297618208645907663912829)
    ·
      refine ⟨10986606828242215373967311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29297618208645907663912829 10986606828242215373967311)
      ·
        refine ⟨16479910242363323060950967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10986606828242215373967311 16479910242363323060950967)
        ·
          refine ⟨24719865363544984591426451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16479910242363323060950967 24719865363544984591426451)
          ·
            refine ⟨37079798045317476887139677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24719865363544984591426451 37079798045317476887139677)
            ·
              refine ⟨13904924266994053832677379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37079798045317476887139677 13904924266994053832677379)
              ·
                refine ⟨20857386400491080749016069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13904924266994053832677379 20857386400491080749016069)
                ·
                  refine ⟨3910759950092077640440513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20857386400491080749016069 3910759950092077640440513)
                  ·
                    refine ⟨2933069962569058230330385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3910759950092077640440513 2933069962569058230330385)
                    ·
                      refine ⟨2199802471926793672747789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933069962569058230330385 2199802471926793672747789)
                      ·
                        rfl

theorem cell23_4284100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_4284100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284100 prefixEnd_4284100 := by exact prefixLift 4284100
  have htrace : WordTrace (prefixWord ++ tailWord_4284100) baseStart_4284100 baseEnd_4284100 := by
    simpa [prefixWord, tailWord_4284100, baseEnd_4284100] using wordTrace_append hprefix tailTrace_4284100
  have hstable : (prefixWord ++ tailWord_4284100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284100).length < 2 ^ (prefixWord ++ tailWord_4284100).sum := by decide
  have hdescent : baseEnd_4284100 < baseStart_4284100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284119 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 7]
def baseStart_4284119 : Nat := 118140960795 + 4284119 * 2 ^ 59
def prefixEnd_4284119 : Nat := 4983230072969 + 3 ^ 40 * 4284119 * 2
def baseEnd_4284119 : Nat := 733270742686409699470067

theorem tailTrace_4284119 : CollatzResearch.WordTrace tailWord_4284119 prefixEnd_4284119 733270742686409699470067 := by
  unfold tailWord_4284119
  simp only [CollatzResearch.WordTrace]
  refine ⟨156254656766376007119143411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104169771177584004746095607 156254656766376007119143411)
  ·
    refine ⟨234381985149564010678715117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156254656766376007119143411 234381985149564010678715117)
    ·
      refine ⟨87893244431086504004518169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234381985149564010678715117 87893244431086504004518169)
      ·
        refine ⟨65919933323314878003388627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87893244431086504004518169 65919933323314878003388627)
        ·
          refine ⟨98879899984972317005082941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65919933323314878003388627 98879899984972317005082941)
          ·
            refine ⟨37079962494364618876906103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98879899984972317005082941 37079962494364618876906103)
            ·
              refine ⟨55619943741546928315359155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37079962494364618876906103 55619943741546928315359155)
              ·
                refine ⟨83429915612320392473038733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55619943741546928315359155 83429915612320392473038733)
                ·
                  refine ⟨31286218354620147177389525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83429915612320392473038733 31286218354620147177389525)
                  ·
                    refine ⟨733270742686409699470067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31286218354620147177389525 733270742686409699470067)
                    ·
                      rfl

theorem cell23_4284119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_4284119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284119 prefixEnd_4284119 := by exact prefixLift 4284119
  have htrace : WordTrace (prefixWord ++ tailWord_4284119) baseStart_4284119 baseEnd_4284119 := by
    simpa [prefixWord, tailWord_4284119, baseEnd_4284119] using wordTrace_append hprefix tailTrace_4284119
  have hstable : (prefixWord ++ tailWord_4284119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284119).length < 2 ^ (prefixWord ++ tailWord_4284119).sum := by decide
  have hdescent : baseEnd_4284119 < baseStart_4284119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284136 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_4284136 : Nat := 118140960795 + 4284136 * 2 ^ 59
def prefixEnd_4284136 : Nat := 4983230072969 + 3 ^ 40 * 4284136 * 2
def baseEnd_4284136 : Nat := 733273652410118510632541

theorem tailTrace_4284136 : CollatzResearch.WordTrace tailWord_4284136 prefixEnd_4284136 733273652410118510632541 := by
  unfold tailWord_4284136
  simp only [CollatzResearch.WordTrace]
  refine ⟨78127638403657209511256131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104170184538209612681674841 78127638403657209511256131)
  ·
    refine ⟨117191457605485814266884197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78127638403657209511256131 117191457605485814266884197)
    ·
      refine ⟨21973398301028590175040787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117191457605485814266884197 21973398301028590175040787)
      ·
        refine ⟨32960097451542885262561181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21973398301028590175040787 32960097451542885262561181)
        ·
          refine ⟨12360036544328581973460443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32960097451542885262561181 12360036544328581973460443)
          ·
            refine ⟨18540054816492872960190665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12360036544328581973460443 18540054816492872960190665)
            ·
              refine ⟨13905041112369654720142999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18540054816492872960190665 13905041112369654720142999)
              ·
                refine ⟨20857561668554482080214499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13905041112369654720142999 20857561668554482080214499)
                ·
                  refine ⟨31286342502831723120321749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20857561668554482080214499 31286342502831723120321749)
                  ·
                    refine ⟨733273652410118510632541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31286342502831723120321749 733273652410118510632541)
                    ·
                      rfl

theorem cell23_4284136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_4284136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284136 prefixEnd_4284136 := by exact prefixLift 4284136
  have htrace : WordTrace (prefixWord ++ tailWord_4284136) baseStart_4284136 baseEnd_4284136 := by
    simpa [prefixWord, tailWord_4284136, baseEnd_4284136] using wordTrace_append hprefix tailTrace_4284136
  have hstable : (prefixWord ++ tailWord_4284136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284136).length < 2 ^ (prefixWord ++ tailWord_4284136).sum := by decide
  have hdescent : baseEnd_4284136 < baseStart_4284136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284146 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4284146 : Nat := 118140960795 + 4284146 * 2 ^ 59
def prefixEnd_4284146 : Nat := 4983230072969 + 3 ^ 40 * 4284146 * 2
def baseEnd_4284146 : Nat := 2199826092036900492772577

theorem tailTrace_4284146 : CollatzResearch.WordTrace tailWord_4284146 prefixEnd_4284146 2199826092036900492772577 := by
  unfold tailWord_4284146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39063910384319547682594073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104170427691518793820250861 39063910384319547682594073)
  ·
    refine ⟨29297932788239660761945555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39063910384319547682594073 29297932788239660761945555)
    ·
      refine ⟨43946899182359491142918333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29297932788239660761945555 43946899182359491142918333)
      ·
        refine ⟨16480087193384809178594375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43946899182359491142918333 16480087193384809178594375)
        ·
          refine ⟨24720130790077213767891563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16480087193384809178594375 24720130790077213767891563)
          ·
            refine ⟨37080196185115820651837345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24720130790077213767891563 37080196185115820651837345)
            ·
              refine ⟨27810147138836865488878009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37080196185115820651837345 27810147138836865488878009)
              ·
                refine ⟨20857610354127649116658507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27810147138836865488878009 20857610354127649116658507)
                ·
                  refine ⟨31286415531191473674987761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20857610354127649116658507 31286415531191473674987761)
                  ·
                    refine ⟨23464811648393605256240821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31286415531191473674987761 23464811648393605256240821)
                    ·
                      refine ⟨2199826092036900492772577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23464811648393605256240821 2199826092036900492772577)
                      ·
                        rfl

theorem cell23_4284146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4284146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284146 prefixEnd_4284146 := by exact prefixLift 4284146
  have htrace : WordTrace (prefixWord ++ tailWord_4284146) baseStart_4284146 baseEnd_4284146 := by
    simpa [prefixWord, tailWord_4284146, baseEnd_4284146] using wordTrace_append hprefix tailTrace_4284146
  have hstable : (prefixWord ++ tailWord_4284146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284146).length < 2 ^ (prefixWord ++ tailWord_4284146).sum := by decide
  have hdescent : baseEnd_4284146 < baseStart_4284146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284179 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 10]
def baseStart_4284179 : Nat := 118140960795 + 4284179 * 2 ^ 59
def prefixEnd_4284179 : Nat := 4983230072969 + 3 ^ 40 * 4284179 * 2
def baseEnd_4284179 : Nat := 244427004099833207073325

theorem tailTrace_4284179 : CollatzResearch.WordTrace tailWord_4284179 prefixEnd_4284179 244427004099833207073325 := by
  unfold tailWord_4284179
  simp only [CollatzResearch.WordTrace]
  refine ⟨156256845146158637366327591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104171230097439091577551727 156256845146158637366327591)
  ·
    refine ⟨234385267719237956049491387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156256845146158637366327591 234385267719237956049491387)
    ·
      refine ⟨351577901578856934074237081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234385267719237956049491387 351577901578856934074237081)
      ·
        refine ⟨263683426184142700555677811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351577901578856934074237081 263683426184142700555677811)
        ·
          refine ⟨395525139276214050833516717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263683426184142700555677811 395525139276214050833516717)
          ·
            refine ⟨148321927228580269062568769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395525139276214050833516717 148321927228580269062568769)
            ·
              refine ⟨111241445421435201796926577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148321927228580269062568769 111241445421435201796926577)
              ·
                refine ⟨83431084066076401347694933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111241445421435201796926577 83431084066076401347694933)
                ·
                  refine ⟨244427004099833207073325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83431084066076401347694933 244427004099833207073325)
                  ·
                    rfl

theorem cell23_4284179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 10].length) (baseStart_4284179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284179 prefixEnd_4284179 := by exact prefixLift 4284179
  have htrace : WordTrace (prefixWord ++ tailWord_4284179) baseStart_4284179 baseEnd_4284179 := by
    simpa [prefixWord, tailWord_4284179, baseEnd_4284179] using wordTrace_append hprefix tailTrace_4284179
  have hstable : (prefixWord ++ tailWord_4284179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284179).length < 2 ^ (prefixWord ++ tailWord_4284179).sum := by decide
  have hdescent : baseEnd_4284179 < baseStart_4284179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284193 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4284193 : Nat := 118140960795 + 4284193 * 2 ^ 59
def prefixEnd_4284193 : Nat := 4983230072969 + 3 ^ 40 * 4284193 * 2
def baseEnd_4284193 : Nat := 2199850225627661808884861

theorem tailTrace_4284193 : CollatzResearch.WordTrace tailWord_4284193 prefixEnd_4284193 2199850225627661808884861 := by
  unfold tailWord_4284193
  simp only [CollatzResearch.WordTrace]
  refine ⟨156257355768107917757337233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104171570512071945171558155 156257355768107917757337233)
  ·
    refine ⟨117193016826080938318002925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156257355768107917757337233 117193016826080938318002925)
    ·
      refine ⟨43947381309780351869251097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117193016826080938318002925 43947381309780351869251097)
      ·
        refine ⟨32960535982335263901938323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43947381309780351869251097 32960535982335263901938323)
        ·
          refine ⟨49440803973502895852907485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32960535982335263901938323 49440803973502895852907485)
          ·
            refine ⟨18540301490063585944840307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49440803973502895852907485 18540301490063585944840307)
            ·
              refine ⟨27810452235095378917260461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18540301490063585944840307 27810452235095378917260461)
              ·
                refine ⟨10428919588160767093972673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27810452235095378917260461 10428919588160767093972673)
                ·
                  refine ⟨7821689691120575320479505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10428919588160767093972673 7821689691120575320479505)
                  ·
                    refine ⟨5866267268340431490359629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7821689691120575320479505 5866267268340431490359629)
                    ·
                      refine ⟨2199850225627661808884861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866267268340431490359629 2199850225627661808884861)
                      ·
                        rfl

theorem cell23_4284193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4284193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284193 prefixEnd_4284193 := by exact prefixLift 4284193
  have htrace : WordTrace (prefixWord ++ tailWord_4284193) baseStart_4284193 baseEnd_4284193 := by
    simpa [prefixWord, tailWord_4284193, baseEnd_4284193] using wordTrace_append hprefix tailTrace_4284193
  have hstable : (prefixWord ++ tailWord_4284193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284193).length < 2 ^ (prefixWord ++ tailWord_4284193).sum := by decide
  have hdescent : baseEnd_4284193 < baseStart_4284193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284233 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 5, 2]
def baseStart_4284233 : Nat := 118140960795 + 4284233 * 2 ^ 59
def prefixEnd_4284233 : Nat := 4983230072969 + 3 ^ 40 * 4284233 * 2
def baseEnd_4284233 : Nat := 2199870764853841652384677

theorem tailTrace_4284233 : CollatzResearch.WordTrace tailWord_4284233 prefixEnd_4284233 2199870764853841652384677 := by
  unfold tailWord_4284233
  simp only [CollatzResearch.WordTrace]
  refine ⟨156258814687963004588793353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104172543125308669725862235 156258814687963004588793353)
  ·
    refine ⟨117194111015972253441595015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156258814687963004588793353 117194111015972253441595015)
    ·
      refine ⟨175791166523958380162392523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117194111015972253441595015 175791166523958380162392523)
      ·
        refine ⟨263686749785937570243588785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175791166523958380162392523 263686749785937570243588785)
        ·
          refine ⟨197765062339453177682691589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263686749785937570243588785 197765062339453177682691589)
          ·
            refine ⟨37080949188647470815504673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197765062339453177682691589 37080949188647470815504673)
            ·
              refine ⟨27810711891485603111628505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37080949188647470815504673 27810711891485603111628505)
              ·
                refine ⟨20858033918614202333721379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27810711891485603111628505 20858033918614202333721379)
                ·
                  refine ⟨31287050877921303500582069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20858033918614202333721379 31287050877921303500582069)
                  ·
                    refine ⟨2933161019805122203179569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31287050877921303500582069 2933161019805122203179569)
                    ·
                      refine ⟨2199870764853841652384677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933161019805122203179569 2199870764853841652384677)
                      ·
                        rfl

theorem cell23_4284233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5, 2].length) (baseStart_4284233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284233 prefixEnd_4284233 := by exact prefixLift 4284233
  have htrace : WordTrace (prefixWord ++ tailWord_4284233) baseStart_4284233 baseEnd_4284233 := by
    simpa [prefixWord, tailWord_4284233, baseEnd_4284233] using wordTrace_append hprefix tailTrace_4284233
  have hstable : (prefixWord ++ tailWord_4284233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284233).length < 2 ^ (prefixWord ++ tailWord_4284233).sum := by decide
  have hdescent : baseEnd_4284233 < baseStart_4284233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284257 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_4284257 : Nat := 118140960795 + 4284257 * 2 ^ 59
def prefixEnd_4284257 : Nat := 4983230072969 + 3 ^ 40 * 4284257 * 2
def baseEnd_4284257 : Nat := 2199883088389549558484567

theorem tailTrace_4284257 : CollatzResearch.WordTrace tailWord_4284257 prefixEnd_4284257 2199883088389549558484567 := by
  unfold tailWord_4284257
  simp only [CollatzResearch.WordTrace]
  refine ⟨156259690039876056687667025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104173126693250704458444683 156259690039876056687667025)
  ·
    refine ⟨117194767529907042515750269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156259690039876056687667025 117194767529907042515750269)
    ·
      refine ⟨43948037823715140943406351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117194767529907042515750269 43948037823715140943406351)
      ·
        refine ⟨65922056735572711415109527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43948037823715140943406351 65922056735572711415109527)
        ·
          refine ⟨98883085103359067122664291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65922056735572711415109527 98883085103359067122664291)
          ·
            refine ⟨148324627655038600683996437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98883085103359067122664291 148324627655038600683996437)
            ·
              refine ⟨6952716921329934407062333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148324627655038600683996437 6952716921329934407062333)
              ·
                refine ⟨2607268845498725402648375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6952716921329934407062333 2607268845498725402648375)
                ·
                  refine ⟨3910903268248088103972563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607268845498725402648375 3910903268248088103972563)
                  ·
                    refine ⟨5866354902372132155958845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910903268248088103972563 5866354902372132155958845)
                    ·
                      refine ⟨2199883088389549558484567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866354902372132155958845 2199883088389549558484567)
                      ·
                        rfl

theorem cell23_4284257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_4284257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284257 prefixEnd_4284257 := by exact prefixLift 4284257
  have htrace : WordTrace (prefixWord ++ tailWord_4284257) baseStart_4284257 baseEnd_4284257 := by
    simpa [prefixWord, tailWord_4284257, baseEnd_4284257] using wordTrace_append hprefix tailTrace_4284257
  have hstable : (prefixWord ++ tailWord_4284257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284257).length < 2 ^ (prefixWord ++ tailWord_4284257).sum := by decide
  have hdescent : baseEnd_4284257 < baseStart_4284257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284260 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_4284260 : Nat := 118140960795 + 4284260 * 2 ^ 59
def prefixEnd_4284260 : Nat := 4983230072969 + 3 ^ 40 * 4284260 * 2
def baseEnd_4284260 : Nat := 733294876277171015582351

theorem tailTrace_4284260 : CollatzResearch.WordTrace tailWord_4284260 prefixEnd_4284260 733294876277171015582351 := by
  unfold tailWord_4284260
  simp only [CollatzResearch.WordTrace]
  refine ⟨78129899729432594100013117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104173199639243458800017489 78129899729432594100013117)
  ·
    refine ⟨29298712398537222787504919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78129899729432594100013117 29298712398537222787504919)
    ·
      refine ⟨43948068597805834181257379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29298712398537222787504919 43948068597805834181257379)
      ·
        refine ⟨65922102896708751271886069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43948068597805834181257379 65922102896708751271886069)
        ·
          refine ⟨6180197146566445431739319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65922102896708751271886069 6180197146566445431739319)
          ·
            refine ⟨9270295719849668147608979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180197146566445431739319 9270295719849668147608979)
            ·
              refine ⟨13905443579774502221413469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9270295719849668147608979 13905443579774502221413469)
              ·
                refine ⟨5214541342415438333030051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13905443579774502221413469 5214541342415438333030051)
                ·
                  refine ⟨7821812013623157499545077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5214541342415438333030051 7821812013623157499545077)
                  ·
                    refine ⟨733294876277171015582351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7821812013623157499545077 733294876277171015582351)
                    ·
                      rfl

theorem cell23_4284260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_4284260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284260 prefixEnd_4284260 := by exact prefixLift 4284260
  have htrace : WordTrace (prefixWord ++ tailWord_4284260) baseStart_4284260 baseEnd_4284260 := by
    simpa [prefixWord, tailWord_4284260, baseEnd_4284260] using wordTrace_append hprefix tailTrace_4284260
  have hstable : (prefixWord ++ tailWord_4284260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284260).length < 2 ^ (prefixWord ++ tailWord_4284260).sum := by decide
  have hdescent : baseEnd_4284260 < baseStart_4284260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284273 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_4284273 : Nat := 118140960795 + 4284273 * 2 ^ 59
def prefixEnd_4284273 : Nat := 4983230072969 + 3 ^ 40 * 4284273 * 2
def baseEnd_4284273 : Nat := 733297101360007165294831

theorem tailTrace_4284273 : CollatzResearch.WordTrace tailWord_4284273 prefixEnd_4284273 733297101360007165294831 := by
  unfold tailWord_4284273
  simp only [CollatzResearch.WordTrace]
  refine ⟨156260273607818091420249473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104173515738545394280166315 156260273607818091420249473)
  ·
    refine ⟨117195205205863568565187105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156260273607818091420249473 117195205205863568565187105)
    ·
      refine ⟨87896403904397676423890329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117195205205863568565187105 87896403904397676423890329)
      ·
        refine ⟨65922302928298257317917747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87896403904397676423890329 65922302928298257317917747)
        ·
          refine ⟨98883454392447385976876621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65922302928298257317917747 98883454392447385976876621)
          ·
            refine ⟨37081295397167769741328733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98883454392447385976876621 37081295397167769741328733)
            ·
              refine ⟨13905485773937913652998275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37081295397167769741328733 13905485773937913652998275)
              ·
                refine ⟨20858228660906870479497413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13905485773937913652998275 20858228660906870479497413)
                ·
                  refine ⟨3910917873920038214905765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20858228660906870479497413 3910917873920038214905765)
                  ·
                    refine ⟨733297101360007165294831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910917873920038214905765 733297101360007165294831)
                    ·
                      rfl

theorem cell23_4284273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_4284273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284273 prefixEnd_4284273 := by exact prefixLift 4284273
  have htrace : WordTrace (prefixWord ++ tailWord_4284273) baseStart_4284273 baseEnd_4284273 := by
    simpa [prefixWord, tailWord_4284273, baseEnd_4284273] using wordTrace_append hprefix tailTrace_4284273
  have hstable : (prefixWord ++ tailWord_4284273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284273).length < 2 ^ (prefixWord ++ tailWord_4284273).sum := by decide
  have hdescent : baseEnd_4284273 < baseStart_4284273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284313 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_4284313 : Nat := 118140960795 + 4284313 * 2 ^ 59
def prefixEnd_4284313 : Nat := 4983230072969 + 3 ^ 40 * 4284313 * 2
def baseEnd_4284313 : Nat := 2199911843306201339384309

theorem tailTrace_4284313 : CollatzResearch.WordTrace tailWord_4284313 prefixEnd_4284313 2199911843306201339384309 := by
  unfold tailWord_4284313
  simp only [CollatzResearch.WordTrace]
  refine ⟨156261732527673178251705593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104174488351782118834470395 156261732527673178251705593)
  ·
    refine ⟨117196299395754883688779195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156261732527673178251705593 117196299395754883688779195)
    ·
      refine ⟨175794449093632325533168793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117196299395754883688779195 175794449093632325533168793)
      ·
        refine ⟨131845836820224244149876595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175794449093632325533168793 131845836820224244149876595)
        ·
          refine ⟨197768755230336366224814893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131845836820224244149876595 197768755230336366224814893)
          ·
            refine ⟨74163283211376137334305585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197768755230336366224814893 74163283211376137334305585)
            ·
              refine ⟨55622462408532103000729189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74163283211376137334305585 55622462408532103000729189)
              ·
                refine ⟨10429211701599769312636723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55622462408532103000729189 10429211701599769312636723)
                ·
                  refine ⟨15643817552399653968955085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10429211701599769312636723 15643817552399653968955085)
                  ·
                    refine ⟨5866431582149870238358157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15643817552399653968955085 5866431582149870238358157)
                    ·
                      refine ⟨2199911843306201339384309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866431582149870238358157 2199911843306201339384309)
                      ·
                        rfl

theorem cell23_4284313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_4284313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284313 prefixEnd_4284313 := by exact prefixLift 4284313
  have htrace : WordTrace (prefixWord ++ tailWord_4284313) baseStart_4284313 baseEnd_4284313 := by
    simpa [prefixWord, tailWord_4284313, baseEnd_4284313] using wordTrace_append hprefix tailTrace_4284313
  have hstable : (prefixWord ++ tailWord_4284313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284313).length < 2 ^ (prefixWord ++ tailWord_4284313).sum := by decide
  have hdescent : baseEnd_4284313 < baseStart_4284313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284397 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_4284397 : Nat := 118140960795 + 4284397 * 2 ^ 59
def prefixEnd_4284397 : Nat := 4983230072969 + 3 ^ 40 * 4284397 * 2
def baseEnd_4284397 : Nat := 733318325227059670244641

theorem tailTrace_4284397 : CollatzResearch.WordTrace tailWord_4284397 prefixEnd_4284397 733318325227059670244641 := by
  unfold tailWord_4284397
  simp only [CollatzResearch.WordTrace]
  refine ⟨156264796259368860597763445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104176530839579240398508963 156264796259368860597763445)
  ·
    refine ⟨14649824649315830681040323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156264796259368860597763445 14649824649315830681040323)
    ·
      refine ⟨21974736973973746021560485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14649824649315830681040323 21974736973973746021560485)
      ·
        refine ⟨4120263182620077379042591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21974736973973746021560485 4120263182620077379042591)
        ·
          refine ⟨6180394773930116068563887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120263182620077379042591 6180394773930116068563887)
          ·
            refine ⟨9270592160895174102845831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180394773930116068563887 9270592160895174102845831)
            ·
              refine ⟨13905888241342761154268747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9270592160895174102845831 13905888241342761154268747)
              ·
                refine ⟨20858832362014141731403121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13905888241342761154268747 20858832362014141731403121)
                ·
                  refine ⟨15644124271510606298552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20858832362014141731403121 15644124271510606298552341)
                  ·
                    refine ⟨733318325227059670244641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15644124271510606298552341 733318325227059670244641)
                    ·
                      rfl

theorem cell23_4284397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_4284397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284397 prefixEnd_4284397 := by exact prefixLift 4284397
  have htrace : WordTrace (prefixWord ++ tailWord_4284397) baseStart_4284397 baseEnd_4284397 := by
    simpa [prefixWord, tailWord_4284397, baseEnd_4284397] using wordTrace_append hprefix tailTrace_4284397
  have hstable : (prefixWord ++ tailWord_4284397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284397).length < 2 ^ (prefixWord ++ tailWord_4284397).sum := by decide
  have hdescent : baseEnd_4284397 < baseStart_4284397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284460 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_4284460 : Nat := 118140960795 + 4284460 * 2 ^ 59
def prefixEnd_4284460 : Nat := 4983230072969 + 3 ^ 40 * 4284460 * 2
def baseEnd_4284460 : Nat := 2199987324962412264246133

theorem tailTrace_4284460 : CollatzResearch.WordTrace tailWord_4284460 prefixEnd_4284460 2199987324962412264246133 := by
  unfold tailWord_4284460
  simp only [CollatzResearch.WordTrace]
  refine ⟨78133547029070311178653417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104178062705427081571537889 78133547029070311178653417)
  ·
    refine ⟨58600160271802733383990063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78133547029070311178653417 58600160271802733383990063)
    ·
      refine ⟨87900240407704100075985095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58600160271802733383990063 87900240407704100075985095)
      ·
        refine ⟨131850360611556150113977643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87900240407704100075985095 131850360611556150113977643)
        ·
          refine ⟨197775540917334225170966465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131850360611556150113977643 197775540917334225170966465)
          ·
            refine ⟨148331655688000668878224849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197775540917334225170966465 148331655688000668878224849)
            ·
              refine ⟨111248741766000501658668637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148331655688000668878224849 111248741766000501658668637)
              ·
                refine ⟨41718278162250188122000739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111248741766000501658668637 41718278162250188122000739)
                ·
                  refine ⟨62577417243375282183001109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41718278162250188122000739 62577417243375282183001109)
                  ·
                    refine ⟨2933316433283216352328177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62577417243375282183001109 2933316433283216352328177)
                    ·
                      refine ⟨2199987324962412264246133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933316433283216352328177 2199987324962412264246133)
                      ·
                        rfl

theorem cell23_4284460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_4284460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284460 prefixEnd_4284460 := by exact prefixLift 4284460
  have htrace : WordTrace (prefixWord ++ tailWord_4284460) baseStart_4284460 baseEnd_4284460 := by
    simpa [prefixWord, tailWord_4284460, baseEnd_4284460] using wordTrace_append hprefix tailTrace_4284460
  have hstable : (prefixWord ++ tailWord_4284460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284460).length < 2 ^ (prefixWord ++ tailWord_4284460).sum := by decide
  have hdescent : baseEnd_4284460 < baseStart_4284460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284470 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4284470 : Nat := 118140960795 + 4284470 * 2 ^ 59
def prefixEnd_4284470 : Nat := 4983230072969 + 3 ^ 40 * 4284470 * 2
def baseEnd_4284470 : Nat := 733330819922985741707029

theorem tailTrace_4284470 : CollatzResearch.WordTrace tailWord_4284470 prefixEnd_4284470 733330819922985741707029 := by
  unfold tailWord_4284470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9766716174256524629073179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104178305858736262710113909 9766716174256524629073179)
  ·
    refine ⟨14650074261384786943609769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9766716174256524629073179 14650074261384786943609769)
    ·
      refine ⟨10987555696038590207707327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14650074261384786943609769 10987555696038590207707327)
      ·
        refine ⟨16481333544057885311560991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10987555696038590207707327 16481333544057885311560991)
        ·
          refine ⟨24722000316086827967341487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16481333544057885311560991 24722000316086827967341487)
          ·
            refine ⟨37083000474130241951012231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24722000316086827967341487 37083000474130241951012231)
            ·
              refine ⟨55624500711195362926518347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37083000474130241951012231 55624500711195362926518347)
              ·
                refine ⟨83436751066793044389777521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55624500711195362926518347 83436751066793044389777521)
                ·
                  refine ⟨62577563300094783292333141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83436751066793044389777521 62577563300094783292333141)
                  ·
                    refine ⟨733330819922985741707029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62577563300094783292333141 733330819922985741707029)
                    ·
                      rfl

theorem cell23_4284470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4284470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284470 prefixEnd_4284470 := by exact prefixLift 4284470
  have htrace : WordTrace (prefixWord ++ tailWord_4284470) baseStart_4284470 baseEnd_4284470 := by
    simpa [prefixWord, tailWord_4284470, baseEnd_4284470] using wordTrace_append hprefix tailTrace_4284470
  have hstable : (prefixWord ++ tailWord_4284470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284470).length < 2 ^ (prefixWord ++ tailWord_4284470).sum := by decide
  have hdescent : baseEnd_4284470 < baseStart_4284470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284480 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_4284480 : Nat := 118140960795 + 4284480 * 2 ^ 59
def prefixEnd_4284480 : Nat := 4983230072969 + 3 ^ 40 * 4284480 * 2
def baseEnd_4284480 : Nat := 2199997594575502185996041

theorem tailTrace_4284480 : CollatzResearch.WordTrace tailWord_4284480 prefixEnd_4284480 2199997594575502185996041 := by
  unfold tailWord_4284480
  simp only [CollatzResearch.WordTrace]
  refine ⟨78133911759034082886517447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104178549012045443848689929 78133911759034082886517447)
  ·
    refine ⟨117200867638551124329776171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78133911759034082886517447 117200867638551124329776171)
    ·
      refine ⟨175801301457826686494664257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117200867638551124329776171 175801301457826686494664257)
      ·
        refine ⟨131850976093370014870998193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175801301457826686494664257 131850976093370014870998193)
        ·
          refine ⟨98888232070027511153248645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131850976093370014870998193 98888232070027511153248645)
          ·
            refine ⟨18541543513130158341234121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98888232070027511153248645 18541543513130158341234121)
            ·
              refine ⟨13906157634847618755925591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18541543513130158341234121 13906157634847618755925591)
              ·
                refine ⟨20859236452271428133888387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13906157634847618755925591 20859236452271428133888387)
                ·
                  refine ⟨31288854678407142200832581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20859236452271428133888387 31288854678407142200832581)
                  ·
                    refine ⟨5866660252201339162656109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31288854678407142200832581 5866660252201339162656109)
                    ·
                      refine ⟨2199997594575502185996041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866660252201339162656109 2199997594575502185996041)
                      ·
                        rfl

theorem cell23_4284480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_4284480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284480 prefixEnd_4284480 := by exact prefixLift 4284480
  have htrace : WordTrace (prefixWord ++ tailWord_4284480) baseStart_4284480 baseEnd_4284480 := by
    simpa [prefixWord, tailWord_4284480, baseEnd_4284480] using wordTrace_append hprefix tailTrace_4284480
  have hstable : (prefixWord ++ tailWord_4284480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284480).length < 2 ^ (prefixWord ++ tailWord_4284480).sum := by decide
  have hdescent : baseEnd_4284480 < baseStart_4284480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284500 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 6]
def baseStart_4284500 : Nat := 118140960795 + 4284500 * 2 ^ 59
def prefixEnd_4284500 : Nat := 4983230072969 + 3 ^ 40 * 4284500 * 2
def baseEnd_4284500 : Nat := 244445318243176900860661

theorem tailTrace_4284500 : CollatzResearch.WordTrace tailWord_4284500 prefixEnd_4284500 244445318243176900860661 := by
  unfold tailWord_4284500
  simp only [CollatzResearch.WordTrace]
  refine ⟨78134276488997854594381477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104179035318663806125841969 78134276488997854594381477)
  ·
    refine ⟨14650176841687097736446527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78134276488997854594381477 14650176841687097736446527)
    ·
      refine ⟨21975265262530646604669791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14650176841687097736446527 21975265262530646604669791)
      ·
        refine ⟨32962897893795969907004687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21975265262530646604669791 32962897893795969907004687)
        ·
          refine ⟨49444346840693954860507031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32962897893795969907004687 49444346840693954860507031)
          ·
            refine ⟨74166520261040932290760547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49444346840693954860507031 74166520261040932290760547)
            ·
              refine ⟨111249780391561398436140821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74166520261040932290760547 111249780391561398436140821)
              ·
                refine ⟨5214833455854440551694101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111249780391561398436140821 5214833455854440551694101)
                ·
                  refine ⟨244445318243176900860661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5214833455854440551694101 244445318243176900860661)
                  ·
                    rfl

theorem cell23_4284500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_4284500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284500 prefixEnd_4284500 := by exact prefixLift 4284500
  have htrace : WordTrace (prefixWord ++ tailWord_4284500) baseStart_4284500 baseEnd_4284500 := by
    simpa [prefixWord, tailWord_4284500, baseEnd_4284500] using wordTrace_append hprefix tailTrace_4284500
  have hstable : (prefixWord ++ tailWord_4284500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284500).length < 2 ^ (prefixWord ++ tailWord_4284500).sum := by decide
  have hdescent : baseEnd_4284500 < baseStart_4284500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284503 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_4284503 : Nat := 118140960795 + 4284503 * 2 ^ 59
def prefixEnd_4284503 : Nat := 4983230072969 + 3 ^ 40 * 4284503 * 2
def baseEnd_4284503 : Nat := 2200009404630555596008435

theorem tailTrace_4284503 : CollatzResearch.WordTrace tailWord_4284503 prefixEnd_4284503 2200009404630555596008435 := by
  unfold tailWord_4284503
  simp only [CollatzResearch.WordTrace]
  refine ⟨156268662396984840701122163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104179108264656560467414775 156268662396984840701122163)
  ·
    refine ⟨234402993595477261051683245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156268662396984840701122163 234402993595477261051683245)
    ·
      refine ⟨87901122598303972894381217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234402993595477261051683245 87901122598303972894381217)
      ·
        refine ⟨65925841948727979670785913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87901122598303972894381217 65925841948727979670785913)
        ·
          refine ⟨49444381461545984753089435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65925841948727979670785913 49444381461545984753089435)
          ·
            refine ⟨74166572192318977129634153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49444381461545984753089435 74166572192318977129634153)
            ·
              refine ⟨55624929144239232847225615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74166572192318977129634153 55624929144239232847225615)
              ·
                refine ⟨83437393716358849270838423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55624929144239232847225615 83437393716358849270838423)
                ·
                  refine ⟨125156090574538273906257635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83437393716358849270838423 125156090574538273906257635)
                  ·
                    refine ⟨187734135861807410859386453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125156090574538273906257635 187734135861807410859386453)
                    ·
                      refine ⟨2200009404630555596008435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187734135861807410859386453 2200009404630555596008435)
                      ·
                        rfl

theorem cell23_4284503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_4284503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284503 prefixEnd_4284503 := by exact prefixLift 4284503
  have htrace : WordTrace (prefixWord ++ tailWord_4284503) baseStart_4284503 baseEnd_4284503 := by
    simpa [prefixWord, tailWord_4284503, baseEnd_4284503] using wordTrace_append hprefix tailTrace_4284503
  have hstable : (prefixWord ++ tailWord_4284503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284503).length < 2 ^ (prefixWord ++ tailWord_4284503).sum := by decide
  have hdescent : baseEnd_4284503 < baseStart_4284503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284513 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_4284513 : Nat := 118140960795 + 4284513 * 2 ^ 59
def prefixEnd_4284513 : Nat := 4983230072969 + 3 ^ 40 * 4284513 * 2
def baseEnd_4284513 : Nat := 733338179812366852294463

theorem tailTrace_4284513 : CollatzResearch.WordTrace tailWord_4284513 prefixEnd_4284513 733338179812366852294463 := by
  unfold tailWord_4284513
  simp only [CollatzResearch.WordTrace]
  refine ⟨156269027126948612408986193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104179351417965741605990795 156269027126948612408986193)
  ·
    refine ⟨117201770345211459306739645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156269027126948612408986193 117201770345211459306739645)
    ·
      refine ⟨43950663879454297240027367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117201770345211459306739645 43950663879454297240027367)
      ·
        refine ⟨65925995819181445860041051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43950663879454297240027367 65925995819181445860041051)
        ·
          refine ⟨98888993728772168790061577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65925995819181445860041051 98888993728772168790061577)
          ·
            refine ⟨74166745296579126592546183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98888993728772168790061577 74166745296579126592546183)
            ·
              refine ⟨111250117944868689888819275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74166745296579126592546183 111250117944868689888819275)
              ·
                refine ⟨166875176917303034833228913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111250117944868689888819275 166875176917303034833228913)
                ·
                  refine ⟨125156382687977276124921685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166875176917303034833228913 125156382687977276124921685)
                  ·
                    refine ⟨733338179812366852294463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125156382687977276124921685 733338179812366852294463)
                    ·
                      rfl

theorem cell23_4284513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_4284513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284513 prefixEnd_4284513 := by exact prefixLift 4284513
  have htrace : WordTrace (prefixWord ++ tailWord_4284513) baseStart_4284513 baseEnd_4284513 := by
    simpa [prefixWord, tailWord_4284513, baseEnd_4284513] using wordTrace_append hprefix tailTrace_4284513
  have hstable : (prefixWord ++ tailWord_4284513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284513).length < 2 ^ (prefixWord ++ tailWord_4284513).sum := by decide
  have hdescent : baseEnd_4284513 < baseStart_4284513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284517 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 6]
def baseStart_4284517 : Nat := 118140960795 + 4284517 * 2 ^ 59
def prefixEnd_4284517 : Nat := 4983230072969 + 3 ^ 40 * 4284517 * 2
def baseEnd_4284517 : Nat := 244446288151079837914819

theorem tailTrace_4284517 : CollatzResearch.WordTrace tailWord_4284517 prefixEnd_4284517 244446288151079837914819 := by
  unfold tailWord_4284517
  simp only [CollatzResearch.WordTrace]
  refine ⟨156269173018934121092131805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104179448679289414061421203 156269173018934121092131805)
  ·
    refine ⟨58600939882100295409549427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156269173018934121092131805 58600939882100295409549427)
    ·
      refine ⟨87901409823150443114324141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58600939882100295409549427 87901409823150443114324141)
      ·
        refine ⟨32963028683681416167871553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87901409823150443114324141 32963028683681416167871553)
        ·
          refine ⟨24722271512761062125903665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32963028683681416167871553 24722271512761062125903665)
          ·
            refine ⟨18541703634570796594427749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24722271512761062125903665 18541703634570796594427749)
            ·
              refine ⟨3476569431482024361455203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18541703634570796594427749 3476569431482024361455203)
              ·
                refine ⟨5214854147223036542182805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476569431482024361455203 5214854147223036542182805)
                ·
                  refine ⟨244446288151079837914819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5214854147223036542182805 244446288151079837914819)
                  ·
                    rfl

theorem cell23_4284517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_4284517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284517 prefixEnd_4284517 := by exact prefixLift 4284517
  have htrace : WordTrace (prefixWord ++ tailWord_4284517) baseStart_4284517 baseEnd_4284517 := by
    simpa [prefixWord, tailWord_4284517, baseEnd_4284517] using wordTrace_append hprefix tailTrace_4284517
  have hstable : (prefixWord ++ tailWord_4284517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284517).length < 2 ^ (prefixWord ++ tailWord_4284517).sum := by decide
  have hdescent : baseEnd_4284517 < baseStart_4284517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 1, 1, 3]
def baseStart_4284544 : Nat := 118140960795 + 4284544 * 2 ^ 59
def prefixEnd_4284544 : Nat := 4983230072969 + 3 ^ 40 * 4284544 * 2
def baseEnd_4284544 : Nat := 2200030457337389935595747

theorem tailTrace_4284544 : CollatzResearch.WordTrace tailWord_4284544 prefixEnd_4284544 2200030457337389935595747 := by
  unfold tailWord_4284544
  simp only [CollatzResearch.WordTrace]
  refine ⟨78135078894918152351682343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104180105193224203135576457 78135078894918152351682343)
  ·
    refine ⟨117202618342377228527523515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78135078894918152351682343 117202618342377228527523515)
    ·
      refine ⟨175803927513565842791285273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117202618342377228527523515 175803927513565842791285273)
      ·
        refine ⟨131852945635174382093463955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175803927513565842791285273 131852945635174382093463955)
        ·
          refine ⟨197779418452761573140195933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131852945635174382093463955 197779418452761573140195933)
          ·
            refine ⟨74167281919785589927573475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197779418452761573140195933 74167281919785589927573475)
            ·
              refine ⟨111250922879678384891360213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74167281919785589927573475 111250922879678384891360213)
              ·
                refine ⟨2607443504992462145891255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111250922879678384891360213 2607443504992462145891255)
                ·
                  refine ⟨3911165257488693218836883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607443504992462145891255 3911165257488693218836883)
                  ·
                    refine ⟨5866747886233039828255325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3911165257488693218836883 5866747886233039828255325)
                    ·
                      refine ⟨2200030457337389935595747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866747886233039828255325 2200030457337389935595747)
                      ·
                        rfl

theorem cell23_4284544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_4284544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284544 prefixEnd_4284544 := by exact prefixLift 4284544
  have htrace : WordTrace (prefixWord ++ tailWord_4284544) baseStart_4284544 baseEnd_4284544 := by
    simpa [prefixWord, tailWord_4284544, baseEnd_4284544] using wordTrace_append hprefix tailTrace_4284544
  have hstable : (prefixWord ++ tailWord_4284544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284544).length < 2 ^ (prefixWord ++ tailWord_4284544).sum := by decide
  have hdescent : baseEnd_4284544 < baseStart_4284544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284554 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4284554 : Nat := 118140960795 + 4284554 * 2 ^ 59
def prefixEnd_4284554 : Nat := 4983230072969 + 3 ^ 40 * 4284554 * 2
def baseEnd_4284554 : Nat := 2200035592143934896470701

theorem tailTrace_4284554 : CollatzResearch.WordTrace tailWord_4284554 prefixEnd_4284554 2200035592143934896470701 := by
  unfold tailWord_4284554
  simp only [CollatzResearch.WordTrace]
  refine ⟨39067630629950019102807179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104180348346533384274152477 39067630629950019102807179)
  ·
    refine ⟨58601445944925028654210769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39067630629950019102807179 58601445944925028654210769)
    ·
      refine ⟨43951084458693771490658077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58601445944925028654210769 43951084458693771490658077)
      ·
        refine ⟨16481656672010164308996779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43951084458693771490658077 16481656672010164308996779)
        ·
          refine ⟨24722485008015246463495169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16481656672010164308996779 24722485008015246463495169)
          ·
            refine ⟨18541863756011434847621377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24722485008015246463495169 18541863756011434847621377)
            ·
              refine ⟨13906397817008576135716033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18541863756011434847621377 13906397817008576135716033)
              ·
                refine ⟨10429798362756432101787025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13906397817008576135716033 10429798362756432101787025)
                ·
                  refine ⟨7822348772067324076340269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10429798362756432101787025 7822348772067324076340269)
                  ·
                    refine ⟨2933380789525246528627601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7822348772067324076340269 2933380789525246528627601)
                    ·
                      refine ⟨2200035592143934896470701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933380789525246528627601 2200035592143934896470701)
                      ·
                        rfl

theorem cell23_4284554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4284554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284554 prefixEnd_4284554 := by exact prefixLift 4284554
  have htrace : WordTrace (prefixWord ++ tailWord_4284554) baseStart_4284554 baseEnd_4284554 := by
    simpa [prefixWord, tailWord_4284554, baseEnd_4284554] using wordTrace_append hprefix tailTrace_4284554
  have hstable : (prefixWord ++ tailWord_4284554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284554).length < 2 ^ (prefixWord ++ tailWord_4284554).sum := by decide
  have hdescent : baseEnd_4284554 < baseStart_4284554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284577 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_4284577 : Nat := 118140960795 + 4284577 * 2 ^ 59
def prefixEnd_4284577 : Nat := 4983230072969 + 3 ^ 40 * 4284577 * 2
def baseEnd_4284577 : Nat := 733349134066329435494365

theorem tailTrace_4284577 : CollatzResearch.WordTrace tailWord_4284577 prefixEnd_4284577 733349134066329435494365 := by
  unfold tailWord_4284577
  simp only [CollatzResearch.WordTrace]
  refine ⟨156271361398716751339315985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104180907599144500892877323 156271361398716751339315985)
  ·
    refine ⟨117203521049037563504486989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156271361398716751339315985 117203521049037563504486989)
    ·
      refine ⟨43951320393389086314182621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117203521049037563504486989 43951320393389086314182621)
      ·
        refine ⟨16481745147520907367818483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43951320393389086314182621 16481745147520907367818483)
        ·
          refine ⟨24722617721281361051727725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16481745147520907367818483 24722617721281361051727725)
          ·
            refine ⟨9270981645480510394397897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24722617721281361051727725 9270981645480510394397897)
            ·
              refine ⟨6953236234110382795798423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9270981645480510394397897 6953236234110382795798423)
              ·
                refine ⟨10429854351165574193697635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953236234110382795798423 10429854351165574193697635)
                ·
                  refine ⟨15644781526748361290546453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10429854351165574193697635 15644781526748361290546453)
                  ·
                    refine ⟨733349134066329435494365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15644781526748361290546453 733349134066329435494365)
                    ·
                      rfl

theorem cell23_4284577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_4284577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284577 prefixEnd_4284577 := by exact prefixLift 4284577
  have htrace : WordTrace (prefixWord ++ tailWord_4284577) baseStart_4284577 baseEnd_4284577 := by
    simpa [prefixWord, tailWord_4284577, baseEnd_4284577] using wordTrace_append hprefix tailTrace_4284577
  have hstable : (prefixWord ++ tailWord_4284577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284577).length < 2 ^ (prefixWord ++ tailWord_4284577).sum := by decide
  have hdescent : baseEnd_4284577 < baseStart_4284577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284634 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_4284634 : Nat := 118140960795 + 4284634 * 2 ^ 59
def prefixEnd_4284634 : Nat := 4983230072969 + 3 ^ 40 * 4284634 * 2
def baseEnd_4284634 : Nat := 2200076670596294583470333

theorem tailTrace_4284634 : CollatzResearch.WordTrace tailWord_4284634 prefixEnd_4284634 2200076670596294583470333 := by
  unfold tailWord_4284634
  simp only [CollatzResearch.WordTrace]
  refine ⟨39068360089877562518535239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104182293573006833382760637 39068360089877562518535239)
  ·
    refine ⟨58602540134816343777802859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39068360089877562518535239 58602540134816343777802859)
    ·
      refine ⟨87903810202224515666704289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58602540134816343777802859 87903810202224515666704289)
      ·
        refine ⟨65927857651668386750028217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87903810202224515666704289 65927857651668386750028217)
        ·
          refine ⟨49445893238751290062521163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65927857651668386750028217 49445893238751290062521163)
          ·
            refine ⟨74168839858126935093781745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49445893238751290062521163 74168839858126935093781745)
            ·
              refine ⟨55626629893595201320336309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74168839858126935093781745 55626629893595201320336309)
              ·
                refine ⟨5214996552524550123781529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55626629893595201320336309 5214996552524550123781529)
                ·
                  refine ⟨3911247414393412592836147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5214996552524550123781529 3911247414393412592836147)
                  ·
                    refine ⟨5866871121590118889254221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3911247414393412592836147 5866871121590118889254221)
                    ·
                      refine ⟨2200076670596294583470333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5866871121590118889254221 2200076670596294583470333)
                      ·
                        rfl

theorem cell23_4284634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_4284634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284634 prefixEnd_4284634 := by exact prefixLift 4284634
  have htrace : WordTrace (prefixWord ++ tailWord_4284634) baseStart_4284634 baseEnd_4284634 := by
    simpa [prefixWord, tailWord_4284634, baseEnd_4284634] using wordTrace_append hprefix tailTrace_4284634
  have hstable : (prefixWord ++ tailWord_4284634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284634).length < 2 ^ (prefixWord ++ tailWord_4284634).sum := by decide
  have hdescent : baseEnd_4284634 < baseStart_4284634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284647 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4284647 : Nat := 118140960795 + 4284647 * 2 ^ 59
def prefixEnd_4284647 : Nat := 4983230072969 + 3 ^ 40 * 4284647 * 2
def baseEnd_4284647 : Nat := 2200083345844803032607773

theorem tailTrace_4284647 : CollatzResearch.WordTrace tailWord_4284647 prefixEnd_4284647 2200083345844803032607773 := by
  unfold tailWord_4284647
  simp only [CollatzResearch.WordTrace]
  refine ⟨156273914508463153294364195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104182609672308768862909463 156273914508463153294364195)
  ·
    refine ⟨234410871762694729941546293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156273914508463153294364195 234410871762694729941546293)
    ·
      refine ⟨21976019227752630932019965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 234410871762694729941546293 21976019227752630932019965)
      ·
        refine ⟨8241007210407236599507487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21976019227752630932019965 8241007210407236599507487)
        ·
          refine ⟨12361510815610854899261231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241007210407236599507487 12361510815610854899261231)
          ·
            refine ⟨18542266223416282348891847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12361510815610854899261231 18542266223416282348891847)
            ·
              refine ⟨27813399335124423523337771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18542266223416282348891847 27813399335124423523337771)
              ·
                refine ⟨41720099002686635285006657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27813399335124423523337771 41720099002686635285006657)
                ·
                  refine ⟨31290074252014976463754993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41720099002686635285006657 31290074252014976463754993)
                  ·
                    refine ⟨23467555689011232347816245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31290074252014976463754993 23467555689011232347816245)
                    ·
                      refine ⟨2200083345844803032607773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23467555689011232347816245 2200083345844803032607773)
                      ·
                        rfl

theorem cell23_4284647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4284647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284647 prefixEnd_4284647 := by exact prefixLift 4284647
  have htrace : WordTrace (prefixWord ++ tailWord_4284647) baseStart_4284647 baseEnd_4284647 := by
    simpa [prefixWord, tailWord_4284647, baseEnd_4284647] using wordTrace_append hprefix tailTrace_4284647
  have hstable : (prefixWord ++ tailWord_4284647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284647).length < 2 ^ (prefixWord ++ tailWord_4284647).sum := by decide
  have hdescent : baseEnd_4284647 < baseStart_4284647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284807 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4284807 : Nat := 118140960795 + 4284807 * 2 ^ 59
def prefixEnd_4284807 : Nat := 4983230072969 + 3 ^ 40 * 4284807 * 2
def baseEnd_4284807 : Nat := 2200165502749522406607037

theorem tailTrace_4284807 : CollatzResearch.WordTrace tailWord_4284807 prefixEnd_4284807 2200165502749522406607037 := by
  unfold tailWord_4284807
  simp only [CollatzResearch.WordTrace]
  refine ⟨156279750187883500620188675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104186500125255667080125783 156279750187883500620188675)
  ·
    refine ⟨234419625281825250930283013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156279750187883500620188675 234419625281825250930283013)
    ·
      refine ⟨43953679740342234549428065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234419625281825250930283013 43953679740342234549428065)
      ·
        refine ⟨32965259805256675912071049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43953679740342234549428065 32965259805256675912071049)
        ·
          refine ⟨24723944853942506934053287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32965259805256675912071049 24723944853942506934053287)
          ·
            refine ⟨37085917280913760401079931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24723944853942506934053287 37085917280913760401079931)
            ·
              refine ⟨55628875921370640601619897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37085917280913760401079931 55628875921370640601619897)
              ·
                refine ⟨41721656941027980451214923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55628875921370640601619897 41721656941027980451214923)
                ·
                  refine ⟨62582485411541970676822385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41721656941027980451214923 62582485411541970676822385)
                  ·
                    refine ⟨46936864058656478007616789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62582485411541970676822385 46936864058656478007616789)
                    ·
                      refine ⟨2200165502749522406607037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46936864058656478007616789 2200165502749522406607037)
                      ·
                        rfl

theorem cell23_4284807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4284807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284807 prefixEnd_4284807 := by exact prefixLift 4284807
  have htrace : WordTrace (prefixWord ++ tailWord_4284807) baseStart_4284807 baseEnd_4284807 := by
    simpa [prefixWord, tailWord_4284807, baseEnd_4284807] using wordTrace_append hprefix tailTrace_4284807
  have hstable : (prefixWord ++ tailWord_4284807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284807).length < 2 ^ (prefixWord ++ tailWord_4284807).sum := by decide
  have hdescent : baseEnd_4284807 < baseStart_4284807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284842 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4284842 : Nat := 118140960795 + 4284842 * 2 ^ 59
def prefixEnd_4284842 : Nat := 4983230072969 + 3 ^ 40 * 4284842 * 2
def baseEnd_4284842 : Nat := 733394491524143256556459

theorem tailTrace_4284842 : CollatzResearch.WordTrace tailWord_4284842 prefixEnd_4284842 733394491524143256556459 := by
  unfold tailWord_4284842
  simp only [CollatzResearch.WordTrace]
  refine ⟨39070256685689175399428195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104187351161837801065141853 39070256685689175399428195)
  ·
    refine ⟨58605385028533763099142293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39070256685689175399428195 58605385028533763099142293)
    ·
      refine ⟨2747127423212520145272295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58605385028533763099142293 2747127423212520145272295)
      ·
        refine ⟨4120691134818780217908443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747127423212520145272295 4120691134818780217908443)
        ·
          refine ⟨6181036702228170326862665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120691134818780217908443 6181036702228170326862665)
          ·
            refine ⟨4635777526671127745146999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181036702228170326862665 4635777526671127745146999)
            ·
              refine ⟨6953666290006691617720499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635777526671127745146999 6953666290006691617720499)
              ·
                refine ⟨10430499435010037426580749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953666290006691617720499 10430499435010037426580749)
                ·
                  refine ⟨3911437288128764034967781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10430499435010037426580749 3911437288128764034967781)
                  ·
                    refine ⟨733394491524143256556459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3911437288128764034967781 733394491524143256556459)
                    ·
                      rfl

theorem cell23_4284842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4284842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284842 prefixEnd_4284842 := by exact prefixLift 4284842
  have htrace : WordTrace (prefixWord ++ tailWord_4284842) baseStart_4284842 baseEnd_4284842 := by
    simpa [prefixWord, tailWord_4284842, baseEnd_4284842] using wordTrace_append hprefix tailTrace_4284842
  have hstable : (prefixWord ++ tailWord_4284842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284842).length < 2 ^ (prefixWord ++ tailWord_4284842).sum := by decide
  have hdescent : baseEnd_4284842 < baseStart_4284842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284871 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_4284871 : Nat := 118140960795 + 4284871 * 2 ^ 59
def prefixEnd_4284871 : Nat := 4983230072969 + 3 ^ 40 * 4284871 * 2
def baseEnd_4284871 : Nat := 2200198365511410156206743

theorem tailTrace_4284871 : CollatzResearch.WordTrace tailWord_4284871 prefixEnd_4284871 2200198365511410156206743 := by
  unfold tailWord_4284871
  simp only [CollatzResearch.WordTrace]
  refine ⟨156282084459651639550518467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104188056306434426367012311 156282084459651639550518467)
  ·
    refine ⟨234423126689477459325777701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156282084459651639550518467 234423126689477459325777701)
    ·
      refine ⟨43954336254277023623583319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234423126689477459325777701 43954336254277023623583319)
      ·
        refine ⟨65931504381415535435374979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43954336254277023623583319 65931504381415535435374979)
        ·
          refine ⟨98897256572123303153062469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65931504381415535435374979 98897256572123303153062469)
          ·
            refine ⟨18543235607273119341199213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98897256572123303153062469 18543235607273119341199213)
            ·
              refine ⟨6953713352727419752949705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18543235607273119341199213 6953713352727419752949705)
              ·
                refine ⟨5215285014545564814712279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6953713352727419752949705 5215285014545564814712279)
                ·
                  refine ⟨7822927521818347222068419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215285014545564814712279 7822927521818347222068419)
                  ·
                    refine ⟨11734391282727520833102629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7822927521818347222068419 11734391282727520833102629)
                    ·
                      refine ⟨2200198365511410156206743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11734391282727520833102629 2200198365511410156206743)
                      ·
                        rfl

theorem cell23_4284871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_4284871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284871 prefixEnd_4284871 := by exact prefixLift 4284871
  have htrace : WordTrace (prefixWord ++ tailWord_4284871) baseStart_4284871 baseEnd_4284871 := by
    simpa [prefixWord, tailWord_4284871, baseEnd_4284871] using wordTrace_append hprefix tailTrace_4284871
  have hstable : (prefixWord ++ tailWord_4284871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284871).length < 2 ^ (prefixWord ++ tailWord_4284871).sum := by decide
  have hdescent : baseEnd_4284871 < baseStart_4284871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284899 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 1, 1, 3]
def baseStart_4284899 : Nat := 118140960795 + 4284899 * 2 ^ 59
def prefixEnd_4284899 : Nat := 4983230072969 + 3 ^ 40 * 4284899 * 2
def baseEnd_4284899 : Nat := 2200212742969736046656615

theorem tailTrace_4284899 : CollatzResearch.WordTrace tailWord_4284899 prefixEnd_4284899 2200212742969736046656615 := by
  unfold tailWord_4284899
  simp only [CollatzResearch.WordTrace]
  refine ⟨156283105703550200332537751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104188737135700133555025167 156283105703550200332537751)
  ·
    refine ⟨234424658555325300498806627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156283105703550200332537751 234424658555325300498806627)
    ·
      refine ⟨351636987832987950748209941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234424658555325300498806627 351636987832987950748209941)
      ·
        refine ⟨16482983804671310191322341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 351636987832987950748209941 16482983804671310191322341)
        ·
          refine ⟨3090559463375870660872939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16482983804671310191322341 3090559463375870660872939)
          ·
            refine ⟨4635839195063805991309409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090559463375870660872939 4635839195063805991309409)
            ·
              refine ⟨3476879396297854493482057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4635839195063805991309409 3476879396297854493482057)
              ·
                refine ⟨2607659547223390870111543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3476879396297854493482057 2607659547223390870111543)
                ·
                  refine ⟨3911489320835086305167315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607659547223390870111543 3911489320835086305167315)
                  ·
                    refine ⟨5867233981252629457750973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3911489320835086305167315 5867233981252629457750973)
                    ·
                      refine ⟨2200212742969736046656615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5867233981252629457750973 2200212742969736046656615)
                      ·
                        rfl

theorem cell23_4284899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_4284899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284899 prefixEnd_4284899 := by exact prefixLift 4284899
  have htrace : WordTrace (prefixWord ++ tailWord_4284899) baseStart_4284899 baseEnd_4284899 := by
    simpa [prefixWord, tailWord_4284899, baseEnd_4284899] using wordTrace_append hprefix tailTrace_4284899
  have hstable : (prefixWord ++ tailWord_4284899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284899).length < 2 ^ (prefixWord ++ tailWord_4284899).sum := by decide
  have hdescent : baseEnd_4284899 < baseStart_4284899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284907 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 9]
def baseStart_4284907 : Nat := 118140960795 + 4284907 * 2 ^ 59
def prefixEnd_4284907 : Nat := 4983230072969 + 3 ^ 40 * 4284907 * 2
def baseEnd_4284907 : Nat := 733405616938324005118859

theorem tailTrace_4284907 : CollatzResearch.WordTrace tailWord_4284907 prefixEnd_4284907 733405616938324005118859 := by
  unfold tailWord_4284907
  simp only [CollatzResearch.WordTrace]
  refine ⟨156283397487521217698828975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104188931658347478465885983 156283397487521217698828975)
  ·
    refine ⟨234425096231281826548243463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156283397487521217698828975 234425096231281826548243463)
    ·
      refine ⟨351637644346922739822365195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234425096231281826548243463 351637644346922739822365195)
      ·
        refine ⟨527456466520384109733547793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351637644346922739822365195 527456466520384109733547793)
        ·
          refine ⟨395592349890288082300160845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527456466520384109733547793 395592349890288082300160845)
          ·
            refine ⟨148347131208858030862560317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395592349890288082300160845 148347131208858030862560317)
            ·
              refine ⟨55630174203321761573460119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148347131208858030862560317 55630174203321761573460119)
              ·
                refine ⟨83445261304982642360190179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55630174203321761573460119 83445261304982642360190179)
                ·
                  refine ⟨125167891957473963540285269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83445261304982642360190179 125167891957473963540285269)
                  ·
                    refine ⟨733405616938324005118859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125167891957473963540285269 733405616938324005118859)
                    ·
                      rfl

theorem cell23_4284907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_4284907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284907 prefixEnd_4284907 := by exact prefixLift 4284907
  have htrace : WordTrace (prefixWord ++ tailWord_4284907) baseStart_4284907 baseEnd_4284907 := by
    simpa [prefixWord, tailWord_4284907, baseEnd_4284907] using wordTrace_append hprefix tailTrace_4284907
  have hstable : (prefixWord ++ tailWord_4284907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284907).length < 2 ^ (prefixWord ++ tailWord_4284907).sum := by decide
  have hdescent : baseEnd_4284907 < baseStart_4284907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284931 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 3, 3, 2]
def baseStart_4284931 : Nat := 118140960795 + 4284931 * 2 ^ 59
def prefixEnd_4284931 : Nat := 4983230072969 + 3 ^ 40 * 4284931 * 2
def baseEnd_4284931 : Nat := 2200229174350679921456467

theorem tailTrace_4284931 : CollatzResearch.WordTrace tailWord_4284931 prefixEnd_4284931 2200229174350679921456467 := by
  unfold tailWord_4284931
  simp only [CollatzResearch.WordTrace]
  refine ⟨156284272839434269797702647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104189515226289513198468431 156284272839434269797702647)
  ·
    refine ⟨234426409259151404696553971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156284272839434269797702647 234426409259151404696553971)
    ·
      refine ⟨351639613888727107044830957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234426409259151404696553971 351639613888727107044830957)
      ·
        refine ⟨131864855208272665141811609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351639613888727107044830957 131864855208272665141811609)
        ·
          refine ⟨98898641406204498856358707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131864855208272665141811609 98898641406204498856358707)
          ·
            refine ⟨148347962109306748284538061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98898641406204498856358707 148347962109306748284538061)
            ·
              refine ⟨55630485790990030606701773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148347962109306748284538061 55630485790990030606701773)
              ·
                refine ⟨20861432171621261477513165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55630485790990030606701773 20861432171621261477513165)
                ·
                  refine ⟨7823037064357973054067437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20861432171621261477513165 7823037064357973054067437)
                  ·
                    refine ⟨2933638899134239895275289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7823037064357973054067437 2933638899134239895275289)
                    ·
                      refine ⟨2200229174350679921456467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933638899134239895275289 2200229174350679921456467)
                      ·
                        rfl

theorem cell23_4284931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_4284931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284931 prefixEnd_4284931 := by exact prefixLift 4284931
  have htrace : WordTrace (prefixWord ++ tailWord_4284931) baseStart_4284931 baseEnd_4284931 := by
    simpa [prefixWord, tailWord_4284931, baseEnd_4284931] using wordTrace_append hprefix tailTrace_4284931
  have hstable : (prefixWord ++ tailWord_4284931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284931).length < 2 ^ (prefixWord ++ tailWord_4284931).sum := by decide
  have hdescent : baseEnd_4284931 < baseStart_4284931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284954 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_4284954 : Nat := 118140960795 + 4284954 * 2 ^ 59
def prefixEnd_4284954 : Nat := 4983230072969 + 3 ^ 40 * 4284954 * 2
def baseEnd_4284954 : Nat := 733413661468577777156287

theorem tailTrace_4284954 : CollatzResearch.WordTrace tailWord_4284954 prefixEnd_4284954 733413661468577777156287 := by
  unfold tailWord_4284954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39071277929587736181447479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104190074478900629817193277 39071277929587736181447479)
  ·
    refine ⟨58606916894381604272171219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39071277929587736181447479 58606916894381604272171219)
    ·
      refine ⟨87910375341572406408256829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58606916894381604272171219 87910375341572406408256829)
      ·
        refine ⟨32966390753089652403096311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87910375341572406408256829 32966390753089652403096311)
        ·
          refine ⟨49449586129634478604644467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32966390753089652403096311 49449586129634478604644467)
          ·
            refine ⟨74174379194451717906966701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49449586129634478604644467 74174379194451717906966701)
            ·
              refine ⟨27815392197919394215112513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74174379194451717906966701 27815392197919394215112513)
              ·
                refine ⟨20861544148439545661334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27815392197919394215112513 20861544148439545661334385)
                ·
                  refine ⟨15646158111329659246000789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20861544148439545661334385 15646158111329659246000789)
                  ·
                    refine ⟨733413661468577777156287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15646158111329659246000789 733413661468577777156287)
                    ·
                      rfl

theorem cell23_4284954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_4284954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284954 prefixEnd_4284954 := by exact prefixLift 4284954
  have htrace : WordTrace (prefixWord ++ tailWord_4284954) baseStart_4284954 baseEnd_4284954 := by
    simpa [prefixWord, tailWord_4284954, baseEnd_4284954] using wordTrace_append hprefix tailTrace_4284954
  have hstable : (prefixWord ++ tailWord_4284954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284954).length < 2 ^ (prefixWord ++ tailWord_4284954).sum := by decide
  have hdescent : baseEnd_4284954 < baseStart_4284954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284978 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_4284978 : Nat := 118140960795 + 4284978 * 2 ^ 59
def prefixEnd_4284978 : Nat := 4983230072969 + 3 ^ 40 * 4284978 * 2
def baseEnd_4284978 : Nat := 2200253307941441237568751

theorem tailTrace_4284978 : CollatzResearch.WordTrace tailWord_4284978 prefixEnd_4284978 2200253307941441237568751 := by
  unfold tailWord_4284978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39071496767565999206165897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104190658046842664549775725 39071496767565999206165897)
  ·
    refine ⟨29303622575674499404624423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39071496767565999206165897 29303622575674499404624423)
    ·
      refine ⟨43955433863511749106936635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29303622575674499404624423 43955433863511749106936635)
      ·
        refine ⟨65933150795267623660404953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43955433863511749106936635 65933150795267623660404953)
        ·
          refine ⟨49449863096450717745303715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65933150795267623660404953 49449863096450717745303715)
          ·
            refine ⟨74174794644676076617955573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49449863096450717745303715 74174794644676076617955573)
            ·
              refine ⟨6953886997938382182933335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74174794644676076617955573 6953886997938382182933335)
              ·
                refine ⟨10430830496907573274400003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953886997938382182933335 10430830496907573274400003)
                ·
                  refine ⟨15646245745361359911600005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10430830496907573274400003 15646245745361359911600005)
                  ·
                    refine ⟨2933671077255254983425001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15646245745361359911600005 2933671077255254983425001)
                    ·
                      refine ⟨2200253307941441237568751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933671077255254983425001 2200253307941441237568751)
                      ·
                        rfl

theorem cell23_4284978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_4284978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284978 prefixEnd_4284978 := by exact prefixLift 4284978
  have htrace : WordTrace (prefixWord ++ tailWord_4284978) baseStart_4284978 baseEnd_4284978 := by
    simpa [prefixWord, tailWord_4284978, baseEnd_4284978] using wordTrace_append hprefix tailTrace_4284978
  have hstable : (prefixWord ++ tailWord_4284978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284978).length < 2 ^ (prefixWord ++ tailWord_4284978).sum := by decide
  have hdescent : baseEnd_4284978 < baseStart_4284978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284982 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4284982 : Nat := 118140960795 + 4284982 * 2 ^ 59
def prefixEnd_4284982 : Nat := 4983230072969 + 3 ^ 40 * 4284982 * 2
def baseEnd_4284982 : Nat := 2200255361864059221918733

theorem tailTrace_4284982 : CollatzResearch.WordTrace tailWord_4284982 prefixEnd_4284982 2200255361864059221918733 := by
  unfold tailWord_4284982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9767883310140594094238075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104190755308166337005206133 9767883310140594094238075)
  ·
    refine ⟨14651824965210891141357113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9767883310140594094238075 14651824965210891141357113)
    ·
      refine ⟨10988868723908168356017835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14651824965210891141357113 10988868723908168356017835)
      ·
        refine ⟨16483303085862252534026753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10988868723908168356017835 16483303085862252534026753)
        ·
          refine ⟨12362477314396689400520065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16483303085862252534026753 12362477314396689400520065)
          ·
            refine ⟨9271857985797517050390049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12362477314396689400520065 9271857985797517050390049)
            ·
              refine ⟨6953893489348137787792537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9271857985797517050390049 6953893489348137787792537)
              ·
                refine ⟨5215420117011103340844403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6953893489348137787792537 5215420117011103340844403)
                ·
                  refine ⟨7823130175516655011266605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215420117011103340844403 7823130175516655011266605)
                  ·
                    refine ⟨2933673815818745629224977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7823130175516655011266605 2933673815818745629224977)
                    ·
                      refine ⟨2200255361864059221918733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933673815818745629224977 2200255361864059221918733)
                      ·
                        rfl

theorem cell23_4284982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4284982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284982 prefixEnd_4284982 := by exact prefixLift 4284982
  have htrace : WordTrace (prefixWord ++ tailWord_4284982) baseStart_4284982 baseEnd_4284982 := by
    simpa [prefixWord, tailWord_4284982, baseEnd_4284982] using wordTrace_append hprefix tailTrace_4284982
  have hstable : (prefixWord ++ tailWord_4284982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284982).length < 2 ^ (prefixWord ++ tailWord_4284982).sum := by decide
  have hdescent : baseEnd_4284982 < baseStart_4284982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284984 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 7]
def baseStart_4284984 : Nat := 118140960795 + 4284984 * 2 ^ 59
def prefixEnd_4284984 : Nat := 4983230072969 + 3 ^ 40 * 4284984 * 2
def baseEnd_4284984 : Nat := 244472932091707579343747

theorem tailTrace_4284984 : CollatzResearch.WordTrace tailWord_4284984 prefixEnd_4284984 244472932091707579343747 := by
  unfold tailWord_4284984
  simp only [CollatzResearch.WordTrace]
  refine ⟨78143102954121129924691003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104190803938828173232921337 78143102954121129924691003)
  ·
    refine ⟨117214654431181694887036505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78143102954121129924691003 117214654431181694887036505)
    ·
      refine ⟨87910990823386271165277379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117214654431181694887036505 87910990823386271165277379)
      ·
        refine ⟨131866486235079406747916069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87910990823386271165277379 131866486235079406747916069)
        ·
          refine ⟨24724966169077388765234263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131866486235079406747916069 24724966169077388765234263)
          ·
            refine ⟨37087449253616083147851395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24724966169077388765234263 37087449253616083147851395)
            ·
              refine ⟨55631173880424124721777093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37087449253616083147851395 55631173880424124721777093)
              ·
                refine ⟨10430845102579523385333205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55631173880424124721777093 10430845102579523385333205)
                ·
                  refine ⟨244472932091707579343747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10430845102579523385333205 244472932091707579343747)
                  ·
                    rfl

theorem cell23_4284984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_4284984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284984 prefixEnd_4284984 := by exact prefixLift 4284984
  have htrace : WordTrace (prefixWord ++ tailWord_4284984) baseStart_4284984 baseEnd_4284984 := by
    simpa [prefixWord, tailWord_4284984, baseEnd_4284984] using wordTrace_append hprefix tailTrace_4284984
  have hstable : (prefixWord ++ tailWord_4284984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284984).length < 2 ^ (prefixWord ++ tailWord_4284984).sum := by decide
  have hdescent : baseEnd_4284984 < baseStart_4284984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4284998 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4284998 : Nat := 118140960795 + 4284998 * 2 ^ 59
def prefixEnd_4284998 : Nat := 4983230072969 + 3 ^ 40 * 4284998 * 2
def baseEnd_4284998 : Nat := 2200263577554531159318659

theorem tailTrace_4284998 : CollatzResearch.WordTrace tailWord_4284998 prefixEnd_4284998 2200263577554531159318659 := by
  unfold tailWord_4284998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883959891568485632512239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104191144353461026826927765 4883959891568485632512239)
  ·
    refine ⟨7325939837352728448768359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4883959891568485632512239 7325939837352728448768359)
    ·
      refine ⟨10988909756029092673152539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7325939837352728448768359 10988909756029092673152539)
      ·
        refine ⟨16483364634043639009728809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10988909756029092673152539 16483364634043639009728809)
        ·
          refine ⟨12362523475532729257296607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16483364634043639009728809 12362523475532729257296607)
          ·
            refine ⟨18543785213299093885944911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12362523475532729257296607 18543785213299093885944911)
            ·
              refine ⟨27815677819948640828917367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18543785213299093885944911 27815677819948640828917367)
              ·
                refine ⟨41723516729922961243376051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27815677819948640828917367 41723516729922961243376051)
                ·
                  refine ⟨62585275094884441865064077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41723516729922961243376051 62585275094884441865064077)
                  ·
                    refine ⟨23469478160581665699399029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62585275094884441865064077 23469478160581665699399029)
                    ·
                      refine ⟨2200263577554531159318659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23469478160581665699399029 2200263577554531159318659)
                      ·
                        rfl

theorem cell23_4284998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4284998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4284998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4284998 prefixEnd_4284998 := by exact prefixLift 4284998
  have htrace : WordTrace (prefixWord ++ tailWord_4284998) baseStart_4284998 baseEnd_4284998 := by
    simpa [prefixWord, tailWord_4284998, baseEnd_4284998] using wordTrace_append hprefix tailTrace_4284998
  have hstable : (prefixWord ++ tailWord_4284998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4284998).length < 2 ^ (prefixWord ++ tailWord_4284998).sum := by decide
  have hdescent : baseEnd_4284998 < baseStart_4284998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4284998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285024 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_4285024 : Nat := 118140960795 + 4285024 * 2 ^ 59
def prefixEnd_4285024 : Nat := 4983230072969 + 3 ^ 40 * 4285024 * 2
def baseEnd_4285024 : Nat := 2200276928051548057593539

theorem tailTrace_4285024 : CollatzResearch.WordTrace tailWord_4285024 prefixEnd_4285024 2200276928051548057593539 := by
  unfold tailWord_4285024
  simp only [CollatzResearch.WordTrace]
  refine ⟨78143832414048673340419063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104191776552064897787225417 78143832414048673340419063)
  ·
    refine ⟨117215748621073010010628595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78143832414048673340419063 117215748621073010010628595)
    ·
      refine ⟨175823622931609515015942893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117215748621073010010628595 175823622931609515015942893)
      ·
        refine ⟨65933858599353568130978585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175823622931609515015942893 65933858599353568130978585)
        ·
          refine ⟨49450393949515176098233939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65933858599353568130978585 49450393949515176098233939)
          ·
            refine ⟨74175590924272764147350909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49450393949515176098233939 74175590924272764147350909)
            ·
              refine ⟨27815846596602286555256591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74175590924272764147350909 27815846596602286555256591)
              ·
                refine ⟨41723769894903429832884887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27815846596602286555256591 41723769894903429832884887)
                ·
                  refine ⟨62585654842355144749327331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41723769894903429832884887 62585654842355144749327331)
                  ·
                    refine ⟨93878482263532717123990997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62585654842355144749327331 93878482263532717123990997)
                    ·
                      refine ⟨2200276928051548057593539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93878482263532717123990997 2200276928051548057593539)
                      ·
                        rfl

theorem cell23_4285024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_4285024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285024 prefixEnd_4285024 := by exact prefixLift 4285024
  have htrace : WordTrace (prefixWord ++ tailWord_4285024) baseStart_4285024 baseEnd_4285024 := by
    simpa [prefixWord, tailWord_4285024, baseEnd_4285024] using wordTrace_append hprefix tailTrace_4285024
  have hstable : (prefixWord ++ tailWord_4285024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285024).length < 2 ^ (prefixWord ++ tailWord_4285024).sum := by decide
  have hdescent : baseEnd_4285024 < baseStart_4285024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285029 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_4285029 : Nat := 118140960795 + 4285029 * 2 ^ 59
def prefixEnd_4285029 : Nat := 4983230072969 + 3 ^ 40 * 4285029 * 2
def baseEnd_4285029 : Nat := 2200279495454820538031017

theorem tailTrace_4285029 : CollatzResearch.WordTrace tailWord_4285029 prefixEnd_4285029 2200279495454820538031017 := by
  unfold tailWord_4285029
  simp only [CollatzResearch.WordTrace]
  refine ⟨156287847193079232534770141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104191898128719488356513427 156287847193079232534770141)
  ·
    refine ⟨58607942697404712200538803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156287847193079232534770141 58607942697404712200538803)
    ·
      refine ⟨87911914046107068300808205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58607942697404712200538803 87911914046107068300808205)
      ·
        refine ⟨32966967767290150612803077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87911914046107068300808205 32966967767290150612803077)
        ·
          refine ⟨6181306456366903239900577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32966967767290150612803077 6181306456366903239900577)
          ·
            refine ⟨4635979842275177429925433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181306456366903239900577 4635979842275177429925433)
            ·
              refine ⟨3476984881706383072444075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4635979842275177429925433 3476984881706383072444075)
              ·
                refine ⟨5215477322559574608666113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476984881706383072444075 5215477322559574608666113)
                ·
                  refine ⟨3911607991919680956499585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5215477322559574608666113 3911607991919680956499585)
                  ·
                    refine ⟨2933705993939760717374689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911607991919680956499585 2933705993939760717374689)
                    ·
                      refine ⟨2200279495454820538031017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933705993939760717374689 2200279495454820538031017)
                      ·
                        rfl

theorem cell23_4285029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_4285029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285029 prefixEnd_4285029 := by exact prefixLift 4285029
  have htrace : WordTrace (prefixWord ++ tailWord_4285029) baseStart_4285029 baseEnd_4285029 := by
    simpa [prefixWord, tailWord_4285029, baseEnd_4285029] using wordTrace_append hprefix tailTrace_4285029
  have hstable : (prefixWord ++ tailWord_4285029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285029).length < 2 ^ (prefixWord ++ tailWord_4285029).sum := by decide
  have hdescent : baseEnd_4285029 < baseStart_4285029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285051 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 6, 2]
def baseStart_4285051 : Nat := 118140960795 + 4285051 * 2 ^ 59
def prefixEnd_4285051 : Nat := 4983230072969 + 3 ^ 40 * 4285051 * 2
def baseEnd_4285051 : Nat := 2200290792029219451955915

theorem tailTrace_4285051 : CollatzResearch.WordTrace tailWord_4285051 prefixEnd_4285051 2200290792029219451955915 := by
  unfold tailWord_4285051
  simp only [CollatzResearch.WordTrace]
  refine ⟨156288649598999530292071007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104192433065999686861380671 156288649598999530292071007)
  ·
    refine ⟨234432974398499295438106511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156288649598999530292071007 234432974398499295438106511)
    ·
      refine ⟨351649461597748943157159767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234432974398499295438106511 351649461597748943157159767)
      ·
        refine ⟨527474192396623414735739651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351649461597748943157159767 527474192396623414735739651)
        ·
          refine ⟨791211288594935122103609477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527474192396623414735739651 791211288594935122103609477)
          ·
            refine ⟨148352116611550335394426777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 791211288594935122103609477 148352116611550335394426777)
            ·
              refine ⟨111264087458662751545820083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148352116611550335394426777 111264087458662751545820083)
              ·
                refine ⟨166896131187994127318730125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111264087458662751545820083 166896131187994127318730125)
                ·
                  refine ⟨62586049195497797744523797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166896131187994127318730125 62586049195497797744523797)
                  ·
                    refine ⟨2933721056038959269274553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62586049195497797744523797 2933721056038959269274553)
                    ·
                      refine ⟨2200290792029219451955915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933721056038959269274553 2200290792029219451955915)
                      ·
                        rfl

theorem cell23_4285051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6, 2].length) (baseStart_4285051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285051 prefixEnd_4285051 := by exact prefixLift 4285051
  have htrace : WordTrace (prefixWord ++ tailWord_4285051) baseStart_4285051 baseEnd_4285051 := by
    simpa [prefixWord, tailWord_4285051, baseEnd_4285051] using wordTrace_append hprefix tailTrace_4285051
  have hstable : (prefixWord ++ tailWord_4285051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285051).length < 2 ^ (prefixWord ++ tailWord_4285051).sum := by decide
  have hdescent : baseEnd_4285051 < baseStart_4285051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285102 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4285102 : Nat := 118140960795 + 4285102 * 2 ^ 59
def prefixEnd_4285102 : Nat := 4983230072969 + 3 ^ 40 * 4285102 * 2
def baseEnd_4285102 : Nat := 2200316979542598752418181

theorem tailTrace_4285102 : CollatzResearch.WordTrace tailWord_4285102 prefixEnd_4285102 2200316979542598752418181 := by
  unfold tailWord_4285102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19536313715226845750272195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104193673147876510668118373 19536313715226845750272195)
  ·
    refine ⟨29304470572840268625408293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19536313715226845750272195 29304470572840268625408293)
    ·
      refine ⟨5494588232407550367264055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29304470572840268625408293 5494588232407550367264055)
      ·
        refine ⟨8241882348611325550896083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494588232407550367264055 8241882348611325550896083)
        ·
          refine ⟨12362823522916988326344125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241882348611325550896083 12362823522916988326344125)
          ·
            refine ⟨4636058821093870622379047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12362823522916988326344125 4636058821093870622379047)
            ·
              refine ⟨6954088231640805933568571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636058821093870622379047 6954088231640805933568571)
              ·
                refine ⟨10431132347461208900352857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6954088231640805933568571 10431132347461208900352857)
                ·
                  refine ⟨7823349260595906675264643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10431132347461208900352857 7823349260595906675264643)
                  ·
                    refine ⟨11735023890893860012896965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7823349260595906675264643 11735023890893860012896965)
                    ·
                      refine ⟨2200316979542598752418181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11735023890893860012896965 2200316979542598752418181)
                      ·
                        rfl

theorem cell23_4285102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4285102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285102 prefixEnd_4285102 := by exact prefixLift 4285102
  have htrace : WordTrace (prefixWord ++ tailWord_4285102) baseStart_4285102 baseEnd_4285102 := by
    simpa [prefixWord, tailWord_4285102, baseEnd_4285102] using wordTrace_append hprefix tailTrace_4285102
  have hstable : (prefixWord ++ tailWord_4285102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285102).length < 2 ^ (prefixWord ++ tailWord_4285102).sum := by decide
  have hdescent : baseEnd_4285102 < baseStart_4285102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285105 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4285105 : Nat := 118140960795 + 4285105 * 2 ^ 59
def prefixEnd_4285105 : Nat := 4983230072969 + 3 ^ 40 * 4285105 * 2
def baseEnd_4285105 : Nat := 2200318519984562240680667

theorem tailTrace_4285105 : CollatzResearch.WordTrace tailWord_4285105 prefixEnd_4285105 2200318519984562240680667 := by
  unfold tailWord_4285105
  simp only [CollatzResearch.WordTrace]
  refine ⟨156290619140803897514536769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104193746093869265009691179 156290619140803897514536769)
  ·
    refine ⟨117217964355602923135902577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156290619140803897514536769 117217964355602923135902577)
    ·
      refine ⟨87913473266702192351926933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117217964355602923135902577 87913473266702192351926933)
      ·
        refine ⟨4120944059376665266496575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87913473266702192351926933 4120944059376665266496575)
        ·
          refine ⟨6181416089064997899744863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120944059376665266496575 6181416089064997899744863)
          ·
            refine ⟨9272124133597496849617295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6181416089064997899744863 9272124133597496849617295)
            ·
              refine ⟨13908186200396245274425943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9272124133597496849617295 13908186200396245274425943)
              ·
                refine ⟨20862279300594367911638915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13908186200396245274425943 20862279300594367911638915)
                ·
                  refine ⟨31293418950891551867458373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20862279300594367911638915 31293418950891551867458373)
                  ·
                    refine ⟨5867516053292165975148445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31293418950891551867458373 5867516053292165975148445)
                    ·
                      refine ⟨2200318519984562240680667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5867516053292165975148445 2200318519984562240680667)
                      ·
                        rfl

theorem cell23_4285105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4285105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285105 prefixEnd_4285105 := by exact prefixLift 4285105
  have htrace : WordTrace (prefixWord ++ tailWord_4285105) baseStart_4285105 baseEnd_4285105 := by
    simpa [prefixWord, tailWord_4285105, baseEnd_4285105] using wordTrace_append hprefix tailTrace_4285105
  have hstable : (prefixWord ++ tailWord_4285105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285105).length < 2 ^ (prefixWord ++ tailWord_4285105).sum := by decide
  have hdescent : baseEnd_4285105 < baseStart_4285105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285155 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 1, 5]
def baseStart_4285155 : Nat := 118140960795 + 4285155 * 2 ^ 59
def prefixEnd_4285155 : Nat := 4983230072969 + 3 ^ 40 * 4285155 * 2
def baseEnd_4285155 : Nat := 733448064672429015018479

theorem tailTrace_4285155 : CollatzResearch.WordTrace tailWord_4285155 prefixEnd_4285155 733448064672429015018479 := by
  unfold tailWord_4285155
  simp only [CollatzResearch.WordTrace]
  refine ⟨156292442790622756053856919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104194961860415170702571279 156292442790622756053856919)
  ·
    refine ⟨234438664185934134080785379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156292442790622756053856919 234438664185934134080785379)
    ·
      refine ⟨351657996278901201121178069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234438664185934134080785379 351657996278901201121178069)
      ·
        refine ⟨8241984287786746901277611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 351657996278901201121178069 8241984287786746901277611)
        ·
          refine ⟨12362976431680120351916417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241984287786746901277611 12362976431680120351916417)
          ·
            refine ⟨9272232323760090263937313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12362976431680120351916417 9272232323760090263937313)
            ·
              refine ⟨6954174242820067697952985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9272232323760090263937313 6954174242820067697952985)
              ·
                refine ⟨5215630682115050773464739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6954174242820067697952985 5215630682115050773464739)
                ·
                  refine ⟨7823446023172576160197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215630682115050773464739 7823446023172576160197109)
                  ·
                    refine ⟨733448064672429015018479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7823446023172576160197109 733448064672429015018479)
                    ·
                      rfl

theorem cell23_4285155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 5].length) (baseStart_4285155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285155 prefixEnd_4285155 := by exact prefixLift 4285155
  have htrace : WordTrace (prefixWord ++ tailWord_4285155) baseStart_4285155 baseEnd_4285155 := by
    simpa [prefixWord, tailWord_4285155, baseEnd_4285155] using wordTrace_append hprefix tailTrace_4285155
  have hstable : (prefixWord ++ tailWord_4285155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285155).length < 2 ^ (prefixWord ++ tailWord_4285155).sum := by decide
  have hdescent : baseEnd_4285155 < baseStart_4285155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285171 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_4285171 : Nat := 118140960795 + 4285171 * 2 ^ 59
def prefixEnd_4285171 : Nat := 4983230072969 + 3 ^ 40 * 4285171 * 2
def baseEnd_4285171 : Nat := 2200352409707758982455363

theorem tailTrace_4285171 : CollatzResearch.WordTrace tailWord_4285171 prefixEnd_4285171 2200352409707758982455363 := by
  unfold tailWord_4285171
  simp only [CollatzResearch.WordTrace]
  refine ⟨156293026358564790786439367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104195350905709860524292911 156293026358564790786439367)
  ·
    refine ⟨234439539537847186179659051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156293026358564790786439367 234439539537847186179659051)
    ·
      refine ⟨351659309306770779269488577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234439539537847186179659051 351659309306770779269488577)
      ·
        refine ⟨263744481980078084452116433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351659309306770779269488577 263744481980078084452116433)
        ·
          refine ⟨197808361485058563339087325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263744481980078084452116433 197808361485058563339087325)
          ·
            refine ⟨74178135556896961252157747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197808361485058563339087325 74178135556896961252157747)
            ·
              refine ⟨111267203335345441878236621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74178135556896961252157747 111267203335345441878236621)
              ·
                refine ⟨41725201250754540704338733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111267203335345441878236621 41725201250754540704338733)
                ·
                  refine ⟨15646950469032952764127025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41725201250754540704338733 15646950469032952764127025)
                  ·
                    refine ⟨11735212851774714573095269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15646950469032952764127025 11735212851774714573095269)
                    ·
                      refine ⟨2200352409707758982455363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11735212851774714573095269 2200352409707758982455363)
                      ·
                        rfl

theorem cell23_4285171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_4285171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285171 prefixEnd_4285171 := by exact prefixLift 4285171
  have htrace : WordTrace (prefixWord ++ tailWord_4285171) baseStart_4285171 baseEnd_4285171 := by
    simpa [prefixWord, tailWord_4285171, baseEnd_4285171] using wordTrace_append hprefix tailTrace_4285171
  have hstable : (prefixWord ++ tailWord_4285171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285171).length < 2 ^ (prefixWord ++ tailWord_4285171).sum := by decide
  have hdescent : baseEnd_4285171 < baseStart_4285171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285186 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4285186 : Nat := 118140960795 + 4285186 * 2 ^ 59
def prefixEnd_4285186 : Nat := 4983230072969 + 3 ^ 40 * 4285186 * 2
def baseEnd_4285186 : Nat := 2200360111917576423767795

theorem tailTrace_4285186 : CollatzResearch.WordTrace tailWord_4285186 prefixEnd_4285186 2200360111917576423767795 := by
  unfold tailWord_4285186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39073393363377612087058853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104195715635673632232156941 39073393363377612087058853)
  ·
    refine ⟨7326261255633302266323535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39073393363377612087058853 7326261255633302266323535)
    ·
      refine ⟨10989391883449953399485303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326261255633302266323535 10989391883449953399485303)
      ·
        refine ⟨16484087825174930099227955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10989391883449953399485303 16484087825174930099227955)
        ·
          refine ⟨24726131737762395148841933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16484087825174930099227955 24726131737762395148841933)
          ·
            refine ⟨9272299401660898180815725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24726131737762395148841933 9272299401660898180815725)
            ·
              refine ⟨3477112275622836817805897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9272299401660898180815725 3477112275622836817805897)
              ·
                refine ⟨2607834206717127613354423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3477112275622836817805897 2607834206717127613354423)
                ·
                  refine ⟨3911751310075691420031635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607834206717127613354423 3911751310075691420031635)
                  ·
                    refine ⟨5867626965113537130047453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3911751310075691420031635 5867626965113537130047453)
                    ·
                      refine ⟨2200360111917576423767795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5867626965113537130047453 2200360111917576423767795)
                      ·
                        rfl

theorem cell23_4285186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4285186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285186 prefixEnd_4285186 := by exact prefixLift 4285186
  have htrace : WordTrace (prefixWord ++ tailWord_4285186) baseStart_4285186 baseEnd_4285186 := by
    simpa [prefixWord, tailWord_4285186, baseEnd_4285186] using wordTrace_append hprefix tailTrace_4285186
  have hstable : (prefixWord ++ tailWord_4285186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285186).length < 2 ^ (prefixWord ++ tailWord_4285186).sum := by decide
  have hdescent : baseEnd_4285186 < baseStart_4285186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285192 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_4285192 : Nat := 118140960795 + 4285192 * 2 ^ 59
def prefixEnd_4285192 : Nat := 4983230072969 + 3 ^ 40 * 4285192 * 2
def baseEnd_4285192 : Nat := 2200363192801503400292767

theorem tailTrace_4285192 : CollatzResearch.WordTrace tailWord_4285192 prefixEnd_4285192 2200363192801503400292767 := by
  unfold tailWord_4285192
  simp only [CollatzResearch.WordTrace]
  refine ⟨78146896145744355686476915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104195861527659140915302553 78146896145744355686476915)
  ·
    refine ⟨117220344218616533529715373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78146896145744355686476915 117220344218616533529715373)
    ·
      refine ⟨43957629081981200073643265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117220344218616533529715373 43957629081981200073643265)
      ·
        refine ⟨32968221811485900055232449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43957629081981200073643265 32968221811485900055232449)
        ·
          refine ⟨24726166358614425041424337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32968221811485900055232449 24726166358614425041424337)
          ·
            refine ⟨18544624768960818781068253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24726166358614425041424337 18544624768960818781068253)
            ·
              refine ⟨6954234288360307042900595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18544624768960818781068253 6954234288360307042900595)
              ·
                refine ⟨10431351432540460564350893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6954234288360307042900595 10431351432540460564350893)
                ·
                  refine ⟨3911756787202672711631585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10431351432540460564350893 3911756787202672711631585)
                  ·
                    refine ⟨2933817590402004533723689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911756787202672711631585 2933817590402004533723689)
                    ·
                      refine ⟨2200363192801503400292767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2933817590402004533723689 2200363192801503400292767)
                      ·
                        rfl

theorem cell23_4285192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_4285192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285192 prefixEnd_4285192 := by exact prefixLift 4285192
  have htrace : WordTrace (prefixWord ++ tailWord_4285192) baseStart_4285192 baseEnd_4285192 := by
    simpa [prefixWord, tailWord_4285192, baseEnd_4285192] using wordTrace_append hprefix tailTrace_4285192
  have hstable : (prefixWord ++ tailWord_4285192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285192).length < 2 ^ (prefixWord ++ tailWord_4285192).sum := by decide
  have hdescent : baseEnd_4285192 < baseStart_4285192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285208 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4285208 : Nat := 118140960795 + 4285208 * 2 ^ 59
def prefixEnd_4285208 : Nat := 4983230072969 + 3 ^ 40 * 4285208 * 2
def baseEnd_4285208 : Nat := 2200371408491975337692693

theorem tailTrace_4285208 : CollatzResearch.WordTrace tailWord_4285208 prefixEnd_4285208 2200371408491975337692693 := by
  unfold tailWord_4285208
  simp only [CollatzResearch.WordTrace]
  refine ⟨78147187929715373052768139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104196250572953830737024185 78147187929715373052768139)
  ·
    refine ⟨117220781894573059579152209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78147187929715373052768139 117220781894573059579152209)
    ·
      refine ⟨87915586420929794684364157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117220781894573059579152209 87915586420929794684364157)
      ·
        refine ⟨32968344907848673006636559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87915586420929794684364157 32968344907848673006636559)
        ·
          refine ⟨49452517361773009509954839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32968344907848673006636559 49452517361773009509954839)
          ·
            refine ⟨74178776042659514264932259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49452517361773009509954839 74178776042659514264932259)
            ·
              refine ⟨111268164063989271397398389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74178776042659514264932259 111268164063989271397398389)
              ·
                refine ⟨10431390380998994193506099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111268164063989271397398389 10431390380998994193506099)
                ·
                  refine ⟨15647085571498491290259149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10431390380998994193506099 15647085571498491290259149)
                  ·
                    refine ⟨5867657089311934233847181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15647085571498491290259149 5867657089311934233847181)
                    ·
                      refine ⟨2200371408491975337692693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5867657089311934233847181 2200371408491975337692693)
                      ·
                        rfl

theorem cell23_4285208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4285208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285208 prefixEnd_4285208 := by exact prefixLift 4285208
  have htrace : WordTrace (prefixWord ++ tailWord_4285208) baseStart_4285208 baseEnd_4285208 := by
    simpa [prefixWord, tailWord_4285208, baseEnd_4285208] using wordTrace_append hprefix tailTrace_4285208
  have hstable : (prefixWord ++ tailWord_4285208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285208).length < 2 ^ (prefixWord ++ tailWord_4285208).sum := by decide
  have hdescent : baseEnd_4285208 < baseStart_4285208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285212 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4285212 : Nat := 118140960795 + 4285212 * 2 ^ 59
def prefixEnd_4285212 : Nat := 4983230072969 + 3 ^ 40 * 4285212 * 2
def baseEnd_4285212 : Nat := 2200373462414593322042675

theorem tailTrace_4285212 : CollatzResearch.WordTrace tailWord_4285212 prefixEnd_4285212 2200373462414593322042675 := by
  unfold tailWord_4285212
  simp only [CollatzResearch.WordTrace]
  refine ⟨78147260875708127394340945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104196347834277503192454593 78147260875708127394340945)
  ·
    refine ⟨58610445656781095545755709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78147260875708127394340945 58610445656781095545755709)
    ·
      refine ⟨21978917121292910829658391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58610445656781095545755709 21978917121292910829658391)
      ·
        refine ⟨32968375681939366244487587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21978917121292910829658391 32968375681939366244487587)
        ·
          refine ⟨49452563522909049366731381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32968375681939366244487587 49452563522909049366731381)
          ·
            refine ⟨4636177830272723378131067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49452563522909049366731381 4636177830272723378131067)
            ·
              refine ⟨6954266745409085067196601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636177830272723378131067 6954266745409085067196601)
              ·
                refine ⟨5215700059056813800397451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6954266745409085067196601 5215700059056813800397451)
                ·
                  refine ⟨7823550088585220700596177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215700059056813800397451 7823550088585220700596177)
                  ·
                    refine ⟨5867662566438915525447133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7823550088585220700596177 5867662566438915525447133)
                    ·
                      refine ⟨2200373462414593322042675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5867662566438915525447133 2200373462414593322042675)
                      ·
                        rfl

theorem cell23_4285212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4285212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285212 prefixEnd_4285212 := by exact prefixLift 4285212
  have htrace : WordTrace (prefixWord ++ tailWord_4285212) baseStart_4285212 baseEnd_4285212 := by
    simpa [prefixWord, tailWord_4285212, baseEnd_4285212] using wordTrace_append hprefix tailTrace_4285212
  have hstable : (prefixWord ++ tailWord_4285212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285212).length < 2 ^ (prefixWord ++ tailWord_4285212).sum := by decide
  have hdescent : baseEnd_4285212 < baseStart_4285212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285229 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4285229 : Nat := 118140960795 + 4285229 * 2 ^ 59
def prefixEnd_4285229 : Nat := 4983230072969 + 3 ^ 40 * 4285229 * 2
def baseEnd_4285229 : Nat := 2200382191585719755530097

theorem tailTrace_4285229 : CollatzResearch.WordTrace tailWord_4285229 prefixEnd_4285229 2200382191585719755530097 := by
  unfold tailWord_4285229
  simp only [CollatzResearch.WordTrace]
  refine ⟨156295141792354666692050741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104196761194903111128033827 156295141792354666692050741)
  ·
    refine ⟨14652669543033250002379757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156295141792354666692050741 14652669543033250002379757)
    ·
      refine ⟨5494751078637468750892409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14652669543033250002379757 5494751078637468750892409)
      ·
        refine ⟨4121063308978101563169307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5494751078637468750892409 4121063308978101563169307)
        ·
          refine ⟨6181594963467152344753961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121063308978101563169307 6181594963467152344753961)
          ·
            refine ⟨4636196222600364258565471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181594963467152344753961 4636196222600364258565471)
            ·
              refine ⟨6954294333900546387848207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636196222600364258565471 6954294333900546387848207)
              ·
                refine ⟨10431441500850819581772311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6954294333900546387848207 10431441500850819581772311)
                ·
                  refine ⟨15647162251276229372658467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10431441500850819581772311 15647162251276229372658467)
                  ·
                    refine ⟨23470743376914344058987701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15647162251276229372658467 23470743376914344058987701)
                    ·
                      refine ⟨2200382191585719755530097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23470743376914344058987701 2200382191585719755530097)
                      ·
                        rfl

theorem cell23_4285229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4285229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285229 prefixEnd_4285229 := by exact prefixLift 4285229
  have htrace : WordTrace (prefixWord ++ tailWord_4285229) baseStart_4285229 baseEnd_4285229 := by
    simpa [prefixWord, tailWord_4285229, baseEnd_4285229] using wordTrace_append hprefix tailTrace_4285229
  have hstable : (prefixWord ++ tailWord_4285229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285229).length < 2 ^ (prefixWord ++ tailWord_4285229).sum := by decide
  have hdescent : baseEnd_4285229 < baseStart_4285229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285231 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_4285231 : Nat := 118140960795 + 4285231 * 2 ^ 59
def prefixEnd_4285231 : Nat := 4983230072969 + 3 ^ 40 * 4285231 * 2
def baseEnd_4285231 : Nat := 2200383218547028747705087

theorem tailTrace_4285231 : CollatzResearch.WordTrace tailWord_4285231 prefixEnd_4285231 2200383218547028747705087 := by
  unfold tailWord_4285231
  simp only [CollatzResearch.WordTrace]
  refine ⟨156295214738347421033623547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104196809825564947355749031 156295214738347421033623547)
  ·
    refine ⟨234442822107521131550435321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156295214738347421033623547 234442822107521131550435321)
    ·
      refine ⟨175832116580640848662826491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234442822107521131550435321 175832116580640848662826491)
      ·
        refine ⟨263748174870961272994239737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175832116580640848662826491 263748174870961272994239737)
        ·
          refine ⟨197811131153220954745679803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263748174870961272994239737 197811131153220954745679803)
          ·
            refine ⟨296716696729831432118519705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197811131153220954745679803 296716696729831432118519705)
            ·
              refine ⟨222537522547373574088889779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296716696729831432118519705 222537522547373574088889779)
              ·
                refine ⟨333806283821060361133334669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222537522547373574088889779 333806283821060361133334669)
                ·
                  refine ⟨125177356432897635425000501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333806283821060361133334669 125177356432897635425000501)
                  ·
                    refine ⟨11735377165584153321093797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125177356432897635425000501 11735377165584153321093797)
                    ·
                      refine ⟨2200383218547028747705087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11735377165584153321093797 2200383218547028747705087)
                      ·
                        rfl

theorem cell23_4285231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_4285231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285231 prefixEnd_4285231 := by exact prefixLift 4285231
  have htrace : WordTrace (prefixWord ++ tailWord_4285231) baseStart_4285231 baseEnd_4285231 := by
    simpa [prefixWord, tailWord_4285231, baseEnd_4285231] using wordTrace_append hprefix tailTrace_4285231
  have hstable : (prefixWord ++ tailWord_4285231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285231).length < 2 ^ (prefixWord ++ tailWord_4285231).sum := by decide
  have hdescent : baseEnd_4285231 < baseStart_4285231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285305 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 5]
def baseStart_4285305 : Nat := 118140960795 + 4285305 * 2 ^ 59
def prefixEnd_4285305 : Nat := 4983230072969 + 3 ^ 40 * 4285305 * 2
def baseEnd_4285305 : Nat := 244491246235051273131083

theorem tailTrace_4285305 : CollatzResearch.WordTrace tailWord_4285305 prefixEnd_4285305 244491246235051273131083 := by
  unfold tailWord_4285305
  simp only [CollatzResearch.WordTrace]
  refine ⟨156297913740079331671817369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104198609160052887781211579 156297913740079331671817369)
  ·
    refine ⟨117223435305059498753863027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156297913740079331671817369 117223435305059498753863027)
    ·
      refine ⟨175835152957589248130794541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117223435305059498753863027 175835152957589248130794541)
      ·
        refine ⟨65938182359095968049047953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175835152957589248130794541 65938182359095968049047953)
        ·
          refine ⟨49453636769321976036785965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65938182359095968049047953 49453636769321976036785965)
          ·
            refine ⟨18545113788495741013794737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49453636769321976036785965 18545113788495741013794737)
            ·
              refine ⟨13908835341371805760346053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18545113788495741013794737 13908835341371805760346053)
              ·
                refine ⟨2607906626507213580064885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13908835341371805760346053 2607906626507213580064885)
                ·
                  refine ⟨244491246235051273131083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2607906626507213580064885 244491246235051273131083)
                  ·
                    rfl

theorem cell23_4285305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 5].length) (baseStart_4285305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285305 prefixEnd_4285305 := by exact prefixLift 4285305
  have htrace : WordTrace (prefixWord ++ tailWord_4285305) baseStart_4285305 baseEnd_4285305 := by
    simpa [prefixWord, tailWord_4285305, baseEnd_4285305] using wordTrace_append hprefix tailTrace_4285305
  have hstable : (prefixWord ++ tailWord_4285305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285305).length < 2 ^ (prefixWord ++ tailWord_4285305).sum := by decide
  have hdescent : baseEnd_4285305 < baseStart_4285305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285425 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_4285425 : Nat := 118140960795 + 4285425 * 2 ^ 59
def prefixEnd_4285425 : Nat := 4983230072969 + 3 ^ 40 * 4285425 * 2
def baseEnd_4285425 : Nat := 733494277931333662893065

theorem tailTrace_4285425 : CollatzResearch.WordTrace tailWord_4285425 prefixEnd_4285425 733494277931333662893065 := by
  unfold tailWord_4285425
  simp only [CollatzResearch.WordTrace]
  refine ⟨156302290499644592166185729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104201526999763061444123819 156302290499644592166185729)
  ·
    refine ⟨117226717874733444124639297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156302290499644592166185729 117226717874733444124639297)
    ·
      refine ⟨87920038406050083093479473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117226717874733444124639297 87920038406050083093479473)
      ·
        refine ⟨65940028804537562320109605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87920038406050083093479473 65940028804537562320109605)
        ·
          refine ⟨12363755400850792935020551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65940028804537562320109605 12363755400850792935020551)
          ·
            refine ⟨18545633101276189402530827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12363755400850792935020551 18545633101276189402530827)
            ·
              refine ⟨27818449651914284103796241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18545633101276189402530827 27818449651914284103796241)
              ·
                refine ⟨20863837238935713077847181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27818449651914284103796241 20863837238935713077847181)
                ·
                  refine ⟨7823938964600892404192693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20863837238935713077847181 7823938964600892404192693)
                  ·
                    refine ⟨733494277931333662893065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7823938964600892404192693 733494277931333662893065)
                    ·
                      rfl

theorem cell23_4285425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_4285425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285425 prefixEnd_4285425 := by exact prefixLift 4285425
  have htrace : WordTrace (prefixWord ++ tailWord_4285425) baseStart_4285425 baseEnd_4285425 := by
    simpa [prefixWord, tailWord_4285425, baseEnd_4285425] using wordTrace_append hprefix tailTrace_4285425
  have hstable : (prefixWord ++ tailWord_4285425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285425).length < 2 ^ (prefixWord ++ tailWord_4285425).sum := by decide
  have hdescent : baseEnd_4285425 < baseStart_4285425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285445 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_4285445 : Nat := 118140960795 + 4285445 * 2 ^ 59
def prefixEnd_4285445 : Nat := 4983230072969 + 3 ^ 40 * 4285445 * 2
def baseEnd_4285445 : Nat := 2200493103407090910429103

theorem tailTrace_4285445 : CollatzResearch.WordTrace tailWord_4285445 prefixEnd_4285445 2200493103407090910429103 := by
  unfold tailWord_4285445
  simp only [CollatzResearch.WordTrace]
  refine ⟨156303019959572135581913789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104202013306381423721275859 156303019959572135581913789)
  ·
    refine ⟨58613632484839550843217671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156303019959572135581913789 58613632484839550843217671)
    ·
      refine ⟨87920448727259326264826507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58613632484839550843217671 87920448727259326264826507)
      ·
        refine ⟨131880673090888989397239761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87920448727259326264826507 131880673090888989397239761)
        ·
          refine ⟨98910504818166742047929821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131880673090888989397239761 98910504818166742047929821)
          ·
            refine ⟨37091439306812528267973683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98910504818166742047929821 37091439306812528267973683)
            ·
              refine ⟨55637158960218792401960525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37091439306812528267973683 55637158960218792401960525)
              ·
                refine ⟨20863934610082047150735197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55637158960218792401960525 20863934610082047150735197)
                ·
                  refine ⟨7823975478780767681525699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20863934610082047150735197 7823975478780767681525699)
                  ·
                    refine ⟨11735963218171151522288549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7823975478780767681525699 11735963218171151522288549)
                    ·
                      refine ⟨2200493103407090910429103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11735963218171151522288549 2200493103407090910429103)
                      ·
                        rfl

theorem cell23_4285445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_4285445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285445 prefixEnd_4285445 := by exact prefixLift 4285445
  have htrace : WordTrace (prefixWord ++ tailWord_4285445) baseStart_4285445 baseEnd_4285445 := by
    simpa [prefixWord, tailWord_4285445, baseEnd_4285445] using wordTrace_append hprefix tailTrace_4285445
  have hstable : (prefixWord ++ tailWord_4285445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285445).length < 2 ^ (prefixWord ++ tailWord_4285445).sum := by decide
  have hdescent : baseEnd_4285445 < baseStart_4285445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285489 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 2, 4]
def baseStart_4285489 : Nat := 118140960795 + 4285489 * 2 ^ 59
def prefixEnd_4285489 : Nat := 4983230072969 + 3 ^ 40 * 4285489 * 2
def baseEnd_4285489 : Nat := 733505232185296246092967

theorem tailTrace_4285489 : CollatzResearch.WordTrace tailWord_4285489 prefixEnd_4285489 733505232185296246092967 := by
  unfold tailWord_4285489
  simp only [CollatzResearch.WordTrace]
  refine ⟨156304624771412731096515521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104203083180941820731010347 156304624771412731096515521)
  ·
    refine ⟨117228468578559548322386641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156304624771412731096515521 117228468578559548322386641)
    ·
      refine ⟨87921351433919661241789981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117228468578559548322386641 87921351433919661241789981)
      ·
        refine ⟨32970506787719872965671243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87921351433919661241789981 32970506787719872965671243)
        ·
          refine ⟨49455760181579809448506865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32970506787719872965671243 49455760181579809448506865)
          ·
            refine ⟨37091820136184857086380149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49455760181579809448506865 37091820136184857086380149)
            ·
              refine ⟨3477358137767330351848139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37091820136184857086380149 3477358137767330351848139)
              ·
                refine ⟨5216037206650995527772209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477358137767330351848139 5216037206650995527772209)
                ·
                  refine ⟨3912027904988246645829157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5216037206650995527772209 3912027904988246645829157)
                  ·
                    refine ⟨733505232185296246092967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3912027904988246645829157 733505232185296246092967)
                    ·
                      rfl

theorem cell23_4285489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_4285489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285489 prefixEnd_4285489 := by exact prefixLift 4285489
  have htrace : WordTrace (prefixWord ++ tailWord_4285489) baseStart_4285489 baseEnd_4285489 := by
    simpa [prefixWord, tailWord_4285489, baseEnd_4285489] using wordTrace_append hprefix tailTrace_4285489
  have hstable : (prefixWord ++ tailWord_4285489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285489).length < 2 ^ (prefixWord ++ tailWord_4285489).sum := by decide
  have hdescent : baseEnd_4285489 < baseStart_4285489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285502 : List Nat := [4, 2, 1, 3, 1, 2, 1, 9]
def baseStart_4285502 : Nat := 118140960795 + 4285502 * 2 ^ 59
def prefixEnd_4285502 : Nat := 4983230072969 + 3 ^ 40 * 4285502 * 2
def baseEnd_4285502 : Nat := 81500828585348043978383

theorem tailTrace_4285502 : CollatzResearch.WordTrace tailWord_4285502 prefixEnd_4285502 81500828585348043978383 := by
  unfold tailWord_4285502
  simp only [CollatzResearch.WordTrace]
  refine ⟨19538137365045704289592345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104203399280243756211159173 19538137365045704289592345)
  ·
    refine ⟨14653603023784278217194259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19538137365045704289592345 14653603023784278217194259)
    ·
      refine ⟨21980404535676417325791389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14653603023784278217194259 21980404535676417325791389)
      ·
        refine ⟨8242651700878656497171771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21980404535676417325791389 8242651700878656497171771)
        ·
          refine ⟨12363977551317984745757657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8242651700878656497171771 12363977551317984745757657)
          ·
            refine ⟨9272983163488488559318243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12363977551317984745757657 9272983163488488559318243)
            ·
              refine ⟨13909474745232732838977365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9272983163488488559318243 13909474745232732838977365)
              ·
                refine ⟨81500828585348043978383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13909474745232732838977365 81500828585348043978383)
                ·
                  rfl

theorem cell23_4285502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_4285502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285502 prefixEnd_4285502 := by exact prefixLift 4285502
  have htrace : WordTrace (prefixWord ++ tailWord_4285502) baseStart_4285502 baseEnd_4285502 := by
    simpa [prefixWord, tailWord_4285502, baseEnd_4285502] using wordTrace_append hprefix tailTrace_4285502
  have hstable : (prefixWord ++ tailWord_4285502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285502).length < 2 ^ (prefixWord ++ tailWord_4285502).sum := by decide
  have hdescent : baseEnd_4285502 < baseStart_4285502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285512 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_4285512 : Nat := 118140960795 + 4285512 * 2 ^ 59
def prefixEnd_4285512 : Nat := 4983230072969 + 3 ^ 40 * 4285512 * 2
def baseEnd_4285512 : Nat := 2200527506610942148291295

theorem tailTrace_4285512 : CollatzResearch.WordTrace tailWord_4285512 prefixEnd_4285512 2200527506610942148291295 := by
  unfold tailWord_4285512
  simp only [CollatzResearch.WordTrace]
  refine ⟨78152731825164703012301395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104203642433552937349735193 78152731825164703012301395)
  ·
    refine ⟨117229097737747054518452093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78152731825164703012301395 117229097737747054518452093)
    ·
      refine ⟨43960911651655145444419535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117229097737747054518452093 43960911651655145444419535)
      ·
        refine ⟨65941367477482718166629303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43960911651655145444419535 65941367477482718166629303)
        ·
          refine ⟨98912051216224077249943955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65941367477482718166629303 98912051216224077249943955)
          ·
            refine ⟨148368076824336115874915933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98912051216224077249943955 148368076824336115874915933)
            ·
              refine ⟨55638028809126043453093475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148368076824336115874915933 55638028809126043453093475)
              ·
                refine ⟨83457043213689065179640213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55638028809126043453093475 83457043213689065179640213)
                ·
                  refine ⟨3912048900641674930295635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83457043213689065179640213 3912048900641674930295635)
                  ·
                    refine ⟨5868073350962512395443453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912048900641674930295635 5868073350962512395443453)
                    ·
                      refine ⟨2200527506610942148291295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868073350962512395443453 2200527506610942148291295)
                      ·
                        rfl

theorem cell23_4285512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_4285512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285512 prefixEnd_4285512 := by exact prefixLift 4285512
  have htrace : WordTrace (prefixWord ++ tailWord_4285512) baseStart_4285512 baseEnd_4285512 := by
    simpa [prefixWord, tailWord_4285512, baseEnd_4285512] using wordTrace_append hprefix tailTrace_4285512
  have hstable : (prefixWord ++ tailWord_4285512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285512).length < 2 ^ (prefixWord ++ tailWord_4285512).sum := by decide
  have hdescent : baseEnd_4285512 < baseStart_4285512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285525 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4285525 : Nat := 118140960795 + 4285525 * 2 ^ 59
def prefixEnd_4285525 : Nat := 4983230072969 + 3 ^ 40 * 4285525 * 2
def baseEnd_4285525 : Nat := 2200534181859450597428735

theorem tailTrace_4285525 : CollatzResearch.WordTrace tailWord_4285525 prefixEnd_4285525 2200534181859450597428735 := by
  unfold tailWord_4285525
  simp only [CollatzResearch.WordTrace]
  refine ⟨156305937799282309244826029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104203958532854872829884019 156305937799282309244826029)
  ·
    refine ⟨58614726674730865966809761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156305937799282309244826029 58614726674730865966809761)
    ·
      refine ⟨43961045006048149475107321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58614726674730865966809761 43961045006048149475107321)
      ·
        refine ⟨32970783754536112106330491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43961045006048149475107321 32970783754536112106330491)
        ·
          refine ⟨49456175631804168159495737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32970783754536112106330491 49456175631804168159495737)
          ·
            refine ⟨37092131723853126119621803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49456175631804168159495737 37092131723853126119621803)
            ·
              refine ⟨55638197585779689179432705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37092131723853126119621803 55638197585779689179432705)
              ·
                refine ⟨41728648189334766884574529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55638197585779689179432705 41728648189334766884574529)
                ·
                  refine ⟨31296486142001075163430897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41728648189334766884574529 31296486142001075163430897)
                  ·
                    refine ⟨23472364606500806372573173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31296486142001075163430897 23472364606500806372573173)
                    ·
                      refine ⟨2200534181859450597428735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23472364606500806372573173 2200534181859450597428735)
                      ·
                        rfl

theorem cell23_4285525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4285525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285525 prefixEnd_4285525 := by exact prefixLift 4285525
  have htrace : WordTrace (prefixWord ++ tailWord_4285525) baseStart_4285525 baseEnd_4285525 := by
    simpa [prefixWord, tailWord_4285525, baseEnd_4285525] using wordTrace_append hprefix tailTrace_4285525
  have hstable : (prefixWord ++ tailWord_4285525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285525).length < 2 ^ (prefixWord ++ tailWord_4285525).sum := by decide
  have hdescent : baseEnd_4285525 < baseStart_4285525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285535 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_4285535 : Nat := 118140960795 + 4285535 * 2 ^ 59
def prefixEnd_4285535 : Nat := 4983230072969 + 3 ^ 40 * 4285535 * 2
def baseEnd_4285535 : Nat := 2200539316665995558303689

theorem tailTrace_4285535 : CollatzResearch.WordTrace tailWord_4285535 prefixEnd_4285535 2200539316665995558303689 := by
  unfold tailWord_4285535
  simp only [CollatzResearch.WordTrace]
  refine ⟨156306302529246080952690059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104204201686164053968460039 156306302529246080952690059)
  ·
    refine ⟨234459453793869121429035089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156306302529246080952690059 234459453793869121429035089)
    ·
      refine ⟨175844590345401841071776317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234459453793869121429035089 175844590345401841071776317)
      ·
        refine ⟨65941721379525690401916119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175844590345401841071776317 65941721379525690401916119)
        ·
          refine ⟨98912582069288535602874179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65941721379525690401916119 98912582069288535602874179)
          ·
            refine ⟨148368873103932803404311269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98912582069288535602874179 148368873103932803404311269)
            ·
              refine ⟨27819163706987400638308363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148368873103932803404311269 27819163706987400638308363)
              ·
                refine ⟨41728745560481100957462545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27819163706987400638308363 41728745560481100957462545)
                ·
                  refine ⟨31296559170360825718096909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41728745560481100957462545 31296559170360825718096909)
                  ·
                    refine ⟨11736209688885309644286341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31296559170360825718096909 11736209688885309644286341)
                    ·
                      refine ⟨2200539316665995558303689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11736209688885309644286341 2200539316665995558303689)
                      ·
                        rfl

theorem cell23_4285535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_4285535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285535 prefixEnd_4285535 := by exact prefixLift 4285535
  have htrace : WordTrace (prefixWord ++ tailWord_4285535) baseStart_4285535 baseEnd_4285535 := by
    simpa [prefixWord, tailWord_4285535, baseEnd_4285535] using wordTrace_append hprefix tailTrace_4285535
  have hstable : (prefixWord ++ tailWord_4285535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285535).length < 2 ^ (prefixWord ++ tailWord_4285535).sum := by decide
  have hdescent : baseEnd_4285535 < baseStart_4285535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285546 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4285546 : Nat := 118140960795 + 4285546 * 2 ^ 59
def prefixEnd_4285546 : Nat := 4983230072969 + 3 ^ 40 * 4285546 * 2
def baseEnd_4285546 : Nat := 2200544964953195015266139

theorem tailTrace_4285546 : CollatzResearch.WordTrace tailWord_4285546 prefixEnd_4285546 2200544964953195015266139 := by
  unfold tailWord_4285546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39076675933051557457835123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104204469154804153220893661 39076675933051557457835123)
  ·
    refine ⟨58615013899577336186752685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39076675933051557457835123 58615013899577336186752685)
    ·
      refine ⟨21980630212341501070032257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58615013899577336186752685 21980630212341501070032257)
      ·
        refine ⟨16485472659256125802524193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21980630212341501070032257 16485472659256125802524193)
        ·
          refine ⟨12364104494442094351893145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16485472659256125802524193 12364104494442094351893145)
          ·
            refine ⟨9273078370831570763919859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12364104494442094351893145 9273078370831570763919859)
            ·
              refine ⟨13909617556247356145879789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9273078370831570763919859 13909617556247356145879789)
              ·
                refine ⟨5216106583592758554704921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13909617556247356145879789 5216106583592758554704921)
                ·
                  refine ⟨3912079937694568916028691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5216106583592758554704921 3912079937694568916028691)
                  ·
                    refine ⟨5868119906541853374043037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912079937694568916028691 5868119906541853374043037)
                    ·
                      refine ⟨2200544964953195015266139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868119906541853374043037 2200544964953195015266139)
                      ·
                        rfl

theorem cell23_4285546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4285546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285546 prefixEnd_4285546 := by exact prefixLift 4285546
  have htrace : WordTrace (prefixWord ++ tailWord_4285546) baseStart_4285546 baseEnd_4285546 := by
    simpa [prefixWord, tailWord_4285546, baseEnd_4285546] using wordTrace_append hprefix tailTrace_4285546
  have hstable : (prefixWord ++ tailWord_4285546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285546).length < 2 ^ (prefixWord ++ tailWord_4285546).sum := by decide
  have hdescent : baseEnd_4285546 < baseStart_4285546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285569 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_4285569 : Nat := 118140960795 + 4285569 * 2 ^ 59
def prefixEnd_4285569 : Nat := 4983230072969 + 3 ^ 40 * 4285569 * 2
def baseEnd_4285569 : Nat := 2200556775008248425278533

theorem tailTrace_4285569 : CollatzResearch.WordTrace tailWord_4285569 prefixEnd_4285569 2200556775008248425278533 := by
  unfold tailWord_4285569
  simp only [CollatzResearch.WordTrace]
  refine ⟨156307542611122904759427761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104205028407415269839618507 156307542611122904759427761)
  ·
    refine ⟨117230656958342178569570821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156307542611122904759427761 117230656958342178569570821)
    ·
      refine ⟨21980748179689158481794529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117230656958342178569570821 21980748179689158481794529)
      ·
        refine ⟨16485561134766868861345897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21980748179689158481794529 16485561134766868861345897)
        ·
          refine ⟨12364170851075151646009423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16485561134766868861345897 12364170851075151646009423)
          ·
            refine ⟨18546256276612727469014135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12364170851075151646009423 18546256276612727469014135)
            ·
              refine ⟨27819384414919091203521203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18546256276612727469014135 27819384414919091203521203)
              ·
                refine ⟨41729076622378636805281805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27819384414919091203521203 41729076622378636805281805)
                ·
                  refine ⟨15648403733391988801980677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41729076622378636805281805 15648403733391988801980677)
                  ·
                    refine ⟨2934075700010997900371377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15648403733391988801980677 2934075700010997900371377)
                    ·
                      refine ⟨2200556775008248425278533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934075700010997900371377 2200556775008248425278533)
                      ·
                        rfl

theorem cell23_4285569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_4285569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285569 prefixEnd_4285569 := by exact prefixLift 4285569
  have htrace : WordTrace (prefixWord ++ tailWord_4285569) baseStart_4285569 baseEnd_4285569 := by
    simpa [prefixWord, tailWord_4285569, baseEnd_4285569] using wordTrace_append hprefix tailTrace_4285569
  have hstable : (prefixWord ++ tailWord_4285569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285569).length < 2 ^ (prefixWord ++ tailWord_4285569).sum := by decide
  have hdescent : baseEnd_4285569 < baseStart_4285569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285572 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_4285572 : Nat := 118140960795 + 4285572 * 2 ^ 59
def prefixEnd_4285572 : Nat := 4983230072969 + 3 ^ 40 * 4285572 * 2
def baseEnd_4285572 : Nat := 2200558315450211913541019

theorem tailTrace_4285572 : CollatzResearch.WordTrace tailWord_4285572 prefixEnd_4285572 2200558315450211913541019 := by
  unfold tailWord_4285572
  simp only [CollatzResearch.WordTrace]
  refine ⟨78153826015056018135893485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104205101353408024181191313 78153826015056018135893485)
  ·
    refine ⟨29307684755646006800960057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78153826015056018135893485 29307684755646006800960057)
    ·
      refine ⟨21980763566734505100720043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29307684755646006800960057 21980763566734505100720043)
      ·
        refine ⟨32971145350101757651080065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21980763566734505100720043 32971145350101757651080065)
        ·
          refine ⟨24728359012576318238310049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32971145350101757651080065 24728359012576318238310049)
          ·
            refine ⟨18546269259432238678732537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24728359012576318238310049 18546269259432238678732537)
            ·
              refine ⟨13909701944574179009049403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18546269259432238678732537 13909701944574179009049403)
              ·
                refine ⟨20864552916861268513574105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13909701944574179009049403 20864552916861268513574105)
                ·
                  refine ⟨15648414687645951385180579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20864552916861268513574105 15648414687645951385180579)
                  ·
                    refine ⟨23472622031468927077770869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15648414687645951385180579 23472622031468927077770869)
                    ·
                      refine ⟨2200558315450211913541019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23472622031468927077770869 2200558315450211913541019)
                      ·
                        rfl

theorem cell23_4285572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_4285572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285572 prefixEnd_4285572 := by exact prefixLift 4285572
  have htrace : WordTrace (prefixWord ++ tailWord_4285572) baseStart_4285572 baseEnd_4285572 := by
    simpa [prefixWord, tailWord_4285572, baseEnd_4285572] using wordTrace_append hprefix tailTrace_4285572
  have hstable : (prefixWord ++ tailWord_4285572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285572).length < 2 ^ (prefixWord ++ tailWord_4285572).sum := by decide
  have hdescent : baseEnd_4285572 < baseStart_4285572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285573 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_4285573 : Nat := 118140960795 + 4285573 * 2 ^ 59
def prefixEnd_4285573 : Nat := 4983230072969 + 3 ^ 40 * 4285573 * 2
def baseEnd_4285573 : Nat := 2200558828930866409628515

theorem tailTrace_4285573 : CollatzResearch.WordTrace tailWord_4285573 prefixEnd_4285573 2200558828930866409628515 := by
  unfold tailWord_4285573
  simp only [CollatzResearch.WordTrace]
  refine ⟨156307688503108413442573373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104205125668738942295048915 156307688503108413442573373)
  ·
    refine ⟨58615383188665655040965015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156307688503108413442573373 58615383188665655040965015)
    ·
      refine ⟨87923074782998482561447523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58615383188665655040965015 87923074782998482561447523)
      ·
        refine ⟨131884612174497723842171285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87923074782998482561447523 131884612174497723842171285)
        ·
          refine ⟨6182091195679580805101779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131884612174497723842171285 6182091195679580805101779)
          ·
            refine ⟨9273136793519371207652669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182091195679580805101779 9273136793519371207652669)
            ·
              refine ⟨3477426297569764202869751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9273136793519371207652669 3477426297569764202869751)
              ·
                refine ⟨5216139446354646304304627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477426297569764202869751 5216139446354646304304627)
                ·
                  refine ⟨7824209169531969456456941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5216139446354646304304627 7824209169531969456456941)
                  ·
                    refine ⟨2934078438574488546171353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7824209169531969456456941 2934078438574488546171353)
                    ·
                      refine ⟨2200558828930866409628515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934078438574488546171353 2200558828930866409628515)
                      ·
                        rfl

theorem cell23_4285573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_4285573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285573 prefixEnd_4285573 := by exact prefixLift 4285573
  have htrace : WordTrace (prefixWord ++ tailWord_4285573) baseStart_4285573 baseEnd_4285573 := by
    simpa [prefixWord, tailWord_4285573, baseEnd_4285573] using wordTrace_append hprefix tailTrace_4285573
  have hstable : (prefixWord ++ tailWord_4285573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285573).length < 2 ^ (prefixWord ++ tailWord_4285573).sum := by decide
  have hdescent : baseEnd_4285573 < baseStart_4285573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285599 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4285599 : Nat := 118140960795 + 4285599 * 2 ^ 59
def prefixEnd_4285599 : Nat := 4983230072969 + 3 ^ 40 * 4285599 * 2
def baseEnd_4285599 : Nat := 2200572179427883307903395

theorem tailTrace_4285599 : CollatzResearch.WordTrace tailWord_4285599 prefixEnd_4285599 2200572179427883307903395 := by
  unfold tailWord_4285599
  simp only [CollatzResearch.WordTrace]
  refine ⟨156308636801014219883019851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104205757867342813255346567 156308636801014219883019851)
  ·
    refine ⟨234462955201521329824529777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156308636801014219883019851 234462955201521329824529777)
    ·
      refine ⟨175847216401140997368397333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234462955201521329824529777 175847216401140997368397333)
      ·
        refine ⟨8242838268803484251643625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175847216401140997368397333 8242838268803484251643625)
        ·
          refine ⟨6182128701602613188732719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8242838268803484251643625 6182128701602613188732719)
          ·
            refine ⟨9273193052403919783099079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182128701602613188732719 9273193052403919783099079)
            ·
              refine ⟨13909789578605879674648619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9273193052403919783099079 13909789578605879674648619)
              ·
                refine ⟨20864684367908819511972929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13909789578605879674648619 20864684367908819511972929)
                ·
                  refine ⟨15648513275931614633979697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20864684367908819511972929 15648513275931614633979697)
                  ·
                    refine ⟨11736384956948710975484773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15648513275931614633979697 11736384956948710975484773)
                    ·
                      refine ⟨2200572179427883307903395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11736384956948710975484773 2200572179427883307903395)
                      ·
                        rfl

theorem cell23_4285599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4285599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285599 prefixEnd_4285599 := by exact prefixLift 4285599
  have htrace : WordTrace (prefixWord ++ tailWord_4285599) baseStart_4285599 baseEnd_4285599 := by
    simpa [prefixWord, tailWord_4285599, baseEnd_4285599] using wordTrace_append hprefix tailTrace_4285599
  have hstable : (prefixWord ++ tailWord_4285599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285599).length < 2 ^ (prefixWord ++ tailWord_4285599).sum := by decide
  have hdescent : baseEnd_4285599 < baseStart_4285599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285615 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_4285615 : Nat := 118140960795 + 4285615 * 2 ^ 59
def prefixEnd_4285615 : Nat := 4983230072969 + 3 ^ 40 * 4285615 * 2
def baseEnd_4285615 : Nat := 2200580395118355245303321

theorem tailTrace_4285615 : CollatzResearch.WordTrace tailWord_4285615 prefixEnd_4285615 2200580395118355245303321 := by
  unfold tailWord_4285615
  simp only [CollatzResearch.WordTrace]
  refine ⟨156309220368956254615602299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104206146912637503077068199 156309220368956254615602299)
  ·
    refine ⟨234463830553434381923403449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156309220368956254615602299 234463830553434381923403449)
    ·
      refine ⟨175847872915075786442552587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234463830553434381923403449 175847872915075786442552587)
      ·
        refine ⟨263771809372613679663828881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175847872915075786442552587 263771809372613679663828881)
        ·
          refine ⟨197828857029460259747871661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263771809372613679663828881 197828857029460259747871661)
          ·
            refine ⟨74185821386047597405451873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197828857029460259747871661 74185821386047597405451873)
            ·
              refine ⟨55639366039535698054088905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74185821386047597405451873 55639366039535698054088905)
              ·
                refine ⟨41729524529651773540566679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55639366039535698054088905 41729524529651773540566679)
                ·
                  refine ⟨62594286794477660310850019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41729524529651773540566679 62594286794477660310850019)
                  ·
                    refine ⟨93891430191716490466275029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62594286794477660310850019 93891430191716490466275029)
                    ·
                      refine ⟨2200580395118355245303321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93891430191716490466275029 2200580395118355245303321)
                      ·
                        rfl

theorem cell23_4285615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_4285615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285615 prefixEnd_4285615 := by exact prefixLift 4285615
  have htrace : WordTrace (prefixWord ++ tailWord_4285615) baseStart_4285615 baseEnd_4285615 := by
    simpa [prefixWord, tailWord_4285615, baseEnd_4285615] using wordTrace_append hprefix tailTrace_4285615
  have hstable : (prefixWord ++ tailWord_4285615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285615).length < 2 ^ (prefixWord ++ tailWord_4285615).sum := by decide
  have hdescent : baseEnd_4285615 < baseStart_4285615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285672 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4285672 : Nat := 118140960795 + 4285672 * 2 ^ 59
def prefixEnd_4285672 : Nat := 4983230072969 + 3 ^ 40 * 4285672 * 2
def baseEnd_4285672 : Nat := 2200609663515661522290559

theorem tailTrace_4285672 : CollatzResearch.WordTrace tailWord_4285672 prefixEnd_4285672 2200609663515661522290559 := by
  unfold tailWord_4285672
  simp only [CollatzResearch.WordTrace]
  refine ⟨78155649664874876675213635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104207532886499835566951513 78155649664874876675213635)
  ·
    refine ⟨117233474497312315012820453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78155649664874876675213635 117233474497312315012820453)
    ·
      refine ⟨21981276468246059064903835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117233474497312315012820453 21981276468246059064903835)
      ·
        refine ⟨32971914702369088597355753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21981276468246059064903835 32971914702369088597355753)
        ·
          refine ⟨24728936026776816448016815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32971914702369088597355753 24728936026776816448016815)
          ·
            refine ⟨37093404040165224672025223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24728936026776816448016815 37093404040165224672025223)
            ·
              refine ⟨55640106060247837008037835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37093404040165224672025223 55640106060247837008037835)
              ·
                refine ⟨83460159090371755512056753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55640106060247837008037835 83460159090371755512056753)
                ·
                  refine ⟨62595119317778816634042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83460159090371755512056753 62595119317778816634042565)
                  ·
                    refine ⟨11736584872083528118882981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62595119317778816634042565 11736584872083528118882981)
                    ·
                      refine ⟨2200609663515661522290559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11736584872083528118882981 2200609663515661522290559)
                      ·
                        rfl

theorem cell23_4285672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4285672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285672 prefixEnd_4285672 := by exact prefixLift 4285672
  have htrace : WordTrace (prefixWord ++ tailWord_4285672) baseStart_4285672 baseEnd_4285672 := by
    simpa [prefixWord, tailWord_4285672, baseEnd_4285672] using wordTrace_append hprefix tailTrace_4285672
  have hstable : (prefixWord ++ tailWord_4285672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285672).length < 2 ^ (prefixWord ++ tailWord_4285672).sum := by decide
  have hdescent : baseEnd_4285672 < baseStart_4285672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285769 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_4285769 : Nat := 118140960795 + 4285769 * 2 ^ 59
def prefixEnd_4285769 : Nat := 4983230072969 + 3 ^ 40 * 4285769 * 2
def baseEnd_4285769 : Nat := 2200659471139147642777613

theorem tailTrace_4285769 : CollatzResearch.WordTrace tailWord_4285769 prefixEnd_4285769 2200659471139147642777613 := by
  unfold tailWord_4285769
  simp only [CollatzResearch.WordTrace]
  refine ⟨156314837210398338916708361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104209891473598892611138907 156314837210398338916708361)
  ·
    refine ⟨117236127907798754187531271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156314837210398338916708361 117236127907798754187531271)
    ·
      refine ⟨175854191861698131281296907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117236127907798754187531271 175854191861698131281296907)
      ·
        refine ⟨263781287792547196921945361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175854191861698131281296907 263781287792547196921945361)
        ·
          refine ⟨197835965844410397691459021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263781287792547196921945361 197835965844410397691459021)
          ·
            refine ⟨74188487191653899134297133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197835965844410397691459021 74188487191653899134297133)
            ·
              refine ⟨27820682696870212175361425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74188487191653899134297133 27820682696870212175361425)
              ·
                refine ⟨20865512022652659131521069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27820682696870212175361425 20865512022652659131521069)
                ·
                  refine ⟨7824567008494747174320401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20865512022652659131521069 7824567008494747174320401)
                  ·
                    refine ⟨5868425256371060380740301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7824567008494747174320401 5868425256371060380740301)
                    ·
                      refine ⟨2200659471139147642777613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868425256371060380740301 2200659471139147642777613)
                      ·
                        rfl

theorem cell23_4285769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_4285769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285769 prefixEnd_4285769 := by exact prefixLift 4285769
  have htrace : WordTrace (prefixWord ++ tailWord_4285769) baseStart_4285769 baseEnd_4285769 := by
    simpa [prefixWord, tailWord_4285769, baseEnd_4285769] using wordTrace_append hprefix tailTrace_4285769
  have hstable : (prefixWord ++ tailWord_4285769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285769).length < 2 ^ (prefixWord ++ tailWord_4285769).sum := by decide
  have hdescent : baseEnd_4285769 < baseStart_4285769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285779 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4]
def baseStart_4285779 : Nat := 118140960795 + 4285779 * 2 ^ 59
def prefixEnd_4285779 : Nat := 4983230072969 + 3 ^ 40 * 4285779 * 2
def baseEnd_4285779 : Nat := 2200664605945692603652567

theorem tailTrace_4285779 : CollatzResearch.WordTrace tailWord_4285779 prefixEnd_4285779 2200664605945692603652567 := by
  unfold tailWord_4285779
  simp only [CollatzResearch.WordTrace]
  refine ⟨156315201940362110624572391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104210134626908073749714927 156315201940362110624572391)
  ·
    refine ⟨234472802910543165936858587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156315201940362110624572391 234472802910543165936858587)
    ·
      refine ⟨351709204365814748905287881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234472802910543165936858587 351709204365814748905287881)
      ·
        refine ⟨263781903274361061678965911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351709204365814748905287881 263781903274361061678965911)
        ·
          refine ⟨395672854911541592518448867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263781903274361061678965911 395672854911541592518448867)
          ·
            refine ⟨593509282367312388777673301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395672854911541592518448867 593509282367312388777673301)
            ·
              refine ⟨6955186902741942055988359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 593509282367312388777673301 6955186902741942055988359)
              ·
                refine ⟨10432780354112913083982539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955186902741942055988359 10432780354112913083982539)
                ·
                  refine ⟨15649170531169369625973809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10432780354112913083982539 15649170531169369625973809)
                  ·
                    refine ⟨11736877898377027219480357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15649170531169369625973809 11736877898377027219480357)
                    ·
                      refine ⟨2200664605945692603652567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11736877898377027219480357 2200664605945692603652567)
                      ·
                        rfl

theorem cell23_4285779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_4285779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285779 prefixEnd_4285779 := by exact prefixLift 4285779
  have htrace : WordTrace (prefixWord ++ tailWord_4285779) baseStart_4285779 baseEnd_4285779 := by
    simpa [prefixWord, tailWord_4285779, baseEnd_4285779] using wordTrace_append hprefix tailTrace_4285779
  have hstable : (prefixWord ++ tailWord_4285779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285779).length < 2 ^ (prefixWord ++ tailWord_4285779).sum := by decide
  have hdescent : baseEnd_4285779 < baseStart_4285779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285783 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_4285783 : Nat := 118140960795 + 4285783 * 2 ^ 59
def prefixEnd_4285783 : Nat := 4983230072969 + 3 ^ 40 * 4285783 * 2
def baseEnd_4285783 : Nat := 2200666659868310588002549

theorem tailTrace_4285783 : CollatzResearch.WordTrace tailWord_4285783 prefixEnd_4285783 2200666659868310588002549 := by
  unfold tailWord_4285783
  simp only [CollatzResearch.WordTrace]
  refine ⟨156315347832347619307718003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104210231888231746205145335 156315347832347619307718003)
  ·
    refine ⟨234473021748521428961577005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156315347832347619307718003 234473021748521428961577005)
    ·
      refine ⟨87927383155695535860591377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234473021748521428961577005 87927383155695535860591377)
      ·
        refine ⟨65945537366771651895443533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87927383155695535860591377 65945537366771651895443533)
        ·
          refine ⟨24729576512539369460791325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65945537366771651895443533 24729576512539369460791325)
          ·
            refine ⟨9273591192202263547796747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24729576512539369460791325 9273591192202263547796747)
            ·
              refine ⟨13910386788303395321695121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9273591192202263547796747 13910386788303395321695121)
              ·
                refine ⟨10432790091227546491271341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13910386788303395321695121 10432790091227546491271341)
                ·
                  refine ⟨3912296284210329934226753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10432790091227546491271341 3912296284210329934226753)
                  ·
                    refine ⟨2934222213157747450670065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3912296284210329934226753 2934222213157747450670065)
                    ·
                      refine ⟨2200666659868310588002549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934222213157747450670065 2200666659868310588002549)
                      ·
                        rfl

theorem cell23_4285783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_4285783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285783 prefixEnd_4285783 := by exact prefixLift 4285783
  have htrace : WordTrace (prefixWord ++ tailWord_4285783) baseStart_4285783 baseEnd_4285783 := by
    simpa [prefixWord, tailWord_4285783, baseEnd_4285783] using wordTrace_append hprefix tailTrace_4285783
  have hstable : (prefixWord ++ tailWord_4285783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285783).length < 2 ^ (prefixWord ++ tailWord_4285783).sum := by decide
  have hdescent : baseEnd_4285783 < baseStart_4285783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285800 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4285800 : Nat := 118140960795 + 4285800 * 2 ^ 59
def prefixEnd_4285800 : Nat := 4983230072969 + 3 ^ 40 * 4285800 * 2
def baseEnd_4285800 : Nat := 2200675389039437021489971

theorem tailTrace_4285800 : CollatzResearch.WordTrace tailWord_4285800 prefixEnd_4285800 2200675389039437021489971 := by
  unfold tailWord_4285800
  simp only [CollatzResearch.WordTrace]
  refine ⟨78157983936643015605543427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104210645248857354140724569 78157983936643015605543427)
  ·
    refine ⟨117236975904964523408315141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78157983936643015605543427 117236975904964523408315141)
    ·
      refine ⟨21981932982180848139059089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117236975904964523408315141 21981932982180848139059089)
      ·
        refine ⟨16486449736635636104294317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21981932982180848139059089 16486449736635636104294317)
        ·
          refine ⟨6182418651238363539110369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16486449736635636104294317 6182418651238363539110369)
          ·
            refine ⟨4636813988428772654332777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6182418651238363539110369 4636813988428772654332777)
            ·
              refine ⟨3477610491321579490749583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636813988428772654332777 3477610491321579490749583)
              ·
                refine ⟨5216415736982369236124375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477610491321579490749583 5216415736982369236124375)
                ·
                  refine ⟨7824623605473553854186563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5216415736982369236124375 7824623605473553854186563)
                  ·
                    refine ⟨11736935408210330781279845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7824623605473553854186563 11736935408210330781279845)
                    ·
                      refine ⟨2200675389039437021489971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11736935408210330781279845 2200675389039437021489971)
                      ·
                        rfl

theorem cell23_4285800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4285800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285800 prefixEnd_4285800 := by exact prefixLift 4285800
  have htrace : WordTrace (prefixWord ++ tailWord_4285800) baseStart_4285800 baseEnd_4285800 := by
    simpa [prefixWord, tailWord_4285800, baseEnd_4285800] using wordTrace_append hprefix tailTrace_4285800
  have hstable : (prefixWord ++ tailWord_4285800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285800).length < 2 ^ (prefixWord ++ tailWord_4285800).sum := by decide
  have hdescent : baseEnd_4285800 < baseStart_4285800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285806 : List Nat := [4, 1, 2, 4, 1, 1, 10]
def baseStart_4285806 : Nat := 118140960795 + 4285806 * 2 ^ 59
def prefixEnd_4285806 : Nat := 4983230072969 + 3 ^ 40 * 4285806 * 2
def baseEnd_4285806 : Nat := 27168869999053876518703

theorem tailTrace_4285806 : CollatzResearch.WordTrace tailWord_4285806 prefixEnd_4285806 27168869999053876518703 := by
  unfold tailWord_4285806
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539523338908036779475659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104210791140842862823870181 19539523338908036779475659)
  ·
    refine ⟨29309285008362055169213489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19539523338908036779475659 29309285008362055169213489)
    ·
      refine ⟨21981963756271541376910117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29309285008362055169213489 21981963756271541376910117)
      ·
        refine ⟨4121618204300914008170647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21981963756271541376910117 4121618204300914008170647)
        ·
          refine ⟨6182427306451371012255971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121618204300914008170647 6182427306451371012255971)
          ·
            refine ⟨9273640959677056518383957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182427306451371012255971 9273640959677056518383957)
            ·
              refine ⟨27168869999053876518703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9273640959677056518383957 27168869999053876518703)
              ·
                rfl

theorem cell23_4285806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 10].length) (baseStart_4285806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285806 prefixEnd_4285806 := by exact prefixLift 4285806
  have htrace : WordTrace (prefixWord ++ tailWord_4285806) baseStart_4285806 baseEnd_4285806 := by
    simpa [prefixWord, tailWord_4285806, baseEnd_4285806] using wordTrace_append hprefix tailTrace_4285806
  have hstable : (prefixWord ++ tailWord_4285806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285806).length < 2 ^ (prefixWord ++ tailWord_4285806).sum := by decide
  have hdescent : baseEnd_4285806 < baseStart_4285806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285833 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_4285833 : Nat := 118140960795 + 4285833 * 2 ^ 59
def prefixEnd_4285833 : Nat := 4983230072969 + 3 ^ 40 * 4285833 * 2
def baseEnd_4285833 : Nat := 2200692333901035392377319

theorem tailTrace_4285833 : CollatzResearch.WordTrace tailWord_4285833 prefixEnd_4285833 2200692333901035392377319 := by
  unfold tailWord_4285833
  simp only [CollatzResearch.WordTrace]
  refine ⟨156317171482166477847038153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104211447654777651898025435 156317171482166477847038153)
  ·
    refine ⟨117237878611624858385278615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156317171482166477847038153 117237878611624858385278615)
    ·
      refine ⟨175856817917437287577917923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117237878611624858385278615 175856817917437287577917923)
      ·
        refine ⟨263785226876155931366876885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175856817917437287577917923 263785226876155931366876885)
        ·
          refine ⟨6182466254909904641411177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 263785226876155931366876885 6182466254909904641411177)
          ·
            refine ⟨4636849691182428481058383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6182466254909904641411177 4636849691182428481058383)
            ·
              refine ⟨6955274536773642721587575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636849691182428481058383 6955274536773642721587575)
              ·
                refine ⟨10432911805160464082381363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955274536773642721587575 10432911805160464082381363)
                ·
                  refine ⟨15649367707740696123572045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10432911805160464082381363 15649367707740696123572045)
                  ·
                    refine ⟨5868512890402761046339517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15649367707740696123572045 5868512890402761046339517)
                    ·
                      refine ⟨2200692333901035392377319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868512890402761046339517 2200692333901035392377319)
                      ·
                        rfl

theorem cell23_4285833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_4285833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285833 prefixEnd_4285833 := by exact prefixLift 4285833
  have htrace : WordTrace (prefixWord ++ tailWord_4285833) baseStart_4285833 baseEnd_4285833 := by
    simpa [prefixWord, tailWord_4285833, baseEnd_4285833] using wordTrace_append hprefix tailTrace_4285833
  have hstable : (prefixWord ++ tailWord_4285833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285833).length < 2 ^ (prefixWord ++ tailWord_4285833).sum := by decide
  have hdescent : baseEnd_4285833 < baseStart_4285833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285856 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2]
def baseStart_4285856 : Nat := 118140960795 + 4285856 * 2 ^ 59
def prefixEnd_4285856 : Nat := 4983230072969 + 3 ^ 40 * 4285856 * 2
def baseEnd_4285856 : Nat := 2200704143956088802389713

theorem tailTrace_4285856 : CollatzResearch.WordTrace tailWord_4285856 prefixEnd_4285856 2200704143956088802389713 := by
  unfold tailWord_4285856
  simp only [CollatzResearch.WordTrace]
  refine ⟨78159005180541576387562711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104212006907388768516750281 78159005180541576387562711)
  ·
    refine ⟨117238507770812364581344067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78159005180541576387562711 117238507770812364581344067)
    ·
      refine ⟨175857761656218546872016101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117238507770812364581344067 175857761656218546872016101)
      ·
        refine ⟨32973330310540977538503019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175857761656218546872016101 32973330310540977538503019)
        ·
          refine ⟨49459995465811466307754529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32973330310540977538503019 49459995465811466307754529)
          ·
            refine ⟨37094996599358599730815897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49459995465811466307754529 37094996599358599730815897)
            ·
              refine ⟨27821247449518949798111923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37094996599358599730815897 27821247449518949798111923)
              ·
                refine ⟨41731871174278424697167885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27821247449518949798111923 41731871174278424697167885)
                ·
                  refine ⟨15649451690354409261437957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41731871174278424697167885 15649451690354409261437957)
                  ·
                    refine ⟨2934272191941451736519617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15649451690354409261437957 2934272191941451736519617)
                    ·
                      refine ⟨2200704143956088802389713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934272191941451736519617 2200704143956088802389713)
                      ·
                        rfl

theorem cell23_4285856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_4285856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285856 prefixEnd_4285856 := by exact prefixLift 4285856
  have htrace : WordTrace (prefixWord ++ tailWord_4285856) baseStart_4285856 baseEnd_4285856 := by
    simpa [prefixWord, tailWord_4285856, baseEnd_4285856] using wordTrace_append hprefix tailTrace_4285856
  have hstable : (prefixWord ++ tailWord_4285856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285856).length < 2 ^ (prefixWord ++ tailWord_4285856).sum := by decide
  have hdescent : baseEnd_4285856 < baseStart_4285856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285859 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_4285859 : Nat := 118140960795 + 4285859 * 2 ^ 59
def prefixEnd_4285859 : Nat := 4983230072969 + 3 ^ 40 * 4285859 * 2
def baseEnd_4285859 : Nat := 2200705684398052290652199

theorem tailTrace_4285859 : CollatzResearch.WordTrace tailWord_4285859 prefixEnd_4285859 2200705684398052290652199 := by
  unfold tailWord_4285859
  simp only [CollatzResearch.WordTrace]
  refine ⟨156318119780072284287484631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104212079853381522858323087 156318119780072284287484631)
  ·
    refine ⟨234477179670108426431226947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156318119780072284287484631 234477179670108426431226947)
    ·
      refine ⟨351715769505162639646840421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234477179670108426431226947 351715769505162639646840421)
      ·
        refine ⟨65946706782217994933782579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 351715769505162639646840421 65946706782217994933782579)
        ·
          refine ⟨98920060173326992400673869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65946706782217994933782579 98920060173326992400673869)
          ·
            refine ⟨37095022564997622150252701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98920060173326992400673869 37095022564997622150252701)
            ·
              refine ⟨13910633461874108306344763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37095022564997622150252701 13910633461874108306344763)
              ·
                refine ⟨20865950192811162459517145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13910633461874108306344763 20865950192811162459517145)
                ·
                  refine ⟨15649462644608371844637859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20865950192811162459517145 15649462644608371844637859)
                  ·
                    refine ⟨23474193966912557766956789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15649462644608371844637859 23474193966912557766956789)
                    ·
                      refine ⟨2200705684398052290652199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23474193966912557766956789 2200705684398052290652199)
                      ·
                        rfl

theorem cell23_4285859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_4285859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285859 prefixEnd_4285859 := by exact prefixLift 4285859
  have htrace : WordTrace (prefixWord ++ tailWord_4285859) baseStart_4285859 baseEnd_4285859 := by
    simpa [prefixWord, tailWord_4285859, baseEnd_4285859] using wordTrace_append hprefix tailTrace_4285859
  have hstable : (prefixWord ++ tailWord_4285859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285859).length < 2 ^ (prefixWord ++ tailWord_4285859).sum := by decide
  have hdescent : baseEnd_4285859 < baseStart_4285859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285873 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4285873 : Nat := 118140960795 + 4285873 * 2 ^ 59
def prefixEnd_4285873 : Nat := 4983230072969 + 3 ^ 40 * 4285873 * 2
def baseEnd_4285873 : Nat := 2200712873127215235877135

theorem tailTrace_4285873 : CollatzResearch.WordTrace tailWord_4285873 prefixEnd_4285873 2200712873127215235877135 := by
  unfold tailWord_4285873
  simp only [CollatzResearch.WordTrace]
  refine ⟨156318630402021564678494273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104212420268014376452329515 156318630402021564678494273)
  ·
    refine ⟨117238972801516173508870705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156318630402021564678494273 117238972801516173508870705)
    ·
      refine ⟨87929229601137130131653029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117238972801516173508870705 87929229601137130131653029)
      ·
        refine ⟨16486730550213211899684943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87929229601137130131653029 16486730550213211899684943)
        ·
          refine ⟨24730095825319817849527415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16486730550213211899684943 24730095825319817849527415)
          ·
            refine ⟨37095143737979726774291123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24730095825319817849527415 37095143737979726774291123)
            ·
              refine ⟨55642715606969590161436685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37095143737979726774291123 55642715606969590161436685)
              ·
                refine ⟨20866018352613596310538757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55642715606969590161436685 20866018352613596310538757)
                ·
                  refine ⟨3912378441115049308226017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20866018352613596310538757 3912378441115049308226017)
                  ·
                    refine ⟨2934283830836286981169513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3912378441115049308226017 2934283830836286981169513)
                    ·
                      refine ⟨2200712873127215235877135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934283830836286981169513 2200712873127215235877135)
                      ·
                        rfl

theorem cell23_4285873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4285873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285873 prefixEnd_4285873 := by exact prefixLift 4285873
  have htrace : WordTrace (prefixWord ++ tailWord_4285873) baseStart_4285873 baseEnd_4285873 := by
    simpa [prefixWord, tailWord_4285873, baseEnd_4285873] using wordTrace_append hprefix tailTrace_4285873
  have hstable : (prefixWord ++ tailWord_4285873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285873).length < 2 ^ (prefixWord ++ tailWord_4285873).sum := by decide
  have hdescent : baseEnd_4285873 < baseStart_4285873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285884 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4285884 : Nat := 118140960795 + 4285884 * 2 ^ 59
def prefixEnd_4285884 : Nat := 4983230072969 + 3 ^ 40 * 4285884 * 2
def baseEnd_4285884 : Nat := 2200718521414414692839585

theorem tailTrace_4285884 : CollatzResearch.WordTrace tailWord_4285884 prefixEnd_4285884 2200718521414414692839585 := by
  unfold tailWord_4285884
  simp only [CollatzResearch.WordTrace]
  refine ⟨78159515802490856778572353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104212687736654475704763137 78159515802490856778572353)
  ·
    refine ⟨58619636851868142583929265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78159515802490856778572353 58619636851868142583929265)
    ·
      refine ⟨43964727638901106937946949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58619636851868142583929265 43964727638901106937946949)
      ·
        refine ⟨8243386432293957550865053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43964727638901106937946949 8243386432293957550865053)
        ·
          refine ⟨3091269912110234081574395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8243386432293957550865053 3091269912110234081574395)
          ·
            refine ⟨4636904868165351122361593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091269912110234081574395 4636904868165351122361593)
            ·
              refine ⟨3477678651124013341771195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636904868165351122361593 3477678651124013341771195)
              ·
                refine ⟨5216517976686020012656793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477678651124013341771195 5216517976686020012656793)
                ·
                  refine ⟨3912388482514515009492595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5216517976686020012656793 3912388482514515009492595)
                  ·
                    refine ⟨5868582723771772514238893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912388482514515009492595 5868582723771772514238893)
                    ·
                      refine ⟨2200718521414414692839585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868582723771772514238893 2200718521414414692839585)
                      ·
                        rfl

theorem cell23_4285884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4285884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285884 prefixEnd_4285884 := by exact prefixLift 4285884
  have htrace : WordTrace (prefixWord ++ tailWord_4285884) baseStart_4285884 baseEnd_4285884 := by
    simpa [prefixWord, tailWord_4285884, baseEnd_4285884] using wordTrace_append hprefix tailTrace_4285884
  have hstable : (prefixWord ++ tailWord_4285884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285884).length < 2 ^ (prefixWord ++ tailWord_4285884).sum := by decide
  have hdescent : baseEnd_4285884 < baseStart_4285884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285919 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_4285919 : Nat := 118140960795 + 4285919 * 2 ^ 59
def prefixEnd_4285919 : Nat := 4983230072969 + 3 ^ 40 * 4285919 * 2
def baseEnd_4285919 : Nat := 2200736493237322055901923

theorem tailTrace_4285919 : CollatzResearch.WordTrace tailWord_4285919 prefixEnd_4285919 2200736493237322055901923 := by
  unfold tailWord_4285919
  simp only [CollatzResearch.WordTrace]
  refine ⟨156320308159854914534668811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104213538773236609689779207 156320308159854914534668811)
  ·
    refine ⟨234480462239782371802003217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156320308159854914534668811 234480462239782371802003217)
    ·
      refine ⟨175860346679836778851502413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234480462239782371802003217 175860346679836778851502413)
      ·
        refine ⟨65947630004938792069313405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175860346679836778851502413 65947630004938792069313405)
        ·
          refine ⟨24730361251852047025992527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65947630004938792069313405 24730361251852047025992527)
          ·
            refine ⟨37095541877778070538988791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24730361251852047025992527 37095541877778070538988791)
            ·
              refine ⟨55643312816667105808483187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37095541877778070538988791 55643312816667105808483187)
              ·
                refine ⟨83464969225000658712724781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55643312816667105808483187 83464969225000658712724781)
                ·
                  refine ⟨31299363459375247017271793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83464969225000658712724781 31299363459375247017271793)
                  ·
                    refine ⟨23474522594531435262953845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31299363459375247017271793 23474522594531435262953845)
                    ·
                      refine ⟨2200736493237322055901923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23474522594531435262953845 2200736493237322055901923)
                      ·
                        rfl

theorem cell23_4285919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_4285919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285919 prefixEnd_4285919 := by exact prefixLift 4285919
  have htrace : WordTrace (prefixWord ++ tailWord_4285919) baseStart_4285919 baseEnd_4285919 := by
    simpa [prefixWord, tailWord_4285919, baseEnd_4285919] using wordTrace_append hprefix tailTrace_4285919
  have hstable : (prefixWord ++ tailWord_4285919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285919).length < 2 ^ (prefixWord ++ tailWord_4285919).sum := by decide
  have hdescent : baseEnd_4285919 < baseStart_4285919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4285969 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 8]
def baseStart_4285969 : Nat := 118140960795 + 4285969 * 2 ^ 59
def prefixEnd_4285969 : Nat := 4983230072969 + 3 ^ 40 * 4285969 * 2
def baseEnd_4285969 : Nat := 244529129696671873364077

theorem tailTrace_4285969 : CollatzResearch.WordTrace tailWord_4285969 prefixEnd_4285969 244529129696671873364077 := by
  unfold tailWord_4285969
  simp only [CollatzResearch.WordTrace]
  refine ⟨156322131809673773073988961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104214754539782515382659307 156322131809673773073988961)
  ·
    refine ⟨117241598857255329805491721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156322131809673773073988961 117241598857255329805491721)
    ·
      refine ⟨87931199142941497354118791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117241598857255329805491721 87931199142941497354118791)
      ·
        refine ⟨131896798714412246031178187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87931199142941497354118791 131896798714412246031178187)
        ·
          refine ⟨197845198071618369046767281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131896798714412246031178187 197845198071618369046767281)
          ·
            refine ⟨148383898553713776785075461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197845198071618369046767281 148383898553713776785075461)
            ·
              refine ⟨27821980978821333147201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148383898553713776785075461 27821980978821333147201649)
              ·
                refine ⟨20866485734115999860401237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27821980978821333147201649 20866485734115999860401237)
                ·
                  refine ⟨244529129696671873364077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20866485734115999860401237 244529129696671873364077)
                  ·
                    rfl

theorem cell23_4285969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_4285969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4285969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4285969 prefixEnd_4285969 := by exact prefixLift 4285969
  have htrace : WordTrace (prefixWord ++ tailWord_4285969) baseStart_4285969 baseEnd_4285969 := by
    simpa [prefixWord, tailWord_4285969, baseEnd_4285969] using wordTrace_append hprefix tailTrace_4285969
  have hstable : (prefixWord ++ tailWord_4285969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4285969).length < 2 ^ (prefixWord ++ tailWord_4285969).sum := by decide
  have hdescent : baseEnd_4285969 < baseStart_4285969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4285969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286003 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 6]
def baseStart_4286003 : Nat := 118140960795 + 4286003 * 2 ^ 59
def prefixEnd_4286003 : Nat := 4983230072969 + 3 ^ 40 * 4286003 * 2
def baseEnd_4286003 : Nat := 244531069512477747472393

theorem tailTrace_4286003 : CollatzResearch.WordTrace tailWord_4286003 prefixEnd_4286003 244531069512477747472393 := by
  unfold tailWord_4286003
  simp only [CollatzResearch.WordTrace]
  refine ⟨156323371891550596880726663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104215581261033731253817775 156323371891550596880726663)
  ·
    refine ⟨234485057837325895321089995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156323371891550596880726663 234485057837325895321089995)
    ·
      refine ⟨351727586755988842981634993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234485057837325895321089995 351727586755988842981634993)
      ·
        refine ⟨263795690066991632236226245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351727586755988842981634993 263795690066991632236226245)
        ·
          refine ⟨49461691887560931044292421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263795690066991632236226245 49461691887560931044292421)
          ·
            refine ⟨9274067228917674570804829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49461691887560931044292421 9274067228917674570804829)
            ·
              refine ⟨3477775210844127964051811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9274067228917674570804829 3477775210844127964051811)
              ·
                refine ⟨5216662816266191946077717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477775210844127964051811 5216662816266191946077717)
                ·
                  refine ⟨244531069512477747472393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5216662816266191946077717 244531069512477747472393)
                  ·
                    rfl

theorem cell23_4286003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 6].length) (baseStart_4286003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286003 prefixEnd_4286003 := by exact prefixLift 4286003
  have htrace : WordTrace (prefixWord ++ tailWord_4286003) baseStart_4286003 baseEnd_4286003 := by
    simpa [prefixWord, tailWord_4286003, baseEnd_4286003] using wordTrace_append hprefix tailTrace_4286003
  have hstable : (prefixWord ++ tailWord_4286003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286003).length < 2 ^ (prefixWord ++ tailWord_4286003).sum := by decide
  have hdescent : baseEnd_4286003 < baseStart_4286003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286070 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4286070 : Nat := 118140960795 + 4286070 * 2 ^ 59
def prefixEnd_4286070 : Nat := 4983230072969 + 3 ^ 40 * 4286070 * 2
def baseEnd_4286070 : Nat := 2200814028816150965113729

theorem tailTrace_4286070 : CollatzResearch.WordTrace tailWord_4286070 prefixEnd_4286070 2200814028816150965113729 := by
  unfold tailWord_4286070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9770363473894241707713479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104217210388205244882277109 9770363473894241707713479)
  ·
    refine ⟨14655545210841362561570219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9770363473894241707713479 14655545210841362561570219)
    ·
      refine ⟨21983317816262043842355329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14655545210841362561570219 21983317816262043842355329)
      ·
        refine ⟨16487488362196532881766497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21983317816262043842355329 16487488362196532881766497)
        ·
          refine ⟨12365616271647399661324873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16487488362196532881766497 12365616271647399661324873)
          ·
            refine ⟨9274212203735549745993655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12365616271647399661324873 9274212203735549745993655)
            ·
              refine ⟨13911318305603324618990483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274212203735549745993655 13911318305603324618990483)
              ·
                refine ⟨20866977458404986928485725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13911318305603324618990483 20866977458404986928485725)
                ·
                  refine ⟨7825116546901870098182147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20866977458404986928485725 7825116546901870098182147)
                  ·
                    refine ⟨11737674820352805147273221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7825116546901870098182147 11737674820352805147273221)
                    ·
                      refine ⟨2200814028816150965113729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11737674820352805147273221 2200814028816150965113729)
                      ·
                        rfl

theorem cell23_4286070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4286070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286070 prefixEnd_4286070 := by exact prefixLift 4286070
  have htrace : WordTrace (prefixWord ++ tailWord_4286070) baseStart_4286070 baseEnd_4286070 := by
    simpa [prefixWord, tailWord_4286070, baseEnd_4286070] using wordTrace_append hprefix tailTrace_4286070
  have hstable : (prefixWord ++ tailWord_4286070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286070).length < 2 ^ (prefixWord ++ tailWord_4286070).sum := by decide
  have hdescent : baseEnd_4286070 < baseStart_4286070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286073 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_4286073 : Nat := 118140960795 + 4286073 * 2 ^ 59
def prefixEnd_4286073 : Nat := 4983230072969 + 3 ^ 40 * 4286073 * 2
def baseEnd_4286073 : Nat := 2200815569258114453376215

theorem tailTrace_4286073 : CollatzResearch.WordTrace tailWord_4286073 prefixEnd_4286073 2200815569258114453376215 := by
  unfold tailWord_4286073
  simp only [CollatzResearch.WordTrace]
  refine ⟨156325925001296998835774873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104217283334197999223849915 156325925001296998835774873)
  ·
    refine ⟨117244443750972749126831155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156325925001296998835774873 117244443750972749126831155)
    ·
      refine ⟨175866665626459123690246733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117244443750972749126831155 175866665626459123690246733)
      ·
        refine ⟨65949999609922171383842525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175866665626459123690246733 65949999609922171383842525)
        ·
          refine ⟨24731249853720814268940947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65949999609922171383842525 24731249853720814268940947)
          ·
            refine ⟨37096874780581221403411421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24731249853720814268940947 37096874780581221403411421)
            ·
              refine ⟨13911328042717958026279283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37096874780581221403411421 13911328042717958026279283)
              ·
                refine ⟨20866992064076937039418925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13911328042717958026279283 20866992064076937039418925)
                ·
                  refine ⟨7825122024028851389782097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20866992064076937039418925 7825122024028851389782097)
                  ·
                    refine ⟨5868841518021638542336573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7825122024028851389782097 5868841518021638542336573)
                    ·
                      refine ⟨2200815569258114453376215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868841518021638542336573 2200815569258114453376215)
                      ·
                        rfl

theorem cell23_4286073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_4286073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286073 prefixEnd_4286073 := by exact prefixLift 4286073
  have htrace : WordTrace (prefixWord ++ tailWord_4286073) baseStart_4286073 baseEnd_4286073 := by
    simpa [prefixWord, tailWord_4286073, baseEnd_4286073] using wordTrace_append hprefix tailTrace_4286073
  have hstable : (prefixWord ++ tailWord_4286073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286073).length < 2 ^ (prefixWord ++ tailWord_4286073).sum := by decide
  have hdescent : baseEnd_4286073 < baseStart_4286073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286090 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4286090 : Nat := 118140960795 + 4286090 * 2 ^ 59
def prefixEnd_4286090 : Nat := 4983230072969 + 3 ^ 40 * 4286090 * 2
def baseEnd_4286090 : Nat := 2200824298429240886863637

theorem tailTrace_4286090 : CollatzResearch.WordTrace tailWord_4286090 prefixEnd_4286090 2200824298429240886863637 := by
  unfold tailWord_4286090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39081636260558852684785931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104217696694823607159429149 39081636260558852684785931)
  ·
    refine ⟨58622454390838279027178897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39081636260558852684785931 58622454390838279027178897)
    ·
      refine ⟨43966840793128709270384173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58622454390838279027178897 43966840793128709270384173)
      ·
        refine ⟨16487565297423265976394065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43966840793128709270384173 16487565297423265976394065)
        ·
          refine ⟨12365673973067449482295549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16487565297423265976394065 12365673973067449482295549)
          ·
            refine ⟨4637127739900293555860831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12365673973067449482295549 4637127739900293555860831)
            ·
              refine ⟨6955691609850440333791247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637127739900293555860831 6955691609850440333791247)
              ·
                refine ⟨10433537414775660500686871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955691609850440333791247 10433537414775660500686871)
                ·
                  refine ⟨15650306122163490751030307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10433537414775660500686871 15650306122163490751030307)
                  ·
                    refine ⟨23475459183245236126545461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15650306122163490751030307 23475459183245236126545461)
                    ·
                      refine ⟨2200824298429240886863637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23475459183245236126545461 2200824298429240886863637)
                      ·
                        rfl

theorem cell23_4286090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4286090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286090 prefixEnd_4286090 := by exact prefixLift 4286090
  have htrace : WordTrace (prefixWord ++ tailWord_4286090) baseStart_4286090 baseEnd_4286090 := by
    simpa [prefixWord, tailWord_4286090, baseEnd_4286090] using wordTrace_append hprefix tailTrace_4286090
  have hstable : (prefixWord ++ tailWord_4286090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286090).length < 2 ^ (prefixWord ++ tailWord_4286090).sum := by decide
  have hdescent : baseEnd_4286090 < baseStart_4286090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286098 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_4286098 : Nat := 118140960795 + 4286098 * 2 ^ 59
def prefixEnd_4286098 : Nat := 4983230072969 + 3 ^ 40 * 4286098 * 2
def baseEnd_4286098 : Nat := 2200828406274476855563601

theorem tailTrace_4286098 : CollatzResearch.WordTrace tailWord_4286098 prefixEnd_4286098 2200828406274476855563601 := by
  unfold tailWord_4286098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39081709206551607026358737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104217891217470952070289965 39081709206551607026358737)
  ·
    refine ⟨29311281904913705269769053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39081709206551607026358737 29311281904913705269769053)
    ·
      refine ⟨10991730714342639476163395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29311281904913705269769053 10991730714342639476163395)
      ·
        refine ⟨16487596071513959214245093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10991730714342639476163395 16487596071513959214245093)
        ·
          refine ⟨3091424263408867352670955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16487596071513959214245093 3091424263408867352670955)
          ·
            refine ⟨4637136395113301029006433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091424263408867352670955 4637136395113301029006433)
            ·
              refine ⟨3477852296334975771754825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637136395113301029006433 3477852296334975771754825)
              ·
                refine ⟨2608389222251231828816119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3477852296334975771754825 2608389222251231828816119)
                ·
                  refine ⟨3912583833376847743224179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2608389222251231828816119 3912583833376847743224179)
                  ·
                    refine ⟨5868875750065271614836269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912583833376847743224179 5868875750065271614836269)
                    ·
                      refine ⟨2200828406274476855563601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868875750065271614836269 2200828406274476855563601)
                      ·
                        rfl

theorem cell23_4286098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_4286098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286098 prefixEnd_4286098 := by exact prefixLift 4286098
  have htrace : WordTrace (prefixWord ++ tailWord_4286098) baseStart_4286098 baseEnd_4286098 := by
    simpa [prefixWord, tailWord_4286098, baseEnd_4286098] using wordTrace_append hprefix tailTrace_4286098
  have hstable : (prefixWord ++ tailWord_4286098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286098).length < 2 ^ (prefixWord ++ tailWord_4286098).sum := by decide
  have hdescent : baseEnd_4286098 < baseStart_4286098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286104 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4286104 : Nat := 118140960795 + 4286104 * 2 ^ 59
def prefixEnd_4286104 : Nat := 4983230072969 + 3 ^ 40 * 4286104 * 2
def baseEnd_4286104 : Nat := 2200831487158403832088573

theorem tailTrace_4286104 : CollatzResearch.WordTrace tailWord_4286104 prefixEnd_4286104 2200831487158403832088573 := by
  unfold tailWord_4286104
  simp only [CollatzResearch.WordTrace]
  refine ⟨78163527832092345565076683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104218037109456460753435577 78163527832092345565076683)
  ·
    refine ⟨117245291748138518347615025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78163527832092345565076683 117245291748138518347615025)
    ·
      refine ⟨87933968811103888760711269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117245291748138518347615025 87933968811103888760711269)
      ·
        refine ⟨16487619152081979142633363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87933968811103888760711269 16487619152081979142633363)
        ·
          refine ⟨24731428728122968713950045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16487619152081979142633363 24731428728122968713950045)
          ·
            refine ⟨9274285773046113267731267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24731428728122968713950045 9274285773046113267731267)
            ·
              refine ⟨13911428659569169901596901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274285773046113267731267 13911428659569169901596901)
              ·
                refine ⟨2608392873669219356549419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13911428659569169901596901 2608392873669219356549419)
                ·
                  refine ⟨3912589310503829034824129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2608392873669219356549419 3912589310503829034824129)
                  ·
                    refine ⟨2934441982877871776118097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3912589310503829034824129 2934441982877871776118097)
                    ·
                      refine ⟨2200831487158403832088573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934441982877871776118097 2200831487158403832088573)
                      ·
                        rfl

theorem cell23_4286104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4286104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286104 prefixEnd_4286104 := by exact prefixLift 4286104
  have htrace : WordTrace (prefixWord ++ tailWord_4286104) baseStart_4286104 baseEnd_4286104 := by
    simpa [prefixWord, tailWord_4286104, baseEnd_4286104] using wordTrace_append hprefix tailTrace_4286104
  have hstable : (prefixWord ++ tailWord_4286104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286104).length < 2 ^ (prefixWord ++ tailWord_4286104).sum := by decide
  have hdescent : baseEnd_4286104 < baseStart_4286104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286110 : List Nat := [4, 3, 1, 1, 1, 4, 1, 8]
def baseStart_4286110 : Nat := 118140960795 + 4286110 * 2 ^ 59
def prefixEnd_4286110 : Nat := 4983230072969 + 3 ^ 40 * 4286110 * 2
def baseEnd_4286110 : Nat := 81512391408975215133835

theorem tailTrace_4286110 : CollatzResearch.WordTrace tailWord_4286110 prefixEnd_4286110 81512391408975215133835 := by
  unfold tailWord_4286110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19540909312770369269358973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104218183001441969436581189 19540909312770369269358973)
  ·
    refine ⟨7327840992288888476009615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19540909312770369269358973 7327840992288888476009615)
    ·
      refine ⟨10991761488433332714014423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7327840992288888476009615 10991761488433332714014423)
      ·
        refine ⟨16487642232649999071021635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10991761488433332714014423 16487642232649999071021635)
        ·
          refine ⟨24731463348974998606532453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16487642232649999071021635 24731463348974998606532453)
          ·
            refine ⟨4637149377932812238724835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24731463348974998606532453 4637149377932812238724835)
            ·
              refine ⟨6955724066899218358087253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637149377932812238724835 6955724066899218358087253)
              ·
                refine ⟨81512391408975215133835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6955724066899218358087253 81512391408975215133835)
                ·
                  rfl

theorem cell23_4286110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_4286110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286110 prefixEnd_4286110 := by exact prefixLift 4286110
  have htrace : WordTrace (prefixWord ++ tailWord_4286110) baseStart_4286110 baseEnd_4286110 := by
    simpa [prefixWord, tailWord_4286110, baseEnd_4286110] using wordTrace_append hprefix tailTrace_4286110
  have hstable : (prefixWord ++ tailWord_4286110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286110).length < 2 ^ (prefixWord ++ tailWord_4286110).sum := by decide
  have hdescent : baseEnd_4286110 < baseStart_4286110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286130 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_4286130 : Nat := 118140960795 + 4286130 * 2 ^ 59
def prefixEnd_4286130 : Nat := 4983230072969 + 3 ^ 40 * 4286130 * 2
def baseEnd_4286130 : Nat := 2200844837655420730363453

theorem tailTrace_4286130 : CollatzResearch.WordTrace tailWord_4286130 prefixEnd_4286130 2200844837655420730363453 := by
  unfold tailWord_4286130
  simp only [CollatzResearch.WordTrace]
  refine ⟨39082000990522624392649961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104218669308060331713733229 39082000990522624392649961)
  ·
    refine ⟨29311500742891968294487471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39082000990522624392649961 29311500742891968294487471)
    ·
      refine ⟨43967251114337952441731207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29311500742891968294487471 43967251114337952441731207)
      ·
        refine ⟨65950876671506928662596811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43967251114337952441731207 65950876671506928662596811)
        ·
          refine ⟨98926315007260392993895217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65950876671506928662596811 98926315007260392993895217)
          ·
            refine ⟨74194736255445294745421413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98926315007260392993895217 74194736255445294745421413)
            ·
              refine ⟨13911513047895992764766515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74194736255445294745421413 13911513047895992764766515)
              ·
                refine ⟨20867269571843989147149773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13911513047895992764766515 20867269571843989147149773)
                ·
                  refine ⟨7825226089441495930181165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20867269571843989147149773 7825226089441495930181165)
                  ·
                    refine ⟨2934459783540560973817937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7825226089441495930181165 2934459783540560973817937)
                    ·
                      refine ⟨2200844837655420730363453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934459783540560973817937 2200844837655420730363453)
                      ·
                        rfl

theorem cell23_4286130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_4286130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286130 prefixEnd_4286130 := by exact prefixLift 4286130
  have htrace : WordTrace (prefixWord ++ tailWord_4286130) baseStart_4286130 baseEnd_4286130 := by
    simpa [prefixWord, tailWord_4286130, baseEnd_4286130] using wordTrace_append hprefix tailTrace_4286130
  have hstable : (prefixWord ++ tailWord_4286130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286130).length < 2 ^ (prefixWord ++ tailWord_4286130).sum := by decide
  have hdescent : baseEnd_4286130 < baseStart_4286130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286154 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_4286154 : Nat := 118140960795 + 4286154 * 2 ^ 59
def prefixEnd_4286154 : Nat := 4983230072969 + 3 ^ 40 * 4286154 * 2
def baseEnd_4286154 : Nat := 2200857161191128636463343

theorem tailTrace_4286154 : CollatzResearch.WordTrace tailWord_4286154 prefixEnd_4286154 2200857161191128636463343 := by
  unfold tailWord_4286154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39082219828500887417368379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104219252876002366446315677 39082219828500887417368379)
  ·
    refine ⟨58623329742751331126052569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39082219828500887417368379 58623329742751331126052569)
    ·
      refine ⟨43967497307063498344539427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58623329742751331126052569 43967497307063498344539427)
      ·
        refine ⟨65951245960595247516809141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43967497307063498344539427 65951245960595247516809141)
        ·
          refine ⟨6182929308805804454700857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65951245960595247516809141 6182929308805804454700857)
          ·
            refine ⟨4637196981604353341025643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6182929308805804454700857 4637196981604353341025643)
            ·
              refine ⟨6955795472406530011538465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637196981604353341025643 6955795472406530011538465)
              ·
                refine ⟨5216846604304897508653849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6955795472406530011538465 5216846604304897508653849)
                ·
                  refine ⟨3912634953228673131490387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5216846604304897508653849 3912634953228673131490387)
                  ·
                    refine ⟨5868952429843009697235581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912634953228673131490387 5868952429843009697235581)
                    ·
                      refine ⟨2200857161191128636463343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5868952429843009697235581 2200857161191128636463343)
                      ·
                        rfl

theorem cell23_4286154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_4286154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286154 prefixEnd_4286154 := by exact prefixLift 4286154
  have htrace : WordTrace (prefixWord ++ tailWord_4286154) baseStart_4286154 baseEnd_4286154 := by
    simpa [prefixWord, tailWord_4286154, baseEnd_4286154] using wordTrace_append hprefix tailTrace_4286154
  have hstable : (prefixWord ++ tailWord_4286154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286154).length < 2 ^ (prefixWord ++ tailWord_4286154).sum := by decide
  have hdescent : baseEnd_4286154 < baseStart_4286154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286277 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_4286277 : Nat := 118140960795 + 4286277 * 2 ^ 59
def prefixEnd_4286277 : Nat := 4983230072969 + 3 ^ 40 * 4286277 * 2
def baseEnd_4286277 : Nat := 733640106437210551741759

theorem tailTrace_4286277 : CollatzResearch.WordTrace tailWord_4286277 prefixEnd_4286277 733640106437210551741759 := by
  unfold tailWord_4286277
  simp only [CollatzResearch.WordTrace]
  refine ⟨156333365492557941676201085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104222243661705294450800723 156333365492557941676201085)
  ·
    refine ⟨58625012059709228128575407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156333365492557941676201085 58625012059709228128575407)
    ·
      refine ⟨87937518089563842192863111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58625012059709228128575407 87937518089563842192863111)
      ·
        refine ⟨131906277134345763289294667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87937518089563842192863111 131906277134345763289294667)
        ·
          refine ⟨197859415701518644933942001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131906277134345763289294667 197859415701518644933942001)
          ·
            refine ⟨148394561776138983700456501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197859415701518644933942001 148394561776138983700456501)
            ·
              refine ⟨13911990166513029721917797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148394561776138983700456501 13911990166513029721917797)
              ·
                refine ⟨2608498156221193072859587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13911990166513029721917797 2608498156221193072859587)
                ·
                  refine ⟨3912747234331789609289381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2608498156221193072859587 3912747234331789609289381)
                  ·
                    refine ⟨733640106437210551741759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3912747234331789609289381 733640106437210551741759)
                    ·
                      rfl

theorem cell23_4286277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_4286277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286277 prefixEnd_4286277 := by exact prefixLift 4286277
  have htrace : WordTrace (prefixWord ++ tailWord_4286277) baseStart_4286277 baseEnd_4286277 := by
    simpa [prefixWord, tailWord_4286277, baseEnd_4286277] using wordTrace_append hprefix tailTrace_4286277
  have hstable : (prefixWord ++ tailWord_4286277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286277).length < 2 ^ (prefixWord ++ tailWord_4286277).sum := by decide
  have hdescent : baseEnd_4286277 < baseStart_4286277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286290 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_4286290 : Nat := 118140960795 + 4286290 * 2 ^ 59
def prefixEnd_4286290 : Nat := 4983230072969 + 3 ^ 40 * 4286290 * 2
def baseEnd_4286290 : Nat := 244547443840015567151413

theorem tailTrace_4286290 : CollatzResearch.WordTrace tailWord_4286290 prefixEnd_4286290 244547443840015567151413 := by
  unfold tailWord_4286290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39083459910377711224106081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104222559761007229930949549 39083459910377711224106081)
  ·
    refine ⟨29312594932783283418079561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39083459910377711224106081 29312594932783283418079561)
    ·
      refine ⟨21984446199587462563559671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29312594932783283418079561 21984446199587462563559671)
      ·
        refine ⟨32976669299381193845339507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21984446199587462563559671 32976669299381193845339507)
        ·
          refine ⟨49465003949071790768009261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32976669299381193845339507 49465003949071790768009261)
          ·
            refine ⟨18549376480901921538003473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49465003949071790768009261 18549376480901921538003473)
            ·
              refine ⟨13912032360676441153502605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18549376480901921538003473 13912032360676441153502605)
              ·
                refine ⟨5217012135253665432563477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13912032360676441153502605 5217012135253665432563477)
                ·
                  refine ⟨244547443840015567151413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5217012135253665432563477 244547443840015567151413)
                  ·
                    rfl

theorem cell23_4286290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_4286290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286290 prefixEnd_4286290 := by exact prefixLift 4286290
  have htrace : WordTrace (prefixWord ++ tailWord_4286290) baseStart_4286290 baseEnd_4286290 := by
    simpa [prefixWord, tailWord_4286290, baseEnd_4286290] using wordTrace_append hprefix tailTrace_4286290
  have hstable : (prefixWord ++ tailWord_4286290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286290).length < 2 ^ (prefixWord ++ tailWord_4286290).sum := by decide
  have hdescent : baseEnd_4286290 < baseStart_4286290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286340 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_4286340 : Nat := 118140960795 + 4286340 * 2 ^ 59
def prefixEnd_4286340 : Nat := 4983230072969 + 3 ^ 40 * 4286340 * 2
def baseEnd_4286340 : Nat := 2200952668592864908737487

theorem tailTrace_4286340 : CollatzResearch.WordTrace tailWord_4286340 prefixEnd_4286340 2200952668592864908737487 := by
  unfold tailWord_4286340
  simp only [CollatzResearch.WordTrace]
  refine ⟨78167831645664851717872237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104223775527553135623829649 78167831645664851717872237)
  ·
    refine ⟨29312936867124319394202089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78167831645664851717872237 29312936867124319394202089)
    ·
      refine ⟨21984702650343239545651567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29312936867124319394202089 21984702650343239545651567)
      ·
        refine ⟨32977053975514859318477351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21984702650343239545651567 32977053975514859318477351)
        ·
          refine ⟨49465580963272288977716027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32977053975514859318477351 49465580963272288977716027)
          ·
            refine ⟨74198371444908433466574041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49465580963272288977716027 74198371444908433466574041)
            ·
              refine ⟨55648778583681325099930531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74198371444908433466574041 55648778583681325099930531)
              ·
                refine ⟨83473167875521987649895797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55648778583681325099930531 83473167875521987649895797)
                ·
                  refine ⟨7825609488330186342177731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83473167875521987649895797 7825609488330186342177731)
                  ·
                    refine ⟨11738414232495279513266597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7825609488330186342177731 11738414232495279513266597)
                    ·
                      refine ⟨2200952668592864908737487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11738414232495279513266597 2200952668592864908737487)
                      ·
                        rfl

theorem cell23_4286340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_4286340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286340 prefixEnd_4286340 := by exact prefixLift 4286340
  have htrace : WordTrace (prefixWord ++ tailWord_4286340) baseStart_4286340 baseEnd_4286340 := by
    simpa [prefixWord, tailWord_4286340, baseEnd_4286340] using wordTrace_append hprefix tailTrace_4286340
  have hstable : (prefixWord ++ tailWord_4286340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286340).length < 2 ^ (prefixWord ++ tailWord_4286340).sum := by decide
  have hdescent : baseEnd_4286340 < baseStart_4286340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286354 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_4286354 : Nat := 118140960795 + 4286354 * 2 ^ 59
def prefixEnd_4286354 : Nat := 4983230072969 + 3 ^ 40 * 4286354 * 2
def baseEnd_4286354 : Nat := 733653285774009284654141

theorem tailTrace_4286354 : CollatzResearch.WordTrace tailWord_4286354 prefixEnd_4286354 733653285774009284654141 := by
  unfold tailWord_4286354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39084043478319745956688529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104224115942185989217836077 39084043478319745956688529)
  ·
    refine ⟨29313032608739809467516397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39084043478319745956688529 29313032608739809467516397)
    ·
      refine ⟨10992387228277428550318649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29313032608739809467516397 10992387228277428550318649)
      ·
        refine ⟨8244290421208071412738987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10992387228277428550318649 8244290421208071412738987)
        ·
          refine ⟨12366435631812107119108481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8244290421208071412738987 12366435631812107119108481)
          ·
            refine ⟨9274826723859080339331361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12366435631812107119108481 9274826723859080339331361)
            ·
              refine ⟨6956120042894310254498521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9274826723859080339331361 6956120042894310254498521)
              ·
                refine ⟨5217090032170732690873891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6956120042894310254498521 5217090032170732690873891)
                ·
                  refine ⟨7825635048256099036310837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217090032170732690873891 7825635048256099036310837)
                  ·
                    refine ⟨733653285774009284654141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7825635048256099036310837 733653285774009284654141)
                    ·
                      rfl

theorem cell23_4286354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_4286354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286354 prefixEnd_4286354 := by exact prefixLift 4286354
  have htrace : WordTrace (prefixWord ++ tailWord_4286354) baseStart_4286354 baseEnd_4286354 := by
    simpa [prefixWord, tailWord_4286354, baseEnd_4286354] using wordTrace_append hprefix tailTrace_4286354
  have hstable : (prefixWord ++ tailWord_4286354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286354).length < 2 ^ (prefixWord ++ tailWord_4286354).sum := by decide
  have hdescent : baseEnd_4286354 < baseStart_4286354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286357 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_4286357 : Nat := 118140960795 + 4286357 * 2 ^ 59
def prefixEnd_4286357 : Nat := 4983230072969 + 3 ^ 40 * 4286357 * 2
def baseEnd_4286357 : Nat := 2200961397763991342224909

theorem tailTrace_4286357 : CollatzResearch.WordTrace tailWord_4286357 prefixEnd_4286357 2200961397763991342224909 := by
  unfold tailWord_4286357
  simp only [CollatzResearch.WordTrace]
  refine ⟨156336283332268115339113325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104224188888178743559408883 156336283332268115339113325)
  ·
    refine ⟨58626106249600543252167497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156336283332268115339113325 58626106249600543252167497)
    ·
      refine ⟨43969579687200407439125623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58626106249600543252167497 43969579687200407439125623)
      ·
        refine ⟨65954369530800611158688435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43969579687200407439125623 65954369530800611158688435)
        ·
          refine ⟨98931554296200916738032653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65954369530800611158688435 98931554296200916738032653)
          ·
            refine ⟨37099332861075343776762245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98931554296200916738032653 37099332861075343776762245)
            ·
              refine ⟨6956124911451626958142921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37099332861075343776762245 6956124911451626958142921)
              ·
                refine ⟨5217093683588720218607191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6956124911451626958142921 5217093683588720218607191)
                ·
                  refine ⟨7825640525383080327910787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217093683588720218607191 7825640525383080327910787)
                  ·
                    refine ⟨11738460788074620491866181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7825640525383080327910787 11738460788074620491866181)
                    ·
                      refine ⟨2200961397763991342224909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11738460788074620491866181 2200961397763991342224909)
                      ·
                        rfl

theorem cell23_4286357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_4286357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286357 prefixEnd_4286357 := by exact prefixLift 4286357
  have htrace : WordTrace (prefixWord ++ tailWord_4286357) baseStart_4286357 baseEnd_4286357 := by
    simpa [prefixWord, tailWord_4286357, baseEnd_4286357] using wordTrace_append hprefix tailTrace_4286357
  have hstable : (prefixWord ++ tailWord_4286357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286357).length < 2 ^ (prefixWord ++ tailWord_4286357).sum := by decide
  have hdescent : baseEnd_4286357 < baseStart_4286357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286428 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4286428 : Nat := 118140960795 + 4286428 * 2 ^ 59
def prefixEnd_4286428 : Nat := 4983230072969 + 3 ^ 40 * 4286428 * 2
def baseEnd_4286428 : Nat := 2200997854890460564437083

theorem tailTrace_4286428 : CollatzResearch.WordTrace tailWord_4286428 prefixEnd_4286428 2200997854890460564437083 := by
  unfold tailWord_4286428
  simp only [CollatzResearch.WordTrace]
  refine ⟨78169436457505447232473969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104225915276673929643298625 78169436457505447232473969)
  ·
    refine ⟨58627077343129085424355477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78169436457505447232473969 58627077343129085424355477)
    ·
      refine ⟨2748144250459175879266663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58627077343129085424355477 2748144250459175879266663)
      ·
        refine ⟨4122216375688763818899995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748144250459175879266663 4122216375688763818899995)
        ·
          refine ⟨6183324563533145728349993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122216375688763818899995 6183324563533145728349993)
          ·
            refine ⟨4637493422649859296262495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6183324563533145728349993 4637493422649859296262495)
            ·
              refine ⟨6956240133974788944393743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637493422649859296262495 6956240133974788944393743)
              ·
                refine ⟨10434360200962183416590615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6956240133974788944393743 10434360200962183416590615)
                ·
                  refine ⟨15651540301443275124885923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10434360200962183416590615 15651540301443275124885923)
                  ·
                    refine ⟨23477310452164912687328885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15651540301443275124885923 23477310452164912687328885)
                    ·
                      refine ⟨2200997854890460564437083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23477310452164912687328885 2200997854890460564437083)
                      ·
                        rfl

theorem cell23_4286428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4286428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286428 prefixEnd_4286428 := by exact prefixLift 4286428
  have htrace : WordTrace (prefixWord ++ tailWord_4286428) baseStart_4286428 baseEnd_4286428 := by
    simpa [prefixWord, tailWord_4286428, baseEnd_4286428] using wordTrace_append hprefix tailTrace_4286428
  have hstable : (prefixWord ++ tailWord_4286428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286428).length < 2 ^ (prefixWord ++ tailWord_4286428).sum := by decide
  have hdescent : baseEnd_4286428 < baseStart_4286428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286440 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_4286440 : Nat := 118140960795 + 4286440 * 2 ^ 59
def prefixEnd_4286440 : Nat := 4983230072969 + 3 ^ 40 * 4286440 * 2
def baseEnd_4286440 : Nat := 733668005552771505829009

theorem tailTrace_4286440 : CollatzResearch.WordTrace tailWord_4286440 prefixEnd_4286440 733668005552771505829009 := by
  unfold tailWord_4286440
  simp only [CollatzResearch.WordTrace]
  refine ⟨78169655295483710257192387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104226207060644947009589849 78169655295483710257192387)
  ·
    refine ⟨117254482943225565385788581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78169655295483710257192387 117254482943225565385788581)
    ·
      refine ⟨21985215551854793509835359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117254482943225565385788581 21985215551854793509835359)
      ·
        refine ⟨32977823327782190264753039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21985215551854793509835359 32977823327782190264753039)
        ·
          refine ⟨49466734991673285397129559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32977823327782190264753039 49466734991673285397129559)
          ·
            refine ⟨74200102487509928095694339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49466734991673285397129559 74200102487509928095694339)
            ·
              refine ⟨111300153731264892143541509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74200102487509928095694339 111300153731264892143541509)
              ·
                refine ⟨20868778824612167276914033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111300153731264892143541509 20868778824612167276914033)
                ·
                  refine ⟨15651584118459125457685525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20868778824612167276914033 15651584118459125457685525)
                  ·
                    refine ⟨733668005552771505829009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15651584118459125457685525 733668005552771505829009)
                    ·
                      rfl

theorem cell23_4286440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_4286440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286440 prefixEnd_4286440 := by exact prefixLift 4286440
  have htrace : WordTrace (prefixWord ++ tailWord_4286440) baseStart_4286440 baseEnd_4286440 := by
    simpa [prefixWord, tailWord_4286440, baseEnd_4286440] using wordTrace_append hprefix tailTrace_4286440
  have hstable : (prefixWord ++ tailWord_4286440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286440).length < 2 ^ (prefixWord ++ tailWord_4286440).sum := by decide
  have hdescent : baseEnd_4286440 < baseStart_4286440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286447 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 3, 4, 2]
def baseStart_4286447 : Nat := 118140960795 + 4286447 * 2 ^ 59
def prefixEnd_4286447 : Nat := 4983230072969 + 3 ^ 40 * 4286447 * 2
def baseEnd_4286447 : Nat := 2201007611022895990099495

theorem tailTrace_4286447 : CollatzResearch.WordTrace tailWord_4286447 prefixEnd_4286447 2201007611022895990099495 := by
  unfold tailWord_4286447
  simp only [CollatzResearch.WordTrace]
  refine ⟨156339565901942060709889595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104226377267961373806593063 156339565901942060709889595)
  ·
    refine ⟨234509348852913091064834393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156339565901942060709889595 234509348852913091064834393)
    ·
      refine ⟨175882011639684818298625795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234509348852913091064834393 175882011639684818298625795)
      ·
        refine ⟨263823017459527227447938693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175882011639684818298625795 263823017459527227447938693)
        ·
          refine ⟨49466815773661355146488505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263823017459527227447938693 49466815773661355146488505)
          ·
            refine ⟨37100111830246016359866379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49466815773661355146488505 37100111830246016359866379)
            ·
              refine ⟨55650167745369024539799569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37100111830246016359866379 55650167745369024539799569)
              ·
                refine ⟨41737625809026768404849677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55650167745369024539799569 41737625809026768404849677)
                ·
                  refine ⟨15651609678385038151818629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41737625809026768404849677 15651609678385038151818629)
                  ·
                    refine ⟨2934676814697194653465993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15651609678385038151818629 2934676814697194653465993)
                    ·
                      refine ⟨2201007611022895990099495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934676814697194653465993 2201007611022895990099495)
                      ·
                        rfl

theorem cell23_4286447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4, 2].length) (baseStart_4286447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286447 prefixEnd_4286447 := by exact prefixLift 4286447
  have htrace : WordTrace (prefixWord ++ tailWord_4286447) baseStart_4286447 baseEnd_4286447 := by
    simpa [prefixWord, tailWord_4286447, baseEnd_4286447] using wordTrace_append hprefix tailTrace_4286447
  have hstable : (prefixWord ++ tailWord_4286447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286447).length < 2 ^ (prefixWord ++ tailWord_4286447).sum := by decide
  have hdescent : baseEnd_4286447 < baseStart_4286447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286485 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_4286485 : Nat := 118140960795 + 4286485 * 2 ^ 59
def prefixEnd_4286485 : Nat := 4983230072969 + 3 ^ 40 * 4286485 * 2
def baseEnd_4286485 : Nat := 2201027123287766841424321

theorem tailTrace_4286485 : CollatzResearch.WordTrace tailWord_4286485 prefixEnd_4286485 2201027123287766841424321 := by
  unfold tailWord_4286485
  simp only [CollatzResearch.WordTrace]
  refine ⟨156340951875804393199772909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104227301250536262133181939 156340951875804393199772909)
  ·
    refine ⟨58627856953426647449914841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156340951875804393199772909 58627856953426647449914841)
    ·
      refine ⟨43970892715069985587436131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58627856953426647449914841 43970892715069985587436131)
      ·
        refine ⟨65956339072604978381154197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43970892715069985587436131 65956339072604978381154197)
        ·
          refine ⟨3091703394028358361616603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65956339072604978381154197 3091703394028358361616603)
          ·
            refine ⟨4637555091042537542424905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091703394028358361616603 4637555091042537542424905)
            ·
              refine ⟨3478166318281903156818679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637555091042537542424905 3478166318281903156818679)
              ·
                refine ⟨5217249477422854735228019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478166318281903156818679 5217249477422854735228019)
                ·
                  refine ⟨7825874216134282102842029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217249477422854735228019 7825874216134282102842029)
                  ·
                    refine ⟨2934702831050355788565761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7825874216134282102842029 2934702831050355788565761)
                    ·
                      refine ⟨2201027123287766841424321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934702831050355788565761 2201027123287766841424321)
                      ·
                        rfl

theorem cell23_4286485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_4286485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286485 prefixEnd_4286485 := by exact prefixLift 4286485
  have htrace : WordTrace (prefixWord ++ tailWord_4286485) baseStart_4286485 baseEnd_4286485 := by
    simpa [prefixWord, tailWord_4286485, baseEnd_4286485] using wordTrace_append hprefix tailTrace_4286485
  have hstable : (prefixWord ++ tailWord_4286485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286485).length < 2 ^ (prefixWord ++ tailWord_4286485).sum := by decide
  have hdescent : baseEnd_4286485 < baseStart_4286485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286507 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 5, 2]
def baseStart_4286507 : Nat := 118140960795 + 4286507 * 2 ^ 59
def prefixEnd_4286507 : Nat := 4983230072969 + 3 ^ 40 * 4286507 * 2
def baseEnd_4286507 : Nat := 2201038419862165755349219

theorem tailTrace_4286507 : CollatzResearch.WordTrace tailWord_4286507 prefixEnd_4286507 2201038419862165755349219 := by
  unfold tailWord_4286507
  simp only [CollatzResearch.WordTrace]
  refine ⟨156341754281724690957073775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104227836187816460638049183 156341754281724690957073775)
  ·
    refine ⟨234512631422587036435610663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156341754281724690957073775 234512631422587036435610663)
    ·
      refine ⟨351768947133880554653415995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234512631422587036435610663 351768947133880554653415995)
      ·
        refine ⟨527653420700820831980123993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351768947133880554653415995 527653420700820831980123993)
        ·
          refine ⟨395740065525615623985092995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527653420700820831980123993 395740065525615623985092995)
          ·
            refine ⟨593610098288423435977639493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395740065525615623985092995 593610098288423435977639493)
            ·
              refine ⟨111301893429079394245807405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 593610098288423435977639493 111301893429079394245807405)
              ·
                refine ⟨41738210035904772842177777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111301893429079394245807405 41738210035904772842177777)
                ·
                  refine ⟨31303657526928579631633333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41738210035904772842177777 31303657526928579631633333)
                  ·
                    refine ⟨2934717893149554340465625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31303657526928579631633333 2934717893149554340465625)
                    ·
                      refine ⟨2201038419862165755349219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934717893149554340465625 2201038419862165755349219)
                      ·
                        rfl

theorem cell23_4286507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5, 2].length) (baseStart_4286507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286507 prefixEnd_4286507 := by exact prefixLift 4286507
  have htrace : WordTrace (prefixWord ++ tailWord_4286507) baseStart_4286507 baseEnd_4286507 := by
    simpa [prefixWord, tailWord_4286507, baseEnd_4286507] using wordTrace_append hprefix tailTrace_4286507
  have hstable : (prefixWord ++ tailWord_4286507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286507).length < 2 ^ (prefixWord ++ tailWord_4286507).sum := by decide
  have hdescent : baseEnd_4286507 < baseStart_4286507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286534 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_4286534 : Nat := 118140960795 + 4286534 * 2 ^ 59
def prefixEnd_4286534 : Nat := 4983230072969 + 3 ^ 40 * 4286534 * 2
def baseEnd_4286534 : Nat := 733684094613279049903865

theorem tailTrace_4286534 : CollatzResearch.WordTrace tailWord_4286534 prefixEnd_4286534 733684094613279049903865 := by
  unfold tailWord_4286534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885710595394589830259583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104228492701751249712204437 4885710595394589830259583)
  ·
    refine ⟨7328565893091884745389375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885710595394589830259583 7328565893091884745389375)
    ·
      refine ⟨10992848839637827118084063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7328565893091884745389375 10992848839637827118084063)
      ·
        refine ⟨16489273259456740677126095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10992848839637827118084063 16489273259456740677126095)
        ·
          refine ⟨24733909889185111015689143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16489273259456740677126095 24733909889185111015689143)
          ·
            refine ⟨37100864833777666523533715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24733909889185111015689143 37100864833777666523533715)
            ·
              refine ⟨55651297250666499785300573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37100864833777666523533715 55651297250666499785300573)
              ·
                refine ⟨20869236468999937419487715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55651297250666499785300573 20869236468999937419487715)
                ·
                  refine ⟨31303854703499906129231573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20869236468999937419487715 31303854703499906129231573)
                  ·
                    refine ⟨733684094613279049903865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31303854703499906129231573 733684094613279049903865)
                    ·
                      rfl

theorem cell23_4286534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_4286534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286534 prefixEnd_4286534 := by exact prefixLift 4286534
  have htrace : WordTrace (prefixWord ++ tailWord_4286534) baseStart_4286534 baseEnd_4286534 := by
    simpa [prefixWord, tailWord_4286534, baseEnd_4286534] using wordTrace_append hprefix tailTrace_4286534
  have hstable : (prefixWord ++ tailWord_4286534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286534).length < 2 ^ (prefixWord ++ tailWord_4286534).sum := by decide
  have hdescent : baseEnd_4286534 < baseStart_4286534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286537 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_4286537 : Nat := 118140960795 + 4286537 * 2 ^ 59
def prefixEnd_4286537 : Nat := 4983230072969 + 3 ^ 40 * 4286537 * 2
def baseEnd_4286537 : Nat := 2201053824281800637974081

theorem tailTrace_4286537 : CollatzResearch.WordTrace tailWord_4286537 prefixEnd_4286537 2201053824281800637974081 := by
  unfold tailWord_4286537
  simp only [CollatzResearch.WordTrace]
  refine ⟨156342848471616006080665865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104228565647744004053777243 156342848471616006080665865)
  ·
    refine ⟨117257136353712004560499399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156342848471616006080665865 117257136353712004560499399)
    ·
      refine ⟨175885704530568006840749099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117257136353712004560499399 175885704530568006840749099)
      ·
        refine ⟨263828556795852010261123649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175885704530568006840749099 263828556795852010261123649)
        ·
          refine ⟨197871417596889007695842737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263828556795852010261123649 197871417596889007695842737)
          ·
            refine ⟨148403563197666755771882053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197871417596889007695842737 148403563197666755771882053)
            ·
              refine ⟨27825668099562516707227885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148403563197666755771882053 27825668099562516707227885)
              ·
                refine ⟨10434625537335943765210457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27825668099562516707227885 10434625537335943765210457)
                ·
                  refine ⟨7825969153001957823907843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10434625537335943765210457 7825969153001957823907843)
                  ·
                    refine ⟨11738953729502936735861765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7825969153001957823907843 11738953729502936735861765)
                    ·
                      refine ⟨2201053824281800637974081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11738953729502936735861765 2201053824281800637974081)
                      ·
                        rfl

theorem cell23_4286537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_4286537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286537 prefixEnd_4286537 := by exact prefixLift 4286537
  have htrace : WordTrace (prefixWord ++ tailWord_4286537) baseStart_4286537 baseEnd_4286537 := by
    simpa [prefixWord, tailWord_4286537, baseEnd_4286537] using wordTrace_append hprefix tailTrace_4286537
  have hstable : (prefixWord ++ tailWord_4286537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286537).length < 2 ^ (prefixWord ++ tailWord_4286537).sum := by decide
  have hdescent : baseEnd_4286537 < baseStart_4286537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286564 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_4286564 : Nat := 118140960795 + 4286564 * 2 ^ 59
def prefixEnd_4286564 : Nat := 4983230072969 + 3 ^ 40 * 4286564 * 2
def baseEnd_4286564 : Nat := 733689229419824010778819

theorem tailTrace_4286564 : CollatzResearch.WordTrace tailWord_4286564 prefixEnd_4286564 733689229419824010778819 := by
  unfold tailWord_4286564
  simp only [CollatzResearch.WordTrace]
  refine ⟨78171916621259094845949373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104229222161678793127932497 78171916621259094845949373)
  ·
    refine ⟨29314468732972160567231015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78171916621259094845949373 29314468732972160567231015)
    ·
      refine ⟨43971703099458240850846523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29314468732972160567231015 43971703099458240850846523)
      ·
        refine ⟨65957554649187361276269785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43971703099458240850846523 65957554649187361276269785)
        ·
          refine ⟨49468165986890520957202339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65957554649187361276269785 49468165986890520957202339)
          ·
            refine ⟨74202248980335781435803509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49468165986890520957202339 74202248980335781435803509)
            ·
              refine ⟨6956460841906479509606579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74202248980335781435803509 6956460841906479509606579)
              ·
                refine ⟨10434691262859719264409869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6956460841906479509606579 10434691262859719264409869)
                ·
                  refine ⟨3913009223572394724153701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10434691262859719264409869 3913009223572394724153701)
                  ·
                    refine ⟨733689229419824010778819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3913009223572394724153701 733689229419824010778819)
                    ·
                      rfl

theorem cell23_4286564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_4286564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286564 prefixEnd_4286564 := by exact prefixLift 4286564
  have htrace : WordTrace (prefixWord ++ tailWord_4286564) baseStart_4286564 baseEnd_4286564 := by
    simpa [prefixWord, tailWord_4286564, baseEnd_4286564] using wordTrace_append hprefix tailTrace_4286564
  have hstable : (prefixWord ++ tailWord_4286564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286564).length < 2 ^ (prefixWord ++ tailWord_4286564).sum := by decide
  have hdescent : baseEnd_4286564 < baseStart_4286564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286574 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_4286574 : Nat := 118140960795 + 4286574 * 2 ^ 59
def prefixEnd_4286574 : Nat := 4983230072969 + 3 ^ 40 * 4286574 * 2
def baseEnd_4286574 : Nat := 2201072823066016993211411

theorem tailTrace_4286574 : CollatzResearch.WordTrace tailWord_4286574 prefixEnd_4286574 2201072823066016993211411 := by
  unfold tailWord_4286574
  simp only [CollatzResearch.WordTrace]
  refine ⟨19543024746560245174970347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104229465314987974266508517 19543024746560245174970347)
  ·
    refine ⟨29314537119840367762455521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19543024746560245174970347 29314537119840367762455521)
    ·
      refine ⟨21985902839880275821841641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29314537119840367762455521 21985902839880275821841641)
      ·
        refine ⟨16489427129910206866381231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21985902839880275821841641 16489427129910206866381231)
        ·
          refine ⟨24734140694865310299571847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16489427129910206866381231 24734140694865310299571847)
          ·
            refine ⟨37101211042297965449357771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24734140694865310299571847 37101211042297965449357771)
            ·
              refine ⟨55651816563446948174036657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37101211042297965449357771 55651816563446948174036657)
              ·
                refine ⟨41738862422585211130527493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55651816563446948174036657 41738862422585211130527493)
                ·
                  refine ⟨7826036704234727086973905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41738862422585211130527493 7826036704234727086973905)
                  ·
                    refine ⟨5869527528176045315230429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7826036704234727086973905 5869527528176045315230429)
                    ·
                      refine ⟨2201072823066016993211411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5869527528176045315230429 2201072823066016993211411)
                      ·
                        rfl

theorem cell23_4286574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_4286574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286574 prefixEnd_4286574 := by exact prefixLift 4286574
  have htrace : WordTrace (prefixWord ++ tailWord_4286574) baseStart_4286574 baseEnd_4286574 := by
    simpa [prefixWord, tailWord_4286574, baseEnd_4286574] using wordTrace_append hprefix tailTrace_4286574
  have hstable : (prefixWord ++ tailWord_4286574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286574).length < 2 ^ (prefixWord ++ tailWord_4286574).sum := by decide
  have hdescent : baseEnd_4286574 < baseStart_4286574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286577 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 6]
def baseStart_4286577 : Nat := 118140960795 + 4286577 * 2 ^ 59
def prefixEnd_4286577 : Nat := 4983230072969 + 3 ^ 40 * 4286577 * 2
def baseEnd_4286577 : Nat := 244563818167553386830433

theorem tailTrace_4286577 : CollatzResearch.WordTrace tailWord_4286577 prefixEnd_4286577 244563818167553386830433 := by
  unfold tailWord_4286577
  simp only [CollatzResearch.WordTrace]
  refine ⟨156344307391471092912121985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104229538260980728608081323 156344307391471092912121985)
  ·
    refine ⟨117258230543603319684091489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156344307391471092912121985 117258230543603319684091489)
    ·
      refine ⟨87943672907702489763068617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117258230543603319684091489 87943672907702489763068617)
      ·
        refine ⟨65957754680776867322301463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87943672907702489763068617 65957754680776867322301463)
        ·
          refine ⟨98936632021165300983452195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65957754680776867322301463 98936632021165300983452195)
          ·
            refine ⟨148404948031747951475178293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98936632021165300983452195 148404948031747951475178293)
            ·
              refine ⟨13912963877976370450797965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148404948031747951475178293 13912963877976370450797965)
              ·
                refine ⟨5217361454241138919049237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13912963877976370450797965 5217361454241138919049237)
                ·
                  refine ⟨244563818167553386830433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5217361454241138919049237 244563818167553386830433)
                  ·
                    rfl

theorem cell23_4286577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_4286577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286577 prefixEnd_4286577 := by exact prefixLift 4286577
  have htrace : WordTrace (prefixWord ++ tailWord_4286577) baseStart_4286577 baseEnd_4286577 := by
    simpa [prefixWord, tailWord_4286577, baseEnd_4286577] using wordTrace_append hprefix tailTrace_4286577
  have hstable : (prefixWord ++ tailWord_4286577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286577).length < 2 ^ (prefixWord ++ tailWord_4286577).sum := by decide
  have hdescent : baseEnd_4286577 < baseStart_4286577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286615 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 1, 4]
def baseStart_4286615 : Nat := 118140960795 + 4286615 * 2 ^ 59
def prefixEnd_4286615 : Nat := 4983230072969 + 3 ^ 40 * 4286615 * 2
def baseEnd_4286615 : Nat := 733697958590950444266241

theorem tailTrace_4286615 : CollatzResearch.WordTrace tailWord_4286615 prefixEnd_4286615 733697958590950444266241 := by
  unfold tailWord_4286615
  simp only [CollatzResearch.WordTrace]
  refine ⟨156345693365333425402005299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104230462243555616934670199 156345693365333425402005299)
  ·
    refine ⟨234518540048000138103007949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156345693365333425402005299 234518540048000138103007949)
    ·
      refine ⟨87944452518000051788627981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234518540048000138103007949 87944452518000051788627981)
      ·
        refine ⟨32979169694250019420735493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87944452518000051788627981 32979169694250019420735493)
        ·
          refine ⟨6183594317671878641387905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32979169694250019420735493 6183594317671878641387905)
          ·
            refine ⟨4637695738253908981040929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6183594317671878641387905 4637695738253908981040929)
            ·
              refine ⟨3478271803690431735780697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637695738253908981040929 3478271803690431735780697)
              ·
                refine ⟨2608703852767823801835523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478271803690431735780697 2608703852767823801835523)
                ·
                  refine ⟨3913055779151735702753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2608703852767823801835523 3913055779151735702753285)
                  ·
                    refine ⟨733697958590950444266241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3913055779151735702753285 733697958590950444266241)
                    ·
                      rfl

theorem cell23_4286615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_4286615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286615 prefixEnd_4286615 := by exact prefixLift 4286615
  have htrace : WordTrace (prefixWord ++ tailWord_4286615) baseStart_4286615 baseEnd_4286615 := by
    simpa [prefixWord, tailWord_4286615, baseEnd_4286615] using wordTrace_append hprefix tailTrace_4286615
  have hstable : (prefixWord ++ tailWord_4286615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286615).length < 2 ^ (prefixWord ++ tailWord_4286615).sum := by decide
  have hdescent : baseEnd_4286615 < baseStart_4286615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286661 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_4286661 : Nat := 118140960795 + 4286661 * 2 ^ 59
def prefixEnd_4286661 : Nat := 4983230072969 + 3 ^ 40 * 4286661 * 2
def baseEnd_4286661 : Nat := 2201117495882958152823511

theorem tailTrace_4286661 : CollatzResearch.WordTrace tailWord_4286661 prefixEnd_4286661 2201117495882958152823511 := by
  unfold tailWord_4286661
  simp only [CollatzResearch.WordTrace]
  refine ⟨156347371123166775258179837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104231580748777850172119891 156347371123166775258179837)
  ·
    refine ⟨58630264171187540721817439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156347371123166775258179837 58630264171187540721817439)
    ·
      refine ⟨87945396256781311082726159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58630264171187540721817439 87945396256781311082726159)
      ·
        refine ⟨131918094385171966624089239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87945396256781311082726159 131918094385171966624089239)
        ·
          refine ⟨197877141577757949936133859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131918094385171966624089239 197877141577757949936133859)
          ·
            refine ⟨296815712366636924904200789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197877141577757949936133859 296815712366636924904200789)
            ·
              refine ⟨3478309129296526463721103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 296815712366636924904200789 3478309129296526463721103)
              ·
                refine ⟨5217463693944789695581655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478309129296526463721103 5217463693944789695581655)
                ·
                  refine ⟨7826195540917184543372483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217463693944789695581655 7826195540917184543372483)
                  ·
                    refine ⟨11739293311375776815058725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7826195540917184543372483 11739293311375776815058725)
                    ·
                      refine ⟨2201117495882958152823511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11739293311375776815058725 2201117495882958152823511)
                      ·
                        rfl

theorem cell23_4286661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_4286661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286661 prefixEnd_4286661 := by exact prefixLift 4286661
  have htrace : WordTrace (prefixWord ++ tailWord_4286661) baseStart_4286661 baseEnd_4286661 := by
    simpa [prefixWord, tailWord_4286661, baseEnd_4286661] using wordTrace_append hprefix tailTrace_4286661
  have hstable : (prefixWord ++ tailWord_4286661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286661).length < 2 ^ (prefixWord ++ tailWord_4286661).sum := by decide
  have hdescent : baseEnd_4286661 < baseStart_4286661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286691 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4286691 : Nat := 118140960795 + 4286691 * 2 ^ 59
def prefixEnd_4286691 : Nat := 4983230072969 + 3 ^ 40 * 4286691 * 2
def baseEnd_4286691 : Nat := 2201132900302593035448373

theorem tailTrace_4286691 : CollatzResearch.WordTrace tailWord_4286691 prefixEnd_4286691 2201132900302593035448373 := by
  unfold tailWord_4286691
  simp only [CollatzResearch.WordTrace]
  refine ⟨156348465313058090381771927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104232310208705393587847951 156348465313058090381771927)
  ·
    refine ⟨234522697969587135572657891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156348465313058090381771927 234522697969587135572657891)
    ·
      refine ⟨351784046954380703358986837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234522697969587135572657891 351784046954380703358986837)
      ·
        refine ⟨4122469300246648867488127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 351784046954380703358986837 4122469300246648867488127)
        ·
          refine ⟨6183703950369973301232191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122469300246648867488127 6183703950369973301232191)
          ·
            refine ⟨9275555925554959951848287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183703950369973301232191 9275555925554959951848287)
            ·
              refine ⟨13913333888332439927772431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9275555925554959951848287 13913333888332439927772431)
              ·
                refine ⟨20870000832498659891658647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13913333888332439927772431 20870000832498659891658647)
                ·
                  refine ⟨31305001248747989837487971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20870000832498659891658647 31305001248747989837487971)
                  ·
                    refine ⟨46957501873121984756231957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31305001248747989837487971 46957501873121984756231957)
                    ·
                      refine ⟨2201132900302593035448373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46957501873121984756231957 2201132900302593035448373)
                      ·
                        rfl

theorem cell23_4286691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4286691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286691 prefixEnd_4286691 := by exact prefixLift 4286691
  have htrace : WordTrace (prefixWord ++ tailWord_4286691) baseStart_4286691 baseEnd_4286691 := by
    simpa [prefixWord, tailWord_4286691, baseEnd_4286691] using wordTrace_append hprefix tailTrace_4286691
  have hstable : (prefixWord ++ tailWord_4286691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286691).length < 2 ^ (prefixWord ++ tailWord_4286691).sum := by decide
  have hdescent : baseEnd_4286691 < baseStart_4286691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286704 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2]
def baseStart_4286704 : Nat := 118140960795 + 4286704 * 2 ^ 59
def prefixEnd_4286704 : Nat := 4983230072969 + 3 ^ 40 * 4286704 * 2
def baseEnd_4286704 : Nat := 2201139575551101484585813

theorem tailTrace_4286704 : CollatzResearch.WordTrace tailWord_4286704 prefixEnd_4286704 2201139575551101484585813 := by
  unfold tailWord_4286704
  simp only [CollatzResearch.WordTrace]
  refine ⟨78174469731005496800997583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104232626308007329067996777 78174469731005496800997583)
  ·
    refine ⟨117261704596508245201496375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78174469731005496800997583 117261704596508245201496375)
    ·
      refine ⟨175892556894762367802244563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117261704596508245201496375 175892556894762367802244563)
      ·
        refine ⟨263838835342143551703366845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175892556894762367802244563 263838835342143551703366845)
        ·
          refine ⟨98939563253303831888762567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263838835342143551703366845 98939563253303831888762567)
          ·
            refine ⟨148409344879955747833143851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98939563253303831888762567 148409344879955747833143851)
            ·
              refine ⟨222614017319933621749715777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148409344879955747833143851 222614017319933621749715777)
              ·
                refine ⟨166960512989950216312286833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222614017319933621749715777 166960512989950216312286833)
                ·
                  refine ⟨125220384742462662234215125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166960512989950216312286833 125220384742462662234215125)
                  ·
                    refine ⟨2934852767401468646114417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125220384742462662234215125 2934852767401468646114417)
                    ·
                      refine ⟨2201139575551101484585813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934852767401468646114417 2201139575551101484585813)
                      ·
                        rfl

theorem cell23_4286704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2].length) (baseStart_4286704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286704 prefixEnd_4286704 := by exact prefixLift 4286704
  have htrace : WordTrace (prefixWord ++ tailWord_4286704) baseStart_4286704 baseEnd_4286704 := by
    simpa [prefixWord, tailWord_4286704, baseEnd_4286704] using wordTrace_append hprefix tailTrace_4286704
  have hstable : (prefixWord ++ tailWord_4286704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286704).length < 2 ^ (prefixWord ++ tailWord_4286704).sum := by decide
  have hdescent : baseEnd_4286704 < baseStart_4286704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286707 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_4286707 : Nat := 118140960795 + 4286707 * 2 ^ 59
def prefixEnd_4286707 : Nat := 4983230072969 + 3 ^ 40 * 4286707 * 2
def baseEnd_4286707 : Nat := 2201141115993064972848299

theorem tailTrace_4286707 : CollatzResearch.WordTrace tailWord_4286707 prefixEnd_4286707 2201141115993064972848299 := by
  unfold tailWord_4286707
  simp only [CollatzResearch.WordTrace]
  refine ⟨156349048881000125114354375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104232699254000083409569583 156349048881000125114354375)
  ·
    refine ⟨234523573321500187671531563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156349048881000125114354375 234523573321500187671531563)
    ·
      refine ⟨351785359982250281507297345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234523573321500187671531563 351785359982250281507297345)
      ·
        refine ⟨263839019986687711130473009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351785359982250281507297345 263839019986687711130473009)
        ·
          refine ⟨197879264990015783347854757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263839019986687711130473009 197879264990015783347854757)
          ·
            refine ⟨37102362185627959377722767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197879264990015783347854757 37102362185627959377722767)
            ·
              refine ⟨55653543278441939066584151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37102362185627959377722767 55653543278441939066584151)
              ·
                refine ⟨83480314917662908599876227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55653543278441939066584151 83480314917662908599876227)
                ·
                  refine ⟨125220472376494362899814341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83480314917662908599876227 125220472376494362899814341)
                  ·
                    refine ⟨23478838570592693043715189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125220472376494362899814341 23478838570592693043715189)
                    ·
                      refine ⟨2201141115993064972848299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23478838570592693043715189 2201141115993064972848299)
                      ·
                        rfl

theorem cell23_4286707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_4286707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286707 prefixEnd_4286707 := by exact prefixLift 4286707
  have htrace : WordTrace (prefixWord ++ tailWord_4286707) baseStart_4286707 baseEnd_4286707 := by
    simpa [prefixWord, tailWord_4286707, baseEnd_4286707] using wordTrace_append hprefix tailTrace_4286707
  have hstable : (prefixWord ++ tailWord_4286707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286707).length < 2 ^ (prefixWord ++ tailWord_4286707).sum := by decide
  have hdescent : baseEnd_4286707 < baseStart_4286707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286717 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4286717 : Nat := 118140960795 + 4286717 * 2 ^ 59
def prefixEnd_4286717 : Nat := 4983230072969 + 3 ^ 40 * 4286717 * 2
def baseEnd_4286717 : Nat := 2201146250799609933723253

theorem tailTrace_4286717 : CollatzResearch.WordTrace tailWord_4286717 prefixEnd_4286717 2201146250799609933723253 := by
  unfold tailWord_4286717
  simp only [CollatzResearch.WordTrace]
  refine ⟨156349413610963896822218405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104232942407309264548145603 156349413610963896822218405)
  ·
    refine ⟨29315515052055730654165951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156349413610963896822218405 29315515052055730654165951)
    ·
      refine ⟨43973272578083595981248927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29315515052055730654165951 43973272578083595981248927)
      ·
        refine ⟨65959908867125393971873391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43973272578083595981248927 65959908867125393971873391)
        ·
          refine ⟨98939863300688090957810087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65959908867125393971873391 98939863300688090957810087)
          ·
            refine ⟨148409794951032136436715131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98939863300688090957810087 148409794951032136436715131)
            ·
              refine ⟨222614692426548204655072697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148409794951032136436715131 222614692426548204655072697)
              ·
                refine ⟨166961019319911153491304523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222614692426548204655072697 166961019319911153491304523)
                ·
                  refine ⟨250441528979866730236956785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166961019319911153491304523 250441528979866730236956785)
                  ·
                    refine ⟨187831146734900047677717589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250441528979866730236956785 187831146734900047677717589)
                    ·
                      refine ⟨2201146250799609933723253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187831146734900047677717589 2201146250799609933723253)
                      ·
                        rfl

theorem cell23_4286717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4286717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286717 prefixEnd_4286717 := by exact prefixLift 4286717
  have htrace : WordTrace (prefixWord ++ tailWord_4286717) baseStart_4286717 baseEnd_4286717 := by
    simpa [prefixWord, tailWord_4286717, baseEnd_4286717] using wordTrace_append hprefix tailTrace_4286717
  have hstable : (prefixWord ++ tailWord_4286717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286717).length < 2 ^ (prefixWord ++ tailWord_4286717).sum := by decide
  have hdescent : baseEnd_4286717 < baseStart_4286717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286734 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4286734 : Nat := 118140960795 + 4286734 * 2 ^ 59
def prefixEnd_4286734 : Nat := 4983230072969 + 3 ^ 40 * 4286734 * 2
def baseEnd_4286734 : Nat := 2201154979970736367210675

theorem tailTrace_4286734 : CollatzResearch.WordTrace tailWord_4286734 prefixEnd_4286734 2201154979970736367210675 := by
  unfold tailWord_4286734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19543754206487788590698407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104233355767934872483724837 19543754206487788590698407)
  ·
    refine ⟨29315631309731682886047611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19543754206487788590698407 29315631309731682886047611)
    ·
      refine ⟨43973446964597524329071417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29315631309731682886047611 43973446964597524329071417)
      ·
        refine ⟨32980085223448143246803563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43973446964597524329071417 32980085223448143246803563)
        ·
          refine ⟨49470127835172214870205345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32980085223448143246803563 49470127835172214870205345)
          ·
            refine ⟨37102595876379161152654009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49470127835172214870205345 37102595876379161152654009)
            ·
              refine ⟨27826946907284370864490507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37102595876379161152654009 27826946907284370864490507)
              ·
                refine ⟨41740420360926556296735761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27826946907284370864490507 41740420360926556296735761)
                ·
                  refine ⟨31305315270694917222551821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41740420360926556296735761 31305315270694917222551821)
                  ·
                    refine ⟨11739493226510593958456933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31305315270694917222551821 11739493226510593958456933)
                    ·
                      refine ⟨2201154979970736367210675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11739493226510593958456933 2201154979970736367210675)
                      ·
                        rfl

theorem cell23_4286734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4286734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286734 prefixEnd_4286734 := by exact prefixLift 4286734
  have htrace : WordTrace (prefixWord ++ tailWord_4286734) baseStart_4286734 baseEnd_4286734 := by
    simpa [prefixWord, tailWord_4286734, baseEnd_4286734] using wordTrace_append hprefix tailTrace_4286734
  have hstable : (prefixWord ++ tailWord_4286734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286734).length < 2 ^ (prefixWord ++ tailWord_4286734).sum := by decide
  have hdescent : baseEnd_4286734 < baseStart_4286734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286772 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4286772 : Nat := 118140960795 + 4286772 * 2 ^ 59
def prefixEnd_4286772 : Nat := 4983230072969 + 3 ^ 40 * 4286772 * 2
def baseEnd_4286772 : Nat := 2201174492235607218535501

theorem tailTrace_4286772 : CollatzResearch.WordTrace tailWord_4286772 prefixEnd_4286772 2201174492235607218535501 := by
  unfold tailWord_4286772
  simp only [CollatzResearch.WordTrace]
  refine ⟨78175709812882320607735285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104234279750509760810313713 78175709812882320607735285)
  ·
    refine ⟨7328972794957717556975183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78175709812882320607735285 7328972794957717556975183)
    ·
      refine ⟨10993459192436576335462775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7328972794957717556975183 10993459192436576335462775)
      ·
        refine ⟨16490188788654864503194163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10993459192436576335462775 16490188788654864503194163)
        ·
          refine ⟨24735283182982296754791245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16490188788654864503194163 24735283182982296754791245)
          ·
            refine ⟨9275731193618361283046717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24735283182982296754791245 9275731193618361283046717)
            ·
              refine ⟨3478399197606885481142519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9275731193618361283046717 3478399197606885481142519)
              ·
                refine ⟨5217598796410328221713779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478399197606885481142519 5217598796410328221713779)
                ·
                  refine ⟨7826398194615492332570669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217598796410328221713779 7826398194615492332570669)
                  ·
                    refine ⟨2934899322980809624714001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7826398194615492332570669 2934899322980809624714001)
                    ·
                      refine ⟨2201174492235607218535501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2934899322980809624714001 2201174492235607218535501)
                      ·
                        rfl

theorem cell23_4286772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4286772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286772 prefixEnd_4286772 := by exact prefixLift 4286772
  have htrace : WordTrace (prefixWord ++ tailWord_4286772) baseStart_4286772 baseEnd_4286772 := by
    simpa [prefixWord, tailWord_4286772, baseEnd_4286772] using wordTrace_append hprefix tailTrace_4286772
  have hstable : (prefixWord ++ tailWord_4286772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286772).length < 2 ^ (prefixWord ++ tailWord_4286772).sum := by decide
  have hdescent : baseEnd_4286772 < baseStart_4286772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286791 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 5]
def baseStart_4286791 : Nat := 118140960795 + 4286791 * 2 ^ 59
def prefixEnd_4286791 : Nat := 4983230072969 + 3 ^ 40 * 4286791 * 2
def baseEnd_4286791 : Nat := 244576027596449182688657

theorem tailTrace_4286791 : CollatzResearch.WordTrace tailWord_4286791 prefixEnd_4286791 244576027596449182688657 := by
  unfold tailWord_4286791
  simp only [CollatzResearch.WordTrace]
  refine ⟨156352112612695807460412227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104234741741797204973608151 156352112612695807460412227)
  ·
    refine ⟨234528168919043711190618341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156352112612695807460412227 234528168919043711190618341)
    ·
      refine ⟨43974031672320695848240939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234528168919043711190618341 43974031672320695848240939)
      ·
        refine ⟨65961047508481043772361409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43974031672320695848240939 65961047508481043772361409)
        ·
          refine ⟨49470785631360782829271057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65961047508481043772361409 49470785631360782829271057)
          ·
            refine ⟨37103089223520587121953293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49470785631360782829271057 37103089223520587121953293)
            ·
              refine ⟨13913658458820220170732485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37103089223520587121953293 13913658458820220170732485)
              ·
                refine ⟨2608810961028791282012341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13913658458820220170732485 2608810961028791282012341)
                ·
                  refine ⟨244576027596449182688657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2608810961028791282012341 244576027596449182688657)
                  ·
                    rfl

theorem cell23_4286791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 5].length) (baseStart_4286791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286791 prefixEnd_4286791 := by exact prefixLift 4286791
  have htrace : WordTrace (prefixWord ++ tailWord_4286791) baseStart_4286791 baseEnd_4286791 := by
    simpa [prefixWord, tailWord_4286791, baseEnd_4286791] using wordTrace_append hprefix tailTrace_4286791
  have hstable : (prefixWord ++ tailWord_4286791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286791).length < 2 ^ (prefixWord ++ tailWord_4286791).sum := by decide
  have hdescent : baseEnd_4286791 < baseStart_4286791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286801 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_4286801 : Nat := 118140960795 + 4286801 * 2 ^ 59
def prefixEnd_4286801 : Nat := 4983230072969 + 3 ^ 40 * 4286801 * 2
def baseEnd_4286801 : Nat := 2201189383174587605072867

theorem tailTrace_4286801 : CollatzResearch.WordTrace tailWord_4286801 prefixEnd_4286801 2201189383174587605072867 := by
  unfold tailWord_4286801
  simp only [CollatzResearch.WordTrace]
  refine ⟨156352477342659579168276257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104234984895106386112184171 156352477342659579168276257)
  ·
    refine ⟨117264358006994684376207193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156352477342659579168276257 117264358006994684376207193)
    ·
      refine ⟨87948268505246013282155395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117264358006994684376207193 87948268505246013282155395)
      ·
        refine ⟨131922402757869019923233093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87948268505246013282155395 131922402757869019923233093)
        ·
          refine ⟨24735450517100441235606205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131922402757869019923233093 24735450517100441235606205)
          ·
            refine ⟨9275793943912665463352327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24735450517100441235606205 9275793943912665463352327)
            ·
              refine ⟨13913690915868998195028491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9275793943912665463352327 13913690915868998195028491)
              ·
                refine ⟨20870536373803497292542737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13913690915868998195028491 20870536373803497292542737)
                ·
                  refine ⟨15652902280352622969407053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20870536373803497292542737 15652902280352622969407053)
                  ·
                    refine ⟨5869838355132233613527645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15652902280352622969407053 5869838355132233613527645)
                    ·
                      refine ⟨2201189383174587605072867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5869838355132233613527645 2201189383174587605072867)
                      ·
                        rfl

theorem cell23_4286801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_4286801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286801 prefixEnd_4286801 := by exact prefixLift 4286801
  have htrace : WordTrace (prefixWord ++ tailWord_4286801) baseStart_4286801 baseEnd_4286801 := by
    simpa [prefixWord, tailWord_4286801, baseEnd_4286801] using wordTrace_append hprefix tailTrace_4286801
  have hstable : (prefixWord ++ tailWord_4286801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286801).length < 2 ^ (prefixWord ++ tailWord_4286801).sum := by decide
  have hdescent : baseEnd_4286801 < baseStart_4286801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286821 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_4286821 : Nat := 118140960795 + 4286821 * 2 ^ 59
def prefixEnd_4286821 : Nat := 4983230072969 + 3 ^ 40 * 4286821 * 2
def baseEnd_4286821 : Nat := 733733217595892508940925

theorem tailTrace_4286821 : CollatzResearch.WordTrace tailWord_4286821 prefixEnd_4286821 733733217595892508940925 := by
  unfold tailWord_4286821
  simp only [CollatzResearch.WordTrace]
  refine ⟨156353206802587122584004317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104235471201724748389336211 156353206802587122584004317)
  ·
    refine ⟨58632452550970170969001619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156353206802587122584004317 58632452550970170969001619)
    ·
      refine ⟨87948678826455256453502429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58632452550970170969001619 87948678826455256453502429)
      ·
        refine ⟨32980754559920721170063411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87948678826455256453502429 32980754559920721170063411)
        ·
          refine ⟨49471131839881081755095117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32980754559920721170063411 49471131839881081755095117)
          ·
            refine ⟨18551674439955405658160669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49471131839881081755095117 18551674439955405658160669)
            ·
              refine ⟨6956877914983277121810251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18551674439955405658160669 6956877914983277121810251)
              ·
                refine ⟨10435316872474915682715377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6956877914983277121810251 10435316872474915682715377)
                ·
                  refine ⟨7826487654356186762036533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10435316872474915682715377 7826487654356186762036533)
                  ·
                    refine ⟨733733217595892508940925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7826487654356186762036533 733733217595892508940925)
                    ·
                      rfl

theorem cell23_4286821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_4286821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286821 prefixEnd_4286821 := by exact prefixLift 4286821
  have htrace : WordTrace (prefixWord ++ tailWord_4286821) baseStart_4286821 baseEnd_4286821 := by
    simpa [prefixWord, tailWord_4286821, baseEnd_4286821] using wordTrace_append hprefix tailTrace_4286821
  have hstable : (prefixWord ++ tailWord_4286821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286821).length < 2 ^ (prefixWord ++ tailWord_4286821).sum := by decide
  have hdescent : baseEnd_4286821 < baseStart_4286821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286904 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_4286904 : Nat := 118140960795 + 4286904 * 2 ^ 59
def prefixEnd_4286904 : Nat := 4983230072969 + 3 ^ 40 * 4286904 * 2
def baseEnd_4286904 : Nat := 2201242271682000702084893

theorem tailTrace_4286904 : CollatzResearch.WordTrace tailWord_4286904 prefixEnd_4286904 2201242271682000702084893 := by
  unfold tailWord_4286904
  simp only [CollatzResearch.WordTrace]
  refine ⟨78178117030643213879637883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104237489374190951839517177 78178117030643213879637883)
  ·
    refine ⟨117267175545964820819456825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78178117030643213879637883 117267175545964820819456825)
    ·
      refine ⟨87950381659473615614592619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117267175545964820819456825 87950381659473615614592619)
      ·
        refine ⟨131925572489210423421888929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87950381659473615614592619 131925572489210423421888929)
        ·
          refine ⟨98944179366907817566416697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131925572489210423421888929 98944179366907817566416697)
          ·
            refine ⟨74208134525180863174812523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98944179366907817566416697 74208134525180863174812523)
            ·
              refine ⟨111312201787771294762218785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74208134525180863174812523 111312201787771294762218785)
              ·
                refine ⟨83484151340828471071664089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111312201787771294762218785 83484151340828471071664089)
                ·
                  refine ⟨62613113505621353303748067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83484151340828471071664089 62613113505621353303748067)
                  ·
                    refine ⟨93919670258432029955622101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62613113505621353303748067 93919670258432029955622101)
                    ·
                      refine ⟨2201242271682000702084893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93919670258432029955622101 2201242271682000702084893)
                      ·
                        rfl

theorem cell23_4286904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_4286904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286904 prefixEnd_4286904 := by exact prefixLift 4286904
  have htrace : WordTrace (prefixWord ++ tailWord_4286904) baseStart_4286904 baseEnd_4286904 := by
    simpa [prefixWord, tailWord_4286904, baseEnd_4286904] using wordTrace_append hprefix tailTrace_4286904
  have hstable : (prefixWord ++ tailWord_4286904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286904).length < 2 ^ (prefixWord ++ tailWord_4286904).sum := by decide
  have hdescent : baseEnd_4286904 < baseStart_4286904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286961 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_4286961 : Nat := 118140960795 + 4286961 * 2 ^ 59
def prefixEnd_4286961 : Nat := 4983230072969 + 3 ^ 40 * 4286961 * 2
def baseEnd_4286961 : Nat := 2201271540079306979072131

theorem tailTrace_4286961 : CollatzResearch.WordTrace tailWord_4286961 prefixEnd_4286961 2201271540079306979072131 := by
  unfold tailWord_4286961
  simp only [CollatzResearch.WordTrace]
  refine ⟨156358313022079926494100737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104238875348053284329400491 156358313022079926494100737)
  ·
    refine ⟨117268734766559944870575553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156358313022079926494100737 117268734766559944870575553)
    ·
      refine ⟨87951551074919958652931665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117268734766559944870575553 87951551074919958652931665)
      ·
        refine ⟨65963663306189968989698749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87951551074919958652931665 65963663306189968989698749)
        ·
          refine ⟨24736373739821238371137031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65963663306189968989698749 24736373739821238371137031)
          ·
            refine ⟨37104560609731857556705547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24736373739821238371137031 37104560609731857556705547)
            ·
              refine ⟨55656840914597786335058321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37104560609731857556705547 55656840914597786335058321)
              ·
                refine ⟨41742630685948339751293741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55656840914597786335058321 41742630685948339751293741)
                ·
                  refine ⟨15653486507230627406735153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41742630685948339751293741 15653486507230627406735153)
                  ·
                    refine ⟨11740114880422970555051365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15653486507230627406735153 11740114880422970555051365)
                    ·
                      refine ⟨2201271540079306979072131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11740114880422970555051365 2201271540079306979072131)
                      ·
                        rfl

theorem cell23_4286961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_4286961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286961 prefixEnd_4286961 := by exact prefixLift 4286961
  have htrace : WordTrace (prefixWord ++ tailWord_4286961) baseStart_4286961 baseEnd_4286961 := by
    simpa [prefixWord, tailWord_4286961, baseEnd_4286961] using wordTrace_append hprefix tailTrace_4286961
  have hstable : (prefixWord ++ tailWord_4286961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286961).length < 2 ^ (prefixWord ++ tailWord_4286961).sum := by decide
  have hdescent : baseEnd_4286961 < baseStart_4286961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286988 : List Nat := [2, 2, 1, 2, 4, 2, 3, 7]
def baseStart_4286988 : Nat := 118140960795 + 4286988 * 2 ^ 59
def prefixEnd_4286988 : Nat := 4983230072969 + 3 ^ 40 * 4286988 * 2
def baseEnd_4286988 : Nat := 81529089039147347164241

theorem tailTrace_4286988 : CollatzResearch.WordTrace tailWord_4286988 prefixEnd_4286988 81529089039147347164241 := by
  unfold tailWord_4286988
  simp only [CollatzResearch.WordTrace]
  refine ⟨78179648896491055052666809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104239531861988073403555745 78179648896491055052666809)
  ·
    refine ⟨58634736672368291289500107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78179648896491055052666809 58634736672368291289500107)
    ·
      refine ⟨87952105008552436934250161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58634736672368291289500107 87952105008552436934250161)
      ·
        refine ⟨65964078756414327700687621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87952105008552436934250161 65964078756414327700687621)
        ·
          refine ⟨12368264766827686443878929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65964078756414327700687621 12368264766827686443878929)
          ·
            refine ⟨9276198575120764832909197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12368264766827686443878929 9276198575120764832909197)
            ·
              refine ⟨3478574465670286812340949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9276198575120764832909197 3478574465670286812340949)
              ·
                refine ⟨81529089039147347164241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3478574465670286812340949 81529089039147347164241)
                ·
                  rfl

theorem cell23_4286988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 7].length) (baseStart_4286988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286988 prefixEnd_4286988 := by exact prefixLift 4286988
  have htrace : WordTrace (prefixWord ++ tailWord_4286988) baseStart_4286988 baseEnd_4286988 := by
    simpa [prefixWord, tailWord_4286988, baseEnd_4286988] using wordTrace_append hprefix tailTrace_4286988
  have hstable : (prefixWord ++ tailWord_4286988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286988).length < 2 ^ (prefixWord ++ tailWord_4286988).sum := by decide
  have hdescent : baseEnd_4286988 < baseStart_4286988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4286999 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4286999 : Nat := 118140960795 + 4286999 * 2 ^ 59
def prefixEnd_4286999 : Nat := 4983230072969 + 3 ^ 40 * 4286999 * 2
def baseEnd_4286999 : Nat := 2201291052344177830396957

theorem tailTrace_4286999 : CollatzResearch.WordTrace tailWord_4286999 prefixEnd_4286999 2201291052344177830396957 := by
  unfold tailWord_4286999
  simp only [CollatzResearch.WordTrace]
  refine ⟨156359698995942258983984051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104239799330628172655989367 156359698995942258983984051)
  ·
    refine ⟨234539548493913388475976077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156359698995942258983984051 234539548493913388475976077)
    ·
      refine ⟨87952330685217520678491029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234539548493913388475976077 87952330685217520678491029)
      ·
        refine ⟨4122765500869571281804267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87952330685217520678491029 4122765500869571281804267)
        ·
          refine ⟨6184148251304356922706401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122765500869571281804267 6184148251304356922706401)
          ·
            refine ⟨4638111188478267692029801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6184148251304356922706401 4638111188478267692029801)
            ·
              refine ⟨3478583391358700769022351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638111188478267692029801 3478583391358700769022351)
              ·
                refine ⟨5217875087038051153533527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478583391358700769022351 5217875087038051153533527)
                ·
                  refine ⟨7826812630557076730300291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217875087038051153533527 7826812630557076730300291)
                  ·
                    refine ⟨11740218945835615095450437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7826812630557076730300291 11740218945835615095450437)
                    ·
                      refine ⟨2201291052344177830396957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11740218945835615095450437 2201291052344177830396957)
                      ·
                        rfl

theorem cell23_4286999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4286999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4286999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4286999 prefixEnd_4286999 := by exact prefixLift 4286999
  have htrace : WordTrace (prefixWord ++ tailWord_4286999) baseStart_4286999 baseEnd_4286999 := by
    simpa [prefixWord, tailWord_4286999, baseEnd_4286999] using wordTrace_append hprefix tailTrace_4286999
  have hstable : (prefixWord ++ tailWord_4286999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4286999).length < 2 ^ (prefixWord ++ tailWord_4286999).sum := by decide
  have hdescent : baseEnd_4286999 < baseStart_4286999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4286999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287031 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 2, 6]
def baseStart_4287031 : Nat := 118140960795 + 4287031 * 2 ^ 59
def prefixEnd_4287031 : Nat := 4983230072969 + 3 ^ 40 * 4287031 * 2
def baseEnd_4287031 : Nat := 733769161241707235065603

theorem tailTrace_4287031 : CollatzResearch.WordTrace tailWord_4287031 prefixEnd_4287031 733769161241707235065603 := by
  unfold tailWord_4287031
  simp only [CollatzResearch.WordTrace]
  refine ⟨156360866131826328449148947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104240577421217552299432631 156360866131826328449148947)
  ·
    refine ⟨234541299197739492673723421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156360866131826328449148947 234541299197739492673723421)
    ·
      refine ⟨87952987199152309752646283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234541299197739492673723421 87952987199152309752646283)
      ·
        refine ⟨131929480798728464628969425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87952987199152309752646283 131929480798728464628969425)
        ·
          refine ⟨98947110599046348471727069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131929480798728464628969425 98947110599046348471727069)
          ·
            refine ⟨37105166474642380676897651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98947110599046348471727069 37105166474642380676897651)
            ·
              refine ⟨55657749711963571015346477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37105166474642380676897651 55657749711963571015346477)
              ·
                refine ⟨20871656141986339130754929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55657749711963571015346477 20871656141986339130754929)
                ·
                  refine ⟨15653742106489754348066197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20871656141986339130754929 15653742106489754348066197)
                  ·
                    refine ⟨733769161241707235065603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15653742106489754348066197 733769161241707235065603)
                    ·
                      rfl

theorem cell23_4287031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_4287031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287031 prefixEnd_4287031 := by exact prefixLift 4287031
  have htrace : WordTrace (prefixWord ++ tailWord_4287031) baseStart_4287031 baseEnd_4287031 := by
    simpa [prefixWord, tailWord_4287031, baseEnd_4287031] using wordTrace_append hprefix tailTrace_4287031
  have hstable : (prefixWord ++ tailWord_4287031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287031).length < 2 ^ (prefixWord ++ tailWord_4287031).sum := by decide
  have hdescent : baseEnd_4287031 < baseStart_4287031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287032 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_4287032 : Nat := 118140960795 + 4287032 * 2 ^ 59
def prefixEnd_4287032 : Nat := 4983230072969 + 3 ^ 40 * 4287032 * 2
def baseEnd_4287032 : Nat := 2201307997205776201284305

theorem tailTrace_4287032 : CollatzResearch.WordTrace tailWord_4287032 prefixEnd_4287032 2201307997205776201284305 := by
  unfold tailWord_4287032
  simp only [CollatzResearch.WordTrace]
  refine ⟨78180451302411352809967675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104240601736548470413290233 78180451302411352809967675)
  ·
    refine ⟨117270676953617029214951513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78180451302411352809967675 117270676953617029214951513)
    ·
      refine ⟨87953007715212771911213635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117270676953617029214951513 87953007715212771911213635)
      ·
        refine ⟨131929511572819157866820453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87953007715212771911213635 131929511572819157866820453)
        ·
          refine ⟨24736783419903592100028835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131929511572819157866820453 24736783419903592100028835)
          ·
            refine ⟨37105175129855388150043253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24736783419903592100028835 37105175129855388150043253)
            ·
              refine ⟨3478610168423942639066555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37105175129855388150043253 3478610168423942639066555)
              ·
                refine ⟨5217915252635913958599833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478610168423942639066555 5217915252635913958599833)
                ·
                  refine ⟨3913436439476935468949875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5217915252635913958599833 3913436439476935468949875)
                  ·
                    refine ⟨5870154659215403203424813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3913436439476935468949875 5870154659215403203424813)
                    ·
                      refine ⟨2201307997205776201284305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870154659215403203424813 2201307997205776201284305)
                      ·
                        rfl

theorem cell23_4287032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_4287032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287032 prefixEnd_4287032 := by exact prefixLift 4287032
  have htrace : WordTrace (prefixWord ++ tailWord_4287032) baseStart_4287032 baseEnd_4287032 := by
    simpa [prefixWord, tailWord_4287032, baseEnd_4287032] using wordTrace_append hprefix tailTrace_4287032
  have hstable : (prefixWord ++ tailWord_4287032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287032).length < 2 ^ (prefixWord ++ tailWord_4287032).sum := by decide
  have hdescent : baseEnd_4287032 < baseStart_4287032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287051 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_4287051 : Nat := 118140960795 + 4287051 * 2 ^ 59
def prefixEnd_4287051 : Nat := 4983230072969 + 3 ^ 40 * 4287051 * 2
def baseEnd_4287051 : Nat := 2201317753338211626946717

theorem tailTrace_4287051 : CollatzResearch.WordTrace tailWord_4287051 prefixEnd_4287051 2201317753338211626946717 := by
  unfold tailWord_4287051
  simp only [CollatzResearch.WordTrace]
  refine ⟨156361595591753871864877007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104241063727835914576584671 156361595591753871864877007)
  ·
    refine ⟨234542393387630807797315511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156361595591753871864877007 234542393387630807797315511)
    ·
      refine ⟨351813590081446211695973267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234542393387630807797315511 351813590081446211695973267)
      ·
        refine ⟨527720385122169317543959901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351813590081446211695973267 527720385122169317543959901)
        ·
          refine ⟨197895144420813494078984963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527720385122169317543959901 197895144420813494078984963)
          ·
            refine ⟨296842716631220241118477445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197895144420813494078984963 296842716631220241118477445)
            ·
              refine ⟨55658009368353795209714521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 296842716631220241118477445 55658009368353795209714521)
              ·
                refine ⟨41743507026265346407285891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55658009368353795209714521 41743507026265346407285891)
                ·
                  refine ⟨62615260539398019610928837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41743507026265346407285891 62615260539398019610928837)
                  ·
                    refine ⟨11740361351137128677049157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62615260539398019610928837 11740361351137128677049157)
                    ·
                      refine ⟨2201317753338211626946717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11740361351137128677049157 2201317753338211626946717)
                      ·
                        rfl

theorem cell23_4287051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_4287051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287051 prefixEnd_4287051 := by exact prefixLift 4287051
  have htrace : WordTrace (prefixWord ++ tailWord_4287051) baseStart_4287051 baseEnd_4287051 := by
    simpa [prefixWord, tailWord_4287051, baseEnd_4287051] using wordTrace_append hprefix tailTrace_4287051
  have hstable : (prefixWord ++ tailWord_4287051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287051).length < 2 ^ (prefixWord ++ tailWord_4287051).sum := by decide
  have hdescent : baseEnd_4287051 < baseStart_4287051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287055 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 4, 2, 2]
def baseStart_4287055 : Nat := 118140960795 + 4287055 * 2 ^ 59
def prefixEnd_4287055 : Nat := 4983230072969 + 3 ^ 40 * 4287055 * 2
def baseEnd_4287055 : Nat := 2201319807260829611296699

theorem tailTrace_4287055 : CollatzResearch.WordTrace tailWord_4287055 prefixEnd_4287055 2201319807260829611296699 := by
  unfold tailWord_4287055
  simp only [CollatzResearch.WordTrace]
  refine ⟨156361741483739380548022619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104241160989159587032015079 156361741483739380548022619)
  ·
    refine ⟨234542612225609070822033929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156361741483739380548022619 234542612225609070822033929)
    ·
      refine ⟨175906959169206803116525447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234542612225609070822033929 175906959169206803116525447)
      ·
        refine ⟨263860438753810204674788171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175906959169206803116525447 263860438753810204674788171)
        ·
          refine ⟨395790658130715307012182257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263860438753810204674788171 395790658130715307012182257)
          ·
            refine ⟨296842993598036480259136693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395790658130715307012182257 296842993598036480259136693)
            ·
              refine ⟨27829030649815920024294065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296842993598036480259136693 27829030649815920024294065)
              ·
                refine ⟨20871772987361940018220549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27829030649815920024294065 20871772987361940018220549)
                ·
                  refine ⟨3913457435130363753416353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20871772987361940018220549 3913457435130363753416353)
                  ·
                    refine ⟨2935093076347772815062265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3913457435130363753416353 2935093076347772815062265)
                    ·
                      refine ⟨2201319807260829611296699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935093076347772815062265 2201319807260829611296699)
                      ·
                        rfl

theorem cell23_4287055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2, 2].length) (baseStart_4287055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287055 prefixEnd_4287055 := by exact prefixLift 4287055
  have htrace : WordTrace (prefixWord ++ tailWord_4287055) baseStart_4287055 baseEnd_4287055 := by
    simpa [prefixWord, tailWord_4287055, baseEnd_4287055] using wordTrace_append hprefix tailTrace_4287055
  have hstable : (prefixWord ++ tailWord_4287055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287055).length < 2 ^ (prefixWord ++ tailWord_4287055).sum := by decide
  have hdescent : baseEnd_4287055 < baseStart_4287055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287058 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_4287058 : Nat := 118140960795 + 4287058 * 2 ^ 59
def prefixEnd_4287058 : Nat := 4983230072969 + 3 ^ 40 * 4287058 * 2
def baseEnd_4287058 : Nat := 2201321347702793099559185

theorem tailTrace_4287058 : CollatzResearch.WordTrace tailWord_4287058 prefixEnd_4287058 2201321347702793099559185 := by
  unfold tailWord_4287058
  simp only [CollatzResearch.WordTrace]
  refine ⟨39090462725682128015095457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104241233935152341373587885 39090462725682128015095457)
  ·
    refine ⟨29317847044261596011321593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39090462725682128015095457 29317847044261596011321593)
    ·
      refine ⟨21988385283196197008491195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29317847044261596011321593 21988385283196197008491195)
      ·
        refine ⟨32982577924794295512736793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21988385283196197008491195 32982577924794295512736793)
        ·
          refine ⟨24736933443595721634552595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32982577924794295512736793 24736933443595721634552595)
          ·
            refine ⟨37105400165393582451828893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24736933443595721634552595 37105400165393582451828893)
            ·
              refine ⟨13914525062022593419435835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37105400165393582451828893 13914525062022593419435835)
              ·
                refine ⟨20871787593033890129153753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13914525062022593419435835 20871787593033890129153753)
                ·
                  refine ⟨15653840694775417596865315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20871787593033890129153753 15653840694775417596865315)
                  ·
                    refine ⟨23480761042163126395297973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15653840694775417596865315 23480761042163126395297973)
                    ·
                      refine ⟨2201321347702793099559185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23480761042163126395297973 2201321347702793099559185)
                      ·
                        rfl

theorem cell23_4287058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_4287058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287058 prefixEnd_4287058 := by exact prefixLift 4287058
  have htrace : WordTrace (prefixWord ++ tailWord_4287058) baseStart_4287058 baseEnd_4287058 := by
    simpa [prefixWord, tailWord_4287058, baseEnd_4287058] using wordTrace_append hprefix tailTrace_4287058
  have hstable : (prefixWord ++ tailWord_4287058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287058).length < 2 ^ (prefixWord ++ tailWord_4287058).sum := by decide
  have hdescent : baseEnd_4287058 < baseStart_4287058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287061 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 9]
def baseStart_4287061 : Nat := 118140960795 + 4287061 * 2 ^ 59
def prefixEnd_4287061 : Nat := 4983230072969 + 3 ^ 40 * 4287061 * 2
def baseEnd_4287061 : Nat := 244591432016084065313519

theorem tailTrace_4287061 : CollatzResearch.WordTrace tailWord_4287061 prefixEnd_4287061 244591432016084065313519 := by
  unfold tailWord_4287061
  simp only [CollatzResearch.WordTrace]
  refine ⟨156361960321717643572741037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104241306881145095715160691 156361960321717643572741037)
  ·
    refine ⟨58635735120644116339777889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156361960321717643572741037 58635735120644116339777889)
    ·
      refine ⟨43976801340483087254833417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58635735120644116339777889 43976801340483087254833417)
      ·
        refine ⟨32982601005362315441125063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43976801340483087254833417 32982601005362315441125063)
        ·
          refine ⟨49473901508043473161687595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32982601005362315441125063 49473901508043473161687595)
          ·
            refine ⟨74210852262065209742531393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49473901508043473161687595 74210852262065209742531393)
            ·
              refine ⟨55658139196548907306898545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74210852262065209742531393 55658139196548907306898545)
              ·
                refine ⟨41743604397411680480173909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55658139196548907306898545 41743604397411680480173909)
                ·
                  refine ⟨244591432016084065313519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41743604397411680480173909 244591432016084065313519)
                  ·
                    rfl

theorem cell23_4287061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_4287061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287061 prefixEnd_4287061 := by exact prefixLift 4287061
  have htrace : WordTrace (prefixWord ++ tailWord_4287061) baseStart_4287061 baseEnd_4287061 := by
    simpa [prefixWord, tailWord_4287061, baseEnd_4287061] using wordTrace_append hprefix tailTrace_4287061
  have hstable : (prefixWord ++ tailWord_4287061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287061).length < 2 ^ (prefixWord ++ tailWord_4287061).sum := by decide
  have hdescent : baseEnd_4287061 < baseStart_4287061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287091 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 7]
def baseStart_4287091 : Nat := 118140960795 + 4287091 * 2 ^ 59
def prefixEnd_4287091 : Nat := 4983230072969 + 3 ^ 40 * 4287091 * 2
def baseEnd_4287091 : Nat := 733779430854797156815511

theorem tailTrace_4287091 : CollatzResearch.WordTrace tailWord_4287091 prefixEnd_4287091 733779430854797156815511 := by
  unfold tailWord_4287091
  simp only [CollatzResearch.WordTrace]
  refine ⟨156363054511608958696333127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104242036341072639130888751 156363054511608958696333127)
  ·
    refine ⟨234544581767413438044499691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156363054511608958696333127 234544581767413438044499691)
    ·
      refine ⟨351816872651120157066749537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234544581767413438044499691 351816872651120157066749537)
      ·
        refine ⟨263862654488340117800062153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351816872651120157066749537 263862654488340117800062153)
        ·
          refine ⟨197896990866255088350046615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263862654488340117800062153 197896990866255088350046615)
          ·
            refine ⟨296845486299382632525069923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197896990866255088350046615 296845486299382632525069923)
            ·
              refine ⟨445268229449073948787604885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296845486299382632525069923 445268229449073948787604885)
              ·
                refine ⟨20871948255425341349418979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 445268229449073948787604885 20871948255425341349418979)
                ·
                  refine ⟨31307922383138012024128469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20871948255425341349418979 31307922383138012024128469)
                  ·
                    refine ⟨733779430854797156815511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31307922383138012024128469 733779430854797156815511)
                    ·
                      rfl

theorem cell23_4287091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_4287091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287091 prefixEnd_4287091 := by exact prefixLift 4287091
  have htrace : WordTrace (prefixWord ++ tailWord_4287091) baseStart_4287091 baseEnd_4287091 := by
    simpa [prefixWord, tailWord_4287091, baseEnd_4287091] using wordTrace_append hprefix tailTrace_4287091
  have hstable : (prefixWord ++ tailWord_4287091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287091).length < 2 ^ (prefixWord ++ tailWord_4287091).sum := by decide
  have hdescent : baseEnd_4287091 < baseStart_4287091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287118 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4287118 : Nat := 118140960795 + 4287118 * 2 ^ 59
def prefixEnd_4287118 : Nat := 4983230072969 + 3 ^ 40 * 4287118 * 2
def baseEnd_4287118 : Nat := 2201352156542062864808909

theorem tailTrace_4287118 : CollatzResearch.WordTrace tailWord_4287118 prefixEnd_4287118 2201352156542062864808909 := by
  unfold tailWord_4287118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19545504910313892788445751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104242692855007428205044005 19545504910313892788445751)
  ·
    refine ⟨29318257365470839182668627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19545504910313892788445751 29318257365470839182668627)
    ·
      refine ⟨43977386048206258774002941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29318257365470839182668627 43977386048206258774002941)
      ·
        refine ⟨16491519768077347040251103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43977386048206258774002941 16491519768077347040251103)
        ·
          refine ⟨24737279652116020560376655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16491519768077347040251103 24737279652116020560376655)
          ·
            refine ⟨37105919478174030840564983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24737279652116020560376655 37105919478174030840564983)
            ·
              refine ⟨55658879217261046260847475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37105919478174030840564983 55658879217261046260847475)
              ·
                refine ⟨83488318825891569391271213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55658879217261046260847475 83488318825891569391271213)
                ·
                  refine ⟨31308119559709338521726705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83488318825891569391271213 31308119559709338521726705)
                  ·
                    refine ⟨23481089669782003891295029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31308119559709338521726705 23481089669782003891295029)
                    ·
                      refine ⟨2201352156542062864808909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23481089669782003891295029 2201352156542062864808909)
                      ·
                        rfl

theorem cell23_4287118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4287118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287118 prefixEnd_4287118 := by exact prefixLift 4287118
  have htrace : WordTrace (prefixWord ++ tailWord_4287118) baseStart_4287118 baseEnd_4287118 := by
    simpa [prefixWord, tailWord_4287118, baseEnd_4287118] using wordTrace_append hprefix tailTrace_4287118
  have hstable : (prefixWord ++ tailWord_4287118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287118).length < 2 ^ (prefixWord ++ tailWord_4287118).sum := by decide
  have hdescent : baseEnd_4287118 < baseStart_4287118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287121 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_4287121 : Nat := 118140960795 + 4287121 * 2 ^ 59
def prefixEnd_4287121 : Nat := 4983230072969 + 3 ^ 40 * 4287121 * 2
def baseEnd_4287121 : Nat := 733784565661342117690465

theorem tailTrace_4287121 : CollatzResearch.WordTrace tailWord_4287121 prefixEnd_4287121 733784565661342117690465 := by
  unfold tailWord_4287121
  simp only [CollatzResearch.WordTrace]
  refine ⟨156364148701500273819925217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104242765801000182546616811 156364148701500273819925217)
  ·
    refine ⟨117273111526125205364943913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156364148701500273819925217 117273111526125205364943913)
    ·
      refine ⟨87954833644593904023707935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117273111526125205364943913 87954833644593904023707935)
      ·
        refine ⟨131932250466890856035561903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87954833644593904023707935 131932250466890856035561903)
        ·
          refine ⟨197898375700336284053342855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131932250466890856035561903 197898375700336284053342855)
          ·
            refine ⟨296847563550504426080014283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197898375700336284053342855 296847563550504426080014283)
            ·
              refine ⟨445271345325756639120021425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296847563550504426080014283 445271345325756639120021425)
              ·
                refine ⟨333953508994317479340016069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445271345325756639120021425 333953508994317479340016069)
                ·
                  refine ⟨62616282936434527376253013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333953508994317479340016069 62616282936434527376253013)
                  ·
                    refine ⟨733784565661342117690465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62616282936434527376253013 733784565661342117690465)
                    ·
                      rfl

theorem cell23_4287121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_4287121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287121 prefixEnd_4287121 := by exact prefixLift 4287121
  have htrace : WordTrace (prefixWord ++ tailWord_4287121) baseStart_4287121 baseEnd_4287121 := by
    simpa [prefixWord, tailWord_4287121, baseEnd_4287121] using wordTrace_append hprefix tailTrace_4287121
  have hstable : (prefixWord ++ tailWord_4287121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287121).length < 2 ^ (prefixWord ++ tailWord_4287121).sum := by decide
  have hdescent : baseEnd_4287121 < baseStart_4287121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287155 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 3, 4]
def baseStart_4287155 : Nat := 118140960795 + 4287155 * 2 ^ 59
def prefixEnd_4287155 : Nat := 4983230072969 + 3 ^ 40 * 4287155 * 2
def baseEnd_4287155 : Nat := 733790385108759740015413

theorem tailTrace_4287155 : CollatzResearch.WordTrace tailWord_4287155 prefixEnd_4287155 733790385108759740015413 := by
  unfold tailWord_4287155
  simp only [CollatzResearch.WordTrace]
  refine ⟨156365388783377097626662919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104243592522251398417775279 156365388783377097626662919)
  ·
    refine ⟨234548083175065646439994379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156365388783377097626662919 234548083175065646439994379)
    ·
      refine ⟨351822124762598469659991569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234548083175065646439994379 351822124762598469659991569)
      ·
        refine ⟨263866593571948852244993677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351822124762598469659991569 263866593571948852244993677)
        ·
          refine ⟨98949972589480819591872629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263866593571948852244993677 98949972589480819591872629)
          ·
            refine ⟨9276559930263826836738059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98949972589480819591872629 9276559930263826836738059)
            ·
              refine ⟨13914839895395740255107089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9276559930263826836738059 13914839895395740255107089)
              ·
                refine ⟨10436129921546805191330317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13914839895395740255107089 10436129921546805191330317)
                ·
                  refine ⟨3913548720580051946748869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10436129921546805191330317 3913548720580051946748869)
                  ·
                    refine ⟨733790385108759740015413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3913548720580051946748869 733790385108759740015413)
                    ·
                      rfl

theorem cell23_4287155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 4].length) (baseStart_4287155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287155 prefixEnd_4287155 := by exact prefixLift 4287155
  have htrace : WordTrace (prefixWord ++ tailWord_4287155) baseStart_4287155 baseEnd_4287155 := by
    simpa [prefixWord, tailWord_4287155, baseEnd_4287155] using wordTrace_append hprefix tailTrace_4287155
  have hstable : (prefixWord ++ tailWord_4287155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287155).length < 2 ^ (prefixWord ++ tailWord_4287155).sum := by decide
  have hdescent : baseEnd_4287155 < baseStart_4287155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287165 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_4287165 : Nat := 118140960795 + 4287165 * 2 ^ 59
def prefixEnd_4287165 : Nat := 4983230072969 + 3 ^ 40 * 4287165 * 2
def baseEnd_4287165 : Nat := 2201376290132824180921193

theorem tailTrace_4287165 : CollatzResearch.WordTrace tailWord_4287165 prefixEnd_4287165 2201376290132824180921193 := by
  unfold tailWord_4287165
  simp only [CollatzResearch.WordTrace]
  refine ⟨156365753513340869334526949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104243835675560579556351299 156365753513340869334526949)
  ·
    refine ⟨29318578783751413000223803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156365753513340869334526949 29318578783751413000223803)
    ·
      refine ⟨43977868175627119500335705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29318578783751413000223803 43977868175627119500335705)
      ·
        refine ⟨32983401131720339625251779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43977868175627119500335705 32983401131720339625251779)
        ·
          refine ⟨49475101697580509437877669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32983401131720339625251779 49475101697580509437877669)
          ·
            refine ⟨9276581568296345519602063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49475101697580509437877669 9276581568296345519602063)
            ·
              refine ⟨13914872352444518279403095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9276581568296345519602063 13914872352444518279403095)
              ·
                refine ⟨20872308528666777419104643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13914872352444518279403095 20872308528666777419104643)
                ·
                  refine ⟨31308462793000166128656965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20872308528666777419104643 31308462793000166128656965)
                  ·
                    refine ⟨5870336773687531149123181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31308462793000166128656965 5870336773687531149123181)
                    ·
                      refine ⟨2201376290132824180921193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870336773687531149123181 2201376290132824180921193)
                      ·
                        rfl

theorem cell23_4287165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_4287165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287165 prefixEnd_4287165 := by exact prefixLift 4287165
  have htrace : WordTrace (prefixWord ++ tailWord_4287165) baseStart_4287165 baseEnd_4287165 := by
    simpa [prefixWord, tailWord_4287165, baseEnd_4287165] using wordTrace_append hprefix tailTrace_4287165
  have hstable : (prefixWord ++ tailWord_4287165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287165).length < 2 ^ (prefixWord ++ tailWord_4287165).sum := by decide
  have hdescent : baseEnd_4287165 < baseStart_4287165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287189 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_4287189 : Nat := 118140960795 + 4287189 * 2 ^ 59
def prefixEnd_4287189 : Nat := 4983230072969 + 3 ^ 40 * 4287189 * 2
def baseEnd_4287189 : Nat := 733796204556177362340361

theorem tailTrace_4287189 : CollatzResearch.WordTrace tailWord_4287189 prefixEnd_4287189 733796204556177362340361 := by
  unfold tailWord_4287189
  simp only [CollatzResearch.WordTrace]
  refine ⟨156366628865253921433400621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104244419243502614288933747 156366628865253921433400621)
  ·
    refine ⟨58637485824470220537525233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156366628865253921433400621 58637485824470220537525233)
    ·
      refine ⟨43978114368352665403143925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58637485824470220537525233 43978114368352665403143925)
      ·
        refine ⟨4122948222033062381544743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43978114368352665403143925 4122948222033062381544743)
        ·
          refine ⟨6184422333049593572317115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122948222033062381544743 6184422333049593572317115)
          ·
            refine ⟨9276633499574390358475673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6184422333049593572317115 9276633499574390358475673)
            ·
              refine ⟨6957475124680792768856755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9276633499574390358475673 6957475124680792768856755)
              ·
                refine ⟨10436212687021189153285133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6957475124680792768856755 10436212687021189153285133)
                ·
                  refine ⟨3913579757632945932481925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10436212687021189153285133 3913579757632945932481925)
                  ·
                    refine ⟨733796204556177362340361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3913579757632945932481925 733796204556177362340361)
                    ·
                      rfl

theorem cell23_4287189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_4287189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287189 prefixEnd_4287189 := by exact prefixLift 4287189
  have htrace : WordTrace (prefixWord ++ tailWord_4287189) baseStart_4287189 baseEnd_4287189 := by
    simpa [prefixWord, tailWord_4287189, baseEnd_4287189] using wordTrace_append hprefix tailTrace_4287189
  have hstable : (prefixWord ++ tailWord_4287189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287189).length < 2 ^ (prefixWord ++ tailWord_4287189).sum := by decide
  have hdescent : baseEnd_4287189 < baseStart_4287189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287215 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 1, 5]
def baseStart_4287215 : Nat := 118140960795 + 4287215 * 2 ^ 59
def prefixEnd_4287215 : Nat := 4983230072969 + 3 ^ 40 * 4287215 * 2
def baseEnd_4287215 : Nat := 733800654721849661765321

theorem tailTrace_4287215 : CollatzResearch.WordTrace tailWord_4287215 prefixEnd_4287215 733800654721849661765321 := by
  unfold tailWord_4287215
  simp only [CollatzResearch.WordTrace]
  refine ⟨156367577163159727873847099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104245051442106485249231399 156367577163159727873847099)
  ·
    refine ⟨234551365744739591810770649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156367577163159727873847099 234551365744739591810770649)
    ·
      refine ⟨175913524308554693858077987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234551365744739591810770649 175913524308554693858077987)
      ·
        refine ⟨263870286462832040787116981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175913524308554693858077987 263870286462832040787116981)
        ·
          refine ⟨24737839355890503823792217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263870286462832040787116981 24737839355890503823792217)
          ·
            refine ⟨18553379516917877867844163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24737839355890503823792217 18553379516917877867844163)
            ·
              refine ⟨27830069275376816801766245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18553379516917877867844163 27830069275376816801766245)
              ·
                refine ⟨5218137989133153150331171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27830069275376816801766245 5218137989133153150331171)
                ·
                  refine ⟨7827206983699729725496757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218137989133153150331171 7827206983699729725496757)
                  ·
                    refine ⟨733800654721849661765321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7827206983699729725496757 733800654721849661765321)
                    ·
                      rfl

theorem cell23_4287215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_4287215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287215 prefixEnd_4287215 := by exact prefixLift 4287215
  have htrace : WordTrace (prefixWord ++ tailWord_4287215) baseStart_4287215 baseEnd_4287215 := by
    simpa [prefixWord, tailWord_4287215, baseEnd_4287215] using wordTrace_append hprefix tailTrace_4287215
  have hstable : (prefixWord ++ tailWord_4287215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287215).length < 2 ^ (prefixWord ++ tailWord_4287215).sum := by decide
  have hdescent : baseEnd_4287215 < baseStart_4287215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287222 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4287222 : Nat := 118140960795 + 4287222 * 2 ^ 59
def prefixEnd_4287222 : Nat := 4983230072969 + 3 ^ 40 * 4287222 * 2
def baseEnd_4287222 : Nat := 2201405558530130457908431

theorem tailTrace_4287222 : CollatzResearch.WordTrace tailWord_4287222 prefixEnd_4287222 2201405558530130457908431 := by
  unfold tailWord_4287222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9772989529633398004334495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104245221649422912046234613 9772989529633398004334495)
  ·
    refine ⟨14659484294450097006501743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9772989529633398004334495 14659484294450097006501743)
    ·
      refine ⟨21989226441675145509752615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14659484294450097006501743 21989226441675145509752615)
      ·
        refine ⟨32983839662512718264628923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21989226441675145509752615 32983839662512718264628923)
        ·
          refine ⟨49475759493769077396943385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32983839662512718264628923 49475759493769077396943385)
          ·
            refine ⟨37106819620326808047707539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49475759493769077396943385 37106819620326808047707539)
            ·
              refine ⟨55660229430490212071561309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37106819620326808047707539 55660229430490212071561309)
              ·
                refine ⟨20872586036433829526835491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55660229430490212071561309 20872586036433829526835491)
                ·
                  refine ⟨31308879054650744290253237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20872586036433829526835491 31308879054650744290253237)
                  ·
                    refine ⟨2935207411373507277211241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31308879054650744290253237 2935207411373507277211241)
                    ·
                      refine ⟨2201405558530130457908431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935207411373507277211241 2201405558530130457908431)
                      ·
                        rfl

theorem cell23_4287222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4287222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287222 prefixEnd_4287222 := by exact prefixLift 4287222
  have htrace : WordTrace (prefixWord ++ tailWord_4287222) baseStart_4287222 baseEnd_4287222 := by
    simpa [prefixWord, tailWord_4287222, baseEnd_4287222] using wordTrace_append hprefix tailTrace_4287222
  have hstable : (prefixWord ++ tailWord_4287222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287222).length < 2 ^ (prefixWord ++ tailWord_4287222).sum := by decide
  have hdescent : baseEnd_4287222 < baseStart_4287222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287239 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4287239 : Nat := 118140960795 + 4287239 * 2 ^ 59
def prefixEnd_4287239 : Nat := 4983230072969 + 3 ^ 40 * 4287239 * 2
def baseEnd_4287239 : Nat := 2201414287701256891395853

theorem tailTrace_4287239 : CollatzResearch.WordTrace tailWord_4287239 prefixEnd_4287239 2201414287701256891395853 := by
  unfold tailWord_4287239
  simp only [CollatzResearch.WordTrace]
  refine ⟨156368452515072779972720771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104245635010048519981813847 156368452515072779972720771)
  ·
    refine ⟨234552678772609169959081157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156368452515072779972720771 234552678772609169959081157)
    ·
      refine ⟨43978627269864219367327717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234552678772609169959081157 43978627269864219367327717)
      ·
        refine ⟨8245992613099541131373947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43978627269864219367327717 8245992613099541131373947)
        ·
          refine ⟨12368988919649311697060921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8245992613099541131373947 12368988919649311697060921)
          ·
            refine ⟨9276741689736983772795691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12368988919649311697060921 9276741689736983772795691)
            ·
              refine ⟨13915112534605475659193537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9276741689736983772795691 13915112534605475659193537)
              ·
                refine ⟨10436334400954106744395153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13915112534605475659193537 10436334400954106744395153)
                ·
                  refine ⟨7827250800715580058296365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10436334400954106744395153 7827250800715580058296365)
                  ·
                    refine ⟨2935219050268342521861137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7827250800715580058296365 2935219050268342521861137)
                    ·
                      refine ⟨2201414287701256891395853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935219050268342521861137 2201414287701256891395853)
                      ·
                        rfl

theorem cell23_4287239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4287239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287239 prefixEnd_4287239 := by exact prefixLift 4287239
  have htrace : WordTrace (prefixWord ++ tailWord_4287239) baseStart_4287239 baseEnd_4287239 := by
    simpa [prefixWord, tailWord_4287239, baseEnd_4287239] using wordTrace_append hprefix tailTrace_4287239
  have hstable : (prefixWord ++ tailWord_4287239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287239).length < 2 ^ (prefixWord ++ tailWord_4287239).sum := by decide
  have hdescent : baseEnd_4287239 < baseStart_4287239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287265 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4287265 : Nat := 118140960795 + 4287265 * 2 ^ 59
def prefixEnd_4287265 : Nat := 4983230072969 + 3 ^ 40 * 4287265 * 2
def baseEnd_4287265 : Nat := 2201427638198273789670733

theorem tailTrace_4287265 : CollatzResearch.WordTrace tailWord_4287265 prefixEnd_4287265 2201427638198273789670733 := by
  unfold tailWord_4287265
  simp only [CollatzResearch.WordTrace]
  refine ⟨156369400812978586413167249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104246267208652390942111499 156369400812978586413167249)
  ·
    refine ⟨117277050609733939809875437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156369400812978586413167249 117277050609733939809875437)
    ·
      refine ⟨43978893978650227428703289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117277050609733939809875437 43978893978650227428703289)
      ·
        refine ⟨32984170483987670571527467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43978893978650227428703289 32984170483987670571527467)
        ·
          refine ⟨49476255725981505857291201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32984170483987670571527467 49476255725981505857291201)
          ·
            refine ⟨37107191794486129392968401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49476255725981505857291201 37107191794486129392968401)
            ·
              refine ⟨27830393845864597044726301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37107191794486129392968401 27830393845864597044726301)
              ·
                refine ⟨10436397692199223891772363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27830393845864597044726301 10436397692199223891772363)
                ·
                  refine ⟨15654596538298835837658545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10436397692199223891772363 15654596538298835837658545)
                  ·
                    refine ⟨11740947403724126878243909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15654596538298835837658545 11740947403724126878243909)
                    ·
                      refine ⟨2201427638198273789670733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11740947403724126878243909 2201427638198273789670733)
                      ·
                        rfl

theorem cell23_4287265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4287265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287265 prefixEnd_4287265 := by exact prefixLift 4287265
  have htrace : WordTrace (prefixWord ++ tailWord_4287265) baseStart_4287265 baseEnd_4287265 := by
    simpa [prefixWord, tailWord_4287265, baseEnd_4287265] using wordTrace_append hprefix tailTrace_4287265
  have hstable : (prefixWord ++ tailWord_4287265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287265).length < 2 ^ (prefixWord ++ tailWord_4287265).sum := by decide
  have hdescent : baseEnd_4287265 < baseStart_4287265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287272 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_4287272 : Nat := 118140960795 + 4287272 * 2 ^ 59
def prefixEnd_4287272 : Nat := 4983230072969 + 3 ^ 40 * 4287272 * 2
def baseEnd_4287272 : Nat := 2201431232562855262283201

theorem tailTrace_4287272 : CollatzResearch.WordTrace tailWord_4287272 prefixEnd_4287272 2201431232562855262283201 := by
  unfold tailWord_4287272
  simp only [CollatzResearch.WordTrace]
  refine ⟨78184828061976613304336035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104246437415968817739114713 78184828061976613304336035)
  ·
    refine ⟨117277242092964919956504053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78184828061976613304336035 117277242092964919956504053)
    ·
      refine ⟨10994741446215461245922255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117277242092964919956504053 10994741446215461245922255)
      ·
        refine ⟨16492112169323191868883383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10994741446215461245922255 16492112169323191868883383)
        ·
          refine ⟨24738168253984787803325075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16492112169323191868883383 24738168253984787803325075)
          ·
            refine ⟨37107252380977181704987613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24738168253984787803325075 37107252380977181704987613)
            ·
              refine ⟨13915219642866443139370355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37107252380977181704987613 13915219642866443139370355)
              ·
                refine ⟨20872829464299664709055533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13915219642866443139370355 20872829464299664709055533)
                ·
                  refine ⟨7827311049112374265895825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20872829464299664709055533 7827311049112374265895825)
                  ·
                    refine ⟨5870483286834280699421869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7827311049112374265895825 5870483286834280699421869)
                    ·
                      refine ⟨2201431232562855262283201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870483286834280699421869 2201431232562855262283201)
                      ·
                        rfl

theorem cell23_4287272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_4287272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287272 prefixEnd_4287272 := by exact prefixLift 4287272
  have htrace : WordTrace (prefixWord ++ tailWord_4287272) baseStart_4287272 baseEnd_4287272 := by
    simpa [prefixWord, tailWord_4287272, baseEnd_4287272] using wordTrace_append hprefix tailTrace_4287272
  have hstable : (prefixWord ++ tailWord_4287272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287272).length < 2 ^ (prefixWord ++ tailWord_4287272).sum := by decide
  have hdescent : baseEnd_4287272 < baseStart_4287272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287297 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4287297 : Nat := 118140960795 + 4287297 * 2 ^ 59
def prefixEnd_4287297 : Nat := 4983230072969 + 3 ^ 40 * 4287297 * 2
def baseEnd_4287297 : Nat := 2201444069579217664470587

theorem tailTrace_4287297 : CollatzResearch.WordTrace tailWord_4287297 prefixEnd_4287297 2201444069579217664470587 := by
  unfold tailWord_4287297
  simp only [CollatzResearch.WordTrace]
  refine ⟨156370567948862655878332145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104247045299241770585554763 156370567948862655878332145)
  ·
    refine ⟨117277925961646991908749109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156370567948862655878332145 117277925961646991908749109)
    ·
      refine ⟨10994805558904405491445229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117277925961646991908749109 10994805558904405491445229)
      ·
        refine ⟨4123052084589152059291961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10994805558904405491445229 4123052084589152059291961)
        ·
          refine ⟨3092289063441864044468971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123052084589152059291961 3092289063441864044468971)
          ·
            refine ⟨4638433595162796066703457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092289063441864044468971 4638433595162796066703457)
            ·
              refine ⟨3478825196372097050027593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638433595162796066703457 3478825196372097050027593)
              ·
                refine ⟨2609118897279072787520695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478825196372097050027593 2609118897279072787520695)
                ·
                  refine ⟨3913678345918609181281043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609118897279072787520695 3913678345918609181281043)
                  ·
                    refine ⟨5870517518877913771921565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3913678345918609181281043 5870517518877913771921565)
                    ·
                      refine ⟨2201444069579217664470587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870517518877913771921565 2201444069579217664470587)
                      ·
                        rfl

theorem cell23_4287297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4287297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287297 prefixEnd_4287297 := by exact prefixLift 4287297
  have htrace : WordTrace (prefixWord ++ tailWord_4287297) baseStart_4287297 baseEnd_4287297 := by
    simpa [prefixWord, tailWord_4287297, baseEnd_4287297] using wordTrace_append hprefix tailTrace_4287297
  have hstable : (prefixWord ++ tailWord_4287297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287297).length < 2 ^ (prefixWord ++ tailWord_4287297).sum := by decide
  have hdescent : baseEnd_4287297 < baseStart_4287297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287309 : List Nat := [1, 6, 1, 2, 2, 2, 1, 8]
def baseStart_4287309 : Nat := 118140960795 + 4287309 * 2 ^ 59
def prefixEnd_4287309 : Nat := 4983230072969 + 3 ^ 40 * 4287309 * 2
def baseEnd_4287309 : Nat := 81535193753595245093353

theorem tailTrace_4287309 : CollatzResearch.WordTrace tailWord_4287309 prefixEnd_4287309 81535193753595245093353 := by
  unfold tailWord_4287309
  simp only [CollatzResearch.WordTrace]
  refine ⟨156371005624819181927768981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104247337083212787951845987 156371005624819181927768981)
  ·
    refine ⟨7329890888663399152864171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156371005624819181927768981 7329890888663399152864171)
    ·
      refine ⟨10994836332995098729296257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329890888663399152864171 10994836332995098729296257)
      ·
        refine ⟨8246127249746324046972193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10994836332995098729296257 8246127249746324046972193)
        ·
          refine ⟨6184595437309743035229145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8246127249746324046972193 6184595437309743035229145)
          ·
            refine ⟨4638446577982307276421859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6184595437309743035229145 4638446577982307276421859)
            ·
              refine ⟨6957669866973460914632789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638446577982307276421859 6957669866973460914632789)
              ·
                refine ⟨81535193753595245093353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6957669866973460914632789 81535193753595245093353)
                ·
                  rfl

theorem cell23_4287309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 8].length) (baseStart_4287309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287309 prefixEnd_4287309 := by exact prefixLift 4287309
  have htrace : WordTrace (prefixWord ++ tailWord_4287309) baseStart_4287309 baseEnd_4287309 := by
    simpa [prefixWord, tailWord_4287309, baseEnd_4287309] using wordTrace_append hprefix tailTrace_4287309
  have hstable : (prefixWord ++ tailWord_4287309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287309).length < 2 ^ (prefixWord ++ tailWord_4287309).sum := by decide
  have hdescent : baseEnd_4287309 < baseStart_4287309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287312 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2]
def baseStart_4287312 : Nat := 118140960795 + 4287312 * 2 ^ 59
def prefixEnd_4287312 : Nat := 4983230072969 + 3 ^ 40 * 4287312 * 2
def baseEnd_4287312 : Nat := 2201451771789035105783017

theorem tailTrace_4287312 : CollatzResearch.WordTrace tailWord_4287312 prefixEnd_4287312 2201451771789035105783017 := by
  unfold tailWord_4287312
  simp only [CollatzResearch.WordTrace]
  refine ⟨78185557521904156720064095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104247410029205542293418793 78185557521904156720064095)
  ·
    refine ⟨117278336282856235080096143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78185557521904156720064095 117278336282856235080096143)
    ·
      refine ⟨175917504424284352620144215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117278336282856235080096143 175917504424284352620144215)
      ·
        refine ⟨263876256636426528930216323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175917504424284352620144215 263876256636426528930216323)
        ·
          refine ⟨395814384954639793395324485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263876256636426528930216323 395814384954639793395324485)
          ·
            refine ⟨74215197178994961261623341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 395814384954639793395324485 74215197178994961261623341)
            ·
              refine ⟨27830698942123110473108753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74215197178994961261623341 27830698942123110473108753)
              ·
                refine ⟨20873024206592332854831565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27830698942123110473108753 20873024206592332854831565)
                ·
                  refine ⟨7827384077472124820561837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20873024206592332854831565 7827384077472124820561837)
                  ·
                    refine ⟨2935269029052046807710689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7827384077472124820561837 2935269029052046807710689)
                    ·
                      refine ⟨2201451771789035105783017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935269029052046807710689 2201451771789035105783017)
                      ·
                        rfl

theorem cell23_4287312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2].length) (baseStart_4287312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287312 prefixEnd_4287312 := by exact prefixLift 4287312
  have htrace : WordTrace (prefixWord ++ tailWord_4287312) baseStart_4287312 baseEnd_4287312 := by
    simpa [prefixWord, tailWord_4287312, baseEnd_4287312] using wordTrace_append hprefix tailTrace_4287312
  have hstable : (prefixWord ++ tailWord_4287312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287312).length < 2 ^ (prefixWord ++ tailWord_4287312).sum := by decide
  have hdescent : baseEnd_4287312 < baseStart_4287312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287319 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_4287319 : Nat := 118140960795 + 4287319 * 2 ^ 59
def prefixEnd_4287319 : Nat := 4983230072969 + 3 ^ 40 * 4287319 * 2
def baseEnd_4287319 : Nat := 2201455366153616578395485

theorem tailTrace_4287319 : CollatzResearch.WordTrace tailWord_4287319 prefixEnd_4287319 2201455366153616578395485 := by
  unfold tailWord_4287319
  simp only [CollatzResearch.WordTrace]
  refine ⟨156371370354782953635633011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104247580236521969090422007 156371370354782953635633011)
  ·
    refine ⟨234557055532174430453449517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156371370354782953635633011 234557055532174430453449517)
    ·
      refine ⟨87958895824565411420043569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234557055532174430453449517 87958895824565411420043569)
      ·
        refine ⟨65969171868424058565032677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87958895824565411420043569 65969171868424058565032677)
        ·
          refine ⟨12369219725329510980943627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65969171868424058565032677 12369219725329510980943627)
          ·
            refine ⟨18553829587994266471415441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12369219725329510980943627 18553829587994266471415441)
            ·
              refine ⟨13915372190995699853561581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18553829587994266471415441 13915372190995699853561581)
              ·
                refine ⟨5218264571623387445085593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13915372190995699853561581 5218264571623387445085593)
                ·
                  refine ⟨3913698428717540583814195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5218264571623387445085593 3913698428717540583814195)
                  ·
                    refine ⟨5870547643076310875721293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3913698428717540583814195 5870547643076310875721293)
                    ·
                      refine ⟨2201455366153616578395485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870547643076310875721293 2201455366153616578395485)
                      ·
                        rfl

theorem cell23_4287319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_4287319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287319 prefixEnd_4287319 := by exact prefixLift 4287319
  have htrace : WordTrace (prefixWord ++ tailWord_4287319) baseStart_4287319 baseEnd_4287319 := by
    simpa [prefixWord, tailWord_4287319, baseEnd_4287319] using wordTrace_append hprefix tailTrace_4287319
  have hstable : (prefixWord ++ tailWord_4287319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287319).length < 2 ^ (prefixWord ++ tailWord_4287319).sum := by decide
  have hdescent : baseEnd_4287319 < baseStart_4287319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287346 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4287346 : Nat := 118140960795 + 4287346 * 2 ^ 59
def prefixEnd_4287346 : Nat := 4983230072969 + 3 ^ 40 * 4287346 * 2
def baseEnd_4287346 : Nat := 2201469230131287972757861

theorem tailTrace_4287346 : CollatzResearch.WordTrace tailWord_4287346 prefixEnd_4287346 2201469230131287972757861 := by
  unfold tailWord_4287346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39093088781421284311716473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104248236750456758164577261 39093088781421284311716473)
  ·
    refine ⟨29319816586065963233787355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39093088781421284311716473 29319816586065963233787355)
    ·
      refine ⟨43979724879098944850681033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29319816586065963233787355 43979724879098944850681033)
      ·
        refine ⟨32984793659324208638010775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43979724879098944850681033 32984793659324208638010775)
        ·
          refine ⟨49477190488986312957016163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32984793659324208638010775 49477190488986312957016163)
          ·
            refine ⟨74215785733479469435524245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49477190488986312957016163 74215785733479469435524245)
            ·
              refine ⟨3478864956256850129790199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74215785733479469435524245 3478864956256850129790199)
              ·
                refine ⟨5218297434385275194685299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478864956256850129790199 5218297434385275194685299)
                ·
                  refine ⟨7827446151577912792027949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218297434385275194685299 7827446151577912792027949)
                  ·
                    refine ⟨2935292306841717297010481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7827446151577912792027949 2935292306841717297010481)
                    ·
                      refine ⟨2201469230131287972757861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935292306841717297010481 2201469230131287972757861)
                      ·
                        rfl

theorem cell23_4287346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4287346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287346 prefixEnd_4287346 := by exact prefixLift 4287346
  have htrace : WordTrace (prefixWord ++ tailWord_4287346) baseStart_4287346 baseEnd_4287346 := by
    simpa [prefixWord, tailWord_4287346, baseEnd_4287346] using wordTrace_append hprefix tailTrace_4287346
  have hstable : (prefixWord ++ tailWord_4287346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287346).length < 2 ^ (prefixWord ++ tailWord_4287346).sum := by decide
  have hdescent : baseEnd_4287346 < baseStart_4287346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287355 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_4287355 : Nat := 118140960795 + 4287355 * 2 ^ 59
def prefixEnd_4287355 : Nat := 4983230072969 + 3 ^ 40 * 4287355 * 2
def baseEnd_4287355 : Nat := 2201473851457178437545319

theorem tailTrace_4287355 : CollatzResearch.WordTrace tailWord_4287355 prefixEnd_4287355 2201473851457178437545319 := by
  unfold tailWord_4287355
  simp only [CollatzResearch.WordTrace]
  refine ⟨156372683382652531783943519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104248455588435021189295679 156372683382652531783943519)
  ·
    refine ⟨234559025073978797675915279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156372683382652531783943519 234559025073978797675915279)
    ·
      refine ⟨351838537610968196513872919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234559025073978797675915279 351838537610968196513872919)
      ·
        refine ⟨527757806416452294770809379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351838537610968196513872919 527757806416452294770809379)
        ·
          refine ⟨791636709624678442156214069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527757806416452294770809379 791636709624678442156214069)
          ·
            refine ⟨74215941527313603952145069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 791636709624678442156214069 74215941527313603952145069)
            ·
              refine ⟨27830978072742601482054401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74215941527313603952145069 27830978072742601482054401)
              ·
                refine ⟨20873233554556951111540801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27830978072742601482054401 20873233554556951111540801)
                ·
                  refine ⟨15654925165917713333655601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20873233554556951111540801 15654925165917713333655601)
                  ·
                    refine ⟨11741193874438285000241701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15654925165917713333655601 11741193874438285000241701)
                    ·
                      refine ⟨2201473851457178437545319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11741193874438285000241701 2201473851457178437545319)
                      ·
                        rfl

theorem cell23_4287355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_4287355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287355 prefixEnd_4287355 := by exact prefixLift 4287355
  have htrace : WordTrace (prefixWord ++ tailWord_4287355) baseStart_4287355 baseEnd_4287355 := by
    simpa [prefixWord, tailWord_4287355, baseEnd_4287355] using wordTrace_append hprefix tailTrace_4287355
  have hstable : (prefixWord ++ tailWord_4287355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287355).length < 2 ^ (prefixWord ++ tailWord_4287355).sum := by decide
  have hdescent : baseEnd_4287355 < baseStart_4287355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287365 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 7]
def baseStart_4287365 : Nat := 118140960795 + 4287365 * 2 ^ 59
def prefixEnd_4287365 : Nat := 4983230072969 + 3 ^ 40 * 4287365 * 2
def baseEnd_4287365 : Nat := 244608776251524822046697

theorem tailTrace_4287365 : CollatzResearch.WordTrace tailWord_4287365 prefixEnd_4287365 244608776251524822046697 := by
  unfold tailWord_4287365
  simp only [CollatzResearch.WordTrace]
  refine ⟨156373048112616303491807549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104248698741744202327871699 156373048112616303491807549)
  ·
    refine ⟨58639893042231113809427831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156373048112616303491807549 58639893042231113809427831)
    ·
      refine ⟨87959839563346670714141747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58639893042231113809427831 87959839563346670714141747)
      ·
        refine ⟨131939759345020006071212621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87959839563346670714141747 131939759345020006071212621)
        ·
          refine ⟨49477409754382502276704733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131939759345020006071212621 49477409754382502276704733)
          ·
            refine ⟨18554028657893438353764275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49477409754382502276704733 18554028657893438353764275)
            ·
              refine ⟨27831042986840157530646413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18554028657893438353764275 27831042986840157530646413)
              ·
                refine ⟨10436641120065059073992405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27831042986840157530646413 10436641120065059073992405)
                ·
                  refine ⟨244608776251524822046697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10436641120065059073992405 244608776251524822046697)
                  ·
                    rfl

theorem cell23_4287365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_4287365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287365 prefixEnd_4287365 := by exact prefixLift 4287365
  have htrace : WordTrace (prefixWord ++ tailWord_4287365) baseStart_4287365 baseEnd_4287365 := by
    simpa [prefixWord, tailWord_4287365, baseEnd_4287365] using wordTrace_append hprefix tailTrace_4287365
  have hstable : (prefixWord ++ tailWord_4287365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287365).length < 2 ^ (prefixWord ++ tailWord_4287365).sum := by decide
  have hdescent : baseEnd_4287365 < baseStart_4287365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287395 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 7]
def baseStart_4287395 : Nat := 118140960795 + 4287395 * 2 ^ 59
def prefixEnd_4287395 : Nat := 4983230072969 + 3 ^ 40 * 4287395 * 2
def baseEnd_4287395 : Nat := 733831463561119427015045

theorem tailTrace_4287395 : CollatzResearch.WordTrace tailWord_4287395 prefixEnd_4287395 733831463561119427015045 := by
  unfold tailWord_4287395
  simp only [CollatzResearch.WordTrace]
  refine ⟨156374142302507618615399639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104249428201671745743599759 156374142302507618615399639)
  ·
    refine ⟨234561213453761427923099459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156374142302507618615399639 234561213453761427923099459)
    ·
      refine ⟨351841820180642141884649189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234561213453761427923099459 351841820180642141884649189)
      ·
        refine ⟨65970341283870401603371723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 351841820180642141884649189 65970341283870401603371723)
        ·
          refine ⟨98955511925805602405057585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65970341283870401603371723 98955511925805602405057585)
          ·
            refine ⟨74216633944354201803793189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98955511925805602405057585 74216633944354201803793189)
            ·
              refine ⟨13915618864566412838211223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74216633944354201803793189 13915618864566412838211223)
              ·
                refine ⟨20873428296849619257316835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13915618864566412838211223 20873428296849619257316835)
                ·
                  refine ⟨31310142445274428885975253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20873428296849619257316835 31310142445274428885975253)
                  ·
                    refine ⟨733831463561119427015045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31310142445274428885975253 733831463561119427015045)
                    ·
                      rfl

theorem cell23_4287395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_4287395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287395 prefixEnd_4287395 := by exact prefixLift 4287395
  have htrace : WordTrace (prefixWord ++ tailWord_4287395) baseStart_4287395 baseEnd_4287395 := by
    simpa [prefixWord, tailWord_4287395, baseEnd_4287395] using wordTrace_append hprefix tailTrace_4287395
  have hstable : (prefixWord ++ tailWord_4287395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287395).length < 2 ^ (prefixWord ++ tailWord_4287395).sum := by decide
  have hdescent : baseEnd_4287395 < baseStart_4287395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287422 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4287422 : Nat := 118140960795 + 4287422 * 2 ^ 59
def prefixEnd_4287422 : Nat := 4983230072969 + 3 ^ 40 * 4287422 * 2
def baseEnd_4287422 : Nat := 2201508254661029675407511

theorem tailTrace_4287422 : CollatzResearch.WordTrace tailWord_4287422 prefixEnd_4287422 2201508254661029675407511 := by
  unfold tailWord_4287422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19546890884176225278329065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104250084715606534817755013 19546890884176225278329065)
  ·
    refine ⟨14660168163132168958746799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19546890884176225278329065 14660168163132168958746799)
    ·
      refine ⟨21990252244698253438120199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14660168163132168958746799 21990252244698253438120199)
      ·
        refine ⟨32985378367047380157180299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21990252244698253438120199 32985378367047380157180299)
        ·
          refine ⟨49478067550571070235770449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32985378367047380157180299 49478067550571070235770449)
          ·
            refine ⟨37108550662928302676827837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49478067550571070235770449 37108550662928302676827837)
            ·
              refine ⟨13915706498598113503810439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37108550662928302676827837 13915706498598113503810439)
              ·
                refine ⟨20873559747897170255715659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13915706498598113503810439 20873559747897170255715659)
                ·
                  refine ⟨31310339621845755383573489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20873559747897170255715659 31310339621845755383573489)
                  ·
                    refine ⟨23482754716384316537680117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31310339621845755383573489 23482754716384316537680117)
                    ·
                      refine ⟨2201508254661029675407511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23482754716384316537680117 2201508254661029675407511)
                      ·
                        rfl

theorem cell23_4287422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4287422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287422 prefixEnd_4287422 := by exact prefixLift 4287422
  have htrace : WordTrace (prefixWord ++ tailWord_4287422) baseStart_4287422 baseEnd_4287422 := by
    simpa [prefixWord, tailWord_4287422, baseEnd_4287422] using wordTrace_append hprefix tailTrace_4287422
  have hstable : (prefixWord ++ tailWord_4287422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287422).length < 2 ^ (prefixWord ++ tailWord_4287422).sum := by decide
  have hdescent : baseEnd_4287422 < baseStart_4287422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287446 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_4287446 : Nat := 118140960795 + 4287446 * 2 ^ 59
def prefixEnd_4287446 : Nat := 4983230072969 + 3 ^ 40 * 4287446 * 2
def baseEnd_4287446 : Nat := 733840192732245860502467

theorem tailTrace_4287446 : CollatzResearch.WordTrace tailWord_4287446 prefixEnd_4287446 733840192732245860502467 := by
  unfold tailWord_4287446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773500151582678395344137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104250668283548569550337461 9773500151582678395344137)
  ·
    refine ⟨7330125113687008796508103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9773500151582678395344137 7330125113687008796508103)
    ·
      refine ⟨10995187670530513194762155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330125113687008796508103 10995187670530513194762155)
      ·
        refine ⟨16492781505795769792143233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10995187670530513194762155 16492781505795769792143233)
        ·
          refine ⟨12369586129346827344107425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16492781505795769792143233 12369586129346827344107425)
          ·
            refine ⟨9277189597010120508080569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12369586129346827344107425 9277189597010120508080569)
            ·
              refine ⟨6957892197757590381060427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9277189597010120508080569 6957892197757590381060427)
              ·
                refine ⟨10436838296636385571590641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6957892197757590381060427 10436838296636385571590641)
                ·
                  refine ⟨7827628722477289178692981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10436838296636385571590641 7827628722477289178692981)
                  ·
                    refine ⟨733840192732245860502467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7827628722477289178692981 733840192732245860502467)
                    ·
                      rfl

theorem cell23_4287446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_4287446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287446 prefixEnd_4287446 := by exact prefixLift 4287446
  have htrace : WordTrace (prefixWord ++ tailWord_4287446) baseStart_4287446 baseEnd_4287446 := by
    simpa [prefixWord, tailWord_4287446, baseEnd_4287446] using wordTrace_append hprefix tailTrace_4287446
  have hstable : (prefixWord ++ tailWord_4287446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287446).length < 2 ^ (prefixWord ++ tailWord_4287446).sum := by decide
  have hdescent : baseEnd_4287446 < baseStart_4287446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287449 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_4287449 : Nat := 118140960795 + 4287449 * 2 ^ 59
def prefixEnd_4287449 : Nat := 4983230072969 + 3 ^ 40 * 4287449 * 2
def baseEnd_4287449 : Nat := 2201522118638701069769887

theorem tailTrace_4287449 : CollatzResearch.WordTrace tailWord_4287449 prefixEnd_4287449 2201522118638701069769887 := by
  unfold tailWord_4287449
  simp only [CollatzResearch.WordTrace]
  refine ⟨156376111844311985837865401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104250741229541323891910267 156376111844311985837865401)
  ·
    refine ⟨117282083883233989378399051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156376111844311985837865401 117282083883233989378399051)
    ·
      refine ⟨175923125824850984067598577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117282083883233989378399051 175923125824850984067598577)
      ·
        refine ⟨131942344368638238050698933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175923125824850984067598577 131942344368638238050698933)
        ·
          refine ⟨12369594784559834817253025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131942344368638238050698933 12369594784559834817253025)
          ·
            refine ⟨9277196088419876112939769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12369594784559834817253025 9277196088419876112939769)
            ·
              refine ⟨6957897066314907084704827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9277196088419876112939769 6957897066314907084704827)
              ·
                refine ⟨10436845599472360627057241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6957897066314907084704827 10436845599472360627057241)
                ·
                  refine ⟨7827634199604270470292931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10436845599472360627057241 7827634199604270470292931)
                  ·
                    refine ⟨11741451299406405705439397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7827634199604270470292931 11741451299406405705439397)
                    ·
                      refine ⟨2201522118638701069769887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11741451299406405705439397 2201522118638701069769887)
                      ·
                        rfl

theorem cell23_4287449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_4287449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287449 prefixEnd_4287449 := by exact prefixLift 4287449
  have htrace : WordTrace (prefixWord ++ tailWord_4287449) baseStart_4287449 baseEnd_4287449 := by
    simpa [prefixWord, tailWord_4287449, baseEnd_4287449] using wordTrace_append hprefix tailTrace_4287449
  have hstable : (prefixWord ++ tailWord_4287449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287449).length < 2 ^ (prefixWord ++ tailWord_4287449).sum := by decide
  have hdescent : baseEnd_4287449 < baseStart_4287449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287499 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 3]
def baseStart_4287499 : Nat := 118140960795 + 4287499 * 2 ^ 59
def prefixEnd_4287499 : Nat := 4983230072969 + 3 ^ 40 * 4287499 * 2
def baseEnd_4287499 : Nat := 2201547792671425874144657

theorem tailTrace_4287499 : CollatzResearch.WordTrace tailWord_4287499 prefixEnd_4287499 2201547792671425874144657 := by
  unfold tailWord_4287499
  simp only [CollatzResearch.WordTrace]
  refine ⟨156377935494130844377185551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104251956996087229584790367 156377935494130844377185551)
  ·
    refine ⟨234566903241196266565778327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156377935494130844377185551 234566903241196266565778327)
    ·
      refine ⟨351850354861794399848667491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234566903241196266565778327 351850354861794399848667491)
      ·
        refine ⟨527775532292691599773001237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351850354861794399848667491 527775532292691599773001237)
        ·
          refine ⟨24739478076219918739359433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 527775532292691599773001237 24739478076219918739359433)
          ·
            refine ⟨18554608557164939054519575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24739478076219918739359433 18554608557164939054519575)
            ·
              refine ⟨27831912835747408581779363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18554608557164939054519575 27831912835747408581779363)
              ·
                refine ⟨41747869253621112872669045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27831912835747408581779363 41747869253621112872669045)
                ·
                  refine ⟨3913862742526979331812723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41747869253621112872669045 3913862742526979331812723)
                  ·
                    refine ⟨5870794113790468997719085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3913862742526979331812723 5870794113790468997719085)
                    ·
                      refine ⟨2201547792671425874144657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870794113790468997719085 2201547792671425874144657)
                      ·
                        rfl

theorem cell23_4287499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 3].length) (baseStart_4287499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287499 prefixEnd_4287499 := by exact prefixLift 4287499
  have htrace : WordTrace (prefixWord ++ tailWord_4287499) baseStart_4287499 baseEnd_4287499 := by
    simpa [prefixWord, tailWord_4287499, baseEnd_4287499] using wordTrace_append hprefix tailTrace_4287499
  have hstable : (prefixWord ++ tailWord_4287499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287499).length < 2 ^ (prefixWord ++ tailWord_4287499).sum := by decide
  have hdescent : baseEnd_4287499 < baseStart_4287499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287515 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 10]
def baseStart_4287515 : Nat := 118140960795 + 4287515 * 2 ^ 59
def prefixEnd_4287515 : Nat := 4983230072969 + 3 ^ 40 * 4287515 * 2
def baseEnd_4287515 : Nat := 733852002787299270514861

theorem tailTrace_4287515 : CollatzResearch.WordTrace tailWord_4287515 prefixEnd_4287515 733852002787299270514861 := by
  unfold tailWord_4287515
  simp only [CollatzResearch.WordTrace]
  refine ⟨156378519062072879109767999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104252346041381919406511999 156378519062072879109767999)
  ·
    refine ⟨234567778593109318664651999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156378519062072879109767999 234567778593109318664651999)
    ·
      refine ⟨351851667889663977996977999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234567778593109318664651999 351851667889663977996977999)
      ·
        refine ⟨527777501834495966995466999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351851667889663977996977999 527777501834495966995466999)
        ·
          refine ⟨791666252751743950493200499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527777501834495966995466999 791666252751743950493200499)
          ·
            refine ⟨1187499379127615925739800749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791666252751743950493200499 1187499379127615925739800749)
            ·
              refine ⟨445312267172855972152425281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1187499379127615925739800749 445312267172855972152425281)
              ·
                refine ⟨333984200379641979114318961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445312267172855972152425281 333984200379641979114318961)
                ·
                  refine ⟨250488150284731484335739221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333984200379641979114318961 250488150284731484335739221)
                  ·
                    refine ⟨733852002787299270514861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 250488150284731484335739221 733852002787299270514861)
                    ·
                      rfl

theorem cell23_4287515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_4287515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287515 prefixEnd_4287515 := by exact prefixLift 4287515
  have htrace : WordTrace (prefixWord ++ tailWord_4287515) baseStart_4287515 baseEnd_4287515 := by
    simpa [prefixWord, tailWord_4287515, baseEnd_4287515] using wordTrace_append hprefix tailTrace_4287515
  have hstable : (prefixWord ++ tailWord_4287515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287515).length < 2 ^ (prefixWord ++ tailWord_4287515).sum := by decide
  have hdescent : baseEnd_4287515 < baseStart_4287515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287519 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 1, 5]
def baseStart_4287519 : Nat := 118140960795 + 4287519 * 2 ^ 59
def prefixEnd_4287519 : Nat := 4983230072969 + 3 ^ 40 * 4287519 * 2
def baseEnd_4287519 : Nat := 733852687428171931964855

theorem tailTrace_4287519 : CollatzResearch.WordTrace tailWord_4287519 prefixEnd_4287519 733852687428171931964855 := by
  unfold tailWord_4287519
  simp only [CollatzResearch.WordTrace]
  refine ⟨156378664954058387792913611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104252443302705591861942407 156378664954058387792913611)
  ·
    refine ⟨234567997431087581689370417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156378664954058387792913611 234567997431087581689370417)
    ·
      refine ⟨175925998073315686267027813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234567997431087581689370417 175925998073315686267027813)
      ·
        refine ⟨32986124638746691175067715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175925998073315686267027813 32986124638746691175067715)
        ·
          refine ⟨49479186958120036762601573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32986124638746691175067715 49479186958120036762601573)
          ·
            refine ⟨9277347554647506892987795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49479186958120036762601573 9277347554647506892987795)
            ·
              refine ⟨13916021331971260339481693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9277347554647506892987795 13916021331971260339481693)
              ·
                refine ⟨5218507999489222627305635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13916021331971260339481693 5218507999489222627305635)
                ·
                  refine ⟨7827761999233833940958453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218507999489222627305635 7827761999233833940958453)
                  ·
                    refine ⟨733852687428171931964855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7827761999233833940958453 733852687428171931964855)
                    ·
                      rfl

theorem cell23_4287519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_4287519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287519 prefixEnd_4287519 := by exact prefixLift 4287519
  have htrace : WordTrace (prefixWord ++ tailWord_4287519) baseStart_4287519 baseEnd_4287519 := by
    simpa [prefixWord, tailWord_4287519, baseEnd_4287519] using wordTrace_append hprefix tailTrace_4287519
  have hstable : (prefixWord ++ tailWord_4287519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287519).length < 2 ^ (prefixWord ++ tailWord_4287519).sum := by decide
  have hdescent : baseEnd_4287519 < baseStart_4287519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287549 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_4287549 : Nat := 118140960795 + 4287549 * 2 ^ 59
def prefixEnd_4287549 : Nat := 4983230072969 + 3 ^ 40 * 4287549 * 2
def baseEnd_4287549 : Nat := 733857822234716892839809

theorem tailTrace_4287549 : CollatzResearch.WordTrace tailWord_4287549 prefixEnd_4287549 733857822234716892839809 := by
  unfold tailWord_4287549
  simp only [CollatzResearch.WordTrace]
  refine ⟨156379759143949702916505701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104253172762633135277670467 156379759143949702916505701)
  ·
    refine ⟨29321204839490569296844819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156379759143949702916505701 29321204839490569296844819)
    ·
      refine ⟨43981807259235853945267229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29321204839490569296844819 43981807259235853945267229)
      ·
        refine ⟨16493177722213445229475211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43981807259235853945267229 16493177722213445229475211)
        ·
          refine ⟨24739766583320167844212817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16493177722213445229475211 24739766583320167844212817)
          ·
            refine ⟨18554824937490125883159613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24739766583320167844212817 18554824937490125883159613)
            ·
              refine ⟨6958059351558797206184855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18554824937490125883159613 6958059351558797206184855)
              ·
                refine ⟨10437089027338195809277283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6958059351558797206184855 10437089027338195809277283)
                ·
                  refine ⟨15655633541007293713915925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10437089027338195809277283 15655633541007293713915925)
                  ·
                    refine ⟨733857822234716892839809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15655633541007293713915925 733857822234716892839809)
                    ·
                      rfl

theorem cell23_4287549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_4287549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287549 prefixEnd_4287549 := by exact prefixLift 4287549
  have htrace : WordTrace (prefixWord ++ tailWord_4287549) baseStart_4287549 baseEnd_4287549 := by
    simpa [prefixWord, tailWord_4287549, baseEnd_4287549] using wordTrace_append hprefix tailTrace_4287549
  have hstable : (prefixWord ++ tailWord_4287549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287549).length < 2 ^ (prefixWord ++ tailWord_4287549).sum := by decide
  have hdescent : baseEnd_4287549 < baseStart_4287549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287552 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_4287552 : Nat := 118140960795 + 4287552 * 2 ^ 59
def prefixEnd_4287552 : Nat := 4983230072969 + 3 ^ 40 * 4287552 * 2
def baseEnd_4287552 : Nat := 2201575007146114166781913

theorem tailTrace_4287552 : CollatzResearch.WordTrace tailWord_4287552 prefixEnd_4287552 2201575007146114166781913 := by
  unfold tailWord_4287552
  simp only [CollatzResearch.WordTrace]
  refine ⟨78189934281469417214432455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104253245708625889619243273 78189934281469417214432455)
  ·
    refine ⟨117284901422204125821648683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78189934281469417214432455 117284901422204125821648683)
    ·
      refine ⟨175927352133306188732473025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117284901422204125821648683 175927352133306188732473025)
      ·
        refine ⟨131945514099979641549354769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175927352133306188732473025 131945514099979641549354769)
        ·
          refine ⟨98959135574984731162016077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131945514099979641549354769 98959135574984731162016077)
          ·
            refine ⟨37109675840619274185756029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98959135574984731162016077 37109675840619274185756029)
            ·
              refine ⟨13916128440232227819658511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37109675840619274185756029 13916128440232227819658511)
              ·
                refine ⟨20874192660348341729487767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13916128440232227819658511 20874192660348341729487767)
                ·
                  refine ⟨31311288990522512594231651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20874192660348341729487767 31311288990522512594231651)
                  ·
                    refine ⟨46966933485783768891347477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31311288990522512594231651 46966933485783768891347477)
                    ·
                      refine ⟨2201575007146114166781913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46966933485783768891347477 2201575007146114166781913)
                      ·
                        rfl

theorem cell23_4287552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_4287552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287552 prefixEnd_4287552 := by exact prefixLift 4287552
  have htrace : WordTrace (prefixWord ++ tailWord_4287552) baseStart_4287552 baseEnd_4287552 := by
    simpa [prefixWord, tailWord_4287552, baseEnd_4287552] using wordTrace_append hprefix tailTrace_4287552
  have hstable : (prefixWord ++ tailWord_4287552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287552).length < 2 ^ (prefixWord ++ tailWord_4287552).sum := by decide
  have hdescent : baseEnd_4287552 < baseStart_4287552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287606 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4287606 : Nat := 118140960795 + 4287606 * 2 ^ 59
def prefixEnd_4287606 : Nat := 4983230072969 + 3 ^ 40 * 4287606 * 2
def baseEnd_4287606 : Nat := 2201602735101456955506665

theorem tailTrace_4287606 : CollatzResearch.WordTrace tailWord_4287606 prefixEnd_4287606 2201602735101456955506665 := by
  unfold tailWord_4287606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773864881546450103208167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104254558736495467767553781 9773864881546450103208167)
  ·
    refine ⟨14660797322319675154812251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9773864881546450103208167 14660797322319675154812251)
    ·
      refine ⟨21991195983479512732218377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14660797322319675154812251 21991195983479512732218377)
      ·
        refine ⟨16493396987609634549163783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21991195983479512732218377 16493396987609634549163783)
        ·
          refine ⟨24740095481414451823745675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16493396987609634549163783 24740095481414451823745675)
          ·
            refine ⟨37110143222121677735618513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24740095481414451823745675 37110143222121677735618513)
            ·
              refine ⟨27832607416591258301713885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37110143222121677735618513 27832607416591258301713885)
              ·
                refine ⟨10437227781221721863142707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27832607416591258301713885 10437227781221721863142707)
                ·
                  refine ⟨15655841671832582794714061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10437227781221721863142707 15655841671832582794714061)
                  ·
                    refine ⟨5870940626937218548017773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15655841671832582794714061 5870940626937218548017773)
                    ·
                      refine ⟨2201602735101456955506665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870940626937218548017773 2201602735101456955506665)
                      ·
                        rfl

theorem cell23_4287606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4287606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287606 prefixEnd_4287606 := by exact prefixLift 4287606
  have htrace : WordTrace (prefixWord ++ tailWord_4287606) baseStart_4287606 baseEnd_4287606 := by
    simpa [prefixWord, tailWord_4287606, baseEnd_4287606] using wordTrace_append hprefix tailTrace_4287606
  have hstable : (prefixWord ++ tailWord_4287606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287606).length < 2 ^ (prefixWord ++ tailWord_4287606).sum := by decide
  have hdescent : baseEnd_4287606 < baseStart_4287606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287632 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_4287632 : Nat := 118140960795 + 4287632 * 2 ^ 59
def prefixEnd_4287632 : Nat := 4983230072969 + 3 ^ 40 * 4287632 * 2
def baseEnd_4287632 : Nat := 2201616085598473853781545

theorem tailTrace_4287632 : CollatzResearch.WordTrace tailWord_4287632 prefixEnd_4287632 2201616085598473853781545 := by
  unfold tailWord_4287632
  simp only [CollatzResearch.WordTrace]
  refine ⟨78191393201324504045888575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104255190935099338727851433 78191393201324504045888575)
  ·
    refine ⟨117287089801986756068832863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78191393201324504045888575 117287089801986756068832863)
    ·
      refine ⟨175930634702980134103249295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117287089801986756068832863 175930634702980134103249295)
      ·
        refine ⟨263895952054470201154873943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175930634702980134103249295 263895952054470201154873943)
        ·
          refine ⟨395843928081705301732310915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263895952054470201154873943 395843928081705301732310915)
          ·
            refine ⟨593765892122557952598466373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395843928081705301732310915 593765892122557952598466373)
            ·
              refine ⟨111331104772979616112212445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 593765892122557952598466373 111331104772979616112212445)
              ·
                refine ⟨41749164289867356042079667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111331104772979616112212445 41749164289867356042079667)
                ·
                  refine ⟨62623746434801034063119501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41749164289867356042079667 62623746434801034063119501)
                  ·
                    refine ⟨23483904913050387773669813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62623746434801034063119501 23483904913050387773669813)
                    ·
                      refine ⟨2201616085598473853781545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23483904913050387773669813 2201616085598473853781545)
                      ·
                        rfl

theorem cell23_4287632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_4287632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287632 prefixEnd_4287632 := by exact prefixLift 4287632
  have htrace : WordTrace (prefixWord ++ tailWord_4287632) baseStart_4287632 baseEnd_4287632 := by
    simpa [prefixWord, tailWord_4287632, baseEnd_4287632] using wordTrace_append hprefix tailTrace_4287632
  have hstable : (prefixWord ++ tailWord_4287632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287632).length < 2 ^ (prefixWord ++ tailWord_4287632).sum := by decide
  have hdescent : baseEnd_4287632 < baseStart_4287632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287646 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4287646 : Nat := 118140960795 + 4287646 * 2 ^ 59
def prefixEnd_4287646 : Nat := 4983230072969 + 3 ^ 40 * 4287646 * 2
def baseEnd_4287646 : Nat := 2201623274327636799006481

theorem tailTrace_4287646 : CollatzResearch.WordTrace tailWord_4287646 prefixEnd_4287646 2201623274327636799006481 := by
  unfold tailWord_4287646
  simp only [CollatzResearch.WordTrace]
  refine ⟨19547912128074786060348349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104255531349732192321857861 19547912128074786060348349)
  ·
    refine ⟨7330467048028044772630631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19547912128074786060348349 7330467048028044772630631)
    ·
      refine ⟨10995700572042067158945947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330467048028044772630631 10995700572042067158945947)
      ·
        refine ⟨16493550858063100738418921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10995700572042067158945947 16493550858063100738418921)
        ·
          refine ⟨12370163143547325553814191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16493550858063100738418921 12370163143547325553814191)
          ·
            refine ⟨18555244715320988330721287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12370163143547325553814191 18555244715320988330721287)
            ·
              refine ⟨27832867072981482496081931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18555244715320988330721287 27832867072981482496081931)
              ·
                refine ⟨41749300609472223744122897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27832867072981482496081931 41749300609472223744122897)
                ·
                  refine ⟨31311975457104167808092173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41749300609472223744122897 31311975457104167808092173)
                  ·
                    refine ⟨11741990796414062928034565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31311975457104167808092173 11741990796414062928034565)
                    ·
                      refine ⟨2201623274327636799006481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11741990796414062928034565 2201623274327636799006481)
                      ·
                        rfl

theorem cell23_4287646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4287646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287646 prefixEnd_4287646 := by exact prefixLift 4287646
  have htrace : WordTrace (prefixWord ++ tailWord_4287646) baseStart_4287646 baseEnd_4287646 := by
    simpa [prefixWord, tailWord_4287646, baseEnd_4287646] using wordTrace_append hprefix tailTrace_4287646
  have hstable : (prefixWord ++ tailWord_4287646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287646).length < 2 ^ (prefixWord ++ tailWord_4287646).sum := by decide
  have hdescent : baseEnd_4287646 < baseStart_4287646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287649 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4287649 : Nat := 118140960795 + 4287649 * 2 ^ 59
def prefixEnd_4287649 : Nat := 4983230072969 + 3 ^ 40 * 4287649 * 2
def baseEnd_4287649 : Nat := 2201624814769600287268967

theorem tailTrace_4287649 : CollatzResearch.WordTrace tailWord_4287649 prefixEnd_4287649 2201624814769600287268967 := by
  unfold tailWord_4287649
  simp only [CollatzResearch.WordTrace]
  refine ⟨156383406443587419995146001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104255604295724946663430667 156383406443587419995146001)
  ·
    refine ⟨117287554832690564996359501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156383406443587419995146001 117287554832690564996359501)
    ·
      refine ⟨43982833062258961873634813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117287554832690564996359501 43982833062258961873634813)
      ·
        refine ⟨16493562398347110702613055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43982833062258961873634813 16493562398347110702613055)
        ·
          refine ⟨24740343597520666053919583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16493562398347110702613055 24740343597520666053919583)
          ·
            refine ⟨37110515396280999080879375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24740343597520666053919583 37110515396280999080879375)
            ·
              refine ⟨55665773094421498621319063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37110515396280999080879375 55665773094421498621319063)
              ·
                refine ⟨83498659641632247931978595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55665773094421498621319063 83498659641632247931978595)
                ·
                  refine ⟨125247989462448371897967893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83498659641632247931978595 125247989462448371897967893)
                  ·
                    refine ⟨5870999506052267432717245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125247989462448371897967893 5870999506052267432717245)
                    ·
                      refine ⟨2201624814769600287268967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5870999506052267432717245 2201624814769600287268967)
                      ·
                        rfl

theorem cell23_4287649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4287649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287649 prefixEnd_4287649 := by exact prefixLift 4287649
  have htrace : WordTrace (prefixWord ++ tailWord_4287649) baseStart_4287649 baseEnd_4287649 := by
    simpa [prefixWord, tailWord_4287649, baseEnd_4287649] using wordTrace_append hprefix tailTrace_4287649
  have hstable : (prefixWord ++ tailWord_4287649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287649).length < 2 ^ (prefixWord ++ tailWord_4287649).sum := by decide
  have hdescent : baseEnd_4287649 < baseStart_4287649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287663 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 2, 2, 2]
def baseStart_4287663 : Nat := 118140960795 + 4287663 * 2 ^ 59
def prefixEnd_4287663 : Nat := 4983230072969 + 3 ^ 40 * 4287663 * 2
def baseEnd_4287663 : Nat := 2201632003498763232493903

theorem tailTrace_4287663 : CollatzResearch.WordTrace tailWord_4287663 prefixEnd_4287663 2201632003498763232493903 := by
  unfold tailWord_4287663
  simp only [CollatzResearch.WordTrace]
  refine ⟨156383917065536700386155643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104255944710357800257437095 156383917065536700386155643)
  ·
    refine ⟨234575875598305050579233465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156383917065536700386155643 234575875598305050579233465)
    ·
      refine ⟨175931906698728787934425099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234575875598305050579233465 175931906698728787934425099)
      ·
        refine ⟨263897860048093181901637649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175931906698728787934425099 263897860048093181901637649)
        ·
          refine ⟨197923395036069886426228237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263897860048093181901637649 197923395036069886426228237)
          ·
            refine ⟨74221273138526207409835589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197923395036069886426228237 74221273138526207409835589)
            ·
              refine ⟨13916488713473663889344173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74221273138526207409835589 13916488713473663889344173)
              ·
                refine ⟨5218683267552623958504065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13916488713473663889344173 5218683267552623958504065)
                ·
                  refine ⟨3914012450664467968878049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5218683267552623958504065 3914012450664467968878049)
                  ·
                    refine ⟨2935509337998350976658537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3914012450664467968878049 2935509337998350976658537)
                    ·
                      refine ⟨2201632003498763232493903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935509337998350976658537 2201632003498763232493903)
                      ·
                        rfl

theorem cell23_4287663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2, 2].length) (baseStart_4287663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287663 prefixEnd_4287663 := by exact prefixLift 4287663
  have htrace : WordTrace (prefixWord ++ tailWord_4287663) baseStart_4287663 baseEnd_4287663 := by
    simpa [prefixWord, tailWord_4287663, baseEnd_4287663] using wordTrace_append hprefix tailTrace_4287663
  have hstable : (prefixWord ++ tailWord_4287663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287663).length < 2 ^ (prefixWord ++ tailWord_4287663).sum := by decide
  have hdescent : baseEnd_4287663 < baseStart_4287663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287684 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_4287684 : Nat := 118140960795 + 4287684 * 2 ^ 59
def prefixEnd_4287684 : Nat := 4983230072969 + 3 ^ 40 * 4287684 * 2
def baseEnd_4287684 : Nat := 2201642786592507650331307

theorem tailTrace_4287684 : CollatzResearch.WordTrace tailWord_4287684 prefixEnd_4287684 2201642786592507650331307 := by
  unfold tailWord_4287684
  simp only [CollatzResearch.WordTrace]
  refine ⟨78192341499230310486335053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104256455332307080648446737 78192341499230310486335053)
  ·
    refine ⟨29322128062211366432375645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78192341499230310486335053 29322128062211366432375645)
    ·
      refine ⟨10995798023329262412140867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29322128062211366432375645 10995798023329262412140867)
      ·
        refine ⟨16493697034993893618211301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10995798023329262412140867 16493697034993893618211301)
        ·
          refine ⟨3092568194061355053414619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16493697034993893618211301 3092568194061355053414619)
          ·
            refine ⟨4638852291092032580121929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092568194061355053414619 4638852291092032580121929)
            ·
              refine ⟨3479139218319024435091447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638852291092032580121929 3479139218319024435091447)
              ·
                refine ⟨5218708827478536652637171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479139218319024435091447 5218708827478536652637171)
                ·
                  refine ⟨7828063241217804978955757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218708827478536652637171 7828063241217804978955757)
                  ·
                    refine ⟨2935523715456676867108409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7828063241217804978955757 2935523715456676867108409)
                    ·
                      refine ⟨2201642786592507650331307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935523715456676867108409 2201642786592507650331307)
                      ·
                        rfl

theorem cell23_4287684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_4287684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287684 prefixEnd_4287684 := by exact prefixLift 4287684
  have htrace : WordTrace (prefixWord ++ tailWord_4287684) baseStart_4287684 baseEnd_4287684 := by
    simpa [prefixWord, tailWord_4287684, baseEnd_4287684] using wordTrace_append hprefix tailTrace_4287684
  have hstable : (prefixWord ++ tailWord_4287684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287684).length < 2 ^ (prefixWord ++ tailWord_4287684).sum := by decide
  have hdescent : baseEnd_4287684 < baseStart_4287684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287756 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_4287756 : Nat := 118140960795 + 4287756 * 2 ^ 59
def prefixEnd_4287756 : Nat := 4983230072969 + 3 ^ 40 * 4287756 * 2
def baseEnd_4287756 : Nat := 2201679757199631368630975

theorem tailTrace_4287756 : CollatzResearch.WordTrace tailWord_4287756 prefixEnd_4287756 2201679757199631368630975 := by
  unfold tailWord_4287756
  simp only [CollatzResearch.WordTrace]
  refine ⟨78193654527099888634645561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104258206036133184846194081 78193654527099888634645561)
  ·
    refine ⟨58645240895324916475984171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78193654527099888634645561 58645240895324916475984171)
    ·
      refine ⟨87967861342987374713976257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58645240895324916475984171 87967861342987374713976257)
      ·
        refine ⟨65975896007240531035482193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87967861342987374713976257 65975896007240531035482193)
        ·
          refine ⟨49481922005430398276611645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65975896007240531035482193 49481922005430398276611645)
          ·
            refine ⟨18555720752036399353729367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49481922005430398276611645 18555720752036399353729367)
            ·
              refine ⟨27833581128054599030594051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18555720752036399353729367 27833581128054599030594051)
              ·
                refine ⟨41750371692081898545891077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27833581128054599030594051 41750371692081898545891077)
                ·
                  refine ⟨7828194692265355977354577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41750371692081898545891077 7828194692265355977354577)
                  ·
                    refine ⟨5871146019199016983015933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7828194692265355977354577 5871146019199016983015933)
                    ·
                      refine ⟨2201679757199631368630975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871146019199016983015933 2201679757199631368630975)
                      ·
                        rfl

theorem cell23_4287756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_4287756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287756 prefixEnd_4287756 := by exact prefixLift 4287756
  have htrace : WordTrace (prefixWord ++ tailWord_4287756) baseStart_4287756 baseEnd_4287756 := by
    simpa [prefixWord, tailWord_4287756, baseEnd_4287756] using wordTrace_append hprefix tailTrace_4287756
  have hstable : (prefixWord ++ tailWord_4287756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287756).length < 2 ^ (prefixWord ++ tailWord_4287756).sum := by decide
  have hdescent : baseEnd_4287756 < baseStart_4287756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287847 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_4287847 : Nat := 118140960795 + 4287847 * 2 ^ 59
def prefixEnd_4287847 : Nat := 4983230072969 + 3 ^ 40 * 4287847 * 2
def baseEnd_4287847 : Nat := 2201726483939190512593057

theorem tailTrace_4287847 : CollatzResearch.WordTrace tailWord_4287847 prefixEnd_4287847 2201726483939190512593057 := by
  unfold tailWord_4287847
  simp only [CollatzResearch.WordTrace]
  refine ⟨156390628096870099810853795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104260418731246733207235863 156390628096870099810853795)
  ·
    refine ⟨234585942145305149716280693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156390628096870099810853795 234585942145305149716280693)
    ·
      refine ⟨21992432076122357785901315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 234585942145305149716280693 21992432076122357785901315)
      ·
        refine ⟨32988648114183536678851973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21992432076122357785901315 32988648114183536678851973)
        ·
          refine ⟨6185371521409413127284745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32988648114183536678851973 6185371521409413127284745)
          ·
            refine ⟨4639028641057059845463559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6185371521409413127284745 4639028641057059845463559)
            ·
              refine ⟨6958542961585589768195339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639028641057059845463559 6958542961585589768195339)
              ·
                refine ⟨10437814442378384652293009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6958542961585589768195339 10437814442378384652293009)
                ·
                  refine ⟨7828360831783788489219757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10437814442378384652293009 7828360831783788489219757)
                  ·
                    refine ⟨2935635311918920683457409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7828360831783788489219757 2935635311918920683457409)
                    ·
                      refine ⟨2201726483939190512593057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935635311918920683457409 2201726483939190512593057)
                      ·
                        rfl

theorem cell23_4287847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_4287847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287847 prefixEnd_4287847 := by exact prefixLift 4287847
  have htrace : WordTrace (prefixWord ++ tailWord_4287847) baseStart_4287847 baseEnd_4287847 := by
    simpa [prefixWord, tailWord_4287847, baseEnd_4287847] using wordTrace_append hprefix tailTrace_4287847
  have hstable : (prefixWord ++ tailWord_4287847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287847).length < 2 ^ (prefixWord ++ tailWord_4287847).sum := by decide
  have hdescent : baseEnd_4287847 < baseStart_4287847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287856 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_4287856 : Nat := 118140960795 + 4287856 * 2 ^ 59
def prefixEnd_4287856 : Nat := 4983230072969 + 3 ^ 40 * 4287856 * 2
def baseEnd_4287856 : Nat := 2201731105265080977380515

theorem tailTrace_4287856 : CollatzResearch.WordTrace tailWord_4287856 prefixEnd_4287856 2201731105265080977380515 := by
  unfold tailWord_4287856
  simp only [CollatzResearch.WordTrace]
  refine ⟨78195478176918747173965711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104260637569224996231954281 78195478176918747173965711)
  ·
    refine ⟨117293217265378120760948567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78195478176918747173965711 117293217265378120760948567)
    ·
      refine ⟨175939825898067181141422851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117293217265378120760948567 175939825898067181141422851)
      ·
        refine ⟨263909738847100771712134277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175939825898067181141422851 263909738847100771712134277)
        ·
          refine ⟨49483076033831394696025177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263909738847100771712134277 49483076033831394696025177)
          ·
            refine ⟨37112307025373546022018883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49483076033831394696025177 37112307025373546022018883)
            ·
              refine ⟨55668460538060319033028325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37112307025373546022018883 55668460538060319033028325)
              ·
                refine ⟨10437836350886309818692811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55668460538060319033028325 10437836350886309818692811)
                ·
                  refine ⟨15656754526329464728039217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10437836350886309818692811 15656754526329464728039217)
                  ·
                    refine ⟨11742565894747098546029413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15656754526329464728039217 11742565894747098546029413)
                    ·
                      refine ⟨2201731105265080977380515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11742565894747098546029413 2201731105265080977380515)
                      ·
                        rfl

theorem cell23_4287856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_4287856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287856 prefixEnd_4287856 := by exact prefixLift 4287856
  have htrace : WordTrace (prefixWord ++ tailWord_4287856) baseStart_4287856 baseEnd_4287856 := by
    simpa [prefixWord, tailWord_4287856, baseEnd_4287856] using wordTrace_append hprefix tailTrace_4287856
  have hstable : (prefixWord ++ tailWord_4287856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287856).length < 2 ^ (prefixWord ++ tailWord_4287856).sum := by decide
  have hdescent : baseEnd_4287856 < baseStart_4287856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287863 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_4287863 : Nat := 118140960795 + 4287863 * 2 ^ 59
def prefixEnd_4287863 : Nat := 4983230072969 + 3 ^ 40 * 4287863 * 2
def baseEnd_4287863 : Nat := 2201734699629662449992983

theorem tailTrace_4287863 : CollatzResearch.WordTrace tailWord_4287863 prefixEnd_4287863 2201734699629662449992983 := by
  unfold tailWord_4287863
  simp only [CollatzResearch.WordTrace]
  refine ⟨156391211664812134543436243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104260807776541423028957495 156391211664812134543436243)
  ·
    refine ⟨234586817497218201815154365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156391211664812134543436243 234586817497218201815154365)
    ·
      refine ⟨87970056561456825680682887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234586817497218201815154365 87970056561456825680682887)
      ·
        refine ⟨131955084842185238521024331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87970056561456825680682887 131955084842185238521024331)
        ·
          refine ⟨197932627263277857781536497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131955084842185238521024331 197932627263277857781536497)
          ·
            refine ⟨148449470447458393336152373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197932627263277857781536497 148449470447458393336152373)
            ·
              refine ⟨13917137854449224375264285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148449470447458393336152373 13917137854449224375264285)
              ·
                refine ⟨5218926695418459140724107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13917137854449224375264285 5218926695418459140724107)
                ·
                  refine ⟨7828390043127688711086161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218926695418459140724107 7828390043127688711086161)
                  ·
                    refine ⟨5871292532345766533314621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7828390043127688711086161 5871292532345766533314621)
                    ·
                      refine ⟨2201734699629662449992983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871292532345766533314621 2201734699629662449992983)
                      ·
                        rfl

theorem cell23_4287863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_4287863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287863 prefixEnd_4287863 := by exact prefixLift 4287863
  have htrace : WordTrace (prefixWord ++ tailWord_4287863) baseStart_4287863 baseEnd_4287863 := by
    simpa [prefixWord, tailWord_4287863, baseEnd_4287863] using wordTrace_append hprefix tailTrace_4287863
  have hstable : (prefixWord ++ tailWord_4287863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287863).length < 2 ^ (prefixWord ++ tailWord_4287863).sum := by decide
  have hdescent : baseEnd_4287863 < baseStart_4287863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287877 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 1, 2, 2]
def baseStart_4287877 : Nat := 118140960795 + 4287877 * 2 ^ 59
def prefixEnd_4287877 : Nat := 4983230072969 + 3 ^ 40 * 4287877 * 2
def baseEnd_4287877 : Nat := 2201741888358825395217919

theorem tailTrace_4287877 : CollatzResearch.WordTrace tailWord_4287877 prefixEnd_4287877 2201741888358825395217919 := by
  unfold tailWord_4287877
  simp only [CollatzResearch.WordTrace]
  refine ⟨156391722286761414934445885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104261148191174276622963923 156391722286761414934445885)
  ·
    refine ⟨58646895857535530600417207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156391722286761414934445885 58646895857535530600417207)
    ·
      refine ⟨87970343786303295900625811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58646895857535530600417207 87970343786303295900625811)
      ·
        refine ⟨131955515679454943850938717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87970343786303295900625811 131955515679454943850938717)
        ·
          refine ⟨49483318379795603944102019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131955515679454943850938717 49483318379795603944102019)
          ·
            refine ⟨74224977569693405916153029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49483318379795603944102019 74224977569693405916153029)
            ·
              refine ⟨13917183294317513609278693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74224977569693405916153029 13917183294317513609278693)
              ·
                refine ⟨2609471867684533801739755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13917183294317513609278693 2609471867684533801739755)
                ·
                  refine ⟨3914207801526800702609633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609471867684533801739755 3914207801526800702609633)
                  ·
                    refine ⟨2935655851145100526957225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3914207801526800702609633 2935655851145100526957225)
                    ·
                      refine ⟨2201741888358825395217919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935655851145100526957225 2201741888358825395217919)
                      ·
                        rfl

theorem cell23_4287877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_4287877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287877 prefixEnd_4287877 := by exact prefixLift 4287877
  have htrace : WordTrace (prefixWord ++ tailWord_4287877) baseStart_4287877 baseEnd_4287877 := by
    simpa [prefixWord, tailWord_4287877, baseEnd_4287877] using wordTrace_append hprefix tailTrace_4287877
  have hstable : (prefixWord ++ tailWord_4287877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287877).length < 2 ^ (prefixWord ++ tailWord_4287877).sum := by decide
  have hdescent : baseEnd_4287877 < baseStart_4287877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287890 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4287890 : Nat := 118140960795 + 4287890 * 2 ^ 59
def prefixEnd_4287890 : Nat := 4983230072969 + 3 ^ 40 * 4287890 * 2
def baseEnd_4287890 : Nat := 2201748563607333844355359

theorem tailTrace_4287890 : CollatzResearch.WordTrace tailWord_4287890 prefixEnd_4287890 2201748563607333844355359 := by
  unfold tailWord_4287890
  simp only [CollatzResearch.WordTrace]
  refine ⟨39098049108928579538667281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104261464290476212103112749 39098049108928579538667281)
  ·
    refine ⟨29323536831696434654000461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39098049108928579538667281 29323536831696434654000461)
    ·
      refine ⟨10996326311886162995250173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29323536831696434654000461 10996326311886162995250173)
      ·
        refine ⟨4123622366957311123218815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10996326311886162995250173 4123622366957311123218815)
        ·
          refine ⟨6185433550435966684828223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4123622366957311123218815 6185433550435966684828223)
          ·
            refine ⟨9278150325653950027242335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6185433550435966684828223 9278150325653950027242335)
            ·
              refine ⟨13917225488480925040863503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9278150325653950027242335 13917225488480925040863503)
              ·
                refine ⟨20875838232721387561295255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13917225488480925040863503 20875838232721387561295255)
                ·
                  refine ⟨31313757349082081341942883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20875838232721387561295255 31313757349082081341942883)
                  ·
                    refine ⟨46970636023623122012914325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31313757349082081341942883 46970636023623122012914325)
                    ·
                      refine ⟨2201748563607333844355359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46970636023623122012914325 2201748563607333844355359)
                      ·
                        rfl

theorem cell23_4287890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4287890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287890 prefixEnd_4287890 := by exact prefixLift 4287890
  have htrace : WordTrace (prefixWord ++ tailWord_4287890) baseStart_4287890 baseEnd_4287890 := by
    simpa [prefixWord, tailWord_4287890, baseEnd_4287890] using wordTrace_append hprefix tailTrace_4287890
  have hstable : (prefixWord ++ tailWord_4287890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287890).length < 2 ^ (prefixWord ++ tailWord_4287890).sum := by decide
  have hdescent : baseEnd_4287890 < baseStart_4287890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4287893 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_4287893 : Nat := 118140960795 + 4287893 * 2 ^ 59
def prefixEnd_4287893 : Nat := 4983230072969 + 3 ^ 40 * 4287893 * 2
def baseEnd_4287893 : Nat := 2201750104049297332617845

theorem tailTrace_4287893 : CollatzResearch.WordTrace tailWord_4287893 prefixEnd_4287893 2201750104049297332617845 := by
  unfold tailWord_4287893
  simp only [CollatzResearch.WordTrace]
  refine ⟨156392305854703449667028333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104261537236468966444685555 156392305854703449667028333)
  ·
    refine ⟨58647114695513793625135625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156392305854703449667028333 58647114695513793625135625)
    ·
      refine ⟨43985336021635345218851719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58647114695513793625135625 43985336021635345218851719)
      ·
        refine ⟨65978004032453017828277579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43985336021635345218851719 65978004032453017828277579)
        ·
          refine ⟨98967006048679526742416369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65978004032453017828277579 98967006048679526742416369)
          ·
            refine ⟨74225254536509645056812277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98967006048679526742416369 74225254536509645056812277)
            ·
              refine ⟨6958617612797779224076151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74225254536509645056812277 6958617612797779224076151)
              ·
                refine ⟨10437926419196668836114227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6958617612797779224076151 10437926419196668836114227)
                ·
                  refine ⟨15656889628795003254171341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10437926419196668836114227 15656889628795003254171341)
                  ·
                    refine ⟨5871333610798126220314253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15656889628795003254171341 5871333610798126220314253)
                    ·
                      refine ⟨2201750104049297332617845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871333610798126220314253 2201750104049297332617845)
                      ·
                        rfl

theorem cell23_4287893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_4287893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4287893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4287893 prefixEnd_4287893 := by exact prefixLift 4287893
  have htrace : WordTrace (prefixWord ++ tailWord_4287893) baseStart_4287893 baseEnd_4287893 := by
    simpa [prefixWord, tailWord_4287893, baseEnd_4287893] using wordTrace_append hprefix tailTrace_4287893
  have hstable : (prefixWord ++ tailWord_4287893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4287893).length < 2 ^ (prefixWord ++ tailWord_4287893).sum := by decide
  have hdescent : baseEnd_4287893 < baseStart_4287893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4287893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288090 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_4288090 : Nat := 118140960795 + 4288090 * 2 ^ 59
def prefixEnd_4288090 : Nat := 4983230072969 + 3 ^ 40 * 4288090 * 2
def baseEnd_4288090 : Nat := 2201851259738233061854439

theorem tailTrace_4288090 : CollatzResearch.WordTrace tailWord_4288090 prefixEnd_4288090 2201851259738233061854439 := by
  unfold tailWord_4288090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39099872758747438077987431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104266327356659834874633149 39099872758747438077987431)
  ·
    refine ⟨58649809138121157116981147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39099872758747438077987431 58649809138121157116981147)
    ·
      refine ⟨87974713707181735675471721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58649809138121157116981147 87974713707181735675471721)
      ·
        refine ⟨65981035280386301756603791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87974713707181735675471721 65981035280386301756603791)
        ·
          refine ⟨98971552920579452634905687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65981035280386301756603791 98971552920579452634905687)
          ·
            refine ⟨148457329380869178952358531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98971552920579452634905687 148457329380869178952358531)
            ·
              refine ⟨222685994071303768428537797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148457329380869178952358531 222685994071303768428537797)
              ·
                refine ⟨41753623888369456580350837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222685994071303768428537797 41753623888369456580350837)
                ·
                  refine ⟨3914402239534636554407891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41753623888369456580350837 3914402239534636554407891)
                  ·
                    refine ⟨5871603359301954831611837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3914402239534636554407891 5871603359301954831611837)
                    ·
                      refine ⟨2201851259738233061854439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871603359301954831611837 2201851259738233061854439)
                      ·
                        rfl

theorem cell23_4288090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_4288090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288090 prefixEnd_4288090 := by exact prefixLift 4288090
  have htrace : WordTrace (prefixWord ++ tailWord_4288090) baseStart_4288090 baseEnd_4288090 := by
    simpa [prefixWord, tailWord_4288090, baseEnd_4288090] using wordTrace_append hprefix tailTrace_4288090
  have hstable : (prefixWord ++ tailWord_4288090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288090).length < 2 ^ (prefixWord ++ tailWord_4288090).sum := by decide
  have hdescent : baseEnd_4288090 < baseStart_4288090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288123 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 1, 6]
def baseStart_4288123 : Nat := 118140960795 + 4288123 * 2 ^ 59
def prefixEnd_4288123 : Nat := 4983230072969 + 3 ^ 40 * 4288123 * 2
def baseEnd_4288123 : Nat := 733956068199943810913929

theorem tailTrace_4288123 : CollatzResearch.WordTrace tailWord_4288123 prefixEnd_4288123 733956068199943810913929 := by
  unfold tailWord_4288123
  simp only [CollatzResearch.WordTrace]
  refine ⟨156400694643870198947901023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104267129762580132631934015 156400694643870198947901023)
  ·
    refine ⟨234601041965805298421851535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156400694643870198947901023 234601041965805298421851535)
    ·
      refine ⟨351901562948707947632777303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234601041965805298421851535 351901562948707947632777303)
      ·
        refine ⟨527852344423061921449165955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351901562948707947632777303 527852344423061921449165955)
        ·
          refine ⟨791778516634592882173748933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527852344423061921449165955 791778516634592882173748933)
          ·
            refine ⟨148458471868986165407577925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 791778516634592882173748933 148458471868986165407577925)
            ·
              refine ⟨27835963475434906013920861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148458471868986165407577925 27835963475434906013920861)
              ·
                refine ⟨10438486303288089755220323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27835963475434906013920861 10438486303288089755220323)
                ·
                  refine ⟨15657729454932134632830485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10438486303288089755220323 15657729454932134632830485)
                  ·
                    refine ⟨733956068199943810913929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15657729454932134632830485 733956068199943810913929)
                    ·
                      rfl

theorem cell23_4288123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 6].length) (baseStart_4288123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288123 prefixEnd_4288123 := by exact prefixLift 4288123
  have htrace : WordTrace (prefixWord ++ tailWord_4288123) baseStart_4288123 baseEnd_4288123 := by
    simpa [prefixWord, tailWord_4288123, baseEnd_4288123] using wordTrace_append hprefix tailTrace_4288123
  have hstable : (prefixWord ++ tailWord_4288123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288123).length < 2 ^ (prefixWord ++ tailWord_4288123).sum := by decide
  have hdescent : baseEnd_4288123 < baseStart_4288123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288158 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_4288158 : Nat := 118140960795 + 4288158 * 2 ^ 59
def prefixEnd_4288158 : Nat := 4983230072969 + 3 ^ 40 * 4288158 * 2
def baseEnd_4288158 : Nat := 2201886176422738795804127

theorem tailTrace_4288158 : CollatzResearch.WordTrace tailWord_4288158 prefixEnd_4288158 2201886176422738795804127 := by
  unfold tailWord_4288158
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550246399842924990678141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104267980799162266616950085 19550246399842924990678141)
  ·
    refine ⟨7331342399941096871504303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19550246399842924990678141 7331342399941096871504303)
    ·
      refine ⟨10997013599911645307256455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7331342399941096871504303 10997013599911645307256455)
      ·
        refine ⟨16495520399867467960884683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10997013599911645307256455 16495520399867467960884683)
        ·
          refine ⟨24743280599801201941327025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16495520399867467960884683 24743280599801201941327025)
          ·
            refine ⟨18557460449850901455995269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24743280599801201941327025 18557460449850901455995269)
            ·
              refine ⟨3479523834347044022999113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18557460449850901455995269 3479523834347044022999113)
              ·
                refine ⟨2609642875760283017249335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479523834347044022999113 2609642875760283017249335)
                ·
                  refine ⟨3914464313640424525874003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609642875760283017249335 3914464313640424525874003)
                  ·
                    refine ⟨5871696470460636788811005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3914464313640424525874003 5871696470460636788811005)
                    ·
                      refine ⟨2201886176422738795804127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871696470460636788811005 2201886176422738795804127)
                      ·
                        rfl

theorem cell23_4288158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_4288158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288158 prefixEnd_4288158 := by exact prefixLift 4288158
  have htrace : WordTrace (prefixWord ++ tailWord_4288158) baseStart_4288158 baseEnd_4288158 := by
    simpa [prefixWord, tailWord_4288158, baseEnd_4288158] using wordTrace_append hprefix tailTrace_4288158
  have hstable : (prefixWord ++ tailWord_4288158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288158).length < 2 ^ (prefixWord ++ tailWord_4288158).sum := by decide
  have hdescent : baseEnd_4288158 < baseStart_4288158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288174 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4288174 : Nat := 118140960795 + 4288174 * 2 ^ 59
def prefixEnd_4288174 : Nat := 4983230072969 + 3 ^ 40 * 4288174 * 2
def baseEnd_4288174 : Nat := 733964797371070244401351

theorem tailTrace_4288174 : CollatzResearch.WordTrace tailWord_4288174 prefixEnd_4288174 733964797371070244401351 := by
  unfold tailWord_4288174
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550319345835679332250947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104268369844456956438671717 19550319345835679332250947)
  ·
    refine ⟨29325479018753518998376421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19550319345835679332250947 29325479018753518998376421)
    ·
      refine ⟨5498527316016284812195579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29325479018753518998376421 5498527316016284812195579)
      ·
        refine ⟨8247790974024427218293369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498527316016284812195579 8247790974024427218293369)
        ·
          refine ⟨6185843230518320413720027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8247790974024427218293369 6185843230518320413720027)
          ·
            refine ⟨9278764845777480620580041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6185843230518320413720027 9278764845777480620580041)
            ·
              refine ⟨6959073634333110465435031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9278764845777480620580041 6959073634333110465435031)
              ·
                refine ⟨10438610451499665698152547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959073634333110465435031 10438610451499665698152547)
                ·
                  refine ⟨15657915677249498547228821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10438610451499665698152547 15657915677249498547228821)
                  ·
                    refine ⟨733964797371070244401351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15657915677249498547228821 733964797371070244401351)
                    ·
                      rfl

theorem cell23_4288174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4288174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288174 prefixEnd_4288174 := by exact prefixLift 4288174
  have htrace : WordTrace (prefixWord ++ tailWord_4288174) baseStart_4288174 baseEnd_4288174 := by
    simpa [prefixWord, tailWord_4288174, baseEnd_4288174] using wordTrace_append hprefix tailTrace_4288174
  have hstable : (prefixWord ++ tailWord_4288174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288174).length < 2 ^ (prefixWord ++ tailWord_4288174).sum := by decide
  have hdescent : baseEnd_4288174 < baseStart_4288174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288181 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4288181 : Nat := 118140960795 + 4288181 * 2 ^ 59
def prefixEnd_4288181 : Nat := 4983230072969 + 3 ^ 40 * 4288181 * 2
def baseEnd_4288181 : Nat := 2201897986477792205816521

theorem tailTrace_4288181 : CollatzResearch.WordTrace tailWord_4288181 prefixEnd_4288181 2201897986477792205816521 := by
  unfold tailWord_4288181
  simp only [CollatzResearch.WordTrace]
  refine ⟨156402810077660074853512397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104268540051773383235674931 156402810077660074853512397)
  ·
    refine ⟨58651053779122528070067149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156402810077660074853512397 58651053779122528070067149)
    ·
      refine ⟨21994145167170948026275181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58651053779122528070067149 21994145167170948026275181)
      ·
        refine ⟨8247804437689105509853193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21994145167170948026275181 8247804437689105509853193)
        ·
          refine ⟨6185853328266829132389895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8247804437689105509853193 6185853328266829132389895)
          ·
            refine ⟨9278779992400243698584843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6185853328266829132389895 9278779992400243698584843)
            ·
              refine ⟨13918169988600365547877265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9278779992400243698584843 13918169988600365547877265)
              ·
                refine ⟨10438627491450274160907949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13918169988600365547877265 10438627491450274160907949)
                ·
                  refine ⟨3914485309293852810340481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10438627491450274160907949 3914485309293852810340481)
                  ·
                    refine ⟨2935863981970389607755361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3914485309293852810340481 2935863981970389607755361)
                    ·
                      refine ⟨2201897986477792205816521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2935863981970389607755361 2201897986477792205816521)
                      ·
                        rfl

theorem cell23_4288181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4288181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288181 prefixEnd_4288181 := by exact prefixLift 4288181
  have htrace : WordTrace (prefixWord ++ tailWord_4288181) baseStart_4288181 baseEnd_4288181 := by
    simpa [prefixWord, tailWord_4288181, baseEnd_4288181] using wordTrace_append hprefix tailTrace_4288181
  have hstable : (prefixWord ++ tailWord_4288181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288181).length < 2 ^ (prefixWord ++ tailWord_4288181).sum := by decide
  have hdescent : baseEnd_4288181 < baseStart_4288181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288198 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4288198 : Nat := 118140960795 + 4288198 * 2 ^ 59
def prefixEnd_4288198 : Nat := 4983230072969 + 3 ^ 40 * 4288198 * 2
def baseEnd_4288198 : Nat := 2201906715648918639303943

theorem tailTrace_4288198 : CollatzResearch.WordTrace tailWord_4288198 prefixEnd_4288198 2201906715648918639303943 := by
  unfold tailWord_4288198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887607191206202711152539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104268953412398991171254165 4887607191206202711152539)
  ·
    refine ⟨7331410786809304066728809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4887607191206202711152539 7331410786809304066728809)
    ·
      refine ⟨5498558090106978050046607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7331410786809304066728809 5498558090106978050046607)
      ·
        refine ⟨8247837135160467075069911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498558090106978050046607 8247837135160467075069911)
        ·
          refine ⟨12371755702740700612604867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8247837135160467075069911 12371755702740700612604867)
          ·
            refine ⟨18557633554111050918907301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12371755702740700612604867 18557633554111050918907301)
            ·
              refine ⟨3479556291395822047295119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18557633554111050918907301 3479556291395822047295119)
              ·
                refine ⟨5219334437093733070942679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479556291395822047295119 5219334437093733070942679)
                ·
                  refine ⟨7829001655640599606414019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5219334437093733070942679 7829001655640599606414019)
                  ·
                    refine ⟨11743502483460899409621029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7829001655640599606414019 11743502483460899409621029)
                    ·
                      refine ⟨2201906715648918639303943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11743502483460899409621029 2201906715648918639303943)
                      ·
                        rfl

theorem cell23_4288198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4288198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288198 prefixEnd_4288198 := by exact prefixLift 4288198
  have htrace : WordTrace (prefixWord ++ tailWord_4288198) baseStart_4288198 baseEnd_4288198 := by
    simpa [prefixWord, tailWord_4288198, baseEnd_4288198] using wordTrace_append hprefix tailTrace_4288198
  have hstable : (prefixWord ++ tailWord_4288198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288198).length < 2 ^ (prefixWord ++ tailWord_4288198).sum := by decide
  have hdescent : baseEnd_4288198 < baseStart_4288198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288231 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4288231 : Nat := 118140960795 + 4288231 * 2 ^ 59
def prefixEnd_4288231 : Nat := 4983230072969 + 3 ^ 40 * 4288231 * 2
def baseEnd_4288231 : Nat := 2201923660510517010191291

theorem tailTrace_4288231 : CollatzResearch.WordTrace tailWord_4288231 prefixEnd_4288231 2201923660510517010191291 := by
  unfold tailWord_4288231
  simp only [CollatzResearch.WordTrace]
  refine ⟨156404633727478933392832547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104269755818319288928555031 156404633727478933392832547)
  ·
    refine ⟨234606950591218400089248821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156404633727478933392832547 234606950591218400089248821)
    ·
      refine ⟨21994401617926725008367077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 234606950591218400089248821 21994401617926725008367077)
      ·
        refine ⟨4123950303361260939068827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21994401617926725008367077 4123950303361260939068827)
        ·
          refine ⟨6185925455041891408603241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4123950303361260939068827 6185925455041891408603241)
          ·
            refine ⟨4639444091281418556452431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6185925455041891408603241 4639444091281418556452431)
            ·
              refine ⟨6959166136922127834678647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639444091281418556452431 6959166136922127834678647)
              ·
                refine ⟨10438749205383191752017971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959166136922127834678647 10438749205383191752017971)
                ·
                  refine ⟨15658123808074787628026957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10438749205383191752017971 15658123808074787628026957)
                  ·
                    refine ⟨5871796428028045360510109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15658123808074787628026957 5871796428028045360510109)
                    ·
                      refine ⟨2201923660510517010191291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871796428028045360510109 2201923660510517010191291)
                      ·
                        rfl

theorem cell23_4288231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4288231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288231 prefixEnd_4288231 := by exact prefixLift 4288231
  have htrace : WordTrace (prefixWord ++ tailWord_4288231) baseStart_4288231 baseEnd_4288231 := by
    simpa [prefixWord, tailWord_4288231, baseEnd_4288231] using wordTrace_append hprefix tailTrace_4288231
  have hstable : (prefixWord ++ tailWord_4288231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288231).length < 2 ^ (prefixWord ++ tailWord_4288231).sum := by decide
  have hdescent : baseEnd_4288231 < baseStart_4288231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288244 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4288244 : Nat := 118140960795 + 4288244 * 2 ^ 59
def prefixEnd_4288244 : Nat := 4983230072969 + 3 ^ 40 * 4288244 * 2
def baseEnd_4288244 : Nat := 2201930335759025459328731

theorem tailTrace_4288244 : CollatzResearch.WordTrace tailWord_4288244 prefixEnd_4288244 2201930335759025459328731 := by
  unfold tailWord_4288244
  simp only [CollatzResearch.WordTrace]
  refine ⟨78202553938215918306527893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104270071917621224408703857 78202553938215918306527893)
  ·
    refine ⟨3665744715853871170618495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78202553938215918306527893 3665744715853871170618495)
    ·
      refine ⟨5498617073780806755927743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665744715853871170618495 5498617073780806755927743)
      ·
        refine ⟨8247925610671210133891615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498617073780806755927743 8247925610671210133891615)
        ·
          refine ⟨12371888416006815200837423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8247925610671210133891615 12371888416006815200837423)
          ·
            refine ⟨18557832624010222801256135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12371888416006815200837423 18557832624010222801256135)
            ·
              refine ⟨27836748936015334201884203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18557832624010222801256135 27836748936015334201884203)
              ·
                refine ⟨41755123404023001302826305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27836748936015334201884203 41755123404023001302826305)
                ·
                  refine ⟨31316342553017250977119729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41755123404023001302826305 31316342553017250977119729)
                  ·
                    refine ⟨23487256914762938232839797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31316342553017250977119729 23487256914762938232839797)
                    ·
                      refine ⟨2201930335759025459328731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23487256914762938232839797 2201930335759025459328731)
                      ·
                        rfl

theorem cell23_4288244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4288244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288244 prefixEnd_4288244 := by exact prefixLift 4288244
  have htrace : WordTrace (prefixWord ++ tailWord_4288244) baseStart_4288244 baseEnd_4288244 := by
    simpa [prefixWord, tailWord_4288244, baseEnd_4288244] using wordTrace_append hprefix tailTrace_4288244
  have hstable : (prefixWord ++ tailWord_4288244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288244).length < 2 ^ (prefixWord ++ tailWord_4288244).sum := by decide
  have hdescent : baseEnd_4288244 < baseStart_4288244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288277 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 7]
def baseStart_4288277 : Nat := 118140960795 + 4288277 * 2 ^ 59
def prefixEnd_4288277 : Nat := 4983230072969 + 3 ^ 40 * 4288277 * 2
def baseEnd_4288277 : Nat := 244660808957847092246231

theorem tailTrace_4288277 : CollatzResearch.WordTrace tailWord_4288277 prefixEnd_4288277 244660808957847092246231 := by
  unfold tailWord_4288277
  simp only [CollatzResearch.WordTrace]
  refine ⟨156406311485312283249007085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104270874323541522166004723 156406311485312283249007085)
  ·
    refine ⟨58652366806992106218377657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156406311485312283249007085 58652366806992106218377657)
    ·
      refine ⟨43989275105244079663783243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58652366806992106218377657 43989275105244079663783243)
      ·
        refine ⟨65983912657866119495674865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43989275105244079663783243 65983912657866119495674865)
        ·
          refine ⟨49487934493399589621756149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65983912657866119495674865 49487934493399589621756149)
          ·
            refine ⟨4639493858756211527039639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49487934493399589621756149 4639493858756211527039639)
            ·
              refine ⟨6959240788134317290559459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639493858756211527039639 6959240788134317290559459)
              ·
                refine ⟨10438861182201475935839189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959240788134317290559459 10438861182201475935839189)
                ·
                  refine ⟨244660808957847092246231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10438861182201475935839189 244660808957847092246231)
                  ·
                    rfl

theorem cell23_4288277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_4288277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288277 prefixEnd_4288277 := by exact prefixLift 4288277
  have htrace : WordTrace (prefixWord ++ tailWord_4288277) baseStart_4288277 baseEnd_4288277 := by
    simpa [prefixWord, tailWord_4288277, baseEnd_4288277] using wordTrace_append hprefix tailTrace_4288277
  have hstable : (prefixWord ++ tailWord_4288277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288277).length < 2 ^ (prefixWord ++ tailWord_4288277).sum := by decide
  have hdescent : baseEnd_4288277 < baseStart_4288277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288317 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4288317 : Nat := 118140960795 + 4288317 * 2 ^ 59
def prefixEnd_4288317 : Nat := 4983230072969 + 3 ^ 40 * 4288317 * 2
def baseEnd_4288317 : Nat := 2201967819846803673715895

theorem tailTrace_4288317 : CollatzResearch.WordTrace tailWord_4288317 prefixEnd_4288317 2201967819846803673715895 := by
  unfold tailWord_4288317
  simp only [CollatzResearch.WordTrace]
  refine ⟨156407770405167370080463205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104271846936778246720308803 156407770405167370080463205)
  ·
    refine ⟨29326456950968881890086851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156407770405167370080463205 29326456950968881890086851)
    ·
      refine ⟨43989685426453322835130277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29326456950968881890086851 43989685426453322835130277)
      ·
        refine ⟨8248066017459998031586927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43989685426453322835130277 8248066017459998031586927)
        ·
          refine ⟨12372099026189997047380391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248066017459998031586927 12372099026189997047380391)
          ·
            refine ⟨18558148539284995571070587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12372099026189997047380391 18558148539284995571070587)
            ·
              refine ⟨27837222808927493356605881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18558148539284995571070587 27837222808927493356605881)
              ·
                refine ⟨20877917106695620017454411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27837222808927493356605881 20877917106695620017454411)
                ·
                  refine ⟨31316875660043430026181617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20877917106695620017454411 31316875660043430026181617)
                  ·
                    refine ⟨23487656745032572519636213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31316875660043430026181617 23487656745032572519636213)
                    ·
                      refine ⟨2201967819846803673715895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23487656745032572519636213 2201967819846803673715895)
                      ·
                        rfl

theorem cell23_4288317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4288317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288317 prefixEnd_4288317 := by exact prefixLift 4288317
  have htrace : WordTrace (prefixWord ++ tailWord_4288317) baseStart_4288317 baseEnd_4288317 := by
    simpa [prefixWord, tailWord_4288317, baseEnd_4288317] using wordTrace_append hprefix tailTrace_4288317
  have hstable : (prefixWord ++ tailWord_4288317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288317).length < 2 ^ (prefixWord ++ tailWord_4288317).sum := by decide
  have hdescent : baseEnd_4288317 < baseStart_4288317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288327 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_4288327 : Nat := 118140960795 + 4288327 * 2 ^ 59
def prefixEnd_4288327 : Nat := 4983230072969 + 3 ^ 40 * 4288327 * 2
def baseEnd_4288327 : Nat := 2201972954653348634590849

theorem tailTrace_4288327 : CollatzResearch.WordTrace tailWord_4288327 prefixEnd_4288327 2201972954653348634590849 := by
  unfold tailWord_4288327
  simp only [CollatzResearch.WordTrace]
  refine ⟨156408135135131141788327235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104272090090087427858884823 156408135135131141788327235)
  ·
    refine ⟨234612202702696712682490853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156408135135131141788327235 234612202702696712682490853)
    ·
      refine ⟨43989788006755633627967035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234612202702696712682490853 43989788006755633627967035)
      ·
        refine ⟨65984682010133450441950553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43989788006755633627967035 65984682010133450441950553)
        ·
          refine ⟨49488511507600087831462915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65984682010133450441950553 49488511507600087831462915)
          ·
            refine ⟨74232767261400131747194373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49488511507600087831462915 74232767261400131747194373)
            ·
              refine ⟨13918643861512524702598945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74232767261400131747194373 13918643861512524702598945)
              ·
                refine ⟨10438982896134393526949209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13918643861512524702598945 10438982896134393526949209)
                ·
                  refine ⟨7829237172100795145211907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10438982896134393526949209 7829237172100795145211907)
                  ·
                    refine ⟨11743855758151192717817861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7829237172100795145211907 11743855758151192717817861)
                    ·
                      refine ⟨2201972954653348634590849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11743855758151192717817861 2201972954653348634590849)
                      ·
                        rfl

theorem cell23_4288327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_4288327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288327 prefixEnd_4288327 := by exact prefixLift 4288327
  have htrace : WordTrace (prefixWord ++ tailWord_4288327) baseStart_4288327 baseEnd_4288327 := by
    simpa [prefixWord, tailWord_4288327, baseEnd_4288327] using wordTrace_append hprefix tailTrace_4288327
  have hstable : (prefixWord ++ tailWord_4288327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288327).length < 2 ^ (prefixWord ++ tailWord_4288327).sum := by decide
  have hdescent : baseEnd_4288327 < baseStart_4288327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
