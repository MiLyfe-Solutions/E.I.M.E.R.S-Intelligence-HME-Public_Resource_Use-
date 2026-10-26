import V185TrunkScan22Chunk125

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1127859 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 7]
def baseStart_1127859 : Nat := 118140960795 + 1127859 * 2 ^ 59
def prefixEnd_1127859 : Nat := 4983230072969 + 3 ^ 40 * 1127859 * 2
def baseEnd_1127859 : Nat := 128696394999868440039017

theorem tailTrace_1127859 : CollatzResearch.WordTrace tailWord_1127859 prefixEnd_1127859 128696394999868440039017 := by
  unfold tailWord_1127859
  simp only [CollatzResearch.WordTrace]
  refine ⟨41136397220966940826810631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27424264813977960551207087 41136397220966940826810631)
  ·
    refine ⟨61704595831450411240215947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41136397220966940826810631 61704595831450411240215947)
    ·
      refine ⟨92556893747175616860323921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61704595831450411240215947 92556893747175616860323921)
      ·
        refine ⟨69417670310381712645242941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92556893747175616860323921 69417670310381712645242941)
        ·
          refine ⟨26031626366393142241966103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69417670310381712645242941 26031626366393142241966103)
          ·
            refine ⟨39047439549589713362949155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26031626366393142241966103 39047439549589713362949155)
            ·
              refine ⟨58571159324384570044423733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39047439549589713362949155 58571159324384570044423733)
              ·
                refine ⟨5491046186661053441664725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58571159324384570044423733 5491046186661053441664725)
                ·
                  refine ⟨128696394999868440039017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5491046186661053441664725 128696394999868440039017)
                  ·
                    rfl

theorem cell22_1127859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_1127859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127859 prefixEnd_1127859 := by exact prefixLift 1127859
  have htrace : WordTrace (prefixWord ++ tailWord_1127859) baseStart_1127859 baseEnd_1127859 := by
    simpa [prefixWord, tailWord_1127859, baseEnd_1127859] using wordTrace_append hprefix tailTrace_1127859
  have hstable : (prefixWord ++ tailWord_1127859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127859).length < 2 ^ (prefixWord ++ tailWord_1127859).sum := by decide
  have hdescent : baseEnd_1127859 < baseStart_1127859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127861 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1127861 : Nat := 118140960795 + 1127861 * 2 ^ 59
def prefixEnd_1127861 : Nat := 4983230072969 + 3 ^ 40 * 1127861 * 2
def baseEnd_1127861 : Nat := 386089869640477981567045

theorem tailTrace_1127861 : CollatzResearch.WordTrace tailWord_1127861 prefixEnd_1127861 386089869640477981567045 := by
  unfold tailWord_1127861
  simp only [CollatzResearch.WordTrace]
  refine ⟨41136470166959695168383437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27424313444639796778922291 41136470166959695168383437)
  ·
    refine ⟨15426176312609885688143789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41136470166959695168383437 15426176312609885688143789)
    ·
      refine ⟨5784816117228707133053921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15426176312609885688143789 5784816117228707133053921)
      ·
        refine ⟨4338612087921530349790441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784816117228707133053921 4338612087921530349790441)
        ·
          refine ⟨3253959065941147762342831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4338612087921530349790441 3253959065941147762342831)
          ·
            refine ⟨4880938598911721643514247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253959065941147762342831 4880938598911721643514247)
            ·
              refine ⟨7321407898367582465271371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880938598911721643514247 7321407898367582465271371)
              ·
                refine ⟨10982111847551373697907057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321407898367582465271371 10982111847551373697907057)
                ·
                  refine ⟨8236583885663530273430293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10982111847551373697907057 8236583885663530273430293)
                  ·
                    refine ⟨386089869640477981567045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8236583885663530273430293 386089869640477981567045)
                    ·
                      rfl

theorem cell22_1127861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1127861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127861 prefixEnd_1127861 := by exact prefixLift 1127861
  have htrace : WordTrace (prefixWord ++ tailWord_1127861) baseStart_1127861 baseEnd_1127861 := by
    simpa [prefixWord, tailWord_1127861, baseEnd_1127861] using wordTrace_append hprefix tailTrace_1127861
  have hstable : (prefixWord ++ tailWord_1127861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127861).length < 2 ^ (prefixWord ++ tailWord_1127861).sum := by decide
  have hdescent : baseEnd_1127861 < baseStart_1127861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127921 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 6]
def baseStart_1127921 : Nat := 118140960795 + 1127921 * 2 ^ 59
def prefixEnd_1127921 : Nat := 4983230072969 + 3 ^ 40 * 1127921 * 2
def baseEnd_1127921 : Nat := 128703469622219275022287

theorem tailTrace_1127921 : CollatzResearch.WordTrace tailWord_1127921 prefixEnd_1127921 128703469622219275022287 := by
  unfold tailWord_1127921
  simp only [CollatzResearch.WordTrace]
  refine ⟨41138658546742325415567617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27425772364494883610378411 41138658546742325415567617)
  ·
    refine ⟨30853993910056744061675713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41138658546742325415567617 30853993910056744061675713)
    ·
      refine ⟨23140495432542558046256785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30853993910056744061675713 23140495432542558046256785)
      ·
        refine ⟨17355371574406918534692589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23140495432542558046256785 17355371574406918534692589)
        ·
          refine ⟨6508264340402594450509721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17355371574406918534692589 6508264340402594450509721)
          ·
            refine ⟨4881198255301945837882291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508264340402594450509721 4881198255301945837882291)
            ·
              refine ⟨7321797382952918756823437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881198255301945837882291 7321797382952918756823437)
              ·
                refine ⟨2745674018607344533808789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7321797382952918756823437 2745674018607344533808789)
                ·
                  refine ⟨128703469622219275022287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2745674018607344533808789 128703469622219275022287)
                  ·
                    rfl

theorem cell22_1127921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_1127921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127921 prefixEnd_1127921 := by exact prefixLift 1127921
  have htrace : WordTrace (prefixWord ++ tailWord_1127921) baseStart_1127921 baseEnd_1127921 := by
    simpa [prefixWord, tailWord_1127921, baseEnd_1127921] using wordTrace_append hprefix tailTrace_1127921
  have hstable : (prefixWord ++ tailWord_1127921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127921).length < 2 ^ (prefixWord ++ tailWord_1127921).sum := by decide
  have hdescent : baseEnd_1127921 < baseStart_1127921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127955 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 4]
def baseStart_1127955 : Nat := 118140960795 + 1127955 * 2 ^ 59
def prefixEnd_1127955 : Nat := 4983230072969 + 3 ^ 40 * 1127955 * 2
def baseEnd_1127955 : Nat := 128707349253831023238919

theorem tailTrace_1127955 : CollatzResearch.WordTrace tailWord_1127955 prefixEnd_1127955 128707349253831023238919 := by
  unfold tailWord_1127955
  simp only [CollatzResearch.WordTrace]
  refine ⟨41139898628619149222305319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27426599085746099481536879 41139898628619149222305319)
  ·
    refine ⟨61709847942928723833457979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41139898628619149222305319 61709847942928723833457979)
    ·
      refine ⟨92564771914393085750186969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61709847942928723833457979 92564771914393085750186969)
      ·
        refine ⟨69423578935794814312640227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92564771914393085750186969 69423578935794814312640227)
        ·
          refine ⟨104135368403692221468960341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69423578935794814312640227 104135368403692221468960341)
          ·
            refine ⟨1220336348480768220339379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 104135368403692221468960341 1220336348480768220339379)
            ·
              refine ⟨1830504522721152330509069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220336348480768220339379 1830504522721152330509069)
              ·
                refine ⟨686439196020432123940901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1830504522721152330509069 686439196020432123940901)
                ·
                  refine ⟨128707349253831023238919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686439196020432123940901 128707349253831023238919)
                  ·
                    rfl

theorem cell22_1127955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 4].length) (baseStart_1127955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127955 prefixEnd_1127955 := by exact prefixLift 1127955
  have htrace : WordTrace (prefixWord ++ tailWord_1127955) baseStart_1127955 baseEnd_1127955 := by
    simpa [prefixWord, tailWord_1127955, baseEnd_1127955] using wordTrace_append hprefix tailTrace_1127955
  have hstable : (prefixWord ++ tailWord_1127955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127955).length < 2 ^ (prefixWord ++ tailWord_1127955).sum := by decide
  have hdescent : baseEnd_1127955 < baseStart_1127955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127968 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_1127968 : Nat := 118140960795 + 1127968 * 2 ^ 59
def prefixEnd_1127968 : Nat := 4983230072969 + 3 ^ 40 * 1127968 * 2
def baseEnd_1127968 : Nat := 386126497927165369141717

theorem tailTrace_1127968 : CollatzResearch.WordTrace tailWord_1127968 prefixEnd_1127968 386126497927165369141717 := by
  unfold tailWord_1127968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570186388786026221264279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27426915185048034961685705 20570186388786026221264279)
  ·
    refine ⟨30855279583179039331896419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20570186388786026221264279 30855279583179039331896419)
    ·
      refine ⟨46282919374768558997844629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30855279583179039331896419 46282919374768558997844629)
      ·
        refine ⟨2169511845692276203023967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46282919374768558997844629 2169511845692276203023967)
        ·
          refine ⟨3254267768538414304535951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169511845692276203023967 3254267768538414304535951)
          ·
            refine ⟨4881401652807621456803927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254267768538414304535951 4881401652807621456803927)
            ·
              refine ⟨7322102479211432185205891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881401652807621456803927 7322102479211432185205891)
              ·
                refine ⟨10983153718817148277808837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322102479211432185205891 10983153718817148277808837)
                ·
                  refine ⟨2059341322278215302089157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10983153718817148277808837 2059341322278215302089157)
                  ·
                    refine ⟨386126497927165369141717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2059341322278215302089157 386126497927165369141717)
                    ·
                      rfl

theorem cell22_1127968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_1127968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127968 prefixEnd_1127968 := by exact prefixLift 1127968
  have htrace : WordTrace (prefixWord ++ tailWord_1127968) baseStart_1127968 baseEnd_1127968 := by
    simpa [prefixWord, tailWord_1127968, baseEnd_1127968] using wordTrace_append hprefix tailTrace_1127968
  have hstable : (prefixWord ++ tailWord_1127968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127968).length < 2 ^ (prefixWord ++ tailWord_1127968).sum := by decide
  have hdescent : baseEnd_1127968 < baseStart_1127968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127987 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 2, 3]
def baseStart_1127987 : Nat := 118140960795 + 1127987 * 2 ^ 59
def prefixEnd_1127987 : Nat := 4983230072969 + 3 ^ 40 * 1127987 * 2
def baseEnd_1127987 : Nat := 386133002015455652916659

theorem tailTrace_1127987 : CollatzResearch.WordTrace tailWord_1127987 prefixEnd_1127987 386133002015455652916659 := by
  unfold tailWord_1127987
  simp only [CollatzResearch.WordTrace]
  refine ⟨41141065764503218687470215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27427377176335479124980143 41141065764503218687470215)
  ·
    refine ⟨61711598646754828031205323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41141065764503218687470215 61711598646754828031205323)
    ·
      refine ⟨92567397970132242046807985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61711598646754828031205323 92567397970132242046807985)
      ·
        refine ⟨69425548477599181535105989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92567397970132242046807985 69425548477599181535105989)
        ·
          refine ⟨13017290339549846537832373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69425548477599181535105989 13017290339549846537832373)
          ·
            refine ⟨1220370969332798112921785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13017290339549846537832373 1220370969332798112921785)
            ·
              refine ⟨915278226999598584691339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220370969332798112921785 915278226999598584691339)
              ·
                refine ⟨1372917340499397877037009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915278226999598584691339 1372917340499397877037009)
                ·
                  refine ⟨1029688005374548407777757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372917340499397877037009 1029688005374548407777757)
                  ·
                    refine ⟨386133002015455652916659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029688005374548407777757 386133002015455652916659)
                    ·
                      rfl

theorem cell22_1127987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 3].length) (baseStart_1127987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127987 prefixEnd_1127987 := by exact prefixLift 1127987
  have htrace : WordTrace (prefixWord ++ tailWord_1127987) baseStart_1127987 baseEnd_1127987 := by
    simpa [prefixWord, tailWord_1127987, baseEnd_1127987] using wordTrace_append hprefix tailTrace_1127987
  have hstable : (prefixWord ++ tailWord_1127987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127987).length < 2 ^ (prefixWord ++ tailWord_1127987).sum := by decide
  have hdescent : baseEnd_1127987 < baseStart_1127987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128015 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 1, 3]
def baseStart_1128015 : Nat := 118140960795 + 1128015 * 2 ^ 59
def prefixEnd_1128015 : Nat := 4983230072969 + 3 ^ 40 * 1128015 * 2
def baseEnd_1128015 : Nat := 386142586987672913216573

theorem tailTrace_1128015 : CollatzResearch.WordTrace tailWord_1128015 prefixEnd_1128015 386142586987672913216573 := by
  unfold tailWord_1128015
  simp only [CollatzResearch.WordTrace]
  refine ⟨41142087008401779469489499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27428058005601186312992999 41142087008401779469489499)
  ·
    refine ⟨61713130512602669204234249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41142087008401779469489499 61713130512602669204234249)
    ·
      refine ⟨46284847884452001903175687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61713130512602669204234249 46284847884452001903175687)
      ·
        refine ⟨69427271826678002854763531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46284847884452001903175687 69427271826678002854763531)
        ·
          refine ⟨104140907740017004282145297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69427271826678002854763531 104140907740017004282145297)
          ·
            refine ⟨78105680805012753211608973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104140907740017004282145297 78105680805012753211608973)
            ·
              refine ⟨29289630301879782454353365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78105680805012753211608973 29289630301879782454353365)
              ·
                refine ⟨686475710200307401273907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29289630301879782454353365 686475710200307401273907)
                ·
                  refine ⟨1029713565300461101910861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686475710200307401273907 1029713565300461101910861)
                  ·
                    refine ⟨386142586987672913216573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029713565300461101910861 386142586987672913216573)
                    ·
                      rfl

theorem cell22_1128015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_1128015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128015 prefixEnd_1128015 := by exact prefixLift 1128015
  have htrace : WordTrace (prefixWord ++ tailWord_1128015) baseStart_1128015 baseEnd_1128015 := by
    simpa [prefixWord, tailWord_1128015, baseEnd_1128015] using wordTrace_append hprefix tailTrace_1128015
  have hstable : (prefixWord ++ tailWord_1128015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128015).length < 2 ^ (prefixWord ++ tailWord_1128015).sum := by decide
  have hdescent : baseEnd_1128015 < baseStart_1128015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128026 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_1128026 : Nat := 118140960795 + 1128026 * 2 ^ 59
def prefixEnd_1128026 : Nat := 4983230072969 + 3 ^ 40 * 1128026 * 2
def baseEnd_1128026 : Nat := 386146352512472551191539

theorem tailTrace_1128026 : CollatzResearch.WordTrace tailWord_1128026 prefixEnd_1128026 386146352512472551191539 := by
  unfold tailWord_1128026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10285622052840482087034983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27428325474241285565426621 10285622052840482087034983)
  ·
    refine ⟨15428433079260723130552475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10285622052840482087034983 15428433079260723130552475)
    ·
      refine ⟨23142649618891084695828713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15428433079260723130552475 23142649618891084695828713)
      ·
        refine ⟨17356987214168313521871535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23142649618891084695828713 17356987214168313521871535)
        ·
          refine ⟨26035480821252470282807303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17356987214168313521871535 26035480821252470282807303)
          ·
            refine ⟨39053221231878705424210955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26035480821252470282807303 39053221231878705424210955)
            ·
              refine ⟨58579831847818058136316433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39053221231878705424210955 58579831847818058136316433)
              ·
                refine ⟨43934873885863543602237325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58579831847818058136316433 43934873885863543602237325)
                ·
                  refine ⟨16475577707198828850838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43934873885863543602237325 16475577707198828850838997)
                  ·
                    refine ⟨386146352512472551191539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16475577707198828850838997 386146352512472551191539)
                    ·
                      rfl

theorem cell22_1128026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_1128026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128026 prefixEnd_1128026 := by exact prefixLift 1128026
  have htrace : WordTrace (prefixWord ++ tailWord_1128026) baseStart_1128026 baseEnd_1128026 := by
    simpa [prefixWord, tailWord_1128026, baseEnd_1128026] using wordTrace_append hprefix tailTrace_1128026
  have hstable : (prefixWord ++ tailWord_1128026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128026).length < 2 ^ (prefixWord ++ tailWord_1128026).sum := by decide
  have hdescent : baseEnd_1128026 < baseStart_1128026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128141 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1128141 : Nat := 118140960795 + 1128141 * 2 ^ 59
def prefixEnd_1128141 : Nat := 4983230072969 + 3 ^ 40 * 1128141 * 2
def baseEnd_1128141 : Nat := 128728573120883528188729

theorem tailTrace_1128141 : CollatzResearch.WordTrace tailWord_1128141 prefixEnd_1128141 128728573120883528188729 := by
  unfold tailWord_1128141
  simp only [CollatzResearch.WordTrace]
  refine ⟨41146682605945302988576277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27431121737296868659050851 41146682605945302988576277)
  ·
    refine ⟨1928750747153686077589513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41146682605945302988576277 1928750747153686077589513)
    ·
      refine ⟨1446563060365264558192135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1928750747153686077589513 1446563060365264558192135)
      ·
        refine ⟨2169844590547896837288203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446563060365264558192135 2169844590547896837288203)
        ·
          refine ⟨3254766885821845255932305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169844590547896837288203 3254766885821845255932305)
          ·
            refine ⟨2441075164366383941949229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3254766885821845255932305 2441075164366383941949229)
            ·
              refine ⟨915403186637393978230961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2441075164366383941949229 915403186637393978230961)
              ·
                refine ⟨686552389978045483673221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915403186637393978230961 686552389978045483673221)
                ·
                  refine ⟨128728573120883528188729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686552389978045483673221 128728573120883528188729)
                  ·
                    rfl

theorem cell22_1128141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1128141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128141 prefixEnd_1128141 := by exact prefixLift 1128141
  have htrace : WordTrace (prefixWord ++ tailWord_1128141) baseStart_1128141 baseEnd_1128141 := by
    simpa [prefixWord, tailWord_1128141, baseEnd_1128141] using wordTrace_append hprefix tailTrace_1128141
  have hstable : (prefixWord ++ tailWord_1128141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128141).length < 2 ^ (prefixWord ++ tailWord_1128141).sum := by decide
  have hdescent : baseEnd_1128141 < baseStart_1128141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128225 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 6]
def baseStart_1128225 : Nat := 118140960795 + 1128225 * 2 ^ 59
def prefixEnd_1128225 : Nat := 4983230072969 + 3 ^ 40 * 1128225 * 2
def baseEnd_1128225 : Nat := 128738158093100788488643

theorem tailTrace_1128225 : CollatzResearch.WordTrace tailWord_1128225 prefixEnd_1128225 128738158093100788488643 := by
  unfold tailWord_1128225
  simp only [CollatzResearch.WordTrace]
  refine ⟨41149746337640985334634129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27433164225093990223089419 41149746337640985334634129)
  ·
    refine ⟨30862309753230739000975597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41149746337640985334634129 30862309753230739000975597)
    ·
      refine ⟨11573366157461527125365849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30862309753230739000975597 11573366157461527125365849)
      ·
        refine ⟨8680024618096145344024387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11573366157461527125365849 8680024618096145344024387)
        ·
          refine ⟨13020036927144218016036581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8680024618096145344024387 13020036927144218016036581)
          ·
            refine ⟨2441256923839540878006859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13020036927144218016036581 2441256923839540878006859)
            ·
              refine ⟨3661885385759311317010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441256923839540878006859 3661885385759311317010289)
              ·
                refine ⟨2746414039319483487757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661885385759311317010289 2746414039319483487757717)
                ·
                  refine ⟨128738158093100788488643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2746414039319483487757717 128738158093100788488643)
                  ·
                    rfl

theorem cell22_1128225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_1128225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128225 prefixEnd_1128225 := by exact prefixLift 1128225
  have htrace : WordTrace (prefixWord ++ tailWord_1128225) baseStart_1128225 baseEnd_1128225 := by
    simpa [prefixWord, tailWord_1128225, baseEnd_1128225] using wordTrace_append hprefix tailTrace_1128225
  have hstable : (prefixWord ++ tailWord_1128225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128225).length < 2 ^ (prefixWord ++ tailWord_1128225).sum := by decide
  have hdescent : baseEnd_1128225 < baseStart_1128225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128242 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1128242 : Nat := 118140960795 + 1128242 * 2 ^ 59
def prefixEnd_1128242 : Nat := 4983230072969 + 3 ^ 40 * 1128242 * 2
def baseEnd_1128242 : Nat := 128740097908906662596959

theorem tailTrace_1128242 : CollatzResearch.WordTrace tailWord_1128242 prefixEnd_1128242 128740097908906662596959 := by
  unfold tailWord_1128242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10287591594644849309500745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27433577585719598158668653 10287591594644849309500745)
  ·
    refine ⟨7715693695983636982125559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10287591594644849309500745 7715693695983636982125559)
    ·
      refine ⟨11573540543975455473188339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7715693695983636982125559 11573540543975455473188339)
      ·
        refine ⟨17360310815963183209782509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11573540543975455473188339 17360310815963183209782509)
        ·
          refine ⟨6510116555986193703668441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17360310815963183209782509 6510116555986193703668441)
          ·
            refine ⟨4882587416989645277751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6510116555986193703668441 4882587416989645277751331)
            ·
              refine ⟨7323881125484467916626997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882587416989645277751331 7323881125484467916626997)
              ·
                refine ⟨686613855514168867183781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7323881125484467916626997 686613855514168867183781)
                ·
                  refine ⟨128740097908906662596959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686613855514168867183781 128740097908906662596959)
                  ·
                    rfl

theorem cell22_1128242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1128242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128242 prefixEnd_1128242 := by exact prefixLift 1128242
  have htrace : WordTrace (prefixWord ++ tailWord_1128242) baseStart_1128242 baseEnd_1128242 := by
    simpa [prefixWord, tailWord_1128242, baseEnd_1128242] using wordTrace_append hprefix tailTrace_1128242
  have hstable : (prefixWord ++ tailWord_1128242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128242).length < 2 ^ (prefixWord ++ tailWord_1128242).sum := by decide
  have hdescent : baseEnd_1128242 < baseStart_1128242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128244 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1128244 : Nat := 118140960795 + 1128244 * 2 ^ 59
def prefixEnd_1128244 : Nat := 4983230072969 + 3 ^ 40 * 1128244 * 2
def baseEnd_1128244 : Nat := 386220978367592649240871

theorem tailTrace_1128244 : CollatzResearch.WordTrace tailWord_1128244 prefixEnd_1128244 386220978367592649240871 := by
  unfold tailWord_1128244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20575219662286075789787893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27433626216381434386383857 20575219662286075789787893)
  ·
    refine ⟨1928926843339319605292615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20575219662286075789787893 1928926843339319605292615)
    ·
      refine ⟨2893390265008979407938923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1928926843339319605292615 2893390265008979407938923)
      ·
        refine ⟨4340085397513469111908385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893390265008979407938923 4340085397513469111908385)
        ·
          refine ⟨3255064048135101833931289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4340085397513469111908385 3255064048135101833931289)
          ·
            refine ⟨2441298036101326375448467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255064048135101833931289 2441298036101326375448467)
            ·
              refine ⟨3661947054151989563172701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441298036101326375448467 3661947054151989563172701)
              ·
                refine ⟨1373230145306996086189763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3661947054151989563172701 1373230145306996086189763)
                ·
                  refine ⟨2059845217960494129284645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373230145306996086189763 2059845217960494129284645)
                  ·
                    refine ⟨386220978367592649240871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2059845217960494129284645 386220978367592649240871)
                    ·
                      rfl

theorem cell22_1128244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1128244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128244 prefixEnd_1128244 := by exact prefixLift 1128244
  have htrace : WordTrace (prefixWord ++ tailWord_1128244) baseStart_1128244 baseEnd_1128244 := by
    simpa [prefixWord, tailWord_1128244, baseEnd_1128244] using wordTrace_append hprefix tailTrace_1128244
  have hstable : (prefixWord ++ tailWord_1128244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128244).length < 2 ^ (prefixWord ++ tailWord_1128244).sum := by decide
  have hdescent : baseEnd_1128244 < baseStart_1128244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128287 : List Nat := [1, 1, 2, 3, 1, 6, 2, 6]
def baseStart_1128287 : Nat := 118140960795 + 1128287 * 2 ^ 59
def prefixEnd_1128287 : Nat := 4983230072969 + 3 ^ 40 * 1128287 * 2
def baseEnd_1128287 : Nat := 42915077571817207823971

theorem tailTrace_1128287 : CollatzResearch.WordTrace tailWord_1128287 prefixEnd_1128287 42915077571817207823971 := by
  unfold tailWord_1128287
  simp only [CollatzResearch.WordTrace]
  refine ⟨41152007663416369923391115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27434671775610913282260743 41152007663416369923391115)
  ·
    refine ⟨61728011495124554885086673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41152007663416369923391115 61728011495124554885086673)
    ·
      refine ⟨46296008621343416163815005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61728011495124554885086673 46296008621343416163815005)
      ·
        refine ⟨17361003233003781061430627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46296008621343416163815005 17361003233003781061430627)
        ·
          refine ⟨26041504849505671592145941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17361003233003781061430627 26041504849505671592145941)
          ·
            refine ⟨1220695539820578355881841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26041504849505671592145941 1220695539820578355881841)
            ·
              refine ⟨915521654865433766911381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220695539820578355881841 915521654865433766911381)
              ·
                refine ⟨42915077571817207823971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 915521654865433766911381 42915077571817207823971)
                ·
                  rfl

theorem cell22_1128287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 6].length) (baseStart_1128287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128287 prefixEnd_1128287 := by exact prefixLift 1128287
  have htrace : WordTrace (prefixWord ++ tailWord_1128287) baseStart_1128287 baseEnd_1128287 := by
    simpa [prefixWord, tailWord_1128287, baseEnd_1128287] using wordTrace_append hprefix tailTrace_1128287
  have hstable : (prefixWord ++ tailWord_1128287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128287).length < 2 ^ (prefixWord ++ tailWord_1128287).sum := by decide
  have hdescent : baseEnd_1128287 < baseStart_1128287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128315 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 5]
def baseStart_1128315 : Nat := 118140960795 + 1128315 * 2 ^ 59
def prefixEnd_1128315 : Nat := 4983230072969 + 3 ^ 40 * 1128315 * 2
def baseEnd_1128315 : Nat := 128748427706190710238551

theorem tailTrace_1128315 : CollatzResearch.WordTrace tailWord_1128315 prefixEnd_1128315 128748427706190710238551 := by
  unfold tailWord_1128315
  simp only [CollatzResearch.WordTrace]
  refine ⟨41153028907314930705410399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27435352604876620470273599 41153028907314930705410399)
  ·
    refine ⟨61729543360972396058115599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41153028907314930705410399 61729543360972396058115599)
    ·
      refine ⟨92594315041458594087173399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61729543360972396058115599 92594315041458594087173399)
      ·
        refine ⟨138891472562187891130760099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92594315041458594087173399 138891472562187891130760099)
        ·
          refine ⟨208337208843281836696140149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138891472562187891130760099 208337208843281836696140149)
          ·
            refine ⟨19531613329057672190263139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208337208843281836696140149 19531613329057672190263139)
            ·
              refine ⟨29297419993586508285394709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19531613329057672190263139 29297419993586508285394709)
              ·
                refine ⟨1373316562199367575877877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29297419993586508285394709 1373316562199367575877877)
                ·
                  refine ⟨128748427706190710238551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1373316562199367575877877 128748427706190710238551)
                  ·
                    rfl

theorem cell22_1128315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 5].length) (baseStart_1128315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128315 prefixEnd_1128315 := by exact prefixLift 1128315
  have htrace : WordTrace (prefixWord ++ tailWord_1128315) baseStart_1128315 baseEnd_1128315 := by
    simpa [prefixWord, tailWord_1128315, baseEnd_1128315] using wordTrace_append hprefix tailTrace_1128315
  have hstable : (prefixWord ++ tailWord_1128315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128315).length < 2 ^ (prefixWord ++ tailWord_1128315).sum := by decide
  have hdescent : baseEnd_1128315 < baseStart_1128315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128375 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1128375 : Nat := 118140960795 + 1128375 * 2 ^ 59
def prefixEnd_1128375 : Nat := 4983230072969 + 3 ^ 40 * 1128375 * 2
def baseEnd_1128375 : Nat := 386265822344751974215469

theorem tailTrace_1128375 : CollatzResearch.WordTrace tailWord_1128375 prefixEnd_1128375 386265822344751974215469 := by
  unfold tailWord_1128375
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155217287097560952594579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27436811524731707301729719 41155217287097560952594579)
  ·
    refine ⟨61732825930646341428891869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41155217287097560952594579 61732825930646341428891869)
    ·
      refine ⟨23149809723992378035834451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61732825930646341428891869 23149809723992378035834451)
      ·
        refine ⟨34724714585988567053751677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23149809723992378035834451 34724714585988567053751677)
        ·
          refine ⟨13021767969745712645156879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34724714585988567053751677 13021767969745712645156879)
          ·
            refine ⟨19532651954618568967735319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13021767969745712645156879 19532651954618568967735319)
            ·
              refine ⟨29298977931927853451602979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19532651954618568967735319 29298977931927853451602979)
              ·
                refine ⟨43948466897891780177404469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29298977931927853451602979 43948466897891780177404469)
                ·
                  refine ⟨4120168771677354391631669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43948466897891780177404469 4120168771677354391631669)
                  ·
                    refine ⟨386265822344751974215469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4120168771677354391631669 386265822344751974215469)
                    ·
                      rfl

theorem cell22_1128375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1128375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128375 prefixEnd_1128375 := by exact prefixLift 1128375
  have htrace : WordTrace (prefixWord ++ tailWord_1128375) baseStart_1128375 baseEnd_1128375 := by
    simpa [prefixWord, tailWord_1128375, baseEnd_1128375] using wordTrace_append hprefix tailTrace_1128375
  have hstable : (prefixWord ++ tailWord_1128375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128375).length < 2 ^ (prefixWord ++ tailWord_1128375).sum := by decide
  have hdescent : baseEnd_1128375 < baseStart_1128375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128392 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1128392 : Nat := 118140960795 + 1128392 * 2 ^ 59
def prefixEnd_1128392 : Nat := 4983230072969 + 3 ^ 40 * 1128392 * 2
def baseEnd_1128392 : Nat := 386271641792169596540417

theorem tailTrace_1128392 : CollatzResearch.WordTrace tailWord_1128392 prefixEnd_1128392 386271641792169596540417 := by
  unfold tailWord_1128392
  simp only [CollatzResearch.WordTrace]
  refine ⟨20577918664017986427981715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27437224885357315237308953 20577918664017986427981715)
  ·
    refine ⟨30866877996026979641972573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20577918664017986427981715 30866877996026979641972573)
    ·
      refine ⟨11575079248510117365739715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30866877996026979641972573 11575079248510117365739715)
      ·
        refine ⟨17362618872765176048609573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11575079248510117365739715 17362618872765176048609573)
        ·
          refine ⟨3255491038643470509114295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17362618872765176048609573 3255491038643470509114295)
          ·
            refine ⟨4883236557965205763671443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3255491038643470509114295 4883236557965205763671443)
            ·
              refine ⟨7324854836947808645507165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4883236557965205763671443 7324854836947808645507165)
              ·
                refine ⟨2746820563855428242065187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7324854836947808645507165 2746820563855428242065187)
                ·
                  refine ⟨4120230845783142363097781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746820563855428242065187 4120230845783142363097781)
                  ·
                    refine ⟨386271641792169596540417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4120230845783142363097781 386271641792169596540417)
                    ·
                      rfl

theorem cell22_1128392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1128392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128392 prefixEnd_1128392 := by exact prefixLift 1128392
  have htrace : WordTrace (prefixWord ++ tailWord_1128392) baseStart_1128392 baseEnd_1128392 := by
    simpa [prefixWord, tailWord_1128392, baseEnd_1128392] using wordTrace_append hprefix tailTrace_1128392
  have hstable : (prefixWord ++ tailWord_1128392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128392).length < 2 ^ (prefixWord ++ tailWord_1128392).sum := by decide
  have hdescent : baseEnd_1128392 < baseStart_1128392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128413 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1128413 : Nat := 118140960795 + 1128413 * 2 ^ 59
def prefixEnd_1128413 : Nat := 4983230072969 + 3 ^ 40 * 1128413 * 2
def baseEnd_1128413 : Nat := 386278830521332541765353

theorem tailTrace_1128413 : CollatzResearch.WordTrace tailWord_1128413 prefixEnd_1128413 386278830521332541765353 := by
  unfold tailWord_1128413
  simp only [CollatzResearch.WordTrace]
  refine ⟨41156603260959893442477893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27437735507306595628318595 41156603260959893442477893)
  ·
    refine ⟨7716863111429980020464605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41156603260959893442477893 7716863111429980020464605)
    ·
      refine ⟨2893823666786242507674227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7716863111429980020464605 2893823666786242507674227)
      ·
        refine ⟨4340735500179363761511341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893823666786242507674227 4340735500179363761511341)
        ·
          refine ⟨1627775812567261410566753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4340735500179363761511341 1627775812567261410566753)
          ·
            refine ⟨1220831859425446057925065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627775812567261410566753 1220831859425446057925065)
            ·
              refine ⟨915623894569084543443799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220831859425446057925065 915623894569084543443799)
              ·
                refine ⟨1373435841853626815165699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915623894569084543443799 1373435841853626815165699)
                ·
                  refine ⟨2060153762780440222748549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373435841853626815165699 2060153762780440222748549)
                  ·
                    refine ⟨386278830521332541765353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060153762780440222748549 386278830521332541765353)
                    ·
                      rfl

theorem cell22_1128413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1128413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128413 prefixEnd_1128413 := by exact prefixLift 1128413
  have htrace : WordTrace (prefixWord ++ tailWord_1128413) baseStart_1128413 baseEnd_1128413 := by
    simpa [prefixWord, tailWord_1128413, baseEnd_1128413] using wordTrace_append hprefix tailTrace_1128413
  have hstable : (prefixWord ++ tailWord_1128413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128413).length < 2 ^ (prefixWord ++ tailWord_1128413).sum := by decide
  have hdescent : baseEnd_1128413 < baseStart_1128413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128435 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_1128435 : Nat := 118140960795 + 1128435 * 2 ^ 59
def prefixEnd_1128435 : Nat := 4983230072969 + 3 ^ 40 * 1128435 * 2
def baseEnd_1128435 : Nat := 386286361570931817715285

theorem tailTrace_1128435 : CollatzResearch.WordTrace tailWord_1128435 prefixEnd_1128435 386286361570931817715285 := by
  unfold tailWord_1128435
  simp only [CollatzResearch.WordTrace]
  refine ⟨41157405666880191199778759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27438270444586794133185839 41157405666880191199778759)
  ·
    refine ⟨61736108500320286799668139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41157405666880191199778759 61736108500320286799668139)
    ·
      refine ⟨92604162750480430199502209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61736108500320286799668139 92604162750480430199502209)
      ·
        refine ⟨69453122062860322649626657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92604162750480430199502209 69453122062860322649626657)
        ·
          refine ⟨52089841547145241987219993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69453122062860322649626657 52089841547145241987219993)
          ·
            refine ⟨39067381160358931490414995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52089841547145241987219993 39067381160358931490414995)
            ·
              refine ⟨58601071740538397235622493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39067381160358931490414995 58601071740538397235622493)
              ·
                refine ⟨21975401902701898963358435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58601071740538397235622493 21975401902701898963358435)
                ·
                  refine ⟨32963102854052848445037653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21975401902701898963358435 32963102854052848445037653)
                  ·
                    refine ⟨386286361570931817715285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32963102854052848445037653 386286361570931817715285)
                    ·
                      rfl

theorem cell22_1128435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_1128435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128435 prefixEnd_1128435 := by exact prefixLift 1128435
  have htrace : WordTrace (prefixWord ++ tailWord_1128435) baseStart_1128435 baseEnd_1128435 := by
    simpa [prefixWord, tailWord_1128435, baseEnd_1128435] using wordTrace_append hprefix tailTrace_1128435
  have hstable : (prefixWord ++ tailWord_1128435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128435).length < 2 ^ (prefixWord ++ tailWord_1128435).sum := by decide
  have hdescent : baseEnd_1128435 < baseStart_1128435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128527 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_1128527 : Nat := 118140960795 + 1128527 * 2 ^ 59
def prefixEnd_1128527 : Nat := 4983230072969 + 3 ^ 40 * 1128527 * 2
def baseEnd_1128527 : Nat := 386317855051074244415003

theorem tailTrace_1128527 : CollatzResearch.WordTrace tailWord_1128527 prefixEnd_1128527 386317855051074244415003 := by
  unfold tailWord_1128527
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160761182546890912127835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27440507455031260608085223 41160761182546890912127835)
  ·
    refine ⟨61741141773820336368191753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41160761182546890912127835 61741141773820336368191753)
    ·
      refine ⟨46305856330365252276143815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61741141773820336368191753 46305856330365252276143815)
      ·
        refine ⟨69458784495547878414215723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46305856330365252276143815 69458784495547878414215723)
        ·
          refine ⟨104188176743321817621323585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69458784495547878414215723 104188176743321817621323585)
          ·
            refine ⟨78141132557491363215992689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104188176743321817621323585 78141132557491363215992689)
            ·
              refine ⟨58605849418118522411994517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78141132557491363215992689 58605849418118522411994517)
              ·
                refine ⟨2747149191474305738062243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58605849418118522411994517 2747149191474305738062243)
                ·
                  refine ⟨4120723787211458607093365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747149191474305738062243 4120723787211458607093365)
                  ·
                    refine ⟨386317855051074244415003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4120723787211458607093365 386317855051074244415003)
                    ·
                      rfl

theorem cell22_1128527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_1128527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128527 prefixEnd_1128527 := by exact prefixLift 1128527
  have htrace : WordTrace (prefixWord ++ tailWord_1128527) baseStart_1128527 baseEnd_1128527 := by
    simpa [prefixWord, tailWord_1128527, baseEnd_1128527] using wordTrace_append hprefix tailTrace_1128527
  have hstable : (prefixWord ++ tailWord_1128527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128527).length < 2 ^ (prefixWord ++ tailWord_1128527).sum := by decide
  have hdescent : baseEnd_1128527 < baseStart_1128527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128529 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 4]
def baseStart_1128529 : Nat := 118140960795 + 1128529 * 2 ^ 59
def prefixEnd_1128529 : Nat := 4983230072969 + 3 ^ 40 * 1128529 * 2
def baseEnd_1128529 : Nat := 128772846563982301954999

theorem tailTrace_1128529 : CollatzResearch.WordTrace tailWord_1128529 prefixEnd_1128529 128772846563982301954999 := by
  unfold tailWord_1128529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160834128539645253700641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27440556085693096835800427 41160834128539645253700641)
  ·
    refine ⟨30870625596404733940275481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41160834128539645253700641 30870625596404733940275481)
    ·
      refine ⟨23152969197303550455206611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30870625596404733940275481 23152969197303550455206611)
      ·
        refine ⟨34729453795955325682809917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23152969197303550455206611 34729453795955325682809917)
        ·
          refine ⟨13023545173483247131053719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34729453795955325682809917 13023545173483247131053719)
          ·
            refine ⟨19535317760224870696580579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023545173483247131053719 19535317760224870696580579)
            ·
              refine ⟨29302976640337306044870869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19535317760224870696580579 29302976640337306044870869)
              ·
                refine ⟨686788515007905610426661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29302976640337306044870869 686788515007905610426661)
                ·
                  refine ⟨128772846563982301954999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686788515007905610426661 128772846563982301954999)
                  ·
                    rfl

theorem cell22_1128529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_1128529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128529 prefixEnd_1128529 := by exact prefixLift 1128529
  have htrace : WordTrace (prefixWord ++ tailWord_1128529) baseStart_1128529 baseEnd_1128529 := by
    simpa [prefixWord, tailWord_1128529, baseEnd_1128529] using wordTrace_append hprefix tailTrace_1128529
  have hstable : (prefixWord ++ tailWord_1128529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128529).length < 2 ^ (prefixWord ++ tailWord_1128529).sum := by decide
  have hdescent : baseEnd_1128529 < baseStart_1128529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128640 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 1, 3]
def baseStart_1128640 : Nat := 118140960795 + 1128640 * 2 ^ 59
def prefixEnd_1128640 : Nat := 4983230072969 + 3 ^ 40 * 1128640 * 2
def baseEnd_1128640 : Nat := 386356537260379616339657

theorem tailTrace_1128640 : CollatzResearch.WordTrace tailWord_1128640 prefixEnd_1128640 386356537260379616339657 := by
  unfold tailWord_1128640
  simp only [CollatzResearch.WordTrace]
  refine ⟨20582441315568755605495687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27443255087425007473994249 20582441315568755605495687)
  ·
    refine ⟨30873661973353133408243531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20582441315568755605495687 30873661973353133408243531)
    ·
      refine ⟨46310492960029700112365297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30873661973353133408243531 46310492960029700112365297)
      ·
        refine ⟨34732869720022275084273973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46310492960029700112365297 34732869720022275084273973)
        ·
          refine ⟨3256206536252088289150685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34732869720022275084273973 3256206536252088289150685)
          ·
            refine ⟨1221077451094533108431507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3256206536252088289150685 1221077451094533108431507)
            ·
              refine ⟨1831616176641799662647261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221077451094533108431507 1831616176641799662647261)
              ·
                refine ⟨686856066240674873492723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1831616176641799662647261 686856066240674873492723)
                ·
                  refine ⟨1030284099361012310239085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686856066240674873492723 1030284099361012310239085)
                  ·
                    refine ⟨386356537260379616339657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030284099361012310239085 386356537260379616339657)
                    ·
                      rfl

theorem cell22_1128640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_1128640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128640 prefixEnd_1128640 := by exact prefixLift 1128640
  have htrace : WordTrace (prefixWord ++ tailWord_1128640) baseStart_1128640 baseEnd_1128640 := by
    simpa [prefixWord, tailWord_1128640, baseEnd_1128640] using wordTrace_append hprefix tailTrace_1128640
  have hstable : (prefixWord ++ tailWord_1128640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128640).length < 2 ^ (prefixWord ++ tailWord_1128640).sum := by decide
  have hdescent : baseEnd_1128640 < baseStart_1128640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128713 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_1128713 : Nat := 118140960795 + 1128713 * 2 ^ 59
def prefixEnd_1128713 : Nat := 4983230072969 + 3 ^ 40 * 1128713 * 2
def baseEnd_1128713 : Nat := 386381526652231759264433

theorem tailTrace_1128713 : CollatzResearch.WordTrace tailWord_1128713 prefixEnd_1128713 386381526652231759264433 := by
  unfold tailWord_1128713
  simp only [CollatzResearch.WordTrace]
  refine ⟨41167545159873044678398793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27445030106582029785599195 41167545159873044678398793)
  ·
    refine ⟨30875658869904783508799095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41167545159873044678398793 30875658869904783508799095)
    ·
      refine ⟨46313488304857175263198643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30875658869904783508799095 46313488304857175263198643)
      ·
        refine ⟨69470232457285762894797965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46313488304857175263198643 69470232457285762894797965)
        ·
          refine ⟨26051337171482161085549237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69470232457285762894797965 26051337171482161085549237)
          ·
            refine ⟨2442312859826452601770241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26051337171482161085549237 2442312859826452601770241)
            ·
              refine ⟨1831734644869839451327681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442312859826452601770241 1831734644869839451327681)
              ·
                refine ⟨1373800983652379588495761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1831734644869839451327681 1373800983652379588495761)
                ·
                  refine ⟨1030350737739284691371821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1373800983652379588495761 1030350737739284691371821)
                  ·
                    refine ⟨386381526652231759264433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030350737739284691371821 386381526652231759264433)
                    ·
                      rfl

theorem cell22_1128713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_1128713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128713 prefixEnd_1128713 := by exact prefixLift 1128713
  have htrace : WordTrace (prefixWord ++ tailWord_1128713) baseStart_1128713 baseEnd_1128713 := by
    simpa [prefixWord, tailWord_1128713, baseEnd_1128713] using wordTrace_append hprefix tailTrace_1128713
  have hstable : (prefixWord ++ tailWord_1128713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128713).length < 2 ^ (prefixWord ++ tailWord_1128713).sum := by decide
  have hdescent : baseEnd_1128713 < baseStart_1128713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128739 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_1128739 : Nat := 118140960795 + 1128739 * 2 ^ 59
def prefixEnd_1128739 : Nat := 4983230072969 + 3 ^ 40 * 1128739 * 2
def baseEnd_1128739 : Nat := 386390426983576358114353

theorem tailTrace_1128739 : CollatzResearch.WordTrace tailWord_1128739 prefixEnd_1128739 386390426983576358114353 := by
  unfold tailWord_1128739
  simp only [CollatzResearch.WordTrace]
  refine ⟨41168493457778851118845271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27445662305185900745896847 41168493457778851118845271)
  ·
    refine ⟨61752740186668276678267907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41168493457778851118845271 61752740186668276678267907)
    ·
      refine ⟨92629110280002415017401861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61752740186668276678267907 92629110280002415017401861)
      ·
        refine ⟨17367958177500452815762849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92629110280002415017401861 17367958177500452815762849)
        ·
          refine ⟨13025968633125339611822137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17367958177500452815762849 13025968633125339611822137)
          ·
            refine ⟨9769476474844004708866603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13025968633125339611822137 9769476474844004708866603)
            ·
              refine ⟨14654214712266007063299905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9769476474844004708866603 14654214712266007063299905)
              ·
                refine ⟨10990661034199505297474929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14654214712266007063299905 10990661034199505297474929)
                ·
                  refine ⟨8242995775649628973106197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10990661034199505297474929 8242995775649628973106197)
                  ·
                    refine ⟨386390426983576358114353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8242995775649628973106197 386390426983576358114353)
                    ·
                      rfl

theorem cell22_1128739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_1128739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128739 prefixEnd_1128739 := by exact prefixLift 1128739
  have htrace : WordTrace (prefixWord ++ tailWord_1128739) baseStart_1128739 baseEnd_1128739 := by
    simpa [prefixWord, tailWord_1128739, baseEnd_1128739] using wordTrace_append hprefix tailTrace_1128739
  have hstable : (prefixWord ++ tailWord_1128739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128739).length < 2 ^ (prefixWord ++ tailWord_1128739).sum := by decide
  have hdescent : baseEnd_1128739 < baseStart_1128739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128771 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 5]
def baseStart_1128771 : Nat := 118140960795 + 1128771 * 2 ^ 59
def prefixEnd_1128771 : Nat := 4983230072969 + 3 ^ 40 * 1128771 * 2
def baseEnd_1128771 : Nat := 128800460412512980438085

theorem tailTrace_1128771 : CollatzResearch.WordTrace tailWord_1128771 prefixEnd_1128771 128800460412512980438085 := by
  unfold tailWord_1128771
  simp only [CollatzResearch.WordTrace]
  refine ⟨41169660593662920584010167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27446440395775280389340111 41169660593662920584010167)
  ·
    refine ⟨61754490890494380876015251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41169660593662920584010167 61754490890494380876015251)
    ·
      refine ⟨92631736335741571314022877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61754490890494380876015251 92631736335741571314022877)
      ·
        refine ⟨34736901125903089242758579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92631736335741571314022877 34736901125903089242758579)
        ·
          refine ⟨52105351688854633864137869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34736901125903089242758579 52105351688854633864137869)
          ·
            refine ⟨19539506883320487699051701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52105351688854633864137869 19539506883320487699051701)
            ·
              refine ⟨1831828770311295721786097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19539506883320487699051701 1831828770311295721786097)
              ·
                refine ⟨1373871577733471791339573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1831828770311295721786097 1373871577733471791339573)
                ·
                  refine ⟨128800460412512980438085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1373871577733471791339573 128800460412512980438085)
                  ·
                    rfl

theorem cell22_1128771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 5].length) (baseStart_1128771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128771 prefixEnd_1128771 := by exact prefixLift 1128771
  have htrace : WordTrace (prefixWord ++ tailWord_1128771) baseStart_1128771 baseEnd_1128771 := by
    simpa [prefixWord, tailWord_1128771, baseEnd_1128771] using wordTrace_append hprefix tailTrace_1128771
  have hstable : (prefixWord ++ tailWord_1128771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128771).length < 2 ^ (prefixWord ++ tailWord_1128771).sum := by decide
  have hdescent : baseEnd_1128771 < baseStart_1128771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128786 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1128786 : Nat := 118140960795 + 1128786 * 2 ^ 59
def prefixEnd_1128786 : Nat := 4983230072969 + 3 ^ 40 * 1128786 * 2
def baseEnd_1128786 : Nat := 386406516044083902189209

theorem tailTrace_1128786 : CollatzResearch.WordTrace tailWord_1128786 prefixEnd_1128786 386406516044083902189209 := by
  unfold tailWord_1128786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10292551922152144536451553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27446805125739052097204141 10292551922152144536451553)
  ·
    refine ⟨7719413941614108402338665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10292551922152144536451553 7719413941614108402338665)
    ·
      refine ⟨5789560456210581301753999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7719413941614108402338665 5789560456210581301753999)
      ·
        refine ⟨8684340684315871952630999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789560456210581301753999 8684340684315871952630999)
        ·
          refine ⟨13026511026473807928946499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8684340684315871952630999 13026511026473807928946499)
          ·
            refine ⟨19539766539710711893419749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13026511026473807928946499 19539766539710711893419749)
            ·
              refine ⟨3663706226195758480016203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19539766539710711893419749 3663706226195758480016203)
              ·
                refine ⟨5495559339293637720024305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663706226195758480016203 5495559339293637720024305)
                ·
                  refine ⟨4121669504470228290018229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5495559339293637720024305 4121669504470228290018229)
                  ·
                    refine ⟨386406516044083902189209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4121669504470228290018229 386406516044083902189209)
                    ·
                      rfl

theorem cell22_1128786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1128786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128786 prefixEnd_1128786 := by exact prefixLift 1128786
  have htrace : WordTrace (prefixWord ++ tailWord_1128786) baseStart_1128786 baseEnd_1128786 := by
    simpa [prefixWord, tailWord_1128786, baseEnd_1128786] using wordTrace_append hprefix tailTrace_1128786
  have hstable : (prefixWord ++ tailWord_1128786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128786).length < 2 ^ (prefixWord ++ tailWord_1128786).sum := by decide
  have hdescent : baseEnd_1128786 < baseStart_1128786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128818 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1128818 : Nat := 118140960795 + 1128818 * 2 ^ 59
def prefixEnd_1128818 : Nat := 4983230072969 + 3 ^ 40 * 1128818 * 2
def baseEnd_1128818 : Nat := 386417470298046485389111

theorem tailTrace_1128818 : CollatzResearch.WordTrace tailWord_1128818 prefixEnd_1128818 386417470298046485389111 := by
  unfold tailWord_1128818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10292843706123161902742777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27447583216328431740647405 10292843706123161902742777)
  ·
    refine ⟨7719632779592371427057083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10292843706123161902742777 7719632779592371427057083)
    ·
      refine ⟨11579449169388557140585625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7719632779592371427057083 11579449169388557140585625)
      ·
        refine ⟨8684586877041417855439219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11579449169388557140585625 8684586877041417855439219)
        ·
          refine ⟨13026880315562126783158829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8684586877041417855439219 13026880315562126783158829)
          ·
            refine ⟨4885080118335797543684561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13026880315562126783158829 4885080118335797543684561)
            ·
              refine ⟨3663810088751848157763421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4885080118335797543684561 3663810088751848157763421)
              ·
                refine ⟨1373928783281943059161283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3663810088751848157763421 1373928783281943059161283)
                ·
                  refine ⟨2060893174922914588741925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373928783281943059161283 2060893174922914588741925)
                  ·
                    refine ⟨386417470298046485389111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060893174922914588741925 386417470298046485389111)
                    ·
                      rfl

theorem cell22_1128818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1128818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128818 prefixEnd_1128818 := by exact prefixLift 1128818
  have htrace : WordTrace (prefixWord ++ tailWord_1128818) baseStart_1128818 baseEnd_1128818 := by
    simpa [prefixWord, tailWord_1128818, baseEnd_1128818] using wordTrace_append hprefix tailTrace_1128818
  have hstable : (prefixWord ++ tailWord_1128818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128818).length < 2 ^ (prefixWord ++ tailWord_1128818).sum := by decide
  have hdescent : baseEnd_1128818 < baseStart_1128818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128833 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 6]
def baseStart_1128833 : Nat := 118140960795 + 1128833 * 2 ^ 59
def prefixEnd_1128833 : Nat := 4983230072969 + 3 ^ 40 * 1128833 * 2
def baseEnd_1128833 : Nat := 128807535034863815421355

theorem tailTrace_1128833 : CollatzResearch.WordTrace tailWord_1128833 prefixEnd_1128833 128807535034863815421355 := by
  unfold tailWord_1128833
  simp only [CollatzResearch.WordTrace]
  refine ⟨41171921919438305172767153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27447947946292203448511435 41171921919438305172767153)
  ·
    refine ⟨30878941439578728879575365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41171921919438305172767153 30878941439578728879575365)
    ·
      refine ⟨5789801519921011664920381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30878941439578728879575365 5789801519921011664920381)
      ·
        refine ⟨2171175569970379374345143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5789801519921011664920381 2171175569970379374345143)
        ·
          refine ⟨3256763354955569061517715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171175569970379374345143 3256763354955569061517715)
          ·
            refine ⟨4885145032433353592276573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256763354955569061517715 4885145032433353592276573)
            ·
              refine ⟨1831929387162507597103715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4885145032433353592276573 1831929387162507597103715)
              ·
                refine ⟨2747894080743761395655573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831929387162507597103715 2747894080743761395655573)
                ·
                  refine ⟨128807535034863815421355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2747894080743761395655573 128807535034863815421355)
                  ·
                    rfl

theorem cell22_1128833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_1128833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128833 prefixEnd_1128833 := by exact prefixLift 1128833
  have htrace : WordTrace (prefixWord ++ tailWord_1128833) baseStart_1128833 baseEnd_1128833 := by
    simpa [prefixWord, tailWord_1128833, baseEnd_1128833] using wordTrace_append hprefix tailTrace_1128833
  have hstable : (prefixWord ++ tailWord_1128833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128833).length < 2 ^ (prefixWord ++ tailWord_1128833).sum := by decide
  have hdescent : baseEnd_1128833 < baseStart_1128833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128852 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1128852 : Nat := 118140960795 + 1128852 * 2 ^ 59
def prefixEnd_1128852 : Nat := 4983230072969 + 3 ^ 40 * 1128852 * 2
def baseEnd_1128852 : Nat := 386429109192881730039007

theorem tailTrace_1128852 : CollatzResearch.WordTrace tailWord_1128852 prefixEnd_1128852 386429109192881730039007 := by
  unfold tailWord_1128852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20586307453184735708854405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27448409937579647611805873 20586307453184735708854405)
  ·
    refine ⟨3859932647472137945410201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20586307453184735708854405 3859932647472137945410201)
    ·
      refine ⟨2894949485604103459057651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3859932647472137945410201 2894949485604103459057651)
      ·
        refine ⟨4342424228406155188586477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894949485604103459057651 4342424228406155188586477)
        ·
          refine ⟨1628409085652308195719929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4342424228406155188586477 1628409085652308195719929)
          ·
            refine ⟨1221306814239231146789947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628409085652308195719929 1221306814239231146789947)
            ·
              refine ⟨1831960221358846720184921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221306814239231146789947 1831960221358846720184921)
              ·
                refine ⟨1373970166019135040138691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1831960221358846720184921 1373970166019135040138691)
                ·
                  refine ⟨2060955249028702560208037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373970166019135040138691 2060955249028702560208037)
                  ·
                    refine ⟨386429109192881730039007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060955249028702560208037 386429109192881730039007)
                    ·
                      rfl

theorem cell22_1128852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1128852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128852 prefixEnd_1128852 := by exact prefixLift 1128852
  have htrace : WordTrace (prefixWord ++ tailWord_1128852) baseStart_1128852 baseEnd_1128852 := by
    simpa [prefixWord, tailWord_1128852, baseEnd_1128852] using wordTrace_append hprefix tailTrace_1128852
  have hstable : (prefixWord ++ tailWord_1128852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128852).length < 2 ^ (prefixWord ++ tailWord_1128852).sum := by decide
  have hdescent : baseEnd_1128852 < baseStart_1128852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128863 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 2, 4]
def baseStart_1128863 : Nat := 118140960795 + 1128863 * 2 ^ 59
def prefixEnd_1128863 : Nat := 4983230072969 + 3 ^ 40 * 1128863 * 2
def baseEnd_1128863 : Nat := 386432874717681368013973

theorem tailTrace_1128863 : CollatzResearch.WordTrace tailWord_1128863 prefixEnd_1128863 386432874717681368013973 := by
  unfold tailWord_1128863
  simp only [CollatzResearch.WordTrace]
  refine ⟨41173016109329620296359243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27448677406219746864239495 41173016109329620296359243)
  ·
    refine ⟨61759524163994430444538865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41173016109329620296359243 61759524163994430444538865)
    ·
      refine ⟨46319643122995822833404149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61759524163994430444538865 46319643122995822833404149)
      ·
        refine ⟨4342466542780858390631639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46319643122995822833404149 4342466542780858390631639)
        ·
          refine ⟨6513699814171287585947459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342466542780858390631639 6513699814171287585947459)
          ·
            refine ⟨9770549721256931378921189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6513699814171287585947459 9770549721256931378921189)
            ·
              refine ⟨1831978072735674633547723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9770549721256931378921189 1831978072735674633547723)
              ·
                refine ⟨2747967109103511950321585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831978072735674633547723 2747967109103511950321585)
                ·
                  refine ⟨2060975331827633962741189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747967109103511950321585 2060975331827633962741189)
                  ·
                    refine ⟨386432874717681368013973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060975331827633962741189 386432874717681368013973)
                    ·
                      rfl

theorem cell22_1128863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_1128863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128863 prefixEnd_1128863 := by exact prefixLift 1128863
  have htrace : WordTrace (prefixWord ++ tailWord_1128863) baseStart_1128863 baseEnd_1128863 := by
    simpa [prefixWord, tailWord_1128863, baseEnd_1128863] using wordTrace_append hprefix tailTrace_1128863
  have hstable : (prefixWord ++ tailWord_1128863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128863).length < 2 ^ (prefixWord ++ tailWord_1128863).sum := by decide
  have hdescent : baseEnd_1128863 < baseStart_1128863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128865 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1128865 : Nat := 118140960795 + 1128865 * 2 ^ 59
def prefixEnd_1128865 : Nat := 4983230072969 + 3 ^ 40 * 1128865 * 2
def baseEnd_1128865 : Nat := 386433559358554029463967

theorem tailTrace_1128865 : CollatzResearch.WordTrace tailWord_1128865 prefixEnd_1128865 386433559358554029463967 := by
  unfold tailWord_1128865
  simp only [CollatzResearch.WordTrace]
  refine ⟨41173089055322374637932049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27448726036881583091954699 41173089055322374637932049)
  ·
    refine ⟨30879816791491780978449037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41173089055322374637932049 30879816791491780978449037)
    ·
      refine ⟨11579931296809417866918389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30879816791491780978449037 11579931296809417866918389)
      ·
        refine ⟨1085618559075882925023599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11579931296809417866918389 1085618559075882925023599)
        ·
          refine ⟨1628427838613824387535399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085618559075882925023599 1628427838613824387535399)
          ·
            refine ⟨2442641757920736581303099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628427838613824387535399 2442641757920736581303099)
            ·
              refine ⟨3663962636881104871954649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442641757920736581303099 3663962636881104871954649)
              ·
                refine ⟨2747971977660828653965987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3663962636881104871954649 2747971977660828653965987)
                ·
                  refine ⟨4121957966491242980948981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747971977660828653965987 4121957966491242980948981)
                  ·
                    refine ⟨386433559358554029463967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4121957966491242980948981 386433559358554029463967)
                    ·
                      rfl

theorem cell22_1128865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1128865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128865 prefixEnd_1128865 := by exact prefixLift 1128865
  have htrace : WordTrace (prefixWord ++ tailWord_1128865) baseStart_1128865 baseEnd_1128865 := by
    simpa [prefixWord, tailWord_1128865, baseEnd_1128865] using wordTrace_append hprefix tailTrace_1128865
  have hstable : (prefixWord ++ tailWord_1128865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128865).length < 2 ^ (prefixWord ++ tailWord_1128865).sum := by decide
  have hdescent : baseEnd_1128865 < baseStart_1128865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128884 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1128884 : Nat := 118140960795 + 1128884 * 2 ^ 59
def prefixEnd_1128884 : Nat := 4983230072969 + 3 ^ 40 * 1128884 * 2
def baseEnd_1128884 : Nat := 128813354482281437746303

theorem tailTrace_1128884 : CollatzResearch.WordTrace tailWord_1128884 prefixEnd_1128884 128813354482281437746303 := by
  unfold tailWord_1128884
  simp only [CollatzResearch.WordTrace]
  refine ⟨20586891021126770441436853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27449188028169027255249137 20586891021126770441436853)
  ·
    refine ⟨1930021033230634728884705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20586891021126770441436853 1930021033230634728884705)
    ·
      refine ⟨1447515774922976046663529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1930021033230634728884705 1447515774922976046663529)
      ·
        refine ⟨1085636831192232034997647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447515774922976046663529 1085636831192232034997647)
        ·
          refine ⟨1628455246788348052496471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085636831192232034997647 1628455246788348052496471)
          ·
            refine ⟨2442682870182522078744707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628455246788348052496471 2442682870182522078744707)
            ·
              refine ⟨3664024305273783118117061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442682870182522078744707 3664024305273783118117061)
              ·
                refine ⟨687004557238834334646949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3664024305273783118117061 687004557238834334646949)
                ·
                  refine ⟨128813354482281437746303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687004557238834334646949 128813354482281437746303)
                  ·
                    rfl

theorem cell22_1128884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1128884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128884 prefixEnd_1128884 := by exact prefixLift 1128884
  have htrace : WordTrace (prefixWord ++ tailWord_1128884) baseStart_1128884 baseEnd_1128884 := by
    simpa [prefixWord, tailWord_1128884, baseEnd_1128884] using wordTrace_append hprefix tailTrace_1128884
  have hstable : (prefixWord ++ tailWord_1128884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128884).length < 2 ^ (prefixWord ++ tailWord_1128884).sum := by decide
  have hdescent : baseEnd_1128884 < baseStart_1128884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128914 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1128914 : Nat := 118140960795 + 1128914 * 2 ^ 59
def prefixEnd_1128914 : Nat := 4983230072969 + 3 ^ 40 * 1128914 * 2
def baseEnd_1128914 : Nat := 386450333059934234988817

theorem tailTrace_1128914 : CollatzResearch.WordTrace tailWord_1128914 prefixEnd_1128914 386450333059934234988817 := by
  unfold tailWord_1128914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293719058036214001616449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27449917488096570670977197 10293719058036214001616449)
  ·
    refine ⟨7720289293527160501212337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10293719058036214001616449 7720289293527160501212337)
    ·
      refine ⟨5790216970145370375909253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7720289293527160501212337 5790216970145370375909253)
      ·
        refine ⟨1085665681902256945482985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5790216970145370375909253 1085665681902256945482985)
        ·
          refine ⟨814249261426692709112239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085665681902256945482985 814249261426692709112239)
          ·
            refine ⟨1221373892140039063668359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814249261426692709112239 1221373892140039063668359)
            ·
              refine ⟨1832060838210058595502539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221373892140039063668359 1832060838210058595502539)
              ·
                refine ⟨2748091257315087893253809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832060838210058595502539 2748091257315087893253809)
                ·
                  refine ⟨2061068442986315919940357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748091257315087893253809 2061068442986315919940357)
                  ·
                    refine ⟨386450333059934234988817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2061068442986315919940357 386450333059934234988817)
                    ·
                      rfl

theorem cell22_1128914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1128914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128914 prefixEnd_1128914 := by exact prefixLift 1128914
  have htrace : WordTrace (prefixWord ++ tailWord_1128914) baseStart_1128914 baseEnd_1128914 := by
    simpa [prefixWord, tailWord_1128914, baseEnd_1128914] using wordTrace_append hprefix tailTrace_1128914
  have hstable : (prefixWord ++ tailWord_1128914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128914).length < 2 ^ (prefixWord ++ tailWord_1128914).sum := by decide
  have hdescent : baseEnd_1128914 < baseStart_1128914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128921 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1128921 : Nat := 118140960795 + 1128921 * 2 ^ 59
def prefixEnd_1128921 : Nat := 4983230072969 + 3 ^ 40 * 1128921 * 2
def baseEnd_1128921 : Nat := 386452729302988550063795

theorem tailTrace_1128921 : CollatzResearch.WordTrace tailWord_1128921 prefixEnd_1128921 386452729302988550063795 := by
  unfold tailWord_1128921
  simp only [CollatzResearch.WordTrace]
  refine ⟨41175131543119496201970617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27450087695412997467980411 41175131543119496201970617)
  ·
    refine ⟨30881348657339622151477963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41175131543119496201970617 30881348657339622151477963)
    ·
      refine ⟨46322022986009433227216945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30881348657339622151477963 46322022986009433227216945)
      ·
        refine ⟨34741517239507074920412709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46322022986009433227216945 34741517239507074920412709)
        ·
          refine ⟨6514034482407576547577383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34741517239507074920412709 6514034482407576547577383)
          ·
            refine ⟨9771051723611364821366075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514034482407576547577383 9771051723611364821366075)
            ·
              refine ⟨14656577585417047232049113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9771051723611364821366075 14656577585417047232049113)
              ·
                refine ⟨10992433189062785424036835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14656577585417047232049113 10992433189062785424036835)
                ·
                  refine ⟨16488649783594178136055253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10992433189062785424036835 16488649783594178136055253)
                  ·
                    refine ⟨386452729302988550063795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16488649783594178136055253 386452729302988550063795)
                    ·
                      rfl

theorem cell22_1128921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1128921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128921 prefixEnd_1128921 := by exact prefixLift 1128921
  have htrace : WordTrace (prefixWord ++ tailWord_1128921) baseStart_1128921 baseEnd_1128921 := by
    simpa [prefixWord, tailWord_1128921, baseEnd_1128921] using wordTrace_append hprefix tailTrace_1128921
  have hstable : (prefixWord ++ tailWord_1128921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128921).length < 2 ^ (prefixWord ++ tailWord_1128921).sum := by decide
  have hdescent : baseEnd_1128921 < baseStart_1128921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128927 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 1, 3]
def baseStart_1128927 : Nat := 118140960795 + 1128927 * 2 ^ 59
def prefixEnd_1128927 : Nat := 4983230072969 + 3 ^ 40 * 1128927 * 2
def baseEnd_1128927 : Nat := 386454783225606534413777

theorem tailTrace_1128927 : CollatzResearch.WordTrace tailWord_1128927 prefixEnd_1128927 386454783225606534413777 := by
  unfold tailWord_1128927
  simp only [CollatzResearch.WordTrace]
  refine ⟨41175350381097759226689035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27450233587398506151126023 41175350381097759226689035)
  ·
    refine ⟨61763025571646638840033553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41175350381097759226689035 61763025571646638840033553)
    ·
      refine ⟨46322269178734979130025165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61763025571646638840033553 46322269178734979130025165)
      ·
        refine ⟨17370850942025617173759437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46322269178734979130025165 17370850942025617173759437)
        ·
          refine ⟨6514069103259606440159789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17370850942025617173759437 6514069103259606440159789)
          ·
            refine ⟨2442775913722352415059921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6514069103259606440159789 2442775913722352415059921)
            ·
              refine ⟨1832081935291764311294941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442775913722352415059921 1832081935291764311294941)
              ·
                refine ⟨687030725734411616735603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1832081935291764311294941 687030725734411616735603)
                ·
                  refine ⟨1030546088601617425103405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687030725734411616735603 1030546088601617425103405)
                  ·
                    refine ⟨386454783225606534413777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030546088601617425103405 386454783225606534413777)
                    ·
                      rfl

theorem cell22_1128927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_1128927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128927 prefixEnd_1128927 := by exact prefixLift 1128927
  have htrace : WordTrace (prefixWord ++ tailWord_1128927) baseStart_1128927 baseEnd_1128927 := by
    simpa [prefixWord, tailWord_1128927, baseEnd_1128927] using wordTrace_append hprefix tailTrace_1128927
  have hstable : (prefixWord ++ tailWord_1128927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128927).length < 2 ^ (prefixWord ++ tailWord_1128927).sum := by decide
  have hdescent : baseEnd_1128927 < baseStart_1128927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128938 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1128938 : Nat := 118140960795 + 1128938 * 2 ^ 59
def prefixEnd_1128938 : Nat := 4983230072969 + 3 ^ 40 * 1128938 * 2
def baseEnd_1128938 : Nat := 386458548750406172388743

theorem tailTrace_1128938 : CollatzResearch.WordTrace tailWord_1128938 prefixEnd_1128938 386458548750406172388743 := by
  unfold tailWord_1128938
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293937896014477026334867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27450501056038605403559645 10293937896014477026334867)
  ·
    refine ⟨15440906844021715539502301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10293937896014477026334867 15440906844021715539502301)
    ·
      refine ⟨5790340066508143327313363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15440906844021715539502301 5790340066508143327313363)
      ·
        refine ⟨8685510099762214990970045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5790340066508143327313363 8685510099762214990970045)
        ·
          refine ⟨3257066287410830621613767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8685510099762214990970045 3257066287410830621613767)
          ·
            refine ⟨4885599431116245932420651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257066287410830621613767 4885599431116245932420651)
            ·
              refine ⟨7328399146674368898630977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885599431116245932420651 7328399146674368898630977)
              ·
                refine ⟨5496299360005776673973233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7328399146674368898630977 5496299360005776673973233)
                ·
                  refine ⟨4122224520004332505479925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496299360005776673973233 4122224520004332505479925)
                  ·
                    refine ⟨386458548750406172388743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4122224520004332505479925 386458548750406172388743)
                    ·
                      rfl

theorem cell22_1128938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1128938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128938 prefixEnd_1128938 := by exact prefixLift 1128938
  have htrace : WordTrace (prefixWord ++ tailWord_1128938) baseStart_1128938 baseEnd_1128938 := by
    simpa [prefixWord, tailWord_1128938, baseEnd_1128938] using wordTrace_append hprefix tailTrace_1128938
  have hstable : (prefixWord ++ tailWord_1128938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128938).length < 2 ^ (prefixWord ++ tailWord_1128938).sum := by decide
  have hdescent : baseEnd_1128938 < baseStart_1128938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128970 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1128970 : Nat := 118140960795 + 1128970 * 2 ^ 59
def prefixEnd_1128970 : Nat := 4983230072969 + 3 ^ 40 * 1128970 * 2
def baseEnd_1128970 : Nat := 386469503004368755588645

theorem tailTrace_1128970 : CollatzResearch.WordTrace tailWord_1128970 prefixEnd_1128970 386469503004368755588645 := by
  unfold tailWord_1128970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10294229679985494392626091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27451279146627985047002909 10294229679985494392626091)
  ·
    refine ⟨15441344519978241588939137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10294229679985494392626091 15441344519978241588939137)
    ·
      refine ⟨11581008389983681191704353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15441344519978241588939137 11581008389983681191704353)
      ·
        refine ⟨8685756292487760893778265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11581008389983681191704353 8685756292487760893778265)
        ·
          refine ⟨6514317219365820670333699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8685756292487760893778265 6514317219365820670333699)
          ·
            refine ⟨9771475829048731005500549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514317219365820670333699 9771475829048731005500549)
            ·
              refine ⟨1832151717946637063531353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9771475829048731005500549 1832151717946637063531353)
              ·
                refine ⟨1374113788459977797648515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832151717946637063531353 1374113788459977797648515)
                ·
                  refine ⟨2061170682689966696472773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374113788459977797648515 2061170682689966696472773)
                  ·
                    refine ⟨386469503004368755588645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2061170682689966696472773 386469503004368755588645)
                    ·
                      rfl

theorem cell22_1128970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1128970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1128970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1128970 prefixEnd_1128970 := by exact prefixLift 1128970
  have htrace : WordTrace (prefixWord ++ tailWord_1128970) baseStart_1128970 baseEnd_1128970 := by
    simpa [prefixWord, tailWord_1128970, baseEnd_1128970] using wordTrace_append hprefix tailTrace_1128970
  have hstable : (prefixWord ++ tailWord_1128970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128970).length < 2 ^ (prefixWord ++ tailWord_1128970).sum := by decide
  have hdescent : baseEnd_1128970 < baseStart_1128970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129013 : List Nat := [1, 3, 3, 1, 1, 2, 4, 7]
def baseStart_1129013 : Nat := 118140960795 + 1129013 * 2 ^ 59
def prefixEnd_1129013 : Nat := 4983230072969 + 3 ^ 40 * 1129013 * 2
def baseEnd_1129013 : Nat := 42942691420347886307057

theorem tailTrace_1129013 : CollatzResearch.WordTrace tailWord_1129013 prefixEnd_1129013 42942691420347886307057 := by
  unfold tailWord_1129013
  simp only [CollatzResearch.WordTrace]
  refine ⟨41178487058786195914319693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27452324705857463942879795 41178487058786195914319693)
  ·
    refine ⟨15441932647044823467869885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41178487058786195914319693 15441932647044823467869885)
    ·
      refine ⟨5790724742641808800451207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15441932647044823467869885 5790724742641808800451207)
      ·
        refine ⟨8686087113962713200676811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5790724742641808800451207 8686087113962713200676811)
        ·
          refine ⟨13029130670944069801015217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8686087113962713200676811 13029130670944069801015217)
          ·
            refine ⟨9771848003208052350761413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13029130670944069801015217 9771848003208052350761413)
            ·
              refine ⟨1832221500601509815767765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9771848003208052350761413 1832221500601509815767765)
              ·
                refine ⟨42942691420347886307057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1832221500601509815767765 42942691420347886307057)
                ·
                  rfl

theorem cell22_1129013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 7].length) (baseStart_1129013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129013 prefixEnd_1129013 := by exact prefixLift 1129013
  have htrace : WordTrace (prefixWord ++ tailWord_1129013) baseStart_1129013 baseEnd_1129013 := by
    simpa [prefixWord, tailWord_1129013, baseEnd_1129013] using wordTrace_append hprefix tailTrace_1129013
  have hstable : (prefixWord ++ tailWord_1129013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129013).length < 2 ^ (prefixWord ++ tailWord_1129013).sum := by decide
  have hdescent : baseEnd_1129013 < baseStart_1129013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129135 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 1, 5]
def baseStart_1129135 : Nat := 118140960795 + 1129135 * 2 ^ 59
def prefixEnd_1129135 : Nat := 4983230072969 + 3 ^ 40 * 1129135 * 2
def baseEnd_1129135 : Nat := 386525985876363325213139

theorem tailTrace_1129135 : CollatzResearch.WordTrace tailWord_1129135 prefixEnd_1129135 386525985876363325213139 := by
  unfold tailWord_1129135
  simp only [CollatzResearch.WordTrace]
  refine ⟨41182936764344210750260859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27455291176229473833507239 41182936764344210750260859)
  ·
    refine ⟨61774405146516316125391289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41182936764344210750260859 61774405146516316125391289)
    ·
      refine ⟨46330803859887237094043467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61774405146516316125391289 46330803859887237094043467)
      ·
        refine ⟨69496205789830855641065201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46330803859887237094043467 69496205789830855641065201)
        ·
          refine ⟨52122154342373141730798901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69496205789830855641065201 52122154342373141730798901)
          ·
            refine ⟨4886451969597482037262397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52122154342373141730798901 4886451969597482037262397)
            ·
              refine ⟨1832419488599055763973399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4886451969597482037262397 1832419488599055763973399)
              ·
                refine ⟨2748629232898583645960099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832419488599055763973399 2748629232898583645960099)
                ·
                  refine ⟨4122943849347875468940149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748629232898583645960099 4122943849347875468940149)
                  ·
                    refine ⟨386525985876363325213139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4122943849347875468940149 386525985876363325213139)
                    ·
                      rfl

theorem cell22_1129135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_1129135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129135 prefixEnd_1129135 := by exact prefixLift 1129135
  have htrace : WordTrace (prefixWord ++ tailWord_1129135) baseStart_1129135 baseEnd_1129135 := by
    simpa [prefixWord, tailWord_1129135, baseEnd_1129135] using wordTrace_append hprefix tailTrace_1129135
  have hstable : (prefixWord ++ tailWord_1129135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129135).length < 2 ^ (prefixWord ++ tailWord_1129135).sum := by decide
  have hdescent : baseEnd_1129135 < baseStart_1129135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129150 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1129150 : Nat := 118140960795 + 1129150 * 2 ^ 59
def prefixEnd_1129150 : Nat := 4983230072969 + 3 ^ 40 * 1129150 * 2
def baseEnd_1129150 : Nat := 386531120682908286088093

theorem tailTrace_1129150 : CollatzResearch.WordTrace tailWord_1129150 prefixEnd_1129150 386531120682908286088093 := by
  unfold tailWord_1129150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147935482411233539007113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27455655906193245541371269 5147935482411233539007113)
  ·
    refine ⟨3860951611808425154255335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5147935482411233539007113 3860951611808425154255335)
    ·
      refine ⟨5791427417712637731383003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860951611808425154255335 5791427417712637731383003)
      ·
        refine ⟨8687141126568956597074505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791427417712637731383003 8687141126568956597074505)
        ·
          refine ⟨6515355844926717447805879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8687141126568956597074505 6515355844926717447805879)
          ·
            refine ⟨9773033767390076171708819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515355844926717447805879 9773033767390076171708819)
            ·
              refine ⟨14659550651085114257563229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9773033767390076171708819 14659550651085114257563229)
              ·
                refine ⟨5497331494156917846586211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14659550651085114257563229 5497331494156917846586211)
                ·
                  refine ⟨8245997241235376769879317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5497331494156917846586211 8245997241235376769879317)
                  ·
                    refine ⟨386531120682908286088093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8245997241235376769879317 386531120682908286088093)
                    ·
                      rfl

theorem cell22_1129150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1129150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129150 prefixEnd_1129150 := by exact prefixLift 1129150
  have htrace : WordTrace (prefixWord ++ tailWord_1129150) baseStart_1129150 baseEnd_1129150 := by
    simpa [prefixWord, tailWord_1129150, baseEnd_1129150] using wordTrace_append hprefix tailTrace_1129150
  have hstable : (prefixWord ++ tailWord_1129150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129150).length < 2 ^ (prefixWord ++ tailWord_1129150).sum := by decide
  have hdescent : baseEnd_1129150 < baseStart_1129150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129197 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1129197 : Nat := 118140960795 + 1129197 * 2 ^ 59
def prefixEnd_1129197 : Nat := 4983230072969 + 3 ^ 40 * 1129197 * 2
def baseEnd_1129197 : Nat := 386547209743415830162949

theorem tailTrace_1129197 : CollatzResearch.WordTrace tailWord_1129197 prefixEnd_1129197 386547209743415830162949 := by
  unfold tailWord_1129197
  simp only [CollatzResearch.WordTrace]
  refine ⟨41185198090119595339017845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27456798726746396892678563 41185198090119595339017845)
  ·
    refine ⟨3861112320948712063032923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41185198090119595339017845 3861112320948712063032923)
    ·
      refine ⟨5791668481423068094549385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861112320948712063032923 5791668481423068094549385)
      ·
        refine ⟨4343751361067301070912039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5791668481423068094549385 4343751361067301070912039)
        ·
          refine ⟨6515627041600951606368059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343751361067301070912039 6515627041600951606368059)
          ·
            refine ⟨9773440562401427409552089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515627041600951606368059 9773440562401427409552089)
            ·
              refine ⟨7330080421801070557164067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9773440562401427409552089 7330080421801070557164067)
              ·
                refine ⟨10995120632701605835746101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7330080421801070557164067 10995120632701605835746101)
                ·
                  refine ⟨1030792559315775547101197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10995120632701605835746101 1030792559315775547101197)
                  ·
                    refine ⟨386547209743415830162949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030792559315775547101197 386547209743415830162949)
                    ·
                      rfl

theorem cell22_1129197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1129197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129197 prefixEnd_1129197 := by exact prefixLift 1129197
  have htrace : WordTrace (prefixWord ++ tailWord_1129197) baseStart_1129197 baseEnd_1129197 := by
    simpa [prefixWord, tailWord_1129197, baseEnd_1129197] using wordTrace_append hprefix tailTrace_1129197
  have hstable : (prefixWord ++ tailWord_1129197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129197).length < 2 ^ (prefixWord ++ tailWord_1129197).sum := by decide
  have hdescent : baseEnd_1129197 < baseStart_1129197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129274 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_1129274 : Nat := 118140960795 + 1129274 * 2 ^ 59
def prefixEnd_1129274 : Nat := 4983230072969 + 3 ^ 40 * 1129274 * 2
def baseEnd_1129274 : Nat := 386573568417013295987713

theorem tailTrace_1129274 : CollatzResearch.WordTrace tailWord_1129274 prefixEnd_1129274 386573568417013295987713 := by
  unfold tailWord_1129274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297001627710159372392719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27458671007227091659713917 10297001627710159372392719)
  ·
    refine ⟨15445502441565239058589079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10297001627710159372392719 15445502441565239058589079)
    ·
      refine ⟨23168253662347858587883619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15445502441565239058589079 23168253662347858587883619)
      ·
        refine ⟨34752380493521787881825429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23168253662347858587883619 34752380493521787881825429)
        ·
          refine ⟨1629017835633833806960567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34752380493521787881825429 1629017835633833806960567)
          ·
            refine ⟨2443526753450750710440851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629017835633833806960567 2443526753450750710440851)
            ·
              refine ⟨3665290130176126065661277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443526753450750710440851 3665290130176126065661277)
              ·
                refine ⟨1374483798816047274622979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3665290130176126065661277 1374483798816047274622979)
                ·
                  refine ⟨2061725698224070911934469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374483798816047274622979 2061725698224070911934469)
                  ·
                    refine ⟨386573568417013295987713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2061725698224070911934469 386573568417013295987713)
                    ·
                      rfl

theorem cell22_1129274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_1129274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129274 prefixEnd_1129274 := by exact prefixLift 1129274
  have htrace : WordTrace (prefixWord ++ tailWord_1129274) baseStart_1129274 baseEnd_1129274 := by
    simpa [prefixWord, tailWord_1129274, baseEnd_1129274] using wordTrace_append hprefix tailTrace_1129274
  have hstable : (prefixWord ++ tailWord_1129274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129274).length < 2 ^ (prefixWord ++ tailWord_1129274).sum := by decide
  have hdescent : baseEnd_1129274 < baseStart_1129274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129317 : List Nat := [1, 3, 1, 3, 1, 1, 6, 6]
def baseStart_1129317 : Nat := 118140960795 + 1129317 * 2 ^ 59
def prefixEnd_1129317 : Nat := 4983230072969 + 3 ^ 40 * 1129317 * 2
def baseEnd_1129317 : Nat := 42954254243975057462509

theorem tailTrace_1129317 : CollatzResearch.WordTrace tailWord_1129317 prefixEnd_1129317 42954254243975057462509 := by
  unfold tailWord_1129317
  simp only [CollatzResearch.WordTrace]
  refine ⟨41189574849684855833386205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27459716566456570555590803 41189574849684855833386205)
  ·
    refine ⟨15446090568631820937519827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41189574849684855833386205 15446090568631820937519827)
    ·
      refine ⟨23169135852947731406279741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15446090568631820937519827 23169135852947731406279741)
      ·
        refine ⟨8688425944855399277354903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23169135852947731406279741 8688425944855399277354903)
        ·
          refine ⟨13032638917283098916032355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8688425944855399277354903 13032638917283098916032355)
          ·
            refine ⟨19548958375924648374048533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13032638917283098916032355 19548958375924648374048533)
            ·
              refine ⟨916357423871467892533525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19548958375924648374048533 916357423871467892533525)
              ·
                refine ⟨42954254243975057462509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 916357423871467892533525 42954254243975057462509)
                ·
                  rfl

theorem cell22_1129317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 6].length) (baseStart_1129317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129317 prefixEnd_1129317 := by exact prefixLift 1129317
  have htrace : WordTrace (prefixWord ++ tailWord_1129317) baseStart_1129317 baseEnd_1129317 := by
    simpa [prefixWord, tailWord_1129317, baseEnd_1129317] using wordTrace_append hprefix tailTrace_1129317
  have hstable : (prefixWord ++ tailWord_1129317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129317).length < 2 ^ (prefixWord ++ tailWord_1129317).sum := by decide
  have hdescent : baseEnd_1129317 < baseStart_1129317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129334 : List Nat := [5, 1, 1, 3, 1, 3, 8]
def baseStart_1129334 : Nat := 118140960795 + 1129334 * 2 ^ 59
def prefixEnd_1129334 : Nat := 4983230072969 + 3 ^ 40 * 1129334 * 2
def baseEnd_1129334 : Nat := 14318300283081227388427

theorem tailTrace_1129334 : CollatzResearch.WordTrace tailWord_1129334 prefixEnd_1129334 14318300283081227388427 := by
  unfold tailWord_1129334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574387180663954233547191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27460129927082178491170037 2574387180663954233547191)
  ·
    refine ⟨3861580770995931350320787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2574387180663954233547191 3861580770995931350320787)
    ·
      refine ⟨5792371156493897025481181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861580770995931350320787 5792371156493897025481181)
      ·
        refine ⟨2172139183685211384555443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5792371156493897025481181 2172139183685211384555443)
        ·
          refine ⟨3258208775527817076833165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172139183685211384555443 3258208775527817076833165)
          ·
            refine ⟨1221828290822931403812437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3258208775527817076833165 1221828290822931403812437)
            ·
              refine ⟨14318300283081227388427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1221828290822931403812437 14318300283081227388427)
              ·
                rfl

theorem cell22_1129334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 8].length) (baseStart_1129334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129334 prefixEnd_1129334 := by exact prefixLift 1129334
  have htrace : WordTrace (prefixWord ++ tailWord_1129334) baseStart_1129334 baseEnd_1129334 := by
    simpa [prefixWord, tailWord_1129334, baseEnd_1129334] using wordTrace_append hprefix tailTrace_1129334
  have hstable : (prefixWord ++ tailWord_1129334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129334).length < 2 ^ (prefixWord ++ tailWord_1129334).sum := by decide
  have hdescent : baseEnd_1129334 < baseStart_1129334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129349 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_1129349 : Nat := 118140960795 + 1129349 * 2 ^ 59
def prefixEnd_1129349 : Nat := 4983230072969 + 3 ^ 40 * 1129349 * 2
def baseEnd_1129349 : Nat := 386599242449738100362483

theorem tailTrace_1129349 : CollatzResearch.WordTrace tailWord_1129349 prefixEnd_1129349 386599242449738100362483 := by
  unfold tailWord_1129349
  simp only [CollatzResearch.WordTrace]
  refine ⟨41190741985568925298551101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27460494657045950199034067 41190741985568925298551101)
  ·
    refine ⟨15446528244588346986956663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41190741985568925298551101 15446528244588346986956663)
    ·
      refine ⟨23169792366882520480434995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15446528244588346986956663 23169792366882520480434995)
      ·
        refine ⟨34754688550323780720652493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23169792366882520480434995 34754688550323780720652493)
        ·
          refine ⟨13033008206371417770244685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34754688550323780720652493 13033008206371417770244685)
          ·
            refine ⟨4887378077389281663841757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13033008206371417770244685 4887378077389281663841757)
            ·
              refine ⟨1832766779020980623940659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4887378077389281663841757 1832766779020980623940659)
              ·
                refine ⟨2749150168531470935910989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832766779020980623940659 2749150168531470935910989)
                ·
                  refine ⟨1030931313199301600966621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2749150168531470935910989 1030931313199301600966621)
                  ·
                    refine ⟨386599242449738100362483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030931313199301600966621 386599242449738100362483)
                    ·
                      rfl

theorem cell22_1129349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_1129349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129349 prefixEnd_1129349 := by exact prefixLift 1129349
  have htrace : WordTrace (prefixWord ++ tailWord_1129349) baseStart_1129349 baseEnd_1129349 := by
    simpa [prefixWord, tailWord_1129349, baseEnd_1129349] using wordTrace_append hprefix tailTrace_1129349
  have hstable : (prefixWord ++ tailWord_1129349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129349).length < 2 ^ (prefixWord ++ tailWord_1129349).sum := by decide
  have hdescent : baseEnd_1129349 < baseStart_1129349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129396 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1129396 : Nat := 118140960795 + 1129396 * 2 ^ 59
def prefixEnd_1129396 : Nat := 4983230072969 + 3 ^ 40 * 1129396 * 2
def baseEnd_1129396 : Nat := 128871777170081881479113

theorem tailTrace_1129396 : CollatzResearch.WordTrace tailWord_1129396 prefixEnd_1129396 128871777170081881479113 := by
  unfold tailWord_1129396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20596228108199326162756021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27461637477599101550341361 20596228108199326162756021)
  ·
    refine ⟨1930896385143686827758377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20596228108199326162756021 1930896385143686827758377)
    ·
      refine ⟨1448172288857765120818783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1930896385143686827758377 1448172288857765120818783)
      ·
        refine ⟨2172258433286647681228175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448172288857765120818783 2172258433286647681228175)
        ·
          refine ⟨3258387649929971521842263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172258433286647681228175 3258387649929971521842263)
          ·
            refine ⟨4887581474894957282763395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258387649929971521842263 4887581474894957282763395)
            ·
              refine ⟨7331372212342435924145093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887581474894957282763395 7331372212342435924145093)
              ·
                refine ⟨1374632289814206735777205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7331372212342435924145093 1374632289814206735777205)
                ·
                  refine ⟨128871777170081881479113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1374632289814206735777205 128871777170081881479113)
                  ·
                    rfl

theorem cell22_1129396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1129396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129396 prefixEnd_1129396 := by exact prefixLift 1129396
  have htrace : WordTrace (prefixWord ++ tailWord_1129396) baseStart_1129396 baseEnd_1129396 := by
    simpa [prefixWord, tailWord_1129396, baseEnd_1129396] using wordTrace_append hprefix tailTrace_1129396
  have hstable : (prefixWord ++ tailWord_1129396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129396).length < 2 ^ (prefixWord ++ tailWord_1129396).sum := by decide
  have hdescent : baseEnd_1129396 < baseStart_1129396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129473 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1129473 : Nat := 118140960795 + 1129473 * 2 ^ 59
def prefixEnd_1129473 : Nat := 4983230072969 + 3 ^ 40 * 1129473 * 2
def baseEnd_1129473 : Nat := 386641690183843110262103

theorem tailTrace_1129473 : CollatzResearch.WordTrace tailWord_1129473 prefixEnd_1129473 386641690183843110262103 := by
  unfold tailWord_1129473
  simp only [CollatzResearch.WordTrace]
  refine ⟨41195264637119694476065073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27463509758079796317376715 41195264637119694476065073)
  ·
    refine ⟨30896448477839770857048805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41195264637119694476065073 30896448477839770857048805)
    ·
      refine ⟨5793084089594957035696651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30896448477839770857048805 5793084089594957035696651)
      ·
        refine ⟨8689626134392435553544977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793084089594957035696651 8689626134392435553544977)
        ·
          refine ⟨6517219600794326665158733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689626134392435553544977 6517219600794326665158733)
          ·
            refine ⟨2443957350297872499434525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6517219600794326665158733 2443957350297872499434525)
            ·
              refine ⟨916484006361702187287947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2443957350297872499434525 916484006361702187287947)
              ·
                refine ⟨1374726009542553280931921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916484006361702187287947 1374726009542553280931921)
                ·
                  refine ⟨1031044507156914960698941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374726009542553280931921 1031044507156914960698941)
                  ·
                    refine ⟨386641690183843110262103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031044507156914960698941 386641690183843110262103)
                    ·
                      rfl

theorem cell22_1129473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1129473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129473 prefixEnd_1129473 := by exact prefixLift 1129473
  have htrace : WordTrace (prefixWord ++ tailWord_1129473) baseStart_1129473 baseEnd_1129473 := by
    simpa [prefixWord, tailWord_1129473, baseEnd_1129473] using wordTrace_append hprefix tailTrace_1129473
  have hstable : (prefixWord ++ tailWord_1129473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129473).length < 2 ^ (prefixWord ++ tailWord_1129473).sum := by decide
  have hdescent : baseEnd_1129473 < baseStart_1129473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129486 : List Nat := [4, 1, 1, 2, 2, 4, 2, 6]
def baseStart_1129486 : Nat := 118140960795 + 1129486 * 2 ^ 59
def prefixEnd_1129486 : Nat := 4983230072969 + 3 ^ 40 * 1129486 * 2
def baseEnd_1129486 : Nat := 42960682261057267743007

theorem tailTrace_1129486 : CollatzResearch.WordTrace tailWord_1129486 prefixEnd_1129486 42960682261057267743007 := by
  unfold tailWord_1129486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149467348259074712036039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27463825857381731797525541 5149467348259074712036039)
  ·
    refine ⟨7724201022388612068054059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5149467348259074712036039 7724201022388612068054059)
    ·
      refine ⟨11586301533582918102081089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7724201022388612068054059 11586301533582918102081089)
      ·
        refine ⟨8689726150187188576560817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11586301533582918102081089 8689726150187188576560817)
        ·
          refine ⟨6517294612640391432420613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689726150187188576560817 6517294612640391432420613)
          ·
            refine ⟨1221992739870073393578865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6517294612640391432420613 1221992739870073393578865)
            ·
              refine ⟨916494554902555045184149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221992739870073393578865 916494554902555045184149)
              ·
                refine ⟨42960682261057267743007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 916494554902555045184149 42960682261057267743007)
                ·
                  rfl

theorem cell22_1129486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_1129486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129486 prefixEnd_1129486 := by exact prefixLift 1129486
  have htrace : WordTrace (prefixWord ++ tailWord_1129486) baseStart_1129486 baseEnd_1129486 := by
    simpa [prefixWord, tailWord_1129486, baseEnd_1129486] using wordTrace_append hprefix tailTrace_1129486
  have hstable : (prefixWord ++ tailWord_1129486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129486).length < 2 ^ (prefixWord ++ tailWord_1129486).sum := by decide
  have hdescent : baseEnd_1129486 < baseStart_1129486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129497 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 7]
def baseStart_1129497 : Nat := 118140960795 + 1129497 * 2 ^ 59
def prefixEnd_1129497 : Nat := 4983230072969 + 3 ^ 40 * 1129497 * 2
def baseEnd_1129497 : Nat := 128883301958105015887343

theorem tailTrace_1129497 : CollatzResearch.WordTrace tailWord_1129497 prefixEnd_1129497 128883301958105015887343 := by
  unfold tailWord_1129497
  simp only [CollatzResearch.WordTrace]
  refine ⟨41196139989032746574938745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27464093326021831049959163 41196139989032746574938745)
  ·
    refine ⟨30897104991774559931204059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41196139989032746574938745 30897104991774559931204059)
    ·
      refine ⟨46345657487661839896806089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30897104991774559931204059 46345657487661839896806089)
      ·
        refine ⟨34759243115746379922604567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46345657487661839896806089 34759243115746379922604567)
        ·
          refine ⟨52138864673619569883906851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34759243115746379922604567 52138864673619569883906851)
          ·
            refine ⟨78208297010429354825860277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52138864673619569883906851 78208297010429354825860277)
            ·
              refine ⟨7332027844727752014924401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78208297010429354825860277 7332027844727752014924401)
              ·
                refine ⟨5499020883545814011193301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7332027844727752014924401 5499020883545814011193301)
                ·
                  refine ⟨128883301958105015887343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5499020883545814011193301 128883301958105015887343)
                  ·
                    rfl

theorem cell22_1129497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_1129497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129497 prefixEnd_1129497 := by exact prefixLift 1129497
  have htrace : WordTrace (prefixWord ++ tailWord_1129497) baseStart_1129497 baseEnd_1129497 := by
    simpa [prefixWord, tailWord_1129497, baseEnd_1129497] using wordTrace_append hprefix tailTrace_1129497
  have hstable : (prefixWord ++ tailWord_1129497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129497).length < 2 ^ (prefixWord ++ tailWord_1129497).sum := by decide
  have hdescent : baseEnd_1129497 < baseStart_1129497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129527 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1129527 : Nat := 118140960795 + 1129527 * 2 ^ 59
def prefixEnd_1129527 : Nat := 4983230072969 + 3 ^ 40 * 1129527 * 2
def baseEnd_1129527 : Nat := 386660175487404969411937

theorem tailTrace_1129527 : CollatzResearch.WordTrace tailWord_1129527 prefixEnd_1129527 386660175487404969411937 := by
  unfold tailWord_1129527
  simp only [CollatzResearch.WordTrace]
  refine ⟨41197234178924061698530835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27464822785949374465687223 41197234178924061698530835)
  ·
    refine ⟨61795851268386092547796253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41197234178924061698530835 61795851268386092547796253)
    ·
      refine ⟨23173444225644784705423595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61795851268386092547796253 23173444225644784705423595)
      ·
        refine ⟨34760166338467177058135393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23173444225644784705423595 34760166338467177058135393)
        ·
          refine ⟨26070124753850382793601545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34760166338467177058135393 26070124753850382793601545)
          ·
            refine ⟨19552593565387787095201159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26070124753850382793601545 19552593565387787095201159)
            ·
              refine ⟨29328890348081680642801739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19552593565387787095201159 29328890348081680642801739)
              ·
                refine ⟨43993335522122520964202609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29328890348081680642801739 43993335522122520964202609)
                ·
                  refine ⟨32995001641591890723151957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43993335522122520964202609 32995001641591890723151957)
                  ·
                    refine ⟨386660175487404969411937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32995001641591890723151957 386660175487404969411937)
                    ·
                      rfl

theorem cell22_1129527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1129527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129527 prefixEnd_1129527 := by exact prefixLift 1129527
  have htrace : WordTrace (prefixWord ++ tailWord_1129527) baseStart_1129527 baseEnd_1129527 := by
    simpa [prefixWord, tailWord_1129527, baseEnd_1129527] using wordTrace_append hprefix tailTrace_1129527
  have hstable : (prefixWord ++ tailWord_1129527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129527).length < 2 ^ (prefixWord ++ tailWord_1129527).sum := by decide
  have hdescent : baseEnd_1129527 < baseStart_1129527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129544 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1129544 : Nat := 118140960795 + 1129544 * 2 ^ 59
def prefixEnd_1129544 : Nat := 4983230072969 + 3 ^ 40 * 1129544 * 2
def baseEnd_1129544 : Nat := 386665994934822591736885

theorem tailTrace_1129544 : CollatzResearch.WordTrace tailWord_1129544 prefixEnd_1129544 386665994934822591736885 := by
  unfold tailWord_1129544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598927109931236800949843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27465236146574982401266457 20598927109931236800949843)
  ·
    refine ⟨30898390664896855201424765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20598927109931236800949843 30898390664896855201424765)
    ·
      refine ⟨11586896499336320700534287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30898390664896855201424765 11586896499336320700534287)
      ·
        refine ⟨17380344749004481050801431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11586896499336320700534287 17380344749004481050801431)
        ·
          refine ⟨26070517123506721576202147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17380344749004481050801431 26070517123506721576202147)
          ·
            refine ⟨39105775685260082364303221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26070517123506721576202147 39105775685260082364303221)
            ·
              refine ⟨3666166470493132721653427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39105775685260082364303221 3666166470493132721653427)
              ·
                refine ⟨5499249705739699082480141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666166470493132721653427 5499249705739699082480141)
                ·
                  refine ⟨2062218639652387155930053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5499249705739699082480141 2062218639652387155930053)
                  ·
                    refine ⟨386665994934822591736885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2062218639652387155930053 386665994934822591736885)
                    ·
                      rfl

theorem cell22_1129544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1129544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129544 prefixEnd_1129544 := by exact prefixLift 1129544
  have htrace : WordTrace (prefixWord ++ tailWord_1129544) baseStart_1129544 baseEnd_1129544 := by
    simpa [prefixWord, tailWord_1129544, baseEnd_1129544] using wordTrace_append hprefix tailTrace_1129544
  have hstable : (prefixWord ++ tailWord_1129544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129544).length < 2 ^ (prefixWord ++ tailWord_1129544).sum := by decide
  have hdescent : baseEnd_1129544 < baseStart_1129544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129591 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 2, 3]
def baseStart_1129591 : Nat := 118140960795 + 1129591 * 2 ^ 59
def prefixEnd_1129591 : Nat := 4983230072969 + 3 ^ 40 * 1129591 * 2
def baseEnd_1129591 : Nat := 386682083995330135811741

theorem tailTrace_1129591 : CollatzResearch.WordTrace tailWord_1129591 prefixEnd_1129591 386682083995330135811741 := by
  unfold tailWord_1129591
  simp only [CollatzResearch.WordTrace]
  refine ⟨41199568450692200628860627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27466378967128133752573751 41199568450692200628860627)
  ·
    refine ⟨61799352676038300943290941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41199568450692200628860627 61799352676038300943290941)
    ·
      refine ⟨23174757253514362853734103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61799352676038300943290941 23174757253514362853734103)
      ·
        refine ⟨34762135880271544280601155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23174757253514362853734103 34762135880271544280601155)
        ·
          refine ⟨52143203820407316420901733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34762135880271544280601155 52143203820407316420901733)
          ·
            refine ⟨9776850716326371828919075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52143203820407316420901733 9776850716326371828919075)
            ·
              refine ⟨14665276074489557743378613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9776850716326371828919075 14665276074489557743378613)
              ·
                refine ⟨1374869631983396038441745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14665276074489557743378613 1374869631983396038441745)
                ·
                  refine ⟨1031152223987547028831309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374869631983396038441745 1031152223987547028831309)
                  ·
                    refine ⟨386682083995330135811741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031152223987547028831309 386682083995330135811741)
                    ·
                      rfl

theorem cell22_1129591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_1129591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129591 prefixEnd_1129591 := by exact prefixLift 1129591
  have htrace : WordTrace (prefixWord ++ tailWord_1129591) baseStart_1129591 baseEnd_1129591 := by
    simpa [prefixWord, tailWord_1129591, baseEnd_1129591] using wordTrace_append hprefix tailTrace_1129591
  have hstable : (prefixWord ++ tailWord_1129591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129591).length < 2 ^ (prefixWord ++ tailWord_1129591).sum := by decide
  have hdescent : baseEnd_1129591 < baseStart_1129591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129642 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1129642 : Nat := 118140960795 + 1129642 * 2 ^ 59
def prefixEnd_1129642 : Nat := 4983230072969 + 3 ^ 40 * 1129642 * 2
def baseEnd_1129642 : Nat := 386699542337583002786585

theorem tailTrace_1129642 : CollatzResearch.WordTrace tailWord_1129642 prefixEnd_1129642 386699542337583002786585 := by
  unfold tailWord_1129642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10300357143376859084741795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27467619049004957559311453 10300357143376859084741795)
  ·
    refine ⟨15450535715065288627112693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10300357143376859084741795 15450535715065288627112693)
    ·
      refine ⟨1448487723287370808791815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15450535715065288627112693 1448487723287370808791815)
      ·
        refine ⟨2172731584931056213187723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448487723287370808791815 2172731584931056213187723)
        ·
          refine ⟨3259097377396584319781585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172731584931056213187723 3259097377396584319781585)
          ·
            refine ⟨2444323033047438239836189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3259097377396584319781585 2444323033047438239836189)
            ·
              refine ⟨916621137392789339938571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444323033047438239836189 916621137392789339938571)
              ·
                refine ⟨1374931706089184009907857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916621137392789339938571 1374931706089184009907857)
                ·
                  refine ⟨1031198779566888007430893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374931706089184009907857 1031198779566888007430893)
                  ·
                    refine ⟨386699542337583002786585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031198779566888007430893 386699542337583002786585)
                    ·
                      rfl

theorem cell22_1129642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1129642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129642 prefixEnd_1129642 := by exact prefixLift 1129642
  have htrace : WordTrace (prefixWord ++ tailWord_1129642) baseStart_1129642 baseEnd_1129642 := by
    simpa [prefixWord, tailWord_1129642, baseEnd_1129642] using wordTrace_append hprefix tailTrace_1129642
  have hstable : (prefixWord ++ tailWord_1129642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129642).length < 2 ^ (prefixWord ++ tailWord_1129642).sum := by decide
  have hdescent : baseEnd_1129642 < baseStart_1129642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129739 : List Nat := [1, 1, 1, 1, 5, 13]
def baseStart_1129739 : Nat := 118140960795 + 1129739 * 2 ^ 59
def prefixEnd_1129739 : Nat := 4983230072969 + 3 ^ 40 * 1129739 * 2
def baseEnd_1129739 : Nat := 4774478363208729421127

theorem tailTrace_1129739 : CollatzResearch.WordTrace tailWord_1129739 prefixEnd_1129739 4774478363208729421127 := by
  unfold tailWord_1129739
  simp only [CollatzResearch.WordTrace]
  refine ⟨41204966454156021905248271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27469977636104014603498847 41204966454156021905248271)
  ·
    refine ⟨61807449681234032857872407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41204966454156021905248271 61807449681234032857872407)
    ·
      refine ⟨92711174521851049286808611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61807449681234032857872407 92711174521851049286808611)
      ·
        refine ⟨139066761782776573930212917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92711174521851049286808611 139066761782776573930212917)
        ·
          refine ⟨13037508917135303805957461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139066761782776573930212917 13037508917135303805957461)
          ·
            refine ⟨4774478363208729421127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 13037508917135303805957461 4774478363208729421127)
            ·
              rfl

theorem cell22_1129739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 13].length) (baseStart_1129739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129739 prefixEnd_1129739 := by exact prefixLift 1129739
  have htrace : WordTrace (prefixWord ++ tailWord_1129739) baseStart_1129739 baseEnd_1129739 := by
    simpa [prefixWord, tailWord_1129739, baseEnd_1129739] using wordTrace_append hprefix tailTrace_1129739
  have hstable : (prefixWord ++ tailWord_1129739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129739).length < 2 ^ (prefixWord ++ tailWord_1129739).sum := by decide
  have hdescent : baseEnd_1129739 < baseStart_1129739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129756 : List Nat := [2, 2, 3, 1, 1, 1, 5, 7]
def baseStart_1129756 : Nat := 118140960795 + 1129756 * 2 ^ 59
def prefixEnd_1129756 : Nat := 4983230072969 + 3 ^ 40 * 1129756 * 2
def baseEnd_1129756 : Nat := 42970951874147189492915

theorem tailTrace_1129756 : CollatzResearch.WordTrace tailWord_1129756 prefixEnd_1129756 42970951874147189492915 := by
  unfold tailWord_1129756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20602793247547216904308561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27470390996729622539078081 20602793247547216904308561)
  ·
    refine ⟨15452094935660412678231421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20602793247547216904308561 15452094935660412678231421)
    ·
      refine ⟨5794535600872654754336783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15452094935660412678231421 5794535600872654754336783)
      ·
        refine ⟨8691803401308982131505175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5794535600872654754336783 8691803401308982131505175)
        ·
          refine ⟨13037705101963473197257763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691803401308982131505175 13037705101963473197257763)
          ·
            refine ⟨19556557652945209795886645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037705101963473197257763 19556557652945209795886645)
            ·
              refine ⟨1833427279963613418364373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19556557652945209795886645 1833427279963613418364373)
              ·
                refine ⟨42970951874147189492915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1833427279963613418364373 42970951874147189492915)
                ·
                  rfl

theorem cell22_1129756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_1129756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129756 prefixEnd_1129756 := by exact prefixLift 1129756
  have htrace : WordTrace (prefixWord ++ tailWord_1129756) baseStart_1129756 baseEnd_1129756 := by
    simpa [prefixWord, tailWord_1129756, baseEnd_1129756] using wordTrace_append hprefix tailTrace_1129756
  have hstable : (prefixWord ++ tailWord_1129756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129756).length < 2 ^ (prefixWord ++ tailWord_1129756).sum := by decide
  have hdescent : baseEnd_1129756 < baseStart_1129756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129816 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1129816 : Nat := 118140960795 + 1129816 * 2 ^ 59
def prefixEnd_1129816 : Nat := 4983230072969 + 3 ^ 40 * 1129816 * 2
def baseEnd_1129816 : Nat := 386759106093504548936051

theorem tailTrace_1129816 : CollatzResearch.WordTrace tailWord_1129816 prefixEnd_1129816 386759106093504548936051 := by
  unfold tailWord_1129816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20603887437438532027900651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27471849916584709370534201 20603887437438532027900651)
  ·
    refine ⟨30905831156157798041850977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20603887437438532027900651 30905831156157798041850977)
    ·
      refine ⟨23179373367118348531388233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30905831156157798041850977 23179373367118348531388233)
      ·
        refine ⟨17384530025338761398541175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23179373367118348531388233 17384530025338761398541175)
        ·
          refine ⟨26076795038008142097811763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17384530025338761398541175 26076795038008142097811763)
          ·
            refine ⟨39115192557012213146717645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26076795038008142097811763 39115192557012213146717645)
            ·
              refine ⟨14668197208879579930019117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39115192557012213146717645 14668197208879579930019117)
              ·
                refine ⟨5500573953329842473757169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14668197208879579930019117 5500573953329842473757169)
                ·
                  refine ⟨4125430464997381855317877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500573953329842473757169 4125430464997381855317877)
                  ·
                    refine ⟨386759106093504548936051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4125430464997381855317877 386759106093504548936051)
                    ·
                      rfl

theorem cell22_1129816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1129816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129816 prefixEnd_1129816 := by exact prefixLift 1129816
  have htrace : WordTrace (prefixWord ++ tailWord_1129816) baseStart_1129816 baseEnd_1129816 := by
    simpa [prefixWord, tailWord_1129816, baseEnd_1129816] using wordTrace_append hprefix tailTrace_1129816
  have hstable : (prefixWord ++ tailWord_1129816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129816).length < 2 ^ (prefixWord ++ tailWord_1129816).sum := by decide
  have hdescent : baseEnd_1129816 < baseStart_1129816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129863 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 6]
def baseStart_1129863 : Nat := 118140960795 + 1129863 * 2 ^ 59
def prefixEnd_1129863 : Nat := 4983230072969 + 3 ^ 40 * 1129863 * 2
def baseEnd_1129863 : Nat := 128925065051337364336969

theorem tailTrace_1129863 : CollatzResearch.WordTrace tailWord_1129863 prefixEnd_1129863 128925065051337364336969 := by
  unfold tailWord_1129863
  simp only [CollatzResearch.WordTrace]
  refine ⟨41209489105706791082762243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27472992737137860721841495 41209489105706791082762243)
  ·
    refine ⟨61814233658560186624143365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41209489105706791082762243 61814233658560186624143365)
    ·
      refine ⟨11590168810980034992026881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61814233658560186624143365 11590168810980034992026881)
      ·
        refine ⟨8692626608235026244020161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11590168810980034992026881 8692626608235026244020161)
        ·
          refine ⟨6519469956176269683015121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8692626608235026244020161 6519469956176269683015121)
          ·
            refine ⟨4889602467132202262261341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6519469956176269683015121 4889602467132202262261341)
            ·
              refine ⟨1833600925174575848348003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4889602467132202262261341 1833600925174575848348003)
              ·
                refine ⟨2750401387761863772522005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833600925174575848348003 2750401387761863772522005)
                ·
                  refine ⟨128925065051337364336969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2750401387761863772522005 128925065051337364336969)
                  ·
                    rfl

theorem cell22_1129863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 6].length) (baseStart_1129863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129863 prefixEnd_1129863 := by exact prefixLift 1129863
  have htrace : WordTrace (prefixWord ++ tailWord_1129863) baseStart_1129863 baseEnd_1129863 := by
    simpa [prefixWord, tailWord_1129863, baseEnd_1129863] using wordTrace_append hprefix tailTrace_1129863
  have hstable : (prefixWord ++ tailWord_1129863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129863).length < 2 ^ (prefixWord ++ tailWord_1129863).sum := by decide
  have hdescent : baseEnd_1129863 < baseStart_1129863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129891 : List Nat := [1, 1, 1, 4, 1, 3, 1, 10]
def baseStart_1129891 : Nat := 118140960795 + 1129891 * 2 ^ 59
def prefixEnd_1129891 : Nat := 4983230072969 + 3 ^ 40 * 1129891 * 2
def baseEnd_1129891 : Nat := 42976086680692150367869

theorem tailTrace_1129891 : CollatzResearch.WordTrace tailWord_1129891 prefixEnd_1129891 42976086680692150367869 := by
  unfold tailWord_1129891
  simp only [CollatzResearch.WordTrace]
  refine ⟨41210510349605351864781527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27473673566403567909854351 41210510349605351864781527)
  ·
    refine ⟨61815765524408027797172291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41210510349605351864781527 61815765524408027797172291)
    ·
      refine ⟨92723648286612041695758437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61815765524408027797172291 92723648286612041695758437)
      ·
        refine ⟨17385684053739757817954707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92723648286612041695758437 17385684053739757817954707)
        ·
          refine ⟨26078526080609636726932061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17385684053739757817954707 26078526080609636726932061)
          ·
            refine ⟨9779447280228613772599523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26078526080609636726932061 9779447280228613772599523)
            ·
              refine ⟨14669170920342920658899285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9779447280228613772599523 14669170920342920658899285)
              ·
                refine ⟨42976086680692150367869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14669170920342920658899285 42976086680692150367869)
                ·
                  rfl

theorem cell22_1129891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 10].length) (baseStart_1129891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129891 prefixEnd_1129891 := by exact prefixLift 1129891
  have htrace : WordTrace (prefixWord ++ tailWord_1129891) baseStart_1129891 baseEnd_1129891 := by
    simpa [prefixWord, tailWord_1129891, baseEnd_1129891] using wordTrace_append hprefix tailTrace_1129891
  have hstable : (prefixWord ++ tailWord_1129891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129891).length < 2 ^ (prefixWord ++ tailWord_1129891).sum := by decide
  have hdescent : baseEnd_1129891 < baseStart_1129891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129908 : List Nat := [2, 5, 2, 13]
def baseStart_1129908 : Nat := 118140960795 + 1129908 * 2 ^ 59
def prefixEnd_1129908 : Nat := 4983230072969 + 3 ^ 40 * 1129908 * 2
def baseEnd_1129908 : Nat := 530576954147663889761

theorem tailTrace_1129908 : CollatzResearch.WordTrace tailWord_1129908 prefixEnd_1129908 530576954147663889761 := by
  unfold tailWord_1129908
  simp only [CollatzResearch.WordTrace]
  refine ⟨20605565195271881884075189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27474086927029175845433585 20605565195271881884075189)
  ·
    refine ⟨1931771737056738926632049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20605565195271881884075189 1931771737056738926632049)
    ·
      refine ⟨1448828802792554194974037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1931771737056738926632049 1448828802792554194974037)
      ·
        refine ⟨530576954147663889761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1448828802792554194974037 530576954147663889761)
        ·
          rfl

theorem cell22_1129908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 13].length) (baseStart_1129908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129908 prefixEnd_1129908 := by exact prefixLift 1129908
  have htrace : WordTrace (prefixWord ++ tailWord_1129908) baseStart_1129908 baseEnd_1129908 := by
    simpa [prefixWord, tailWord_1129908, baseEnd_1129908] using wordTrace_append hprefix tailTrace_1129908
  have hstable : (prefixWord ++ tailWord_1129908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129908).length < 2 ^ (prefixWord ++ tailWord_1129908).sum := by decide
  have hdescent : baseEnd_1129908 < baseStart_1129908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129942 : List Nat := [5, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1129942 : Nat := 118140960795 + 1129942 * 2 ^ 59
def prefixEnd_1129942 : Nat := 4983230072969 + 3 ^ 40 * 1129942 * 2
def baseEnd_1129942 : Nat := 42978026496498024476185

theorem tailTrace_1129942 : CollatzResearch.WordTrace tailWord_1129942 prefixEnd_1129942 42978026496498024476185 := by
  unfold tailWord_1129942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575773154526286723430505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27474913648280391716592053 2575773154526286723430505)
  ·
    refine ⟨1931829865894715042572879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2575773154526286723430505 1931829865894715042572879)
    ·
      refine ⟨2897744798842072563859319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931829865894715042572879 2897744798842072563859319)
      ·
        refine ⟨4346617198263108845788979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897744798842072563859319 4346617198263108845788979)
        ·
          refine ⟨6519925797394663268683469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346617198263108845788979 6519925797394663268683469)
          ·
            refine ⟨2444972174022998725756301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6519925797394663268683469 2444972174022998725756301)
            ·
              refine ⟨916864565258624522158613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444972174022998725756301 916864565258624522158613)
              ·
                refine ⟨42978026496498024476185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 916864565258624522158613 42978026496498024476185)
                ·
                  rfl

theorem cell22_1129942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1129942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129942 prefixEnd_1129942 := by exact prefixLift 1129942
  have htrace : WordTrace (prefixWord ++ tailWord_1129942) baseStart_1129942 baseEnd_1129942 := by
    simpa [prefixWord, tailWord_1129942, baseEnd_1129942] using wordTrace_append hprefix tailTrace_1129942
  have hstable : (prefixWord ++ tailWord_1129942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129942).length < 2 ^ (prefixWord ++ tailWord_1129942).sum := by decide
  have hdescent : baseEnd_1129942 < baseStart_1129942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129968 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1129968 : Nat := 118140960795 + 1129968 * 2 ^ 59
def prefixEnd_1129968 : Nat := 4983230072969 + 3 ^ 40 * 1129968 * 2
def baseEnd_1129968 : Nat := 386811138799826819135585

theorem tailTrace_1129968 : CollatzResearch.WordTrace tailWord_1129968 prefixEnd_1129968 386811138799826819135585 := by
  unfold tailWord_1129968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606659385163197007667279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27475545846884262676889705 20606659385163197007667279)
  ·
    refine ⟨30909989077744795511500919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20606659385163197007667279 30909989077744795511500919)
    ·
      refine ⟨46364983616617193267251379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30909989077744795511500919 46364983616617193267251379)
      ·
        refine ⟨69547475424925789900877069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46364983616617193267251379 69547475424925789900877069)
        ·
          refine ⟨26080303284347171212828901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69547475424925789900877069 26080303284347171212828901)
          ·
            refine ⟨4890056865815094602405419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26080303284347171212828901 4890056865815094602405419)
            ·
              refine ⟨7335085298722641903608129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890056865815094602405419 7335085298722641903608129)
              ·
                refine ⟨5501313974041981427706097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335085298722641903608129 5501313974041981427706097)
                ·
                  refine ⟨4125985480531486070779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5501313974041981427706097 4125985480531486070779573)
                  ·
                    refine ⟨386811138799826819135585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4125985480531486070779573 386811138799826819135585)
                    ·
                      rfl

theorem cell22_1129968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1129968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129968 prefixEnd_1129968 := by exact prefixLift 1129968
  have htrace : WordTrace (prefixWord ++ tailWord_1129968) baseStart_1129968 baseEnd_1129968 := by
    simpa [prefixWord, tailWord_1129968, baseEnd_1129968] using wordTrace_append hprefix tailTrace_1129968
  have hstable : (prefixWord ++ tailWord_1129968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129968).length < 2 ^ (prefixWord ++ tailWord_1129968).sum := by decide
  have hdescent : baseEnd_1129968 < baseStart_1129968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129970 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1129970 : Nat := 118140960795 + 1129970 * 2 ^ 59
def prefixEnd_1129970 : Nat := 4983230072969 + 3 ^ 40 * 1129970 * 2
def baseEnd_1129970 : Nat := 128937274480233160195193

theorem tailTrace_1129970 : CollatzResearch.WordTrace tailWord_1129970 prefixEnd_1129970 128937274480233160195193 := by
  unfold tailWord_1129970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303347929079787089226841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27475594477546098904604909 10303347929079787089226841)
  ·
    refine ⟨7727510946809840316920131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10303347929079787089226841 7727510946809840316920131)
    ·
      refine ⟨11591266420214760475380197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727510946809840316920131 11591266420214760475380197)
      ·
        refine ⟨2173362453790267589133787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11591266420214760475380197 2173362453790267589133787)
        ·
          refine ⟨3260043680685401383700681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173362453790267589133787 3260043680685401383700681)
          ·
            refine ⟨2445032760514051037775511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3260043680685401383700681 2445032760514051037775511)
            ·
              refine ⟨3667549140771076556663267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445032760514051037775511 3667549140771076556663267)
              ·
                refine ⟨5501323711156614834994901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667549140771076556663267 5501323711156614834994901)
                ·
                  refine ⟨128937274480233160195193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5501323711156614834994901 128937274480233160195193)
                  ·
                    rfl

theorem cell22_1129970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1129970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129970 prefixEnd_1129970 := by exact prefixLift 1129970
  have htrace : WordTrace (prefixWord ++ tailWord_1129970) baseStart_1129970 baseEnd_1129970 := by
    simpa [prefixWord, tailWord_1129970, baseEnd_1129970] using wordTrace_append hprefix tailTrace_1129970
  have hstable : (prefixWord ++ tailWord_1129970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129970).length < 2 ^ (prefixWord ++ tailWord_1129970).sum := by decide
  have hdescent : baseEnd_1129970 < baseStart_1129970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129974 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_1129974 : Nat := 118140960795 + 1129974 * 2 ^ 59
def prefixEnd_1129974 : Nat := 4983230072969 + 3 ^ 40 * 1129974 * 2
def baseEnd_1129974 : Nat := 386813192722444803485567

theorem tailTrace_1129974 : CollatzResearch.WordTrace tailWord_1129974 prefixEnd_1129974 386813192722444803485567 := by
  unfold tailWord_1129974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575846100519041065003311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27475691738869771360035317 2575846100519041065003311)
  ·
    refine ⟨3863769150778561597504967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575846100519041065003311 3863769150778561597504967)
    ·
      refine ⟨5795653726167842396257451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863769150778561597504967 5795653726167842396257451)
      ·
        refine ⟨8693480589251763594386177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5795653726167842396257451 8693480589251763594386177)
        ·
          refine ⟨6520110441938822695789633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8693480589251763594386177 6520110441938822695789633)
          ·
            refine ⟨4890082831454117021842225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6520110441938822695789633 4890082831454117021842225)
            ·
              refine ⟨3667562123590587766381669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890082831454117021842225 3667562123590587766381669)
              ·
                refine ⟨687667898173235206196563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3667562123590587766381669 687667898173235206196563)
                ·
                  refine ⟨1031501847259852809294845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687667898173235206196563 1031501847259852809294845)
                  ·
                    refine ⟨386813192722444803485567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031501847259852809294845 386813192722444803485567)
                    ·
                      rfl

theorem cell22_1129974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_1129974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129974 prefixEnd_1129974 := by exact prefixLift 1129974
  have htrace : WordTrace (prefixWord ++ tailWord_1129974) baseStart_1129974 baseEnd_1129974 := by
    simpa [prefixWord, tailWord_1129974, baseEnd_1129974] using wordTrace_append hprefix tailTrace_1129974
  have hstable : (prefixWord ++ tailWord_1129974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129974).length < 2 ^ (prefixWord ++ tailWord_1129974).sum := by decide
  have hdescent : baseEnd_1129974 < baseStart_1129974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129983 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_1129983 : Nat := 118140960795 + 1129983 * 2 ^ 59
def prefixEnd_1129983 : Nat := 4983230072969 + 3 ^ 40 * 1129983 * 2
def baseEnd_1129983 : Nat := 386816273606371780010539

theorem tailTrace_1129983 : CollatzResearch.WordTrace tailWord_1129983 prefixEnd_1129983 386816273606371780010539 := by
  unfold tailWord_1129983
  simp only [CollatzResearch.WordTrace]
  refine ⟨41213865865272051577130603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27475910576848034384753735 41213865865272051577130603)
  ·
    refine ⟨61820798797908077365695905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41213865865272051577130603 61820798797908077365695905)
    ·
      refine ⟨46365599098431058024271929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61820798797908077365695905 46365599098431058024271929)
      ·
        refine ⟨34774199323823293518203947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46365599098431058024271929 34774199323823293518203947)
        ·
          refine ⟨52161298985734940277305921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34774199323823293518203947 52161298985734940277305921)
          ·
            refine ⟨39120974239301205207979441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52161298985734940277305921 39120974239301205207979441)
            ·
              refine ⟨29340730679475903905984581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39120974239301205207979441 29340730679475903905984581)
              ·
                refine ⟨5501387002401731982372109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29340730679475903905984581 5501387002401731982372109)
                ·
                  refine ⟨2063020125900649493389541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5501387002401731982372109 2063020125900649493389541)
                  ·
                    refine ⟨386816273606371780010539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2063020125900649493389541 386816273606371780010539)
                    ·
                      rfl

theorem cell22_1129983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_1129983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1129983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1129983 prefixEnd_1129983 := by exact prefixLift 1129983
  have htrace : WordTrace (prefixWord ++ tailWord_1129983) baseStart_1129983 baseEnd_1129983 := by
    simpa [prefixWord, tailWord_1129983, baseEnd_1129983] using wordTrace_append hprefix tailTrace_1129983
  have hstable : (prefixWord ++ tailWord_1129983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129983).length < 2 ^ (prefixWord ++ tailWord_1129983).sum := by decide
  have hdescent : baseEnd_1129983 < baseStart_1129983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130047 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 2, 3]
def baseStart_1130047 : Nat := 118140960795 + 1130047 * 2 ^ 59
def prefixEnd_1130047 : Nat := 4983230072969 + 3 ^ 40 * 1130047 * 2
def baseEnd_1130047 : Nat := 386838182114296946410343

theorem tailTrace_1130047 : CollatzResearch.WordTrace tailWord_1130047 prefixEnd_1130047 386838182114296946410343 := by
  unfold tailWord_1130047
  simp only [CollatzResearch.WordTrace]
  refine ⟨41216200137040190507460395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27477466758026793671640263 41216200137040190507460395)
  ·
    refine ⟨61824300205560285761190593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41216200137040190507460395 61824300205560285761190593)
    ·
      refine ⟨46368225154170214320892945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61824300205560285761190593 46368225154170214320892945)
      ·
        refine ⟨34776168865627660740669709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46368225154170214320892945 34776168865627660740669709)
        ·
          refine ⟨13041063324610372777751141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34776168865627660740669709 13041063324610372777751141)
          ·
            refine ⟨2445199373364444895828339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13041063324610372777751141 2445199373364444895828339)
            ·
              refine ⟨3667799060046667343742509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445199373364444895828339 3667799060046667343742509)
              ·
                refine ⟨1375424647517500253903441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3667799060046667343742509 1375424647517500253903441)
                ·
                  refine ⟨1031568485638125190427581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375424647517500253903441 1031568485638125190427581)
                  ·
                    refine ⟨386838182114296946410343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031568485638125190427581 386838182114296946410343)
                    ·
                      rfl

theorem cell22_1130047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_1130047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130047 prefixEnd_1130047 := by exact prefixLift 1130047
  have htrace : WordTrace (prefixWord ++ tailWord_1130047) baseStart_1130047 baseEnd_1130047 := by
    simpa [prefixWord, tailWord_1130047, baseEnd_1130047] using wordTrace_append hprefix tailTrace_1130047
  have hstable : (prefixWord ++ tailWord_1130047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130047).length < 2 ^ (prefixWord ++ tailWord_1130047).sum := by decide
  have hdescent : baseEnd_1130047 < baseStart_1130047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130073 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1130073 : Nat := 118140960795 + 1130073 * 2 ^ 59
def prefixEnd_1130073 : Nat := 4983230072969 + 3 ^ 40 * 1130073 * 2
def baseEnd_1130073 : Nat := 386847082445641545260263

theorem tailTrace_1130073 : CollatzResearch.WordTrace tailWord_1130073 prefixEnd_1130073 386847082445641545260263 := by
  unfold tailWord_1130073
  simp only [CollatzResearch.WordTrace]
  refine ⟨41217148434945996947906873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27478098956630664631937915 41217148434945996947906873)
  ·
    refine ⟨30912861326209497710930155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41217148434945996947906873 30912861326209497710930155)
    ·
      refine ⟨46369291989314246566395233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30912861326209497710930155 46369291989314246566395233)
      ·
        refine ⟨34776968991985684924796425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46369291989314246566395233 34776968991985684924796425)
        ·
          refine ⟨26082726743989263693597319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34776968991985684924796425 26082726743989263693597319)
          ·
            refine ⟨39124090115983895540395979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26082726743989263693597319 39124090115983895540395979)
            ·
              refine ⟨58686135173975843310593969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39124090115983895540395979 58686135173975843310593969)
              ·
                refine ⟨44014601380481882482945477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58686135173975843310593969 44014601380481882482945477)
                ·
                  refine ⟨8252737758840352965552277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44014601380481882482945477 8252737758840352965552277)
                  ·
                    refine ⟨386847082445641545260263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8252737758840352965552277 386847082445641545260263)
                    ·
                      rfl

theorem cell22_1130073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1130073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130073 prefixEnd_1130073 := by exact prefixLift 1130073
  have htrace : WordTrace (prefixWord ++ tailWord_1130073) baseStart_1130073 baseEnd_1130073 := by
    simpa [prefixWord, tailWord_1130073, baseEnd_1130073] using wordTrace_append hprefix tailTrace_1130073
  have hstable : (prefixWord ++ tailWord_1130073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130073).length < 2 ^ (prefixWord ++ tailWord_1130073).sum := by decide
  have hdescent : baseEnd_1130073 < baseStart_1130073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130077 : List Nat := [1, 4, 4, 2, 1, 10]
def baseStart_1130077 : Nat := 118140960795 + 1130077 * 2 ^ 59
def prefixEnd_1130077 : Nat := 4983230072969 + 3 ^ 40 * 1130077 * 2
def baseEnd_1130077 : Nat := 4775906811449220594571

theorem tailTrace_1130077 : CollatzResearch.WordTrace tailWord_1130077 prefixEnd_1130077 4775906811449220594571 := by
  unfold tailWord_1130077
  simp only [CollatzResearch.WordTrace]
  refine ⟨41217294326931505631052485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27478196217954337087368323 41217294326931505631052485)
  ·
    refine ⟨7728242686299657305822341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41217294326931505631052485 7728242686299657305822341)
    ·
      refine ⟨1449045503681185744841689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7728242686299657305822341 1449045503681185744841689)
      ·
        refine ⟨1086784127760889308631267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1449045503681185744841689 1086784127760889308631267)
        ·
          refine ⟨1630176191641333962946901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086784127760889308631267 1630176191641333962946901)
          ·
            refine ⟨4775906811449220594571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1630176191641333962946901 4775906811449220594571)
            ·
              rfl

theorem cell22_1130077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 10].length) (baseStart_1130077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130077 prefixEnd_1130077 := by exact prefixLift 1130077
  have htrace : WordTrace (prefixWord ++ tailWord_1130077) baseStart_1130077 baseEnd_1130077 := by
    simpa [prefixWord, tailWord_1130077, baseEnd_1130077] using wordTrace_append hprefix tailTrace_1130077
  have hstable : (prefixWord ++ tailWord_1130077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130077).length < 2 ^ (prefixWord ++ tailWord_1130077).sum := by decide
  have hdescent : baseEnd_1130077 < baseStart_1130077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130090 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1130090 : Nat := 118140960795 + 1130090 * 2 ^ 59
def prefixEnd_1130090 : Nat := 4983230072969 + 3 ^ 40 * 1130090 * 2
def baseEnd_1130090 : Nat := 386852901893059167585211

theorem tailTrace_1130090 : CollatzResearch.WordTrace tailWord_1130090 prefixEnd_1130090 386852901893059167585211 := by
  unfold tailWord_1130090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10304442118971102212818931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27478512317256272567517149 10304442118971102212818931)
  ·
    refine ⟨15456663178456653319228397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10304442118971102212818931 15456663178456653319228397)
    ·
      refine ⟨5796248691921244994710649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15456663178456653319228397 5796248691921244994710649)
      ·
        refine ⟨4347186518940933746032987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5796248691921244994710649 4347186518940933746032987)
        ·
          refine ⟨6520779778411400619049481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347186518940933746032987 6520779778411400619049481)
          ·
            refine ⟨4890584833808550464287111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6520779778411400619049481 4890584833808550464287111)
            ·
              refine ⟨7335877250712825696430667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890584833808550464287111 7335877250712825696430667)
              ·
                refine ⟨11003815876069238544646001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7335877250712825696430667 11003815876069238544646001)
                ·
                  refine ⟨8252861907051928908484501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11003815876069238544646001 8252861907051928908484501)
                  ·
                    refine ⟨386852901893059167585211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8252861907051928908484501 386852901893059167585211)
                    ·
                      rfl

theorem cell22_1130090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1130090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130090 prefixEnd_1130090 := by exact prefixLift 1130090
  have htrace : WordTrace (prefixWord ++ tailWord_1130090) baseStart_1130090 baseEnd_1130090 := by
    simpa [prefixWord, tailWord_1130090, baseEnd_1130090] using wordTrace_append hprefix tailTrace_1130090
  have hstable : (prefixWord ++ tailWord_1130090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130090).length < 2 ^ (prefixWord ++ tailWord_1130090).sum := by decide
  have hdescent : baseEnd_1130090 < baseStart_1130090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130094 : List Nat := [4, 1, 2, 2, 4, 1, 1, 7]
def baseStart_1130094 : Nat := 118140960795 + 1130094 * 2 ^ 59
def prefixEnd_1130094 : Nat := 4983230072969 + 3 ^ 40 * 1130094 * 2
def baseEnd_1130094 : Nat := 42983807908311610053911

theorem tailTrace_1130094 : CollatzResearch.WordTrace tailWord_1130094 prefixEnd_1130094 42983807908311610053911 := by
  unfold tailWord_1130094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152239295983739691802667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27478609578579945022947557 5152239295983739691802667)
  ·
    refine ⟨7728358943975609537704001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152239295983739691802667 7728358943975609537704001)
    ·
      refine ⟨5796269207981707153278001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7728358943975609537704001 5796269207981707153278001)
      ·
        refine ⟨4347201905986280364958501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5796269207981707153278001 4347201905986280364958501)
        ·
          refine ⟨815100357372427568429719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4347201905986280364958501 815100357372427568429719)
          ·
            refine ⟨1222650536058641352644579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815100357372427568429719 1222650536058641352644579)
            ·
              refine ⟨1833975804087962028966869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222650536058641352644579 1833975804087962028966869)
              ·
                refine ⟨42983807908311610053911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1833975804087962028966869 42983807908311610053911)
                ·
                  rfl

theorem cell22_1130094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_1130094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130094 prefixEnd_1130094 := by exact prefixLift 1130094
  have htrace : WordTrace (prefixWord ++ tailWord_1130094) baseStart_1130094 baseEnd_1130094 := by
    simpa [prefixWord, tailWord_1130094, baseEnd_1130094] using wordTrace_append hprefix tailTrace_1130094
  have hstable : (prefixWord ++ tailWord_1130094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130094).length < 2 ^ (prefixWord ++ tailWord_1130094).sum := by decide
  have hdescent : baseEnd_1130094 < baseStart_1130094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130105 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 5]
def baseStart_1130105 : Nat := 118140960795 + 1130105 * 2 ^ 59
def prefixEnd_1130105 : Nat := 4983230072969 + 3 ^ 40 * 1130105 * 2
def baseEnd_1130105 : Nat := 128952678899868042820055

theorem tailTrace_1130105 : CollatzResearch.WordTrace tailWord_1130105 prefixEnd_1130105 128952678899868042820055 := by
  unfold tailWord_1130105
  simp only [CollatzResearch.WordTrace]
  refine ⟨41218315570830066413071769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27478877047220044275381179 41218315570830066413071769)
  ·
    refine ⟨30913736678122549809803827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41218315570830066413071769 30913736678122549809803827)
    ·
      refine ⟨46370605017183824714705741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30913736678122549809803827 46370605017183824714705741)
      ·
        refine ⟨17388976881443934268014653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46370605017183824714705741 17388976881443934268014653)
        ·
          refine ⟨6520866330541475350505495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17388976881443934268014653 6520866330541475350505495)
          ·
            refine ⟨9781299495812213025758243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520866330541475350505495 9781299495812213025758243)
            ·
              refine ⟨14671949243718319538637365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781299495812213025758243 14671949243718319538637365)
              ·
                refine ⟨1375495241598592456747253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14671949243718319538637365 1375495241598592456747253)
                ·
                  refine ⟨128952678899868042820055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1375495241598592456747253 128952678899868042820055)
                  ·
                    rfl

theorem cell22_1130105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_1130105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130105 prefixEnd_1130105 := by exact prefixLift 1130105
  have htrace : WordTrace (prefixWord ++ tailWord_1130105) baseStart_1130105 baseEnd_1130105 := by
    simpa [prefixWord, tailWord_1130105, baseEnd_1130105] using wordTrace_append hprefix tailTrace_1130105
  have hstable : (prefixWord ++ tailWord_1130105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130105).length < 2 ^ (prefixWord ++ tailWord_1130105).sum := by decide
  have hdescent : baseEnd_1130105 < baseStart_1130105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130126 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1130126 : Nat := 118140960795 + 1130126 * 2 ^ 59
def prefixEnd_1130126 : Nat := 4983230072969 + 3 ^ 40 * 1130126 * 2
def baseEnd_1130126 : Nat := 386865225428767073685101

theorem tailTrace_1130126 : CollatzResearch.WordTrace tailWord_1130126 prefixEnd_1130126 386865225428767073685101 := by
  unfold tailWord_1130126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152385187969248374948279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27479387669169324666390821 5152385187969248374948279)
  ·
    refine ⟨7728577781953872562422419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152385187969248374948279 7728577781953872562422419)
    ·
      refine ⟨11592866672930808843633629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728577781953872562422419 11592866672930808843633629)
      ·
        refine ⟨4347325002349053316362611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11592866672930808843633629 4347325002349053316362611)
        ·
          refine ⟨6520987503523579974543917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347325002349053316362611 6520987503523579974543917)
          ·
            refine ⟨2445370313821342490453969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6520987503523579974543917 2445370313821342490453969)
            ·
              refine ⟨1834027735366006867840477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445370313821342490453969 1834027735366006867840477)
              ·
                refine ⟨687760400762252575440179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1834027735366006867840477 687760400762252575440179)
                ·
                  refine ⟨1031640601143378863160269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687760400762252575440179 1031640601143378863160269)
                  ·
                    refine ⟨386865225428767073685101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031640601143378863160269 386865225428767073685101)
                    ·
                      rfl

theorem cell22_1130126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1130126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130126 prefixEnd_1130126 := by exact prefixLift 1130126
  have htrace : WordTrace (prefixWord ++ tailWord_1130126) baseStart_1130126 baseEnd_1130126 := by
    simpa [prefixWord, tailWord_1130126, baseEnd_1130126] using wordTrace_append hprefix tailTrace_1130126
  have hstable : (prefixWord ++ tailWord_1130126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130126).length < 2 ^ (prefixWord ++ tailWord_1130126).sum := by decide
  have hdescent : baseEnd_1130126 < baseStart_1130126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130216 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1130216 : Nat := 118140960795 + 1130216 * 2 ^ 59
def prefixEnd_1130216 : Nat := 4983230072969 + 3 ^ 40 * 1130216 * 2
def baseEnd_1130216 : Nat := 386896034268036838934825

theorem tailTrace_1130216 : CollatzResearch.WordTrace tailWord_1130216 prefixEnd_1130216 386896034268036838934825 := by
  unfold tailWord_1130216
  simp only [CollatzResearch.WordTrace]
  refine ⟨20611182036713966185181251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27481576048951954913575001 20611182036713966185181251)
  ·
    refine ⟨30916773055070949277771877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20611182036713966185181251 30916773055070949277771877)
    ·
      refine ⟨5796894947825802989582227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30916773055070949277771877 5796894947825802989582227)
      ·
        refine ⟨8695342421738704484373341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796894947825802989582227 8695342421738704484373341)
        ·
          refine ⟨3260753408152014181640003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8695342421738704484373341 3260753408152014181640003)
          ·
            refine ⟨4891130112228021272460005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260753408152014181640003 4891130112228021272460005)
            ·
              refine ⟨917086896042753988586251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4891130112228021272460005 917086896042753988586251)
              ·
                refine ⟨1375630344064130982879377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917086896042753988586251 1375630344064130982879377)
                ·
                  refine ⟨1031722758048098237159533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375630344064130982879377 1031722758048098237159533)
                  ·
                    refine ⟨386896034268036838934825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031722758048098237159533 386896034268036838934825)
                    ·
                      rfl

theorem cell22_1130216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1130216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130216 prefixEnd_1130216 := by exact prefixLift 1130216
  have htrace : WordTrace (prefixWord ++ tailWord_1130216) baseStart_1130216 baseEnd_1130216 := by
    simpa [prefixWord, tailWord_1130216, baseEnd_1130216] using wordTrace_append hprefix tailTrace_1130216
  have hstable : (prefixWord ++ tailWord_1130216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130216).length < 2 ^ (prefixWord ++ tailWord_1130216).sum := by decide
  have hdescent : baseEnd_1130216 < baseStart_1130216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130227 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 3, 3]
def baseStart_1130227 : Nat := 118140960795 + 1130227 * 2 ^ 59
def prefixEnd_1130227 : Nat := 4983230072969 + 3 ^ 40 * 1130227 * 2
def baseEnd_1130227 : Nat := 386899799792836476909791

theorem tailTrace_1130227 : CollatzResearch.WordTrace tailWord_1130227 prefixEnd_1130227 386899799792836476909791 := by
  unfold tailWord_1130227
  simp only [CollatzResearch.WordTrace]
  refine ⟨41222765276388081249012935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27481843517592054166008623 41222765276388081249012935)
  ·
    refine ⟨61834147914582121873519403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41222765276388081249012935 61834147914582121873519403)
    ·
      refine ⟨92751221871873182810279105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61834147914582121873519403 92751221871873182810279105)
      ·
        refine ⟨69563416403904887107709329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92751221871873182810279105 69563416403904887107709329)
        ·
          refine ⟨52172562302928665330781997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69563416403904887107709329 52172562302928665330781997)
          ·
            refine ⟨19564710863598249499043249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52172562302928665330781997 19564710863598249499043249)
            ·
              refine ⟨14673533147698687124282437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19564710863598249499043249 14673533147698687124282437)
              ·
                refine ⟨2751287465193503835802957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14673533147698687124282437 2751287465193503835802957)
                ·
                  refine ⟨1031732799447563938426109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2751287465193503835802957 1031732799447563938426109)
                  ·
                    refine ⟨386899799792836476909791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031732799447563938426109 386899799792836476909791)
                    ·
                      rfl

theorem cell22_1130227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3].length) (baseStart_1130227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130227 prefixEnd_1130227 := by exact prefixLift 1130227
  have htrace : WordTrace (prefixWord ++ tailWord_1130227) baseStart_1130227 baseEnd_1130227 := by
    simpa [prefixWord, tailWord_1130227, baseEnd_1130227] using wordTrace_append hprefix tailTrace_1130227
  have hstable : (prefixWord ++ tailWord_1130227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130227).length < 2 ^ (prefixWord ++ tailWord_1130227).sum := by decide
  have hdescent : baseEnd_1130227 < baseStart_1130227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130261 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_1130261 : Nat := 118140960795 + 1130261 * 2 ^ 59
def prefixEnd_1130261 : Nat := 4983230072969 + 3 ^ 40 * 1130261 * 2
def baseEnd_1130261 : Nat := 386911438687671721559687

theorem tailTrace_1130261 : CollatzResearch.WordTrace tailWord_1130261 prefixEnd_1130261 386911438687671721559687 := by
  unfold tailWord_1130261
  simp only [CollatzResearch.WordTrace]
  refine ⟨41224005358264905055750637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27482670238843270037167091 41224005358264905055750637)
  ·
    refine ⟨15459002009349339395906489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41224005358264905055750637 15459002009349339395906489)
    ·
      refine ⟨11594251507012004546929867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15459002009349339395906489 11594251507012004546929867)
      ·
        refine ⟨17391377260518006820394801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594251507012004546929867 17391377260518006820394801)
        ·
          refine ⟨13043532945388505115296101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17391377260518006820394801 13043532945388505115296101)
          ·
            refine ⟨2445662427260344709118019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13043532945388505115296101 2445662427260344709118019)
            ·
              refine ⟨3668493640890517063677029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445662427260344709118019 3668493640890517063677029)
              ·
                refine ⟨687842557666971949439443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3668493640890517063677029 687842557666971949439443)
                ·
                  refine ⟨1031763836500457924159165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687842557666971949439443 1031763836500457924159165)
                  ·
                    refine ⟨386911438687671721559687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031763836500457924159165 386911438687671721559687)
                    ·
                      rfl

theorem cell22_1130261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_1130261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130261 prefixEnd_1130261 := by exact prefixLift 1130261
  have htrace : WordTrace (prefixWord ++ tailWord_1130261) baseStart_1130261 baseEnd_1130261 := by
    simpa [prefixWord, tailWord_1130261, baseEnd_1130261] using wordTrace_append hprefix tailTrace_1130261
  have hstable : (prefixWord ++ tailWord_1130261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130261).length < 2 ^ (prefixWord ++ tailWord_1130261).sum := by decide
  have hdescent : baseEnd_1130261 < baseStart_1130261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130272 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_1130272 : Nat := 118140960795 + 1130272 * 2 ^ 59
def prefixEnd_1130272 : Nat := 4983230072969 + 3 ^ 40 * 1130272 * 2
def baseEnd_1130272 : Nat := 386915204212471359534653

theorem tailTrace_1130272 : CollatzResearch.WordTrace tailWord_1130272 prefixEnd_1130272 386915204212471359534653 := by
  unfold tailWord_1130272
  simp only [CollatzResearch.WordTrace]
  refine ⟨20612203280612526967200535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27482937707483369289600713 20612203280612526967200535)
  ·
    refine ⟨30918304920918790450800803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20612203280612526967200535 30918304920918790450800803)
    ·
      refine ⟨46377457381378185676201205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30918304920918790450800803 46377457381378185676201205)
      ·
        refine ⟨4347886629504204907143863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46377457381378185676201205 4347886629504204907143863)
        ·
          refine ⟨6521829944256307360715795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347886629504204907143863 6521829944256307360715795)
          ·
            refine ⟨9782744916384461041073693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6521829944256307360715795 9782744916384461041073693)
            ·
              refine ⟨3668529343644172890402635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9782744916384461041073693 3668529343644172890402635)
              ·
                refine ⟨5502794015466259335603953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668529343644172890402635 5502794015466259335603953)
                ·
                  refine ⟨4127095511599694501702965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502794015466259335603953 4127095511599694501702965)
                  ·
                    refine ⟨386915204212471359534653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4127095511599694501702965 386915204212471359534653)
                    ·
                      rfl

theorem cell22_1130272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_1130272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130272 prefixEnd_1130272 := by exact prefixLift 1130272
  have htrace : WordTrace (prefixWord ++ tailWord_1130272) baseStart_1130272 baseEnd_1130272 := by
    simpa [prefixWord, tailWord_1130272, baseEnd_1130272] using wordTrace_append hprefix tailTrace_1130272
  have hstable : (prefixWord ++ tailWord_1130272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130272).length < 2 ^ (prefixWord ++ tailWord_1130272).sum := by decide
  have hdescent : baseEnd_1130272 < baseStart_1130272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130366 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1130366 : Nat := 118140960795 + 1130366 * 2 ^ 59
def prefixEnd_1130366 : Nat := 4983230072969 + 3 ^ 40 * 1130366 * 2
def baseEnd_1130366 : Nat := 386947382333486447684365

theorem tailTrace_1130366 : CollatzResearch.WordTrace tailWord_1130366 prefixEnd_1130366 386947382333486447684365 := by
  unfold tailWord_1130366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153479377860563498540369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27485223348589671992215301 5153479377860563498540369)
  ·
    refine ⟨3865109533395422623905277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5153479377860563498540369 3865109533395422623905277)
    ·
      refine ⟨1449416075023283483964479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3865109533395422623905277 1449416075023283483964479)
      ·
        refine ⟨2174124112534925225946719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449416075023283483964479 2174124112534925225946719)
        ·
          refine ⟨3261186168802387838920079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174124112534925225946719 3261186168802387838920079)
          ·
            refine ⟨4891779253203581758380119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261186168802387838920079 4891779253203581758380119)
            ·
              refine ⟨7337668879805372637570179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891779253203581758380119 7337668879805372637570179)
              ·
                refine ⟨11006503319708058956355269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337668879805372637570179 11006503319708058956355269)
                ·
                  refine ⟨2063719372445261054316613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11006503319708058956355269 2063719372445261054316613)
                  ·
                    refine ⟨386947382333486447684365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2063719372445261054316613 386947382333486447684365)
                    ·
                      rfl

theorem cell22_1130366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1130366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130366 prefixEnd_1130366 := by exact prefixLift 1130366
  have htrace : WordTrace (prefixWord ++ tailWord_1130366) baseStart_1130366 baseEnd_1130366 := by
    simpa [prefixWord, tailWord_1130366, baseEnd_1130366] using wordTrace_append hprefix tailTrace_1130366
  have hstable : (prefixWord ++ tailWord_1130366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130366).length < 2 ^ (prefixWord ++ tailWord_1130366).sum := by decide
  have hdescent : baseEnd_1130366 < baseStart_1130366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130377 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1130377 : Nat := 118140960795 + 1130377 * 2 ^ 59
def prefixEnd_1130377 : Nat := 4983230072969 + 3 ^ 40 * 1130377 * 2
def baseEnd_1130377 : Nat := 386951147858286085659331

theorem tailTrace_1130377 : CollatzResearch.WordTrace tailWord_1130377 prefixEnd_1130377 386951147858286085659331 := by
  unfold tailWord_1130377
  simp only [CollatzResearch.WordTrace]
  refine ⟨41228236225844656866973385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27485490817229771244648923 41228236225844656866973385)
  ·
    refine ⟨30921177169383492650230039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41228236225844656866973385 30921177169383492650230039)
    ·
      refine ⟨46381765754075238975345059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30921177169383492650230039 46381765754075238975345059)
      ·
        refine ⟨69572648631112858463017589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46381765754075238975345059 69572648631112858463017589)
        ·
          refine ⟨6522435809166830480907899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69572648631112858463017589 6522435809166830480907899)
          ·
            refine ⟨9783653713750245721361849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6522435809166830480907899 9783653713750245721361849)
            ·
              refine ⟨7337740285312684291021387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783653713750245721361849 7337740285312684291021387)
              ·
                refine ⟨11006610427969026436532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337740285312684291021387 11006610427969026436532081)
                ·
                  refine ⟨8254957820976769827399061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11006610427969026436532081 8254957820976769827399061)
                  ·
                    refine ⟨386951147858286085659331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8254957820976769827399061 386951147858286085659331)
                    ·
                      rfl

theorem cell22_1130377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1130377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130377 prefixEnd_1130377 := by exact prefixLift 1130377
  have htrace : WordTrace (prefixWord ++ tailWord_1130377) baseStart_1130377 baseEnd_1130377 := by
    simpa [prefixWord, tailWord_1130377, baseEnd_1130377] using wordTrace_append hprefix tailTrace_1130377
  have hstable : (prefixWord ++ tailWord_1130377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130377).length < 2 ^ (prefixWord ++ tailWord_1130377).sum := by decide
  have hdescent : baseEnd_1130377 < baseStart_1130377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130430 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_1130430 : Nat := 118140960795 + 1130430 * 2 ^ 59
def prefixEnd_1130430 : Nat := 4983230072969 + 3 ^ 40 * 1130430 * 2
def baseEnd_1130430 : Nat := 386969290841411614084169

theorem tailTrace_1130430 : CollatzResearch.WordTrace tailWord_1130430 prefixEnd_1130430 386969290841411614084169 := by
  unfold tailWord_1130430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153771161831580864831593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27486779529768431279101829 5153771161831580864831593)
  ·
    refine ⟨3865328371373685648623695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5153771161831580864831593 3865328371373685648623695)
    ·
      refine ⟨5797992557060528472935543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865328371373685648623695 5797992557060528472935543)
      ·
        refine ⟨8696988835590792709403315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5797992557060528472935543 8696988835590792709403315)
        ·
          refine ⟨13045483253386189064104973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8696988835590792709403315 13045483253386189064104973)
          ·
            refine ⟨4892056220019820899039365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13045483253386189064104973 4892056220019820899039365)
            ·
              refine ⟨917260541253716418569881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4892056220019820899039365 917260541253716418569881)
              ·
                refine ⟨687945405940287313927411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917260541253716418569881 687945405940287313927411)
                ·
                  refine ⟨1031918108910430970891117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687945405940287313927411 1031918108910430970891117)
                  ·
                    refine ⟨386969290841411614084169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031918108910430970891117 386969290841411614084169)
                    ·
                      rfl

theorem cell22_1130430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_1130430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130430 prefixEnd_1130430 := by exact prefixLift 1130430
  have htrace : WordTrace (prefixWord ++ tailWord_1130430) baseStart_1130430 baseEnd_1130430 := by
    simpa [prefixWord, tailWord_1130430, baseEnd_1130430] using wordTrace_append hprefix tailTrace_1130430
  have hstable : (prefixWord ++ tailWord_1130430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130430).length < 2 ^ (prefixWord ++ tailWord_1130430).sum := by decide
  have hdescent : baseEnd_1130430 < baseStart_1130430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130544 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_1130544 : Nat := 118140960795 + 1130544 * 2 ^ 59
def prefixEnd_1130544 : Nat := 4983230072969 + 3 ^ 40 * 1130544 * 2
def baseEnd_1130544 : Nat := 129002771790384438911273

theorem tailTrace_1130544 : CollatzResearch.WordTrace tailWord_1130544 prefixEnd_1130544 129002771790384438911273 := by
  unfold tailWord_1130544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617163608119822194151343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27489551477493096258868457 20617163608119822194151343)
  ·
    refine ⟨30925745412179733291227015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20617163608119822194151343 30925745412179733291227015)
    ·
      refine ⟨46388618118269599936840523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30925745412179733291227015 46388618118269599936840523)
      ·
        refine ⟨69582927177404399905260785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46388618118269599936840523 69582927177404399905260785)
        ·
          refine ⟨52187195383053299928945589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69582927177404399905260785 52187195383053299928945589)
          ·
            refine ⟨4892549567161246868338649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52187195383053299928945589 4892549567161246868338649)
            ·
              refine ⟨3669412175370935151253987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892549567161246868338649 3669412175370935151253987)
              ·
                refine ⟨5504118263056402726880981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669412175370935151253987 5504118263056402726880981)
                ·
                  refine ⟨129002771790384438911273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5504118263056402726880981 129002771790384438911273)
                  ·
                    rfl

theorem cell22_1130544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_1130544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130544 prefixEnd_1130544 := by exact prefixLift 1130544
  have htrace : WordTrace (prefixWord ++ tailWord_1130544) baseStart_1130544 baseEnd_1130544 := by
    simpa [prefixWord, tailWord_1130544, baseEnd_1130544] using wordTrace_append hprefix tailTrace_1130544
  have hstable : (prefixWord ++ tailWord_1130544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130544).length < 2 ^ (prefixWord ++ tailWord_1130544).sum := by decide
  have hdescent : baseEnd_1130544 < baseStart_1130544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130559 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_1130559 : Nat := 118140960795 + 1130559 * 2 ^ 59
def prefixEnd_1130559 : Nat := 4983230072969 + 3 ^ 40 * 1130559 * 2
def baseEnd_1130559 : Nat := 387013450177698277608773

theorem tailTrace_1130559 : CollatzResearch.WordTrace tailWord_1130559 prefixEnd_1130559 387013450177698277608773 := by
  unfold tailWord_1130559
  simp only [CollatzResearch.WordTrace]
  refine ⟨41234874311185301950098731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27489916207456867966732487 41234874311185301950098731)
  ·
    refine ⟨61852311466777952925148097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41234874311185301950098731 61852311466777952925148097)
    ·
      refine ⟨46389233600083464693861073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61852311466777952925148097 46389233600083464693861073)
      ·
        refine ⟨34791925200062598520395805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46389233600083464693861073 34791925200062598520395805)
        ·
          refine ⟨13046971950023474445148427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34791925200062598520395805 13046971950023474445148427)
          ·
            refine ⟨19570457925035211667722641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13046971950023474445148427 19570457925035211667722641)
            ·
              refine ⟨14677843443776408750791981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19570457925035211667722641 14677843443776408750791981)
              ·
                refine ⟨5504191291416153281546993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14677843443776408750791981 5504191291416153281546993)
                ·
                  refine ⟨4128143468562114961160245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5504191291416153281546993 4128143468562114961160245)
                  ·
                    refine ⟨387013450177698277608773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4128143468562114961160245 387013450177698277608773)
                    ·
                      rfl

theorem cell22_1130559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_1130559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130559 prefixEnd_1130559 := by exact prefixLift 1130559
  have htrace : WordTrace (prefixWord ++ tailWord_1130559) baseStart_1130559 baseEnd_1130559 := by
    simpa [prefixWord, tailWord_1130559, baseEnd_1130559] using wordTrace_append hprefix tailTrace_1130559
  have hstable : (prefixWord ++ tailWord_1130559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130559).length < 2 ^ (prefixWord ++ tailWord_1130559).sum := by decide
  have hdescent : baseEnd_1130559 < baseStart_1130559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130606 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1130606 : Nat := 118140960795 + 1130606 * 2 ^ 59
def prefixEnd_1130606 : Nat := 4983230072969 + 3 ^ 40 * 1130606 * 2
def baseEnd_1130606 : Nat := 129009846412735273894543

theorem tailTrace_1130606 : CollatzResearch.WordTrace tailWord_1130606 prefixEnd_1130606 129009846412735273894543 := by
  unfold tailWord_1130606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154573567751878622132459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27491059028010019318039781 5154573567751878622132459)
  ·
    refine ⟨7731860351627817933198689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5154573567751878622132459 7731860351627817933198689)
    ·
      refine ⟨5798895263720863449899017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7731860351627817933198689 5798895263720863449899017)
      ·
        refine ⟨4349171447790647587424263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5798895263720863449899017 4349171447790647587424263)
        ·
          refine ⟨6523757171685971381136395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349171447790647587424263 6523757171685971381136395)
          ·
            refine ⟨9785635757528957071704593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523757171685971381136395 9785635757528957071704593)
            ·
              refine ⟨7339226818146717803778445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9785635757528957071704593 7339226818146717803778445)
              ·
                refine ⟨2752210056805019176416917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7339226818146717803778445 2752210056805019176416917)
                ·
                  refine ⟨129009846412735273894543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2752210056805019176416917 129009846412735273894543)
                  ·
                    rfl

theorem cell22_1130606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1130606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130606 prefixEnd_1130606 := by exact prefixLift 1130606
  have htrace : WordTrace (prefixWord ++ tailWord_1130606) baseStart_1130606 baseEnd_1130606 := by
    simpa [prefixWord, tailWord_1130606, baseEnd_1130606] using wordTrace_append hprefix tailTrace_1130606
  have hstable : (prefixWord ++ tailWord_1130606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130606).length < 2 ^ (prefixWord ++ tailWord_1130606).sum := by decide
  have hdescent : baseEnd_1130606 < baseStart_1130606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130621 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1130621 : Nat := 118140960795 + 1130621 * 2 ^ 59
def prefixEnd_1130621 : Nat := 4983230072969 + 3 ^ 40 * 1130621 * 2
def baseEnd_1130621 : Nat := 387034674044750782558583

theorem tailTrace_1130621 : CollatzResearch.WordTrace tailWord_1130621 prefixEnd_1130621 387034674044750782558583 := by
  unfold tailWord_1130621
  simp only [CollatzResearch.WordTrace]
  refine ⟨41237135636960686538855717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27491423757973791025903811 41237135636960686538855717)
  ·
    refine ⟨7731962931930128726035447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41237135636960686538855717 7731962931930128726035447)
    ·
      refine ⟨11597944397895193089053171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7731962931930128726035447 11597944397895193089053171)
      ·
        refine ⟨17396916596842789633579757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11597944397895193089053171 17396916596842789633579757)
        ·
          refine ⟨6523843723816046112592409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17396916596842789633579757 6523843723816046112592409)
          ·
            refine ⟨4892882792862034584444307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6523843723816046112592409 4892882792862034584444307)
            ·
              refine ⟨7339324189293051876666461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892882792862034584444307 7339324189293051876666461)
              ·
                refine ⟨2752246570984894453749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7339324189293051876666461 2752246570984894453749923)
                ·
                  refine ⟨4128369856477341680624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752246570984894453749923 4128369856477341680624885)
                  ·
                    refine ⟨387034674044750782558583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4128369856477341680624885 387034674044750782558583)
                    ·
                      rfl

theorem cell22_1130621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1130621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130621 prefixEnd_1130621 := by exact prefixLift 1130621
  have htrace : WordTrace (prefixWord ++ tailWord_1130621) baseStart_1130621 baseEnd_1130621 := by
    simpa [prefixWord, tailWord_1130621, baseEnd_1130621] using wordTrace_append hprefix tailTrace_1130621
  have hstable : (prefixWord ++ tailWord_1130621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130621).length < 2 ^ (prefixWord ++ tailWord_1130621).sum := by decide
  have hdescent : baseEnd_1130621 < baseStart_1130621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130646 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1130646 : Nat := 118140960795 + 1130646 * 2 ^ 59
def prefixEnd_1130646 : Nat := 4983230072969 + 3 ^ 40 * 1130646 * 2
def baseEnd_1130646 : Nat := 129014410685219683561169

theorem tailTrace_1130646 : CollatzResearch.WordTrace tailWord_1130646 prefixEnd_1130646 129014410685219683561169 := by
  unfold tailWord_1130646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577377966366882238032237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27492031641246743872343861 2577377966366882238032237)
  ·
    refine ⟨966516737387580839262089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2577377966366882238032237 966516737387580839262089)
    ·
      refine ⟨724887553040685629446567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 966516737387580839262089 724887553040685629446567)
      ·
        refine ⟨1087331329561028444169851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724887553040685629446567 1087331329561028444169851)
        ·
          refine ⟨1630996994341542666254777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087331329561028444169851 1630996994341542666254777)
          ·
            refine ⟨1223247745756156999691083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630996994341542666254777 1223247745756156999691083)
            ·
              refine ⟨1834871618634235499536625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223247745756156999691083 1834871618634235499536625)
              ·
                refine ⟨1376153713975676624652469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834871618634235499536625 1376153713975676624652469)
                ·
                  refine ⟨129014410685219683561169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1376153713975676624652469 129014410685219683561169)
                  ·
                    rfl

theorem cell22_1130646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1130646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130646 prefixEnd_1130646 := by exact prefixLift 1130646
  have htrace : WordTrace (prefixWord ++ tailWord_1130646) baseStart_1130646 baseEnd_1130646 := by
    simpa [prefixWord, tailWord_1130646, baseEnd_1130646] using wordTrace_append hprefix tailTrace_1130646
  have hstable : (prefixWord ++ tailWord_1130646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130646).length < 2 ^ (prefixWord ++ tailWord_1130646).sum := by decide
  have hdescent : baseEnd_1130646 < baseStart_1130646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130649 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1130649 : Nat := 118140960795 + 1130649 * 2 ^ 59
def prefixEnd_1130649 : Nat := 4983230072969 + 3 ^ 40 * 1130649 * 2
def baseEnd_1130649 : Nat := 387044259016968042858497

theorem tailTrace_1130649 : CollatzResearch.WordTrace tailWord_1130649 prefixEnd_1130649 387044259016968042858497 := by
  unfold tailWord_1130649
  simp only [CollatzResearch.WordTrace]
  refine ⟨41238156880859247320875001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27492104587239498213916667 41238156880859247320875001)
  ·
    refine ⟨30928617660644435490656251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41238156880859247320875001 30928617660644435490656251)
    ·
      refine ⟨46392926490966653235984377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30928617660644435490656251 46392926490966653235984377)
      ·
        refine ⟨34794694868224989926988283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46392926490966653235984377 34794694868224989926988283)
        ·
          refine ⟨52192042302337484890482425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34794694868224989926988283 52192042302337484890482425)
          ·
            refine ⟨39144031726753113667861819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52192042302337484890482425 39144031726753113667861819)
            ·
              refine ⟨58716047590129670501792729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39144031726753113667861819 58716047590129670501792729)
              ·
                refine ⟨44037035692597252876344547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58716047590129670501792729 44037035692597252876344547)
                ·
                  refine ⟨66055553538895879314516821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44037035692597252876344547 66055553538895879314516821)
                  ·
                    refine ⟨387044259016968042858497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66055553538895879314516821 387044259016968042858497)
                    ·
                      rfl

theorem cell22_1130649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1130649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130649 prefixEnd_1130649 := by exact prefixLift 1130649
  have htrace : WordTrace (prefixWord ++ tailWord_1130649) baseStart_1130649 baseEnd_1130649 := by
    simpa [prefixWord, tailWord_1130649, baseEnd_1130649] using wordTrace_append hprefix tailTrace_1130649
  have hstable : (prefixWord ++ tailWord_1130649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130649).length < 2 ^ (prefixWord ++ tailWord_1130649).sum := by decide
  have hdescent : baseEnd_1130649 < baseStart_1130649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130655 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 2, 3]
def baseStart_1130655 : Nat := 118140960795 + 1130655 * 2 ^ 59
def prefixEnd_1130655 : Nat := 4983230072969 + 3 ^ 40 * 1130655 * 2
def baseEnd_1130655 : Nat := 387046312939586027208479

theorem tailTrace_1130655 : CollatzResearch.WordTrace tailWord_1130655 prefixEnd_1130655 387046312939586027208479 := by
  unfold tailWord_1130655
  simp only [CollatzResearch.WordTrace]
  refine ⟨41238375718837510345593419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27492250479225006897062279 41238375718837510345593419)
  ·
    refine ⟨61857563578256265518390129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41238375718837510345593419 61857563578256265518390129)
    ·
      refine ⟨46393172683692199138792597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61857563578256265518390129 46393172683692199138792597)
      ·
        refine ⟨2174679969548071834630903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46393172683692199138792597 2174679969548071834630903)
        ·
          refine ⟨3262019954322107751946355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174679969548071834630903 3262019954322107751946355)
          ·
            refine ⟨4893029931483161627919533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262019954322107751946355 4893029931483161627919533)
            ·
              refine ⟨1834886224306185610469825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4893029931483161627919533 1834886224306185610469825)
              ·
                refine ⟨1376164668229639207852369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834886224306185610469825 1376164668229639207852369)
                ·
                  refine ⟨1032123501172229405889277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376164668229639207852369 1032123501172229405889277)
                  ·
                    refine ⟨387046312939586027208479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032123501172229405889277 387046312939586027208479)
                    ·
                      rfl

theorem cell22_1130655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_1130655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130655 prefixEnd_1130655 := by exact prefixLift 1130655
  have htrace : WordTrace (prefixWord ++ tailWord_1130655) baseStart_1130655 baseEnd_1130655 := by
    simpa [prefixWord, tailWord_1130655, baseEnd_1130655] using wordTrace_append hprefix tailTrace_1130655
  have hstable : (prefixWord ++ tailWord_1130655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130655).length < 2 ^ (prefixWord ++ tailWord_1130655).sum := by decide
  have hdescent : baseEnd_1130655 < baseStart_1130655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130717 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1130717 : Nat := 118140960795 + 1130717 * 2 ^ 59
def prefixEnd_1130717 : Nat := 4983230072969 + 3 ^ 40 * 1130717 * 2
def baseEnd_1130717 : Nat := 387067536806638532158289

theorem tailTrace_1130717 : CollatzResearch.WordTrace tailWord_1130717 prefixEnd_1130717 387067536806638532158289 := by
  unfold tailWord_1130717
  simp only [CollatzResearch.WordTrace]
  refine ⟨41240637044612894934350405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27493758029741929956233603 41240637044612894934350405)
  ·
    refine ⟨7732619445864917800190701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41240637044612894934350405 7732619445864917800190701)
    ·
      refine ⟨2899732292199344175071513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7732619445864917800190701 2899732292199344175071513)
      ·
        refine ⟨2174799219149508131303635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2899732292199344175071513 2174799219149508131303635)
        ·
          refine ⟨3262198828724262196955453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174799219149508131303635 3262198828724262196955453)
          ·
            refine ⟨1223324560771598323858295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3262198828724262196955453 1223324560771598323858295)
            ·
              refine ⟨1834986841157397485787443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223324560771598323858295 1834986841157397485787443)
              ·
                refine ⟨2752480261736096228681165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834986841157397485787443 2752480261736096228681165)
                ·
                  refine ⟨1032180098151036085755437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2752480261736096228681165 1032180098151036085755437)
                  ·
                    refine ⟨387067536806638532158289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032180098151036085755437 387067536806638532158289)
                    ·
                      rfl

theorem cell22_1130717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1130717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130717 prefixEnd_1130717 := by exact prefixLift 1130717
  have htrace : WordTrace (prefixWord ++ tailWord_1130717) baseStart_1130717 baseEnd_1130717 := by
    simpa [prefixWord, tailWord_1130717, baseEnd_1130717] using wordTrace_append hprefix tailTrace_1130717
  have hstable : (prefixWord ++ tailWord_1130717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130717).length < 2 ^ (prefixWord ++ tailWord_1130717).sum := by decide
  have hdescent : baseEnd_1130717 < baseStart_1130717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130773 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1130773 : Nat := 118140960795 + 1130773 * 2 ^ 59
def prefixEnd_1130773 : Nat := 4983230072969 + 3 ^ 40 * 1130773 * 2
def baseEnd_1130773 : Nat := 387086706751073052758117

theorem tailTrace_1130773 : CollatzResearch.WordTrace tailWord_1130773 prefixEnd_1130773 387086706751073052758117 := by
  unfold tailWord_1130773
  simp only [CollatzResearch.WordTrace]
  refine ⟨41242679532410016498388973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27495119688273344332259315 41242679532410016498388973)
  ·
    refine ⟨15466004824653756186895865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41242679532410016498388973 15466004824653756186895865)
    ·
      refine ⟨11599503618490317140171899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15466004824653756186895865 11599503618490317140171899)
      ·
        refine ⟨17399255427735475710257849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11599503618490317140171899 17399255427735475710257849)
        ·
          refine ⟨13049441570801606782693387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17399255427735475710257849 13049441570801606782693387)
          ·
            refine ⟨19574162356202410174040081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13049441570801606782693387 19574162356202410174040081)
            ·
              refine ⟨14680621767151807630530061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19574162356202410174040081 14680621767151807630530061)
              ·
                refine ⟨5505233162681927861448773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14680621767151807630530061 5505233162681927861448773)
                ·
                  refine ⟨1032231218002861474021645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5505233162681927861448773 1032231218002861474021645)
                  ·
                    refine ⟨387086706751073052758117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032231218002861474021645 387086706751073052758117)
                    ·
                      rfl

theorem cell22_1130773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1130773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130773 prefixEnd_1130773 := by exact prefixLift 1130773
  have htrace : WordTrace (prefixWord ++ tailWord_1130773) baseStart_1130773 baseEnd_1130773 := by
    simpa [prefixWord, tailWord_1130773, baseEnd_1130773] using wordTrace_append hprefix tailTrace_1130773
  have hstable : (prefixWord ++ tailWord_1130773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130773).length < 2 ^ (prefixWord ++ tailWord_1130773).sum := by decide
  have hdescent : baseEnd_1130773 < baseStart_1130773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130775 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 4]
def baseStart_1130775 : Nat := 118140960795 + 1130775 * 2 ^ 59
def prefixEnd_1130775 : Nat := 4983230072969 + 3 ^ 40 * 1130775 * 2
def baseEnd_1130775 : Nat := 129029130463981904736037

theorem tailTrace_1130775 : CollatzResearch.WordTrace tailWord_1130775 prefixEnd_1130775 129029130463981904736037 := by
  unfold tailWord_1130775
  simp only [CollatzResearch.WordTrace]
  refine ⟨41242752478402770839961779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27495168318935180559974519 41242752478402770839961779)
  ·
    refine ⟨61864128717604156259942669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41242752478402770839961779 61864128717604156259942669)
    ·
      refine ⟨23199048269101558597478501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61864128717604156259942669 23199048269101558597478501)
      ·
        refine ⟨4349821550456542237027219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23199048269101558597478501 4349821550456542237027219)
        ·
          refine ⟨6524732325684813355540829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349821550456542237027219 6524732325684813355540829)
          ·
            refine ⟨2446774622131805008327811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6524732325684813355540829 2446774622131805008327811)
            ·
              refine ⟨3670161933197707512491717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446774622131805008327811 3670161933197707512491717)
              ·
                refine ⟨688155362474570158592197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3670161933197707512491717 688155362474570158592197)
                ·
                  refine ⟨129029130463981904736037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688155362474570158592197 129029130463981904736037)
                  ·
                    rfl

theorem cell22_1130775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 4].length) (baseStart_1130775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130775 prefixEnd_1130775 := by exact prefixLift 1130775
  have htrace : WordTrace (prefixWord ++ tailWord_1130775) baseStart_1130775 baseEnd_1130775 := by
    simpa [prefixWord, tailWord_1130775, baseEnd_1130775] using wordTrace_append hprefix tailTrace_1130775
  have hstable : (prefixWord ++ tailWord_1130775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130775).length < 2 ^ (prefixWord ++ tailWord_1130775).sum := by decide
  have hdescent : baseEnd_1130775 < baseStart_1130775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130803 : List Nat := [1, 1, 1, 2, 5, 1, 5, 6]
def baseStart_1130803 : Nat := 118140960795 + 1130803 * 2 ^ 59
def prefixEnd_1130803 : Nat := 4983230072969 + 3 ^ 40 * 1130803 * 2
def baseEnd_1130803 : Nat := 43010775151573663834225

theorem tailTrace_1130803 : CollatzResearch.WordTrace tailWord_1130803 prefixEnd_1130803 43010775151573663834225 := by
  unfold tailWord_1130803
  simp only [CollatzResearch.WordTrace]
  refine ⟨41243773722301331621981063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27495849148200887747987375 41243773722301331621981063)
  ·
    refine ⟨61865660583451997432971595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41243773722301331621981063 61865660583451997432971595)
    ·
      refine ⟨92798490875177996149457393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61865660583451997432971595 92798490875177996149457393)
      ·
        refine ⟨69598868156383497112093045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92798490875177996149457393 69598868156383497112093045)
        ·
          refine ⟨6524893889660952854258723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69598868156383497112093045 6524893889660952854258723)
          ·
            refine ⟨9787340834491429281388085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6524893889660952854258723 9787340834491429281388085)
            ·
              refine ⟨917563203233571495130133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9787340834491429281388085 917563203233571495130133)
              ·
                refine ⟨43010775151573663834225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 917563203233571495130133 43010775151573663834225)
                ·
                  rfl

theorem cell22_1130803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 6].length) (baseStart_1130803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130803 prefixEnd_1130803 := by exact prefixLift 1130803
  have htrace : WordTrace (prefixWord ++ tailWord_1130803) baseStart_1130803 baseEnd_1130803 := by
    simpa [prefixWord, tailWord_1130803, baseEnd_1130803] using wordTrace_append hprefix tailTrace_1130803
  have hstable : (prefixWord ++ tailWord_1130803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130803).length < 2 ^ (prefixWord ++ tailWord_1130803).sum := by decide
  have hdescent : baseEnd_1130803 < baseStart_1130803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130816 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1130816 : Nat := 118140960795 + 1130816 * 2 ^ 59
def prefixEnd_1130816 : Nat := 4983230072969 + 3 ^ 40 * 1130816 * 2
def baseEnd_1130816 : Nat := 387101426529835273932985

theorem tailTrace_1130816 : CollatzResearch.WordTrace tailWord_1130816 prefixEnd_1130816 387101426529835273932985 := by
  unfold tailWord_1130816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20622123935627117421102151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27496165247502823228136201 20622123935627117421102151)
  ·
    refine ⟨30933185903440676131653227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20622123935627117421102151 30933185903440676131653227)
    ·
      refine ⟨46399778855161014197479841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30933185903440676131653227 46399778855161014197479841)
      ·
        refine ⟨34799834141370760648109881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46399778855161014197479841 34799834141370760648109881)
        ·
          refine ⟨26099875606028070486082411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34799834141370760648109881 26099875606028070486082411)
          ·
            refine ⟨39149813409042105729123617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26099875606028070486082411 39149813409042105729123617)
            ·
              refine ⟨29362360056781579296842713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39149813409042105729123617 29362360056781579296842713)
              ·
                refine ⟨22021770042586184472632035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29362360056781579296842713 22021770042586184472632035)
                ·
                  refine ⟨33032655063879276708948053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22021770042586184472632035 33032655063879276708948053)
                  ·
                    refine ⟨387101426529835273932985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33032655063879276708948053 387101426529835273932985)
                    ·
                      rfl

theorem cell22_1130816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1130816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130816 prefixEnd_1130816 := by exact prefixLift 1130816
  have htrace : WordTrace (prefixWord ++ tailWord_1130816) baseStart_1130816 baseEnd_1130816 := by
    simpa [prefixWord, tailWord_1130816, baseEnd_1130816] using wordTrace_append hprefix tailTrace_1130816
  have hstable : (prefixWord ++ tailWord_1130816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130816).length < 2 ^ (prefixWord ++ tailWord_1130816).sum := by decide
  have hdescent : baseEnd_1130816 < baseStart_1130816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130820 : List Nat := [2, 3, 4, 1, 2, 1, 9]
def baseStart_1130820 : Nat := 118140960795 + 1130820 * 2 ^ 59
def prefixEnd_1130820 : Nat := 4983230072969 + 3 ^ 40 * 1130820 * 2
def baseEnd_1130820 : Nat := 14337140585614096178999

theorem tailTrace_1130820 : CollatzResearch.WordTrace tailWord_1130820 prefixEnd_1130820 14337140585614096178999 := by
  unfold tailWord_1130820
  simp only [CollatzResearch.WordTrace]
  refine ⟨20622196881619871762674957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27496262508826495683566609 20622196881619871762674957)
  ·
    refine ⟨7733323830607451911003109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20622196881619871762674957 7733323830607451911003109)
    ·
      refine ⟨1449998218238897233313083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7733323830607451911003109 1449998218238897233313083)
      ·
        refine ⟨2174997327358345849969625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449998218238897233313083 2174997327358345849969625)
        ·
          refine ⟨1631247995518759387477219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2174997327358345849969625 1631247995518759387477219)
          ·
            refine ⟨2446871993278139081215829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631247995518759387477219 2446871993278139081215829)
            ·
              refine ⟨14337140585614096178999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2446871993278139081215829 14337140585614096178999)
              ·
                rfl

theorem cell22_1130820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 9].length) (baseStart_1130820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130820 prefixEnd_1130820 := by exact prefixLift 1130820
  have htrace : WordTrace (prefixWord ++ tailWord_1130820) baseStart_1130820 baseEnd_1130820 := by
    simpa [prefixWord, tailWord_1130820, baseEnd_1130820] using wordTrace_append hprefix tailTrace_1130820
  have hstable : (prefixWord ++ tailWord_1130820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130820).length < 2 ^ (prefixWord ++ tailWord_1130820).sum := by decide
  have hdescent : baseEnd_1130820 < baseStart_1130820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130869 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1130869 : Nat := 118140960795 + 1130869 * 2 ^ 59
def prefixEnd_1130869 : Nat := 4983230072969 + 3 ^ 40 * 1130869 * 2
def baseEnd_1130869 : Nat := 387119569512960802357823

theorem tailTrace_1130869 : CollatzResearch.WordTrace tailWord_1130869 prefixEnd_1130869 387119569512960802357823 := by
  unfold tailWord_1130869
  simp only [CollatzResearch.WordTrace]
  refine ⟨41246180940062224893883661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27497453960041483262589107 41246180940062224893883661)
  ·
    refine ⟨15467317852523334335206373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41246180940062224893883661 15467317852523334335206373)
    ·
      refine ⟨2900122097348125187851195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15467317852523334335206373 2900122097348125187851195)
      ·
        refine ⟨4350183146022187781776793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900122097348125187851195 4350183146022187781776793)
        ·
          refine ⟨3262637359516640836332595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4350183146022187781776793 3262637359516640836332595)
          ·
            refine ⟨4893956039274961254498893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262637359516640836332595 4893956039274961254498893)
            ·
              refine ⟨1835233514728110470437085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4893956039274961254498893 1835233514728110470437085)
              ·
                refine ⟨688212568023041426413907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1835233514728110470437085 688212568023041426413907)
                ·
                  refine ⟨1032318852034562139620861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688212568023041426413907 1032318852034562139620861)
                  ·
                    refine ⟨387119569512960802357823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032318852034562139620861 387119569512960802357823)
                    ·
                      rfl

theorem cell22_1130869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1130869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130869 prefixEnd_1130869 := by exact prefixLift 1130869
  have htrace : WordTrace (prefixWord ++ tailWord_1130869) baseStart_1130869 baseEnd_1130869 := by
    simpa [prefixWord, tailWord_1130869, baseEnd_1130869] using wordTrace_append hprefix tailTrace_1130869
  have hstable : (prefixWord ++ tailWord_1130869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130869).length < 2 ^ (prefixWord ++ tailWord_1130869).sum := by decide
  have hdescent : baseEnd_1130869 < baseStart_1130869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130912 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_1130912 : Nat := 118140960795 + 1130912 * 2 ^ 59
def prefixEnd_1130912 : Nat := 4983230072969 + 3 ^ 40 * 1130912 * 2
def baseEnd_1130912 : Nat := 387134289291723023532691

theorem tailTrace_1130912 : CollatzResearch.WordTrace tailWord_1130912 prefixEnd_1130912 387134289291723023532691 := by
  unfold tailWord_1130912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623874639453221618849495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27498499519270962158465993 20623874639453221618849495)
  ·
    refine ⟨30935811959179832428274243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20623874639453221618849495 30935811959179832428274243)
    ·
      refine ⟨46403717938769748642411365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30935811959179832428274243 46403717938769748642411365)
      ·
        refine ⟨8700697113519327870452131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46403717938769748642411365 8700697113519327870452131)
        ·
          refine ⟨13051045670278991805678197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700697113519327870452131 13051045670278991805678197)
          ·
            refine ⟨1223535531588655481782331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13051045670278991805678197 1223535531588655481782331)
            ·
              refine ⟨1835303297382983222673497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223535531588655481782331 1835303297382983222673497)
              ·
                refine ⟨1376477473037237417005123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835303297382983222673497 1376477473037237417005123)
                ·
                  refine ⟨2064716209555856125507685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376477473037237417005123 2064716209555856125507685)
                  ·
                    refine ⟨387134289291723023532691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2064716209555856125507685 387134289291723023532691)
                    ·
                      rfl

theorem cell22_1130912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_1130912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130912 prefixEnd_1130912 := by exact prefixLift 1130912
  have htrace : WordTrace (prefixWord ++ tailWord_1130912) baseStart_1130912 baseEnd_1130912 := by
    simpa [prefixWord, tailWord_1130912, baseEnd_1130912] using wordTrace_append hprefix tailTrace_1130912
  have hstable : (prefixWord ++ tailWord_1130912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130912).length < 2 ^ (prefixWord ++ tailWord_1130912).sum := by decide
  have hdescent : baseEnd_1130912 < baseStart_1130912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130942 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1130942 : Nat := 118140960795 + 1130942 * 2 ^ 59
def prefixEnd_1130942 : Nat := 4983230072969 + 3 ^ 40 * 1130942 * 2
def baseEnd_1130942 : Nat := 387144558904812945282599

theorem tailTrace_1130942 : CollatzResearch.WordTrace tailWord_1130942 prefixEnd_1130942 387144558904812945282599 := by
  unfold tailWord_1130942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156105433599719795161385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27499228979198505574194053 5156105433599719795161385)
  ·
    refine ⟨3867079075199789846371039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5156105433599719795161385 3867079075199789846371039)
    ·
      refine ⟨5800618612799684769556559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867079075199789846371039 5800618612799684769556559)
      ·
        refine ⟨8700927919199527154334839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800618612799684769556559 8700927919199527154334839)
        ·
          refine ⟨13051391878799290731502259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700927919199527154334839 13051391878799290731502259)
          ·
            refine ⟨19577087818198936097253389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13051391878799290731502259 19577087818198936097253389)
            ·
              refine ⟨7341407931824601036470021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19577087818198936097253389 7341407931824601036470021)
              ·
                refine ⟨1376513987217112694338129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7341407931824601036470021 1376513987217112694338129)
                ·
                  refine ⟨1032385490412834520753597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376513987217112694338129 1032385490412834520753597)
                  ·
                    refine ⟨387144558904812945282599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032385490412834520753597 387144558904812945282599)
                    ·
                      rfl

theorem cell22_1130942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1130942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130942 prefixEnd_1130942 := by exact prefixLift 1130942
  have htrace : WordTrace (prefixWord ++ tailWord_1130942) baseStart_1130942 baseEnd_1130942 := by
    simpa [prefixWord, tailWord_1130942, baseEnd_1130942] using wordTrace_append hprefix tailTrace_1130942
  have hstable : (prefixWord ++ tailWord_1130942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130942).length < 2 ^ (prefixWord ++ tailWord_1130942).sum := by decide
  have hdescent : baseEnd_1130942 < baseStart_1130942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130968 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1130968 : Nat := 118140960795 + 1130968 * 2 ^ 59
def prefixEnd_1130968 : Nat := 4983230072969 + 3 ^ 40 * 1130968 * 2
def baseEnd_1130968 : Nat := 387153459236157544132519

theorem tailTrace_1130968 : CollatzResearch.WordTrace tailWord_1130968 prefixEnd_1130968 387153459236157544132519 := by
  unfold tailWord_1130968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20624895883351782400868779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27499861177802376534491705 20624895883351782400868779)
  ·
    refine ⟨30937343825027673601303169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20624895883351782400868779 30937343825027673601303169)
    ·
      refine ⟨23203007868770755200977377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30937343825027673601303169 23203007868770755200977377)
      ·
        refine ⟨17402255901578066400733033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23203007868770755200977377 17402255901578066400733033)
        ·
          refine ⟨13051691926183549800549775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17402255901578066400733033 13051691926183549800549775)
          ·
            refine ⟨19577537889275324700824663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13051691926183549800549775 19577537889275324700824663)
            ·
              refine ⟨29366306833912987051236995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19577537889275324700824663 29366306833912987051236995)
              ·
                refine ⟨44049460250869480576855493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29366306833912987051236995 44049460250869480576855493)
                ·
                  refine ⟨8259273797038027608160405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44049460250869480576855493 8259273797038027608160405)
                  ·
                    refine ⟨387153459236157544132519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8259273797038027608160405 387153459236157544132519)
                    ·
                      rfl

theorem cell22_1130968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1130968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1130968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1130968 prefixEnd_1130968 := by exact prefixLift 1130968
  have htrace : WordTrace (prefixWord ++ tailWord_1130968) baseStart_1130968 baseEnd_1130968 := by
    simpa [prefixWord, tailWord_1130968, baseEnd_1130968] using wordTrace_append hprefix tailTrace_1130968
  have hstable : (prefixWord ++ tailWord_1130968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130968).length < 2 ^ (prefixWord ++ tailWord_1130968).sum := by decide
  have hdescent : baseEnd_1130968 < baseStart_1130968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131021 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1131021 : Nat := 118140960795 + 1131021 * 2 ^ 59
def prefixEnd_1131021 : Nat := 4983230072969 + 3 ^ 40 * 1131021 * 2
def baseEnd_1131021 : Nat := 387171602219283072557357

theorem tailTrace_1131021 : CollatzResearch.WordTrace tailWord_1131021 prefixEnd_1131021 387171602219283072557357 := by
  unfold tailWord_1131021
  simp only [CollatzResearch.WordTrace]
  refine ⟨41251724835511554853416917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27501149890341036568944611 41251724835511554853416917)
  ·
    refine ⟨966837300832302066876959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41251724835511554853416917 966837300832302066876959)
    ·
      refine ⟨1450255951248453100315439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966837300832302066876959 1450255951248453100315439)
      ·
        refine ⟨2175383926872679650473159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450255951248453100315439 2175383926872679650473159)
        ·
          refine ⟨3263075890309019475709739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175383926872679650473159 3263075890309019475709739)
          ·
            refine ⟨4894613835463529213564609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263075890309019475709739 4894613835463529213564609)
            ·
              refine ⟨3670960376597646910173457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4894613835463529213564609 3670960376597646910173457)
              ·
                refine ⟨2753220282448235182630093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670960376597646910173457 2753220282448235182630093)
                ·
                  refine ⟨1032457605918088193486285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2753220282448235182630093 1032457605918088193486285)
                  ·
                    refine ⟨387171602219283072557357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032457605918088193486285 387171602219283072557357)
                    ·
                      rfl

theorem cell22_1131021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1131021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131021 prefixEnd_1131021 := by exact prefixLift 1131021
  have htrace : WordTrace (prefixWord ++ tailWord_1131021) baseStart_1131021 baseEnd_1131021 := by
    simpa [prefixWord, tailWord_1131021, baseEnd_1131021] using wordTrace_append hprefix tailTrace_1131021
  have hstable : (prefixWord ++ tailWord_1131021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131021).length < 2 ^ (prefixWord ++ tailWord_1131021).sum := by decide
  have hdescent : baseEnd_1131021 < baseStart_1131021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131090 : List Nat := [3, 2, 2, 1, 2, 1, 1, 10]
def baseStart_1131090 : Nat := 118140960795 + 1131090 * 2 ^ 59
def prefixEnd_1131090 : Nat := 4983230072969 + 3 ^ 40 * 1131090 * 2
def baseEnd_1131090 : Nat := 43021691369932210286905

theorem tailTrace_1131090 : CollatzResearch.WordTrace tailWord_1131090 prefixEnd_1131090 43021691369932210286905 := by
  unfold tailWord_1131090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10313560368065394909419681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27502827648174386425119149 10313560368065394909419681)
  ·
    refine ⟨7735170276049046182064761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10313560368065394909419681 7735170276049046182064761)
    ·
      refine ⟨5801377707036784636548571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7735170276049046182064761 5801377707036784636548571)
      ·
        refine ⟨8702066560555176954822857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801377707036784636548571 8702066560555176954822857)
        ·
          refine ⟨6526549920416382716117143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8702066560555176954822857 6526549920416382716117143)
          ·
            refine ⟨9789824880624574074175715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526549920416382716117143 9789824880624574074175715)
            ·
              refine ⟨14684737320936861111263573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789824880624574074175715 14684737320936861111263573)
              ·
                refine ⟨43021691369932210286905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14684737320936861111263573 43021691369932210286905)
                ·
                  rfl

theorem cell22_1131090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_1131090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131090 prefixEnd_1131090 := by exact prefixLift 1131090
  have htrace : WordTrace (prefixWord ++ tailWord_1131090) baseStart_1131090 baseEnd_1131090 := by
    simpa [prefixWord, tailWord_1131090, baseEnd_1131090] using wordTrace_append hprefix tailTrace_1131090
  have hstable : (prefixWord ++ tailWord_1131090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131090).length < 2 ^ (prefixWord ++ tailWord_1131090).sum := by decide
  have hdescent : baseEnd_1131090 < baseStart_1131090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131092 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1131092 : Nat := 118140960795 + 1131092 * 2 ^ 59
def prefixEnd_1131092 : Nat := 4983230072969 + 3 ^ 40 * 1131092 * 2
def baseEnd_1131092 : Nat := 387195906970262554032139

theorem tailTrace_1131092 : CollatzResearch.WordTrace tailWord_1131092 prefixEnd_1131092 387195906970262554032139 := by
  unfold tailWord_1131092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20627157209127166989625765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27502876278836222652834353 20627157209127166989625765)
  ·
    refine ⟨3867591976711343810554831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20627157209127166989625765 3867591976711343810554831)
    ·
      refine ⟨5801387965067015715832247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867591976711343810554831 5801387965067015715832247)
      ·
        refine ⟨8702081947600523573748371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801387965067015715832247 8702081947600523573748371)
        ·
          refine ⟨13053122921400785360622557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702081947600523573748371 13053122921400785360622557)
          ·
            refine ⟨4894921095525294510233459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13053122921400785360622557 4894921095525294510233459)
            ·
              refine ⟨7342381643287941765350189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894921095525294510233459 7342381643287941765350189)
              ·
                refine ⟨2753393116232978162006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7342381643287941765350189 2753393116232978162006321)
                ·
                  refine ⟨2065044837174733621504741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753393116232978162006321 2065044837174733621504741)
                  ·
                    refine ⟨387195906970262554032139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2065044837174733621504741 387195906970262554032139)
                    ·
                      rfl

theorem cell22_1131092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1131092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131092 prefixEnd_1131092 := by exact prefixLift 1131092
  have htrace : WordTrace (prefixWord ++ tailWord_1131092) baseStart_1131092 baseEnd_1131092 := by
    simpa [prefixWord, tailWord_1131092, baseEnd_1131092] using wordTrace_append hprefix tailTrace_1131092
  have hstable : (prefixWord ++ tailWord_1131092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131092).length < 2 ^ (prefixWord ++ tailWord_1131092).sum := by decide
  have hdescent : baseEnd_1131092 < baseStart_1131092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131197 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 6]
def baseStart_1131197 : Nat := 118140960795 + 1131197 * 2 ^ 59
def prefixEnd_1131197 : Nat := 4983230072969 + 3 ^ 40 * 1131197 * 2
def baseEnd_1131197 : Nat := 129077283538692426718939

theorem tailTrace_1131197 : CollatzResearch.WordTrace tailWord_1131197 prefixEnd_1131197 129077283538692426718939 := by
  unfold tailWord_1131197
  simp only [CollatzResearch.WordTrace]
  refine ⟨41258144082873936911823845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27505429388582624607882563 41258144082873936911823845)
  ·
    refine ⟨7735902015538863170966971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41258144082873936911823845 7735902015538863170966971)
    ·
      refine ⟨11603853023308294756450457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7735902015538863170966971 11603853023308294756450457)
      ·
        refine ⟨8702889767481221067337843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11603853023308294756450457 8702889767481221067337843)
        ·
          refine ⟨13054334651221831601006765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702889767481221067337843 13054334651221831601006765)
          ·
            refine ⟨4895375494208186850377537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13054334651221831601006765 4895375494208186850377537)
            ·
              refine ⟨3671531620656140137783153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895375494208186850377537 3671531620656140137783153)
              ·
                refine ⟨2753648715492105103337365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3671531620656140137783153 2753648715492105103337365)
                ·
                  refine ⟨129077283538692426718939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2753648715492105103337365 129077283538692426718939)
                  ·
                    rfl

theorem cell22_1131197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_1131197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131197 prefixEnd_1131197 := by exact prefixLift 1131197
  have htrace : WordTrace (prefixWord ++ tailWord_1131197) baseStart_1131197 baseEnd_1131197 := by
    simpa [prefixWord, tailWord_1131197, baseEnd_1131197] using wordTrace_append hprefix tailTrace_1131197
  have hstable : (prefixWord ++ tailWord_1131197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131197).length < 2 ^ (prefixWord ++ tailWord_1131197).sum := by decide
  have hdescent : baseEnd_1131197 < baseStart_1131197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131199 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 1, 4]
def baseStart_1131199 : Nat := 118140960795 + 1131199 * 2 ^ 59
def prefixEnd_1131199 : Nat := 4983230072969 + 3 ^ 40 * 1131199 * 2
def baseEnd_1131199 : Nat := 387232535256949941606811

theorem tailTrace_1131199 : CollatzResearch.WordTrace tailWord_1131199 prefixEnd_1131199 387232535256949941606811 := by
  unfold tailWord_1131199
  simp only [CollatzResearch.WordTrace]
  refine ⟨41258217028866691253396651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27505478019244460835597767 41258217028866691253396651)
  ·
    refine ⟨61887325543300036880094977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41258217028866691253396651 61887325543300036880094977)
    ·
      refine ⟨46415494157475027660071233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61887325543300036880094977 46415494157475027660071233)
      ·
        refine ⟨34811620618106270745053425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46415494157475027660071233 34811620618106270745053425)
        ·
          refine ⟨26108715463579703058790069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34811620618106270745053425 26108715463579703058790069)
          ·
            refine ⟨2447692074710597161761569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26108715463579703058790069 2447692074710597161761569)
            ·
              refine ⟨1835769056032947871321177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447692074710597161761569 1835769056032947871321177)
              ·
                refine ⟨1376826792024710903490883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835769056032947871321177 1376826792024710903490883)
                ·
                  refine ⟨2065240188037066355236325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376826792024710903490883 2065240188037066355236325)
                  ·
                    refine ⟨387232535256949941606811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2065240188037066355236325 387232535256949941606811)
                    ·
                      rfl

theorem cell22_1131199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_1131199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131199 prefixEnd_1131199 := by exact prefixLift 1131199
  have htrace : WordTrace (prefixWord ++ tailWord_1131199) baseStart_1131199 baseEnd_1131199 := by
    simpa [prefixWord, tailWord_1131199, baseEnd_1131199] using wordTrace_append hprefix tailTrace_1131199
  have hstable : (prefixWord ++ tailWord_1131199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131199).length < 2 ^ (prefixWord ++ tailWord_1131199).sum := by decide
  have hdescent : baseEnd_1131199 < baseStart_1131199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131231 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 4]
def baseStart_1131231 : Nat := 118140960795 + 1131231 * 2 ^ 59
def prefixEnd_1131231 : Nat := 4983230072969 + 3 ^ 40 * 1131231 * 2
def baseEnd_1131231 : Nat := 129081163170304174935571

theorem tailTrace_1131231 : CollatzResearch.WordTrace tailWord_1131231 prefixEnd_1131231 129081163170304174935571 := by
  unfold tailWord_1131231
  simp only [CollatzResearch.WordTrace]
  refine ⟨41259384164750760718561547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27506256109833840479041031 41259384164750760718561547)
  ·
    refine ⟨61889076247126141077842321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41259384164750760718561547 61889076247126141077842321)
    ·
      refine ⟨46416807185344605808381741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61889076247126141077842321 46416807185344605808381741)
      ·
        refine ⟨17406302694504227178143153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46416807185344605808381741 17406302694504227178143153)
        ·
          refine ⟨13054727020878170383607365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17406302694504227178143153 13054727020878170383607365)
          ·
            refine ⟨2447761316414656946926381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13054727020878170383607365 2447761316414656946926381)
            ·
              refine ⟨917910493655496355097393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2447761316414656946926381 917910493655496355097393)
              ·
                refine ⟨688432870241622266323045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917910493655496355097393 688432870241622266323045)
                ·
                  refine ⟨129081163170304174935571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688432870241622266323045 129081163170304174935571)
                  ·
                    rfl

theorem cell22_1131231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 4].length) (baseStart_1131231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131231 prefixEnd_1131231 := by exact prefixLift 1131231
  have htrace : WordTrace (prefixWord ++ tailWord_1131231) baseStart_1131231 baseEnd_1131231 := by
    simpa [prefixWord, tailWord_1131231, baseEnd_1131231] using wordTrace_append hprefix tailTrace_1131231
  have hstable : (prefixWord ++ tailWord_1131231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131231).length < 2 ^ (prefixWord ++ tailWord_1131231).sum := by decide
  have hdescent : baseEnd_1131231 < baseStart_1131231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131246 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1131246 : Nat := 118140960795 + 1131246 * 2 ^ 59
def prefixEnd_1131246 : Nat := 4983230072969 + 3 ^ 40 * 1131246 * 2
def baseEnd_1131246 : Nat := 387248624317457485681667

theorem tailTrace_1131246 : CollatzResearch.WordTrace tailWord_1131246 prefixEnd_1131246 387248624317457485681667 := by
  unfold tailWord_1131246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157491407462052285044699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27506620839797612186905061 5157491407462052285044699)
  ·
    refine ⟨7736237111193078427567049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5157491407462052285044699 7736237111193078427567049)
    ·
      refine ⟨5802177833394808820675287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7736237111193078427567049 5802177833394808820675287)
      ·
        refine ⟨8703266750092213231012931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802177833394808820675287 8703266750092213231012931)
        ·
          refine ⟨13054900125138319846519397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8703266750092213231012931 13054900125138319846519397)
          ·
            refine ⟨2447793773463434971222387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13054900125138319846519397 2447793773463434971222387)
            ·
              refine ⟨3671690660195152456833581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447793773463434971222387 3671690660195152456833581)
              ·
                refine ⟨1376883997573182171312593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3671690660195152456833581 1376883997573182171312593)
                ·
                  refine ⟨1032662998179886628484445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376883997573182171312593 1032662998179886628484445)
                  ·
                    refine ⟨387248624317457485681667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032662998179886628484445 387248624317457485681667)
                    ·
                      rfl

theorem cell22_1131246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1131246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131246 prefixEnd_1131246 := by exact prefixLift 1131246
  have htrace : WordTrace (prefixWord ++ tailWord_1131246) baseStart_1131246 baseEnd_1131246 := by
    simpa [prefixWord, tailWord_1131246, baseEnd_1131246] using wordTrace_append hprefix tailTrace_1131246
  have hstable : (prefixWord ++ tailWord_1131246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131246).length < 2 ^ (prefixWord ++ tailWord_1131246).sum := by decide
  have hdescent : baseEnd_1131246 < baseStart_1131246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131282 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_1131282 : Nat := 118140960795 + 1131282 * 2 ^ 59
def prefixEnd_1131282 : Nat := 4983230072969 + 3 ^ 40 * 1131282 * 2
def baseEnd_1131282 : Nat := 129086982617721797260519

theorem tailTrace_1131282 : CollatzResearch.WordTrace tailWord_1131282 prefixEnd_1131282 129086982617721797260519 := by
  unfold tailWord_1131282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10315311071891499107167025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27507496191710664285778733 10315311071891499107167025)
  ·
    refine ⟨7736483303918624330375269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10315311071891499107167025 7736483303918624330375269)
    ·
      refine ⟨1450590619484742061945363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7736483303918624330375269 1450590619484742061945363)
      ·
        refine ⟨2175885929227113092918045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450590619484742061945363 2175885929227113092918045)
        ·
          refine ⟨815957223460167409844267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2175885929227113092918045 815957223460167409844267)
          ·
            refine ⟨1223935835190251114766401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815957223460167409844267 1223935835190251114766401)
            ·
              refine ⟨917951876392688336074801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223935835190251114766401 917951876392688336074801)
              ·
                refine ⟨688463907294516252056101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917951876392688336074801 688463907294516252056101)
                ·
                  refine ⟨129086982617721797260519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688463907294516252056101 129086982617721797260519)
                  ·
                    rfl

theorem cell22_1131282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_1131282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131282 prefixEnd_1131282 := by exact prefixLift 1131282
  have htrace : WordTrace (prefixWord ++ tailWord_1131282) baseStart_1131282 baseEnd_1131282 := by
    simpa [prefixWord, tailWord_1131282, baseEnd_1131282] using wordTrace_append hprefix tailTrace_1131282
  have hstable : (prefixWord ++ tailWord_1131282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131282).length < 2 ^ (prefixWord ++ tailWord_1131282).sum := by decide
  have hdescent : baseEnd_1131282 < baseStart_1131282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131293 : List Nat := [1, 4, 2, 4, 2, 1, 1, 7]
def baseStart_1131293 : Nat := 118140960795 + 1131293 * 2 ^ 59
def prefixEnd_1131293 : Nat := 4983230072969 + 3 ^ 40 * 1131293 * 2
def baseEnd_1131293 : Nat := 43029412597551669972947

theorem tailTrace_1131293 : CollatzResearch.WordTrace tailWord_1131293 prefixEnd_1131293 43029412597551669972947 := by
  unfold tailWord_1131293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41261645490526145307318533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27507763660350763538212355 41261645490526145307318533)
  ·
    refine ⟨7736558529473652245122225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41261645490526145307318533 7736558529473652245122225)
    ·
      refine ⟨5802418897105239183841669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7736558529473652245122225 5802418897105239183841669)
      ·
        refine ⟨1087953543207232346970313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5802418897105239183841669 1087953543207232346970313)
        ·
          refine ⟨815965157405424260227735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087953543207232346970313 815965157405424260227735)
          ·
            refine ⟨1223947736108136390341603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815965157405424260227735 1223947736108136390341603)
            ·
              refine ⟨1835921604162204585512405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223947736108136390341603 1835921604162204585512405)
              ·
                refine ⟨43029412597551669972947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1835921604162204585512405 43029412597551669972947)
                ·
                  rfl

theorem cell22_1131293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 7].length) (baseStart_1131293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131293 prefixEnd_1131293 := by exact prefixLift 1131293
  have htrace : WordTrace (prefixWord ++ tailWord_1131293) baseStart_1131293 baseEnd_1131293 := by
    simpa [prefixWord, tailWord_1131293, baseEnd_1131293] using wordTrace_append hprefix tailTrace_1131293
  have hstable : (prefixWord ++ tailWord_1131293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131293).length < 2 ^ (prefixWord ++ tailWord_1131293).sum := by decide
  have hdescent : baseEnd_1131293 < baseStart_1131293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131304 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_1131304 : Nat := 118140960795 + 1131304 * 2 ^ 59
def prefixEnd_1131304 : Nat := 4983230072969 + 3 ^ 40 * 1131304 * 2
def baseEnd_1131304 : Nat := 129089492967588222577163

theorem tailTrace_1131304 : CollatzResearch.WordTrace tailWord_1131304 prefixEnd_1131304 129089492967588222577163 := by
  unfold tailWord_1131304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20631023346743147092984483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27508031128990862790645977 20631023346743147092984483)
  ·
    refine ⟨30946535020114720639476725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20631023346743147092984483 30946535020114720639476725)
    ·
      refine ⟨2901237658135755059950943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30946535020114720639476725 2901237658135755059950943)
      ·
        refine ⟨4351856487203632589926415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901237658135755059950943 4351856487203632589926415)
        ·
          refine ⟨6527784730805448884889623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4351856487203632589926415 6527784730805448884889623)
          ·
            refine ⟨9791677096208173327334435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6527784730805448884889623 9791677096208173327334435)
            ·
              refine ⟨14687515644312259991001653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9791677096208173327334435 14687515644312259991001653)
              ·
                refine ⟨1376954591654274374156405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14687515644312259991001653 1376954591654274374156405)
                ·
                  refine ⟨129089492967588222577163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1376954591654274374156405 129089492967588222577163)
                  ·
                    rfl

theorem cell22_1131304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_1131304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131304 prefixEnd_1131304 := by exact prefixLift 1131304
  have htrace : WordTrace (prefixWord ++ tailWord_1131304) baseStart_1131304 baseEnd_1131304 := by
    simpa [prefixWord, tailWord_1131304, baseEnd_1131304] using wordTrace_append hprefix tailTrace_1131304
  have hstable : (prefixWord ++ tailWord_1131304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131304).length < 2 ^ (prefixWord ++ tailWord_1131304).sum := by decide
  have hdescent : baseEnd_1131304 < baseStart_1131304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131325 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_1131325 : Nat := 118140960795 + 1131325 * 2 ^ 59
def prefixEnd_1131325 : Nat := 4983230072969 + 3 ^ 40 * 1131325 * 2
def baseEnd_1131325 : Nat := 387275667631927612956425

theorem tailTrace_1131325 : CollatzResearch.WordTrace tailWord_1131325 prefixEnd_1131325 387275667631927612956425 := by
  unfold tailWord_1131325
  simp only [CollatzResearch.WordTrace]
  refine ⟨41262812626410214772483429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27508541750940143181655619 41262812626410214772483429)
  ·
    refine ⟨7736777367451915269840643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41262812626410214772483429 7736777367451915269840643)
    ·
      refine ⟨11605166051177872904760965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7736777367451915269840643 11605166051177872904760965)
      ·
        refine ⟨2175968634595851169642681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11605166051177872904760965 2175968634595851169642681)
        ·
          refine ⟨1631976475946888377232011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175968634595851169642681 1631976475946888377232011)
          ·
            refine ⟨2447964713920332565848017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631976475946888377232011 2447964713920332565848017)
            ·
              refine ⟨1835973535440249424386013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447964713920332565848017 1835973535440249424386013)
              ·
                refine ⟨688490075790093534144755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1835973535440249424386013 688490075790093534144755)
                ·
                  refine ⟨1032735113685140301217133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688490075790093534144755 1032735113685140301217133)
                  ·
                    refine ⟨387275667631927612956425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032735113685140301217133 387275667631927612956425)
                    ·
                      rfl

theorem cell22_1131325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_1131325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131325 prefixEnd_1131325 := by exact prefixLift 1131325
  have htrace : WordTrace (prefixWord ++ tailWord_1131325) baseStart_1131325 baseEnd_1131325 := by
    simpa [prefixWord, tailWord_1131325, baseEnd_1131325] using wordTrace_append hprefix tailTrace_1131325
  have hstable : (prefixWord ++ tailWord_1131325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131325).length < 2 ^ (prefixWord ++ tailWord_1131325).sum := by decide
  have hdescent : baseEnd_1131325 < baseStart_1131325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131347 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_1131347 : Nat := 118140960795 + 1131347 * 2 ^ 59
def prefixEnd_1131347 : Nat := 4983230072969 + 3 ^ 40 * 1131347 * 2
def baseEnd_1131347 : Nat := 387283198681526888906357

theorem tailTrace_1131347 : CollatzResearch.WordTrace tailWord_1131347 prefixEnd_1131347 387283198681526888906357 := by
  unfold tailWord_1131347
  simp only [CollatzResearch.WordTrace]
  refine ⟨41263615032330512529784295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27509076688220341686522863 41263615032330512529784295)
  ·
    refine ⟨61895422548495768794676443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41263615032330512529784295 61895422548495768794676443)
    ·
      refine ⟨92843133822743653192014665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61895422548495768794676443 92843133822743653192014665)
      ·
        refine ⟨69632350367057739894010999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92843133822743653192014665 69632350367057739894010999)
        ·
          refine ⟨104448525550586609841016499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69632350367057739894010999 104448525550586609841016499)
          ·
            refine ⟨156672788325879914761524749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104448525550586609841016499 156672788325879914761524749)
            ·
              refine ⟨58752295622204968035571781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156672788325879914761524749 58752295622204968035571781)
              ·
                refine ⟨11016055429163431506669709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58752295622204968035571781 11016055429163431506669709)
                ·
                  refine ⟨4131020785936286815001141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11016055429163431506669709 4131020785936286815001141)
                  ·
                    refine ⟨387283198681526888906357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4131020785936286815001141 387283198681526888906357)
                    ·
                      rfl

theorem cell22_1131347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_1131347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131347 prefixEnd_1131347 := by exact prefixLift 1131347
  have htrace : WordTrace (prefixWord ++ tailWord_1131347) baseStart_1131347 baseEnd_1131347 := by
    simpa [prefixWord, tailWord_1131347, baseEnd_1131347] using wordTrace_append hprefix tailTrace_1131347
  have hstable : (prefixWord ++ tailWord_1131347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131347).length < 2 ^ (prefixWord ++ tailWord_1131347).sum := by decide
  have hdescent : baseEnd_1131347 < baseStart_1131347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131349 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 6]
def baseStart_1131349 : Nat := 118140960795 + 1131349 * 2 ^ 59
def prefixEnd_1131349 : Nat := 4983230072969 + 3 ^ 40 * 1131349 * 2
def baseEnd_1131349 : Nat := 129094627774133183452117

theorem tailTrace_1131349 : CollatzResearch.WordTrace tailWord_1131349 prefixEnd_1131349 129094627774133183452117 := by
  unfold tailWord_1131349
  simp only [CollatzResearch.WordTrace]
  refine ⟨41263687978323266871357101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27509125318882177914238067 41263687978323266871357101)
  ·
    refine ⟨15473882991871225076758913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41263687978323266871357101 15473882991871225076758913)
    ·
      refine ⟨11605412243903418807569185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15473882991871225076758913 11605412243903418807569185)
      ·
        refine ⟨8704059182927564105676889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11605412243903418807569185 8704059182927564105676889)
        ·
          refine ⟨6528044387195673079257667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8704059182927564105676889 6528044387195673079257667)
          ·
            refine ⟨9792066580793509618886501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528044387195673079257667 9792066580793509618886501)
            ·
              refine ⟨1836012483898783053541219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9792066580793509618886501 1836012483898783053541219)
              ·
                refine ⟨2754018725848174580311829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836012483898783053541219 2754018725848174580311829)
                ·
                  refine ⟨129094627774133183452117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2754018725848174580311829 129094627774133183452117)
                  ·
                    rfl

theorem cell22_1131349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_1131349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131349 prefixEnd_1131349 := by exact prefixLift 1131349
  have htrace : WordTrace (prefixWord ++ tailWord_1131349) baseStart_1131349 baseEnd_1131349 := by
    simpa [prefixWord, tailWord_1131349, baseEnd_1131349] using wordTrace_append hprefix tailTrace_1131349
  have hstable : (prefixWord ++ tailWord_1131349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131349).length < 2 ^ (prefixWord ++ tailWord_1131349).sum := by decide
  have hdescent : baseEnd_1131349 < baseStart_1131349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131381 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1131381 : Nat := 118140960795 + 1131381 * 2 ^ 59
def prefixEnd_1131381 : Nat := 4983230072969 + 3 ^ 40 * 1131381 * 2
def baseEnd_1131381 : Nat := 387294837576362133556253

theorem tailTrace_1131381 : CollatzResearch.WordTrace tailWord_1131381 prefixEnd_1131381 387294837576362133556253 := by
  unfold tailWord_1131381
  simp only [CollatzResearch.WordTrace]
  refine ⟨41264855114207336336521997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27509903409471557557681331 41264855114207336336521997)
  ·
    refine ⟨15474320667827751126195749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41264855114207336336521997 15474320667827751126195749)
    ·
      refine ⟨2901435125217703336161703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15474320667827751126195749 2901435125217703336161703)
      ·
        refine ⟨4352152687826555004242555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901435125217703336161703 4352152687826555004242555)
        ·
          refine ⟨6528229031739832506363833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352152687826555004242555 6528229031739832506363833)
          ·
            refine ⟨4896171773804874379772875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6528229031739832506363833 4896171773804874379772875)
            ·
              refine ⟨7344257660707311569659313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896171773804874379772875 7344257660707311569659313)
              ·
                refine ⟨5508193245530483677244485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7344257660707311569659313 5508193245530483677244485)
                ·
                  refine ⟨1032786233536965689483341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5508193245530483677244485 1032786233536965689483341)
                  ·
                    refine ⟨387294837576362133556253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032786233536965689483341 387294837576362133556253)
                    ·
                      rfl

theorem cell22_1131381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1131381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131381 prefixEnd_1131381 := by exact prefixLift 1131381
  have htrace : WordTrace (prefixWord ++ tailWord_1131381) baseStart_1131381 baseEnd_1131381 := by
    simpa [prefixWord, tailWord_1131381, baseEnd_1131381] using wordTrace_append hprefix tailTrace_1131381
  have hstable : (prefixWord ++ tailWord_1131381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131381).length < 2 ^ (prefixWord ++ tailWord_1131381).sum := by decide
  have hdescent : baseEnd_1131381 < baseStart_1131381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131456 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_1131456 : Nat := 118140960795 + 1131456 * 2 ^ 59
def prefixEnd_1131456 : Nat := 4983230072969 + 3 ^ 40 * 1131456 * 2
def baseEnd_1131456 : Nat := 129106837203028979310341

theorem tailTrace_1131456 : CollatzResearch.WordTrace tailWord_1131456 prefixEnd_1131456 129106837203028979310341 := by
  unfold tailWord_1131456
  simp only [CollatzResearch.WordTrace]
  refine ⟨20633795294467812072751111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27511727059290416097001481 20633795294467812072751111)
  ·
    refine ⟨30950692941701718109126667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20633795294467812072751111 30950692941701718109126667)
    ·
      refine ⟨46426039412552577163690001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30950692941701718109126667 46426039412552577163690001)
      ·
        refine ⟨34819529559414432872767501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46426039412552577163690001 34819529559414432872767501)
        ·
          refine ⟨13057323584780412327287813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34819529559414432872767501 13057323584780412327287813)
          ·
            refine ⟨2448248172146327311366465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13057323584780412327287813 2448248172146327311366465)
            ·
              refine ⟨1836186129109745483524849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2448248172146327311366465 1836186129109745483524849)
              ·
                refine ⟨1377139596832309112643637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836186129109745483524849 1377139596832309112643637)
                ·
                  refine ⟨129106837203028979310341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1377139596832309112643637 129106837203028979310341)
                  ·
                    rfl

theorem cell22_1131456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_1131456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131456 prefixEnd_1131456 := by exact prefixLift 1131456
  have htrace : WordTrace (prefixWord ++ tailWord_1131456) baseStart_1131456 baseEnd_1131456 := by
    simpa [prefixWord, tailWord_1131456, baseEnd_1131456] using wordTrace_append hprefix tailTrace_1131456
  have hstable : (prefixWord ++ tailWord_1131456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131456).length < 2 ^ (prefixWord ++ tailWord_1131456).sum := by decide
  have hdescent : baseEnd_1131456 < baseStart_1131456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131503 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 1, 4]
def baseStart_1131503 : Nat := 118140960795 + 1131503 * 2 ^ 59
def prefixEnd_1131503 : Nat := 4983230072969 + 3 ^ 40 * 1131503 * 2
def baseEnd_1131503 : Nat := 387336600669594482005879

theorem tailTrace_1131503 : CollatzResearch.WordTrace tailWord_1131503 prefixEnd_1131503 387336600669594482005879 := by
  unfold tailWord_1131503
  simp only [CollatzResearch.WordTrace]
  refine ⟨41269304819765351172463163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27512869879843567448308775 41269304819765351172463163)
  ·
    refine ⟨61903957229648026758694745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41269304819765351172463163 61903957229648026758694745)
    ·
      refine ⟨46427967922236020069021059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61903957229648026758694745 46427967922236020069021059)
      ·
        refine ⟨69641951883354030103531589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46427967922236020069021059 69641951883354030103531589)
        ·
          refine ⟨13057865978128880644412173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69641951883354030103531589 13057865978128880644412173)
          ·
            refine ⟨4896699741798330241654565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13057865978128880644412173 4896699741798330241654565)
            ·
              refine ⟨918131201587186920310231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4896699741798330241654565 918131201587186920310231)
              ·
                refine ⟨1377196802380780380465347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918131201587186920310231 1377196802380780380465347)
                ·
                  refine ⟨2065795203571170570698021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377196802380780380465347 2065795203571170570698021)
                  ·
                    refine ⟨387336600669594482005879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2065795203571170570698021 387336600669594482005879)
                    ·
                      rfl

theorem cell22_1131503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_1131503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131503 prefixEnd_1131503 := by exact prefixLift 1131503
  have htrace : WordTrace (prefixWord ++ tailWord_1131503) baseStart_1131503 baseEnd_1131503 := by
    simpa [prefixWord, tailWord_1131503, baseEnd_1131503] using wordTrace_append hprefix tailTrace_1131503
  have hstable : (prefixWord ++ tailWord_1131503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131503).length < 2 ^ (prefixWord ++ tailWord_1131503).sum := by decide
  have hdescent : baseEnd_1131503 < baseStart_1131503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131552 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_1131552 : Nat := 118140960795 + 1131552 * 2 ^ 59
def prefixEnd_1131552 : Nat := 4983230072969 + 3 ^ 40 * 1131552 * 2
def baseEnd_1131552 : Nat := 129117791456991562510243

theorem tailTrace_1131552 : CollatzResearch.WordTrace tailWord_1131552 prefixEnd_1131552 129117791456991562510243 := by
  unfold tailWord_1131552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20635545998293916270498455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27514061331058555027331273 20635545998293916270498455)
  ·
    refine ⟨30953318997440874405747683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20635545998293916270498455 30953318997440874405747683)
    ·
      refine ⟨46429978496161311608621525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30953318997440874405747683 46429978496161311608621525)
      ·
        refine ⟨1088202621003780740827067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46429978496161311608621525 1088202621003780740827067)
        ·
          refine ⟨1632303931505671111240601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088202621003780740827067 1632303931505671111240601)
          ·
            refine ⟨1224227948629253333430451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632303931505671111240601 1224227948629253333430451)
            ·
              refine ⟨1836341922943880000145677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224227948629253333430451 1836341922943880000145677)
              ·
                refine ⟨688628221103955000054629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1836341922943880000145677 688628221103955000054629)
                ·
                  refine ⟨129117791456991562510243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688628221103955000054629 129117791456991562510243)
                  ·
                    rfl

theorem cell22_1131552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_1131552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131552 prefixEnd_1131552 := by exact prefixLift 1131552
  have htrace : WordTrace (prefixWord ++ tailWord_1131552) baseStart_1131552 baseEnd_1131552 := by
    simpa [prefixWord, tailWord_1131552, baseEnd_1131552] using wordTrace_append hprefix tailTrace_1131552
  have hstable : (prefixWord ++ tailWord_1131552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131552).length < 2 ^ (prefixWord ++ tailWord_1131552).sum := by decide
  have hdescent : baseEnd_1131552 < baseStart_1131552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131578 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_1131578 : Nat := 118140960795 + 1131578 * 2 ^ 59
def prefixEnd_1131578 : Nat := 4983230072969 + 3 ^ 40 * 1131578 * 2
def baseEnd_1131578 : Nat := 387362274702319286380649

theorem tailTrace_1131578 : CollatzResearch.WordTrace tailWord_1131578 prefixEnd_1131578 387362274702319286380649 := by
  unfold tailWord_1131578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318010073623409745360847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27514693529662425987628925 10318010073623409745360847)
  ·
    refine ⟨15477015110435114618041271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10318010073623409745360847 15477015110435114618041271)
    ·
      refine ⟨23215522665652671927061907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15477015110435114618041271 23215522665652671927061907)
      ·
        refine ⟨34823283998479007890592861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23215522665652671927061907 34823283998479007890592861)
        ·
          refine ⟨13058731499429627958972323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34823283998479007890592861 13058731499429627958972323)
          ·
            refine ⟨19588097249144441938458485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13058731499429627958972323 19588097249144441938458485)
            ·
              refine ⟨1836384117107291431730483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19588097249144441938458485 1836384117107291431730483)
              ·
                refine ⟨2754576175660937147595725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836384117107291431730483 2754576175660937147595725)
                ·
                  refine ⟨1032966065872851430348397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2754576175660937147595725 1032966065872851430348397)
                  ·
                    refine ⟨387362274702319286380649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032966065872851430348397 387362274702319286380649)
                    ·
                      rfl

theorem cell22_1131578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_1131578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131578 prefixEnd_1131578 := by exact prefixLift 1131578
  have htrace : WordTrace (prefixWord ++ tailWord_1131578) baseStart_1131578 baseEnd_1131578 := by
    simpa [prefixWord, tailWord_1131578, baseEnd_1131578] using wordTrace_append hprefix tailTrace_1131578
  have hstable : (prefixWord ++ tailWord_1131578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131578).length < 2 ^ (prefixWord ++ tailWord_1131578).sum := by decide
  have hdescent : baseEnd_1131578 < baseStart_1131578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131629 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_1131629 : Nat := 118140960795 + 1131629 * 2 ^ 59
def prefixEnd_1131629 : Nat := 4983230072969 + 3 ^ 40 * 1131629 * 2
def baseEnd_1131629 : Nat := 387379733044572153355493

theorem tailTrace_1131629 : CollatzResearch.WordTrace tailWord_1131629 prefixEnd_1131629 387379733044572153355493 := by
  unfold tailWord_1131629
  simp only [CollatzResearch.WordTrace]
  refine ⟨41273900417308874691549941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27515933611539249794366627 41273900417308874691549941)
  ·
    refine ⟨3869428164122707002332807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41273900417308874691549941 3869428164122707002332807)
    ·
      refine ⟨5804142246184060503499211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869428164122707002332807 5804142246184060503499211)
      ·
        refine ⟨8706213369276090755248817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804142246184060503499211 8706213369276090755248817)
        ·
          refine ⟨6529660026957068066436613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8706213369276090755248817 6529660026957068066436613)
          ·
            refine ⟨1224311255054450262456865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6529660026957068066436613 1224311255054450262456865)
            ·
              refine ⟨918233441290837696842649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1224311255054450262456865 918233441290837696842649)
              ·
                refine ⟨688675080968128272631987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918233441290837696842649 688675080968128272631987)
                ·
                  refine ⟨1033012621452192408947981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688675080968128272631987 1033012621452192408947981)
                  ·
                    refine ⟨387379733044572153355493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033012621452192408947981 387379733044572153355493)
                    ·
                      rfl

theorem cell22_1131629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_1131629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131629 prefixEnd_1131629 := by exact prefixLift 1131629
  have htrace : WordTrace (prefixWord ++ tailWord_1131629) baseStart_1131629 baseEnd_1131629 := by
    simpa [prefixWord, tailWord_1131629, baseEnd_1131629] using wordTrace_append hprefix tailTrace_1131629
  have hstable : (prefixWord ++ tailWord_1131629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131629).length < 2 ^ (prefixWord ++ tailWord_1131629).sum := by decide
  have hdescent : baseEnd_1131629 < baseStart_1131629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131638 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1131638 : Nat := 118140960795 + 1131638 * 2 ^ 59
def prefixEnd_1131638 : Nat := 4983230072969 + 3 ^ 40 * 1131638 * 2
def baseEnd_1131638 : Nat := 387382813928499129880465

theorem tailTrace_1131638 : CollatzResearch.WordTrace tailWord_1131638 prefixEnd_1131638 387382813928499129880465 := by
  unfold tailWord_1131638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579639292142266826789223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27516152449517512819085045 2579639292142266826789223)
  ·
    refine ⟨3869458938213400240183835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2579639292142266826789223 3869458938213400240183835)
    ·
      refine ⟨5804188407320100360275753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869458938213400240183835 5804188407320100360275753)
      ·
        refine ⟨4353141305490075270206815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804188407320100360275753 4353141305490075270206815)
        ·
          refine ⟨6529711958235112905310223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353141305490075270206815 6529711958235112905310223)
          ·
            refine ⟨9794567937352669357965335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529711958235112905310223 9794567937352669357965335)
            ·
              refine ⟨14691851906029004036948003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9794567937352669357965335 14691851906029004036948003)
              ·
                refine ⟨22037777859043506055422005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14691851906029004036948003 22037777859043506055422005)
                ·
                  refine ⟨2066041674285328692695813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22037777859043506055422005 2066041674285328692695813)
                  ·
                    refine ⟨387382813928499129880465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066041674285328692695813 387382813928499129880465)
                    ·
                      rfl

theorem cell22_1131638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1131638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131638 prefixEnd_1131638 := by exact prefixLift 1131638
  have htrace : WordTrace (prefixWord ++ tailWord_1131638) baseStart_1131638 baseEnd_1131638 := by
    simpa [prefixWord, tailWord_1131638, baseEnd_1131638] using wordTrace_append hprefix tailTrace_1131638
  have hstable : (prefixWord ++ tailWord_1131638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131638).length < 2 ^ (prefixWord ++ tailWord_1131638).sum := by decide
  have hdescent : baseEnd_1131638 < baseStart_1131638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131653 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 6]
def baseStart_1131653 : Nat := 118140960795 + 1131653 * 2 ^ 59
def prefixEnd_1131653 : Nat := 4983230072969 + 3 ^ 40 * 1131653 * 2
def baseEnd_1131653 : Nat := 129129316245014696918473

theorem tailTrace_1131653 : CollatzResearch.WordTrace tailWord_1131653 prefixEnd_1131653 129129316245014696918473 := by
  unfold tailWord_1131653
  simp only [CollatzResearch.WordTrace]
  refine ⟨41274775769221926790423613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27516517179481284526949075 41274775769221926790423613)
  ·
    refine ⟨15478040913458222546408855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41274775769221926790423613 15478040913458222546408855)
    ·
      refine ⟨23217061370187333819613283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15478040913458222546408855 23217061370187333819613283)
      ·
        refine ⟨34825592055281000729419925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23217061370187333819613283 34825592055281000729419925)
        ·
          refine ⟨1632449627591296909191559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34825592055281000729419925 1632449627591296909191559)
          ·
            refine ⟨2448674441386945363787339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632449627591296909191559 2448674441386945363787339)
            ·
              refine ⟨3673011662080418045681009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448674441386945363787339 3673011662080418045681009)
              ·
                refine ⟨2754758746560313534260757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673011662080418045681009 2754758746560313534260757)
                ·
                  refine ⟨129129316245014696918473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2754758746560313534260757 129129316245014696918473)
                  ·
                    rfl

theorem cell22_1131653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_1131653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131653 prefixEnd_1131653 := by exact prefixLift 1131653
  have htrace : WordTrace (prefixWord ++ tailWord_1131653) baseStart_1131653 baseEnd_1131653 := by
    simpa [prefixWord, tailWord_1131653, baseEnd_1131653] using wordTrace_append hprefix tailTrace_1131653
  have hstable : (prefixWord ++ tailWord_1131653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131653).length < 2 ^ (prefixWord ++ tailWord_1131653).sum := by decide
  have hdescent : baseEnd_1131653 < baseStart_1131653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131672 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_1131672 : Nat := 118140960795 + 1131672 * 2 ^ 59
def prefixEnd_1131672 : Nat := 4983230072969 + 3 ^ 40 * 1131672 * 2
def baseEnd_1131672 : Nat := 387394452823334374530361

theorem tailTrace_1131672 : CollatzResearch.WordTrace tailWord_1131672 prefixEnd_1131672 387394452823334374530361 := by
  unfold tailWord_1131672
  simp only [CollatzResearch.WordTrace]
  refine ⟨20637734378076546517682635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27516979170768728690243513 20637734378076546517682635)
  ·
    refine ⟨30956601567114819776523953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20637734378076546517682635 30956601567114819776523953)
    ·
      refine ⟨23217451175336114832392965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30956601567114819776523953 23217451175336114832392965)
      ·
        refine ⟨4353272095375521531073681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23217451175336114832392965 4353272095375521531073681)
        ·
          refine ⟨3264954071531641148305261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4353272095375521531073681 3264954071531641148305261)
          ·
            refine ⟨1224357776824365430614473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3264954071531641148305261 1224357776824365430614473)
            ·
              refine ⟨918268332618274072960855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1224357776824365430614473 918268332618274072960855)
              ·
                refine ⟨1377402498927411109441283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918268332618274072960855 1377402498927411109441283)
                ·
                  refine ⟨2066103748391116664161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377402498927411109441283 2066103748391116664161925)
                  ·
                    refine ⟨387394452823334374530361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066103748391116664161925 387394452823334374530361)
                    ·
                      rfl

theorem cell22_1131672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_1131672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131672 prefixEnd_1131672 := by exact prefixLift 1131672
  have htrace : WordTrace (prefixWord ++ tailWord_1131672) baseStart_1131672 baseEnd_1131672 := by
    simpa [prefixWord, tailWord_1131672, baseEnd_1131672] using wordTrace_append hprefix tailTrace_1131672
  have hstable : (prefixWord ++ tailWord_1131672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131672).length < 2 ^ (prefixWord ++ tailWord_1131672).sum := by decide
  have hdescent : baseEnd_1131672 < baseStart_1131672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131681 : List Nat := [1, 2, 3, 3, 1, 1, 11]
def baseStart_1131681 : Nat := 118140960795 + 1131681 * 2 ^ 59
def prefixEnd_1131681 : Nat := 4983230072969 + 3 ^ 40 * 1131681 * 2
def baseEnd_1131681 : Nat := 14348056803972642631679

theorem tailTrace_1131681 : CollatzResearch.WordTrace tailWord_1131681 prefixEnd_1131681 14348056803972642631679 := by
  unfold tailWord_1131681
  simp only [CollatzResearch.WordTrace]
  refine ⟨41275797013120487572442897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27517198008746991714961931 41275797013120487572442897)
  ·
    refine ⟨30956847759840365679332173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41275797013120487572442897 30956847759840365679332173)
    ·
      refine ⟨11608817909940137129749565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30956847759840365679332173 11608817909940137129749565)
      ·
        refine ⟨4353306716227551423656087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11608817909940137129749565 4353306716227551423656087)
        ·
          refine ⟨6529960074341327135484131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353306716227551423656087 6529960074341327135484131)
          ·
            refine ⟨9794940111511990703226197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529960074341327135484131 9794940111511990703226197)
            ·
              refine ⟨14348056803972642631679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9794940111511990703226197 14348056803972642631679)
              ·
                rfl

theorem cell22_1131681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 11].length) (baseStart_1131681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131681 prefixEnd_1131681 := by exact prefixLift 1131681
  have htrace : WordTrace (prefixWord ++ tailWord_1131681) baseStart_1131681 baseEnd_1131681 := by
    simpa [prefixWord, tailWord_1131681, baseEnd_1131681] using wordTrace_append hprefix tailTrace_1131681
  have hstable : (prefixWord ++ tailWord_1131681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131681).length < 2 ^ (prefixWord ++ tailWord_1131681).sum := by decide
  have hdescent : baseEnd_1131681 < baseStart_1131681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131685 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_1131685 : Nat := 118140960795 + 1131685 * 2 ^ 59
def prefixEnd_1131685 : Nat := 4983230072969 + 3 ^ 40 * 1131685 * 2
def baseEnd_1131685 : Nat := 387398902989006673955321

theorem tailTrace_1131685 : CollatzResearch.WordTrace tailWord_1131685 prefixEnd_1131685 387398902989006673955321 := by
  unfold tailWord_1131685
  simp only [CollatzResearch.WordTrace]
  refine ⟨41275942905105996255588509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27517295270070664170392339 41275942905105996255588509)
  ·
    refine ⟨15478478589414748595845691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41275942905105996255588509 15478478589414748595845691)
    ·
      refine ⟨23217717884122122893768537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15478478589414748595845691 23217717884122122893768537)
      ·
        refine ⟨17413288413091592170326403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23217717884122122893768537 17413288413091592170326403)
        ·
          refine ⟨26119932619637388255489605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17413288413091592170326403 26119932619637388255489605)
          ·
            refine ⟨4897487366182010297904301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26119932619637388255489605 4897487366182010297904301)
            ·
              refine ⟨1836557762318253861714113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4897487366182010297904301 1836557762318253861714113)
              ·
                refine ⟨1377418321738690396285585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836557762318253861714113 1377418321738690396285585)
                ·
                  refine ⟨1033063741304017797214189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1377418321738690396285585 1033063741304017797214189)
                  ·
                    refine ⟨387398902989006673955321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033063741304017797214189 387398902989006673955321)
                    ·
                      rfl

theorem cell22_1131685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_1131685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131685 prefixEnd_1131685 := by exact prefixLift 1131685
  have htrace : WordTrace (prefixWord ++ tailWord_1131685) baseStart_1131685 baseEnd_1131685 := by
    simpa [prefixWord, tailWord_1131685, baseEnd_1131685] using wordTrace_append hprefix tailTrace_1131685
  have hstable : (prefixWord ++ tailWord_1131685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131685).length < 2 ^ (prefixWord ++ tailWord_1131685).sum := by decide
  have hdescent : baseEnd_1131685 < baseStart_1131685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131711 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_1131711 : Nat := 118140960795 + 1131711 * 2 ^ 59
def prefixEnd_1131711 : Nat := 4983230072969 + 3 ^ 40 * 1131711 * 2
def baseEnd_1131711 : Nat := 387407803320351272805241

theorem tailTrace_1131711 : CollatzResearch.WordTrace tailWord_1131711 prefixEnd_1131711 387407803320351272805241 := by
  unfold tailWord_1131711
  simp only [CollatzResearch.WordTrace]
  refine ⟨41276891203011802696034987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27517927468674535130689991 41276891203011802696034987)
  ·
    refine ⟨61915336804517704044052481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41276891203011802696034987 61915336804517704044052481)
    ·
      refine ⟨46436502603388278033039361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61915336804517704044052481 46436502603388278033039361)
      ·
        refine ⟨34827376952541208524779521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46436502603388278033039361 34827376952541208524779521)
        ·
          refine ⟨26120532714405906393584641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34827376952541208524779521 26120532714405906393584641)
          ·
            refine ⟨19590399535804429795188481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26120532714405906393584641 19590399535804429795188481)
            ·
              refine ⟨14692799651853322346391361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19590399535804429795188481 14692799651853322346391361)
              ·
                refine ⟨11019599738889991759793521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14692799651853322346391361 11019599738889991759793521)
                ·
                  refine ⟨8264699804167493819845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11019599738889991759793521 8264699804167493819845141)
                  ·
                    refine ⟨387407803320351272805241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8264699804167493819845141 387407803320351272805241)
                    ·
                      rfl

theorem cell22_1131711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_1131711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131711 prefixEnd_1131711 := by exact prefixLift 1131711
  have htrace : WordTrace (prefixWord ++ tailWord_1131711) baseStart_1131711 baseEnd_1131711 := by
    simpa [prefixWord, tailWord_1131711, baseEnd_1131711] using wordTrace_append hprefix tailTrace_1131711
  have hstable : (prefixWord ++ tailWord_1131711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131711).length < 2 ^ (prefixWord ++ tailWord_1131711).sum := by decide
  have hdescent : baseEnd_1131711 < baseStart_1131711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131732 : List Nat := [2, 4, 1, 4, 2, 1, 8]
def baseStart_1131732 : Nat := 118140960795 + 1131732 * 2 ^ 59
def prefixEnd_1131732 : Nat := 4983230072969 + 3 ^ 40 * 1131732 * 2
def baseEnd_1131732 : Nat := 14348703409241267334451

theorem tailTrace_1131732 : CollatzResearch.WordTrace tailWord_1131732 prefixEnd_1131732 14348703409241267334451 := by
  unfold tailWord_1131732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638828567967861641274725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27518438090623815521699633 20638828567967861641274725)
  ·
    refine ⟨3869780356493974057739011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20638828567967861641274725 3869780356493974057739011)
    ·
      refine ⟨5804670534740961086608517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869780356493974057739011 5804670534740961086608517)
      ·
        refine ⟨1088375725263930203739097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5804670534740961086608517 1088375725263930203739097)
        ·
          refine ⟨816281793947947652804323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088375725263930203739097 816281793947947652804323)
          ·
            refine ⟨1224422690921921479206485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816281793947947652804323 1224422690921921479206485)
            ·
              refine ⟨14348703409241267334451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1224422690921921479206485 14348703409241267334451)
              ·
                rfl

theorem cell22_1131732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 8].length) (baseStart_1131732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131732 prefixEnd_1131732 := by exact prefixLift 1131732
  have htrace : WordTrace (prefixWord ++ tailWord_1131732) baseStart_1131732 baseEnd_1131732 := by
    simpa [prefixWord, tailWord_1131732, baseEnd_1131732] using wordTrace_append hprefix tailTrace_1131732
  have hstable : (prefixWord ++ tailWord_1131732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131732).length < 2 ^ (prefixWord ++ tailWord_1131732).sum := by decide
  have hdescent : baseEnd_1131732 < baseStart_1131732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131758 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1131758 : Nat := 118140960795 + 1131758 * 2 ^ 59
def prefixEnd_1131758 : Nat := 4983230072969 + 3 ^ 40 * 1131758 * 2
def baseEnd_1131758 : Nat := 387423892380858816880097

theorem tailTrace_1131758 : CollatzResearch.WordTrace tailWord_1131758 prefixEnd_1131758 387423892380858816880097 := by
  unfold tailWord_1131758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159825679230191215374491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27519070289227686481997285 5159825679230191215374491)
  ·
    refine ⟨7739738518845286823061737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159825679230191215374491 7739738518845286823061737)
    ·
      refine ⟨5804803889133965117296303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7739738518845286823061737 5804803889133965117296303)
      ·
        refine ⟨8707205833700947675944455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804803889133965117296303 8707205833700947675944455)
        ·
          refine ⟨13060808750551421513916683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8707205833700947675944455 13060808750551421513916683)
          ·
            refine ⟨19591213125827132270875025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13060808750551421513916683 19591213125827132270875025)
            ·
              refine ⟨14693409844370349203156269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19591213125827132270875025 14693409844370349203156269)
              ·
                refine ⟨5510028691638880951183601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14693409844370349203156269 5510028691638880951183601)
                ·
                  refine ⟨4132521518729160713387701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5510028691638880951183601 4132521518729160713387701)
                  ·
                    refine ⟨387423892380858816880097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4132521518729160713387701 387423892380858816880097)
                    ·
                      rfl

theorem cell22_1131758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1131758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131758 prefixEnd_1131758 := by exact prefixLift 1131758
  have htrace : WordTrace (prefixWord ++ tailWord_1131758) baseStart_1131758 baseEnd_1131758 := by
    simpa [prefixWord, tailWord_1131758, baseEnd_1131758] using wordTrace_append hprefix tailTrace_1131758
  have hstable : (prefixWord ++ tailWord_1131758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131758).length < 2 ^ (prefixWord ++ tailWord_1131758).sum := by decide
  have hdescent : baseEnd_1131758 < baseStart_1131758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131794 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1131794 : Nat := 118140960795 + 1131794 * 2 ^ 59
def prefixEnd_1131794 : Nat := 4983230072969 + 3 ^ 40 * 1131794 * 2
def baseEnd_1131794 : Nat := 129145405305522240993329

theorem tailTrace_1131794 : CollatzResearch.WordTrace tailWord_1131794 prefixEnd_1131794 129145405305522240993329 := by
  unfold tailWord_1131794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10319979615427776967826609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27519945641140738580870957 10319979615427776967826609)
  ·
    refine ⟨7739984711570832725869957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10319979615427776967826609 7739984711570832725869957)
    ·
      refine ⟨1451247133419531136100617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7739984711570832725869957 1451247133419531136100617)
      ·
        refine ⟨1088435350064648352075463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451247133419531136100617 1088435350064648352075463)
        ·
          refine ⟨1632653025096972528113195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088435350064648352075463 1632653025096972528113195)
          ·
            refine ⟨2448979537645458792169793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632653025096972528113195 2448979537645458792169793)
            ·
              refine ⟨1836734653234094094127345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2448979537645458792169793 1836734653234094094127345)
              ·
                refine ⟨1377550989925570570595509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836734653234094094127345 1377550989925570570595509)
                ·
                  refine ⟨129145405305522240993329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1377550989925570570595509 129145405305522240993329)
                  ·
                    rfl

theorem cell22_1131794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1131794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131794 prefixEnd_1131794 := by exact prefixLift 1131794
  have htrace : WordTrace (prefixWord ++ tailWord_1131794) baseStart_1131794 baseEnd_1131794 := by
    simpa [prefixWord, tailWord_1131794, baseEnd_1131794] using wordTrace_append hprefix tailTrace_1131794
  have hstable : (prefixWord ++ tailWord_1131794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131794).length < 2 ^ (prefixWord ++ tailWord_1131794).sum := by decide
  have hdescent : baseEnd_1131794 < baseStart_1131794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131865 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_1131865 : Nat := 118140960795 + 1131865 * 2 ^ 59
def prefixEnd_1131865 : Nat := 4983230072969 + 3 ^ 40 * 1131865 * 2
def baseEnd_1131865 : Nat := 387460520667546204454769

theorem tailTrace_1131865 : CollatzResearch.WordTrace tailWord_1131865 prefixEnd_1131865 387460520667546204454769 := by
  unfold tailWord_1131865
  simp only [CollatzResearch.WordTrace]
  refine ⟨41282508044453886997141049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27521672029635924664760699 41282508044453886997141049)
  ·
    refine ⟨30961881033340415247855787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41282508044453886997141049 30961881033340415247855787)
    ·
      refine ⟨46442821550010622871783681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30961881033340415247855787 46442821550010622871783681)
      ·
        refine ⟨34832116162507967153837761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46442821550010622871783681 34832116162507967153837761)
        ·
          refine ⟨26124087121880975365378321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34832116162507967153837761 26124087121880975365378321)
          ·
            refine ⟨19593065341410731524033741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26124087121880975365378321 19593065341410731524033741)
            ·
              refine ⟨7347399503029024321512653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19593065341410731524033741 7347399503029024321512653)
              ·
                refine ⟨2755274813635884120567245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7347399503029024321512653 2755274813635884120567245)
                ·
                  refine ⟨1033228055113456545212717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2755274813635884120567245 1033228055113456545212717)
                  ·
                    refine ⟨387460520667546204454769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033228055113456545212717 387460520667546204454769)
                    ·
                      rfl

theorem cell22_1131865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_1131865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131865 prefixEnd_1131865 := by exact prefixLift 1131865
  have htrace : WordTrace (prefixWord ++ tailWord_1131865) baseStart_1131865 baseEnd_1131865 := by
    simpa [prefixWord, tailWord_1131865, baseEnd_1131865] using wordTrace_append hprefix tailTrace_1131865
  have hstable : (prefixWord ++ tailWord_1131865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131865).length < 2 ^ (prefixWord ++ tailWord_1131865).sum := by decide
  have hdescent : baseEnd_1131865 < baseStart_1131865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131955 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 6, 3]
def baseStart_1131955 : Nat := 118140960795 + 1131955 * 2 ^ 59
def prefixEnd_1131955 : Nat := 4983230072969 + 3 ^ 40 * 1131955 * 2
def baseEnd_1131955 : Nat := 387491329506815969704493

theorem tailTrace_1131955 : CollatzResearch.WordTrace tailWord_1131955 prefixEnd_1131955 387491329506815969704493 := by
  unfold tailWord_1131955
  simp only [CollatzResearch.WordTrace]
  refine ⟨41285790614127832367917319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27523860409418554911944879 41285790614127832367917319)
  ·
    refine ⟨61928685921191748551875979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41285790614127832367917319 61928685921191748551875979)
    ·
      refine ⟨92893028881787622827813969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61928685921191748551875979 92893028881787622827813969)
      ·
        refine ⟨69669771661340717120860477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92893028881787622827813969 69669771661340717120860477)
        ·
          refine ⟨26126164373002768920322679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69669771661340717120860477 26126164373002768920322679)
          ·
            refine ⟨39189246559504153380484019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26126164373002768920322679 39189246559504153380484019)
            ·
              refine ⟨58783869839256230070726029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39189246559504153380484019 58783869839256230070726029)
              ·
                refine ⟨22043951189721086276522261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58783869839256230070726029 22043951189721086276522261)
                ·
                  refine ⟨1033310212018175919211981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22043951189721086276522261 1033310212018175919211981)
                  ·
                    refine ⟨387491329506815969704493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033310212018175919211981 387491329506815969704493)
                    ·
                      rfl

theorem cell22_1131955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3].length) (baseStart_1131955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1131955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1131955 prefixEnd_1131955 := by exact prefixLift 1131955
  have htrace : WordTrace (prefixWord ++ tailWord_1131955) baseStart_1131955 baseEnd_1131955 := by
    simpa [prefixWord, tailWord_1131955, baseEnd_1131955] using wordTrace_append hprefix tailTrace_1131955
  have hstable : (prefixWord ++ tailWord_1131955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131955).length < 2 ^ (prefixWord ++ tailWord_1131955).sum := by decide
  have hdescent : baseEnd_1131955 < baseStart_1131955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132105 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1132105 : Nat := 118140960795 + 1132105 * 2 ^ 59
def prefixEnd_1132105 : Nat := 4983230072969 + 3 ^ 40 * 1132105 * 2
def baseEnd_1132105 : Nat := 387542677572265578454033

theorem tailTrace_1132105 : CollatzResearch.WordTrace tailWord_1132105 prefixEnd_1132105 387542677572265578454033 := by
  unfold tailWord_1132105
  simp only [CollatzResearch.WordTrace]
  refine ⟨41291261563584407985877769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27527507709056271990585179 41291261563584407985877769)
  ·
    refine ⟨30968446172688305989408327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41291261563584407985877769 30968446172688305989408327)
    ·
      refine ⟨46452669259032458984112491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30968446172688305989408327 46452669259032458984112491)
      ·
        refine ⟨69679003888548688476168737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46452669259032458984112491 69679003888548688476168737)
        ·
          refine ⟨52259252916411516357126553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69679003888548688476168737 52259252916411516357126553)
          ·
            refine ⟨39194439687308637267844915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52259252916411516357126553 39194439687308637267844915)
            ·
              refine ⟨58791659530962955901767373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39194439687308637267844915 58791659530962955901767373)
              ·
                refine ⟨22046872324111108463162765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58791659530962955901767373 22046872324111108463162765)
                ·
                  refine ⟨8267577121541665673686037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22046872324111108463162765 8267577121541665673686037)
                  ·
                    refine ⟨387542677572265578454033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8267577121541665673686037 387542677572265578454033)
                    ·
                      rfl

theorem cell22_1132105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1132105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132105 prefixEnd_1132105 := by exact prefixLift 1132105
  have htrace : WordTrace (prefixWord ++ tailWord_1132105) baseStart_1132105 baseEnd_1132105 := by
    simpa [prefixWord, tailWord_1132105, baseEnd_1132105] using wordTrace_append hprefix tailTrace_1132105
  have hstable : (prefixWord ++ tailWord_1132105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132105).length < 2 ^ (prefixWord ++ tailWord_1132105).sum := by decide
  have hdescent : baseEnd_1132105 < baseStart_1132105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132124 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1132124 : Nat := 118140960795 + 1132124 * 2 ^ 59
def prefixEnd_1132124 : Nat := 4983230072969 + 3 ^ 40 * 1132124 * 2
def baseEnd_1132124 : Nat := 387549181660555862228975

theorem tailTrace_1132124 : CollatzResearch.WordTrace tailWord_1132124 prefixEnd_1132124 387549181660555862228975 := by
  unfold tailWord_1132124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645977275257787115409713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27527969700343716153879617 20645977275257787115409713)
  ·
    refine ⟨15484482956443340336557285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20645977275257787115409713 15484482956443340336557285)
    ·
      refine ⟨2903340554333126313104491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15484482956443340336557285 2903340554333126313104491)
      ·
        refine ⟨4355010831499689469656737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903340554333126313104491 4355010831499689469656737)
        ·
          refine ⟨3266258123624767102242553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4355010831499689469656737 3266258123624767102242553)
          ·
            refine ⟨2449693592718575326681915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266258123624767102242553 2449693592718575326681915)
            ·
              refine ⟨3674540389077862990022873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449693592718575326681915 3674540389077862990022873)
              ·
                refine ⟨2755905291808397242517155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674540389077862990022873 2755905291808397242517155)
                ·
                  refine ⟨4133857937712595863775733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755905291808397242517155 4133857937712595863775733)
                  ·
                    refine ⟨387549181660555862228975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4133857937712595863775733 387549181660555862228975)
                    ·
                      rfl

theorem cell22_1132124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1132124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132124 prefixEnd_1132124 := by exact prefixLift 1132124
  have htrace : WordTrace (prefixWord ++ tailWord_1132124) baseStart_1132124 baseEnd_1132124 := by
    simpa [prefixWord, tailWord_1132124, baseEnd_1132124] using wordTrace_append hprefix tailTrace_1132124
  have hstable : (prefixWord ++ tailWord_1132124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132124).length < 2 ^ (prefixWord ++ tailWord_1132124).sum := by decide
  have hdescent : baseEnd_1132124 < baseStart_1132124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132197 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1132197 : Nat := 118140960795 + 1132197 * 2 ^ 59
def prefixEnd_1132197 : Nat := 4983230072969 + 3 ^ 40 * 1132197 * 2
def baseEnd_1132197 : Nat := 387574171052408005153751

theorem tailTrace_1132197 : CollatzResearch.WordTrace tailWord_1132197 prefixEnd_1132197 387574171052408005153751 := by
  unfold tailWord_1132197
  simp only [CollatzResearch.WordTrace]
  refine ⟨41294617079251107698226845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27529744719500738465484563 41294617079251107698226845)
  ·
    refine ⟨15485481404719165386835067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41294617079251107698226845 15485481404719165386835067)
    ·
      refine ⟨23228222107078748080252601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15485481404719165386835067 23228222107078748080252601)
      ·
        refine ⟨17421166580309061060189451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23228222107078748080252601 17421166580309061060189451)
        ·
          refine ⟨26131749870463591590284177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17421166580309061060189451 26131749870463591590284177)
          ·
            refine ⟨19598812402847693692713133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26131749870463591590284177 19598812402847693692713133)
            ·
              refine ⟨7349554651067885134767425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19598812402847693692713133 7349554651067885134767425)
              ·
                refine ⟨5512165988300913851075569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7349554651067885134767425 5512165988300913851075569)
                ·
                  refine ⟨4134124491225685388306677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512165988300913851075569 4134124491225685388306677)
                  ·
                    refine ⟨387574171052408005153751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4134124491225685388306677 387574171052408005153751)
                    ·
                      rfl

theorem cell22_1132197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1132197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132197 prefixEnd_1132197 := by exact prefixLift 1132197
  have htrace : WordTrace (prefixWord ++ tailWord_1132197) baseStart_1132197 baseEnd_1132197 := by
    simpa [prefixWord, tailWord_1132197, baseEnd_1132197] using wordTrace_append hprefix tailTrace_1132197
  have hstable : (prefixWord ++ tailWord_1132197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132197).length < 2 ^ (prefixWord ++ tailWord_1132197).sum := by decide
  have hdescent : baseEnd_1132197 < baseStart_1132197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132237 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1132237 : Nat := 118140960795 + 1132237 * 2 ^ 59
def prefixEnd_1132237 : Nat := 4983230072969 + 3 ^ 40 * 1132237 * 2
def baseEnd_1132237 : Nat := 387587863869861234153629

theorem tailTrace_1132237 : CollatzResearch.WordTrace tailWord_1132237 prefixEnd_1132237 387587863869861234153629 := by
  unfold tailWord_1132237
  simp only [CollatzResearch.WordTrace]
  refine ⟨41296075999106194529682965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27530717332737463019788643 41296075999106194529682965)
  ·
    refine ⟨1935753562458102868578889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41296075999106194529682965 1935753562458102868578889)
    ·
      refine ⟨1451815171843577151434167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1935753562458102868578889 1451815171843577151434167)
      ·
        refine ⟨2177722757765365727151251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451815171843577151434167 2177722757765365727151251)
        ·
          refine ⟨3266584136648048590726877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177722757765365727151251 3266584136648048590726877)
          ·
            refine ⟨1224969051243018221522579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3266584136648048590726877 1224969051243018221522579)
            ·
              refine ⟨1837453576864527332283869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224969051243018221522579 1837453576864527332283869)
              ·
                refine ⟨689045091324197749606451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1837453576864527332283869 689045091324197749606451)
                ·
                  refine ⟨1033567636986296624409677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689045091324197749606451 1033567636986296624409677)
                  ·
                    refine ⟨387587863869861234153629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033567636986296624409677 387587863869861234153629)
                    ·
                      rfl

theorem cell22_1132237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1132237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132237 prefixEnd_1132237 := by exact prefixLift 1132237
  have htrace : WordTrace (prefixWord ++ tailWord_1132237) baseStart_1132237 baseEnd_1132237 := by
    simpa [prefixWord, tailWord_1132237, baseEnd_1132237] using wordTrace_append hprefix tailTrace_1132237
  have hstable : (prefixWord ++ tailWord_1132237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132237).length < 2 ^ (prefixWord ++ tailWord_1132237).sum := by decide
  have hdescent : baseEnd_1132237 < baseStart_1132237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132274 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1132274 : Nat := 118140960795 + 1132274 * 2 ^ 59
def prefixEnd_1132274 : Nat := 4983230072969 + 3 ^ 40 * 1132274 * 2
def baseEnd_1132274 : Nat := 387600529726005470978515

theorem tailTrace_1132274 : CollatzResearch.WordTrace tailWord_1132274 prefixEnd_1132274 387600529726005470978515 := by
  unfold tailWord_1132274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10324356374993037462194969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27531616999981433232519917 10324356374993037462194969)
  ·
    refine ⟨7743267281244778096646227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10324356374993037462194969 7743267281244778096646227)
    ·
      refine ⟨11614900921867167144969341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7743267281244778096646227 11614900921867167144969341)
      ·
        refine ⟨4355587845700187679363503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11614900921867167144969341 4355587845700187679363503)
        ·
          refine ⟨6533381768550281519045255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355587845700187679363503 6533381768550281519045255)
          ·
            refine ⟨9800072652825422278567883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533381768550281519045255 9800072652825422278567883)
            ·
              refine ⟨14700108979238133417851825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9800072652825422278567883 14700108979238133417851825)
              ·
                refine ⟨11025081734428600063388869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14700108979238133417851825 11025081734428600063388869)
                ·
                  refine ⟨2067202825205362511885413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11025081734428600063388869 2067202825205362511885413)
                  ·
                    refine ⟨387600529726005470978515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067202825205362511885413 387600529726005470978515)
                    ·
                      rfl

theorem cell22_1132274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1132274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132274 prefixEnd_1132274 := by exact prefixLift 1132274
  have htrace : WordTrace (prefixWord ++ tailWord_1132274) baseStart_1132274 baseEnd_1132274 := by
    simpa [prefixWord, tailWord_1132274, baseEnd_1132274] using wordTrace_append hprefix tailTrace_1132274
  have hstable : (prefixWord ++ tailWord_1132274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132274).length < 2 ^ (prefixWord ++ tailWord_1132274).sum := by decide
  have hdescent : baseEnd_1132274 < baseStart_1132274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132287 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_1132287 : Nat := 118140960795 + 1132287 * 2 ^ 59
def prefixEnd_1132287 : Nat := 4983230072969 + 3 ^ 40 * 1132287 * 2
def baseEnd_1132287 : Nat := 387604979891677770403475

theorem tailTrace_1132287 : CollatzResearch.WordTrace tailWord_1132287 prefixEnd_1132287 387604979891677770403475 := by
  unfold tailWord_1132287
  simp only [CollatzResearch.WordTrace]
  refine ⟨41297899648925053069003115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27531933099283368712668743 41297899648925053069003115)
  ·
    refine ⟨61946849473387579603504673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41297899648925053069003115 61946849473387579603504673)
    ·
      refine ⟨46460137105040684702628505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61946849473387579603504673 46460137105040684702628505)
      ·
        refine ⟨34845102828780513526971379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46460137105040684702628505 34845102828780513526971379)
        ·
          refine ⟨52267654243170770290457069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34845102828780513526971379 52267654243170770290457069)
          ·
            refine ⟨19600370341189038858921401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52267654243170770290457069 19600370341189038858921401)
            ·
              refine ⟨14700277755891779144191051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19600370341189038858921401 14700277755891779144191051)
              ·
                refine ⟨22050416633837668716286577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14700277755891779144191051 22050416633837668716286577)
                ·
                  refine ⟨16537812475378251537214933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22050416633837668716286577 16537812475378251537214933)
                  ·
                    refine ⟨387604979891677770403475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16537812475378251537214933 387604979891677770403475)
                    ·
                      rfl

theorem cell22_1132287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_1132287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132287 prefixEnd_1132287 := by exact prefixLift 1132287
  have htrace : WordTrace (prefixWord ++ tailWord_1132287) baseStart_1132287 baseEnd_1132287 := by
    simpa [prefixWord, tailWord_1132287, baseEnd_1132287] using wordTrace_append hprefix tailTrace_1132287
  have hstable : (prefixWord ++ tailWord_1132287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132287).length < 2 ^ (prefixWord ++ tailWord_1132287).sum := by decide
  have hdescent : baseEnd_1132287 < baseStart_1132287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132398 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1132398 : Nat := 118140960795 + 1132398 * 2 ^ 59
def prefixEnd_1132398 : Nat := 4983230072969 + 3 ^ 40 * 1132398 * 2
def baseEnd_1132398 : Nat := 387642977460110480878135

theorem tailTrace_1132398 : CollatzResearch.WordTrace tailWord_1132398 prefixEnd_1132398 387642977460110480878135 := by
  unfold tailWord_1132398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162743518940364878286731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27534632101015279350862565 5162743518940364878286731)
  ·
    refine ⟨7744115278410547317430097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162743518940364878286731 7744115278410547317430097)
    ·
      refine ⟨5808086458807910488072573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7744115278410547317430097 5808086458807910488072573)
      ·
        refine ⟨2178032422052966433027215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5808086458807910488072573 2178032422052966433027215)
        ·
          refine ⟨3267048633079449649540823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178032422052966433027215 3267048633079449649540823)
          ·
            refine ⟨4900572949619174474311235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267048633079449649540823 4900572949619174474311235)
            ·
              refine ⟨7350859424428761711466853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900572949619174474311235 7350859424428761711466853)
              ·
                refine ⟨1378286142080392820900035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7350859424428761711466853 1378286142080392820900035)
                ·
                  refine ⟨2067429213120589231350053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378286142080392820900035 2067429213120589231350053)
                  ·
                    refine ⟨387642977460110480878135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067429213120589231350053 387642977460110480878135)
                    ·
                      rfl

theorem cell22_1132398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1132398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132398 prefixEnd_1132398 := by exact prefixLift 1132398
  have htrace : WordTrace (prefixWord ++ tailWord_1132398) baseStart_1132398 baseEnd_1132398 := by
    simpa [prefixWord, tailWord_1132398, baseEnd_1132398] using wordTrace_append hprefix tailTrace_1132398
  have hstable : (prefixWord ++ tailWord_1132398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132398).length < 2 ^ (prefixWord ++ tailWord_1132398).sum := by decide
  have hdescent : baseEnd_1132398 < baseStart_1132398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132409 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_1132409 : Nat := 118140960795 + 1132409 * 2 ^ 59
def prefixEnd_1132409 : Nat := 4983230072969 + 3 ^ 40 * 1132409 * 2
def baseEnd_1132409 : Nat := 387646742984910118853101

theorem tailTrace_1132409 : CollatzResearch.WordTrace tailWord_1132409 prefixEnd_1132409 387646742984910118853101 := by
  unfold tailWord_1132409
  simp only [CollatzResearch.WordTrace]
  refine ⟨41302349354483067904944281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27534899569655378603296187 41302349354483067904944281)
  ·
    refine ⟨30976762015862300928708211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41302349354483067904944281 30976762015862300928708211)
    ·
      refine ⟨46465143023793451393062317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30976762015862300928708211 46465143023793451393062317)
      ·
        refine ⟨17424428633922544272398369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46465143023793451393062317 17424428633922544272398369)
        ·
          refine ⟨13068321475441908204298777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17424428633922544272398369 13068321475441908204298777)
          ·
            refine ⟨9801241106581431153224083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13068321475441908204298777 9801241106581431153224083)
            ·
              refine ⟨14701861659872146729836125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9801241106581431153224083 14701861659872146729836125)
              ·
                refine ⟨5513198122452055023688547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14701861659872146729836125 5513198122452055023688547)
                ·
                  refine ⟨8269797183678082535532821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5513198122452055023688547 8269797183678082535532821)
                  ·
                    refine ⟨387646742984910118853101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8269797183678082535532821 387646742984910118853101)
                    ·
                      rfl

theorem cell22_1132409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_1132409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132409 prefixEnd_1132409 := by exact prefixLift 1132409
  have htrace : WordTrace (prefixWord ++ tailWord_1132409) baseStart_1132409 baseEnd_1132409 := by
    simpa [prefixWord, tailWord_1132409, baseEnd_1132409] using wordTrace_append hprefix tailTrace_1132409
  have hstable : (prefixWord ++ tailWord_1132409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132409).length < 2 ^ (prefixWord ++ tailWord_1132409).sum := by decide
  have hdescent : baseEnd_1132409 < baseStart_1132409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132430 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1132430 : Nat := 118140960795 + 1132430 * 2 ^ 59
def prefixEnd_1132430 : Nat := 4983230072969 + 3 ^ 40 * 1132430 * 2
def baseEnd_1132430 : Nat := 129217977238024354692679

theorem tailTrace_1132430 : CollatzResearch.WordTrace tailWord_1132430 prefixEnd_1132430 129217977238024354692679 := by
  unfold tailWord_1132430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162889410925873561432343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27535410191604658994305829 5162889410925873561432343)
  ·
    refine ⟨7744334116388810342148515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162889410925873561432343 7744334116388810342148515)
    ·
      refine ⟨11616501174583215513222773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7744334116388810342148515 11616501174583215513222773)
      ·
        refine ⟨1089046985117176454364635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11616501174583215513222773 1089046985117176454364635)
        ·
          refine ⟨1633570477675764681546953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089046985117176454364635 1633570477675764681546953)
          ·
            refine ⟨1225177858256823511160215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633570477675764681546953 1225177858256823511160215)
            ·
              refine ⟨1837766787385235266740323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225177858256823511160215 1837766787385235266740323)
              ·
                refine ⟨2756650181077852900110485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837766787385235266740323 2756650181077852900110485)
                ·
                  refine ⟨129217977238024354692679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2756650181077852900110485 129217977238024354692679)
                  ·
                    rfl

theorem cell22_1132430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1132430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132430 prefixEnd_1132430 := by exact prefixLift 1132430
  have htrace : WordTrace (prefixWord ++ tailWord_1132430) baseStart_1132430 baseEnd_1132430 := by
    simpa [prefixWord, tailWord_1132430, baseEnd_1132430] using wordTrace_append hprefix tailTrace_1132430
  have hstable : (prefixWord ++ tailWord_1132430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132430).length < 2 ^ (prefixWord ++ tailWord_1132430).sum := by decide
  have hdescent : baseEnd_1132430 < baseStart_1132430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132445 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1132445 : Nat := 118140960795 + 1132445 * 2 ^ 59
def prefixEnd_1132445 : Nat := 4983230072969 + 3 ^ 40 * 1132445 * 2
def baseEnd_1132445 : Nat := 387659066520618024952991

theorem tailTrace_1132445 : CollatzResearch.WordTrace tailWord_1132445 prefixEnd_1132445 387659066520618024952991 := by
  unfold tailWord_1132445
  simp only [CollatzResearch.WordTrace]
  refine ⟨41303662382352646053254789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27535774921568430702169859 41303662382352646053254789)
  ·
    refine ⟨7744436696691121134985273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41303662382352646053254789 7744436696691121134985273)
    ·
      refine ⟨5808327522518340851238955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7744436696691121134985273 5808327522518340851238955)
      ·
        refine ⟨8712491283777511276858433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808327522518340851238955 8712491283777511276858433)
        ·
          refine ⟨6534368462833133457643825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8712491283777511276858433 6534368462833133457643825)
          ·
            refine ⟨4900776347124850093232869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6534368462833133457643825 4900776347124850093232869)
            ·
              refine ⟨918895565085909392481163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4900776347124850093232869 918895565085909392481163)
              ·
                refine ⟨1378343347628864088721745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918895565085909392481163 1378343347628864088721745)
                ·
                  refine ⟨1033757510721648066541309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378343347628864088721745 1033757510721648066541309)
                  ·
                    refine ⟨387659066520618024952991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033757510721648066541309 387659066520618024952991)
                    ·
                      rfl

theorem cell22_1132445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1132445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132445 prefixEnd_1132445 := by exact prefixLift 1132445
  have htrace : WordTrace (prefixWord ++ tailWord_1132445) baseStart_1132445 baseEnd_1132445 := by
    simpa [prefixWord, tailWord_1132445, baseEnd_1132445] using wordTrace_append hprefix tailTrace_1132445
  have hstable : (prefixWord ++ tailWord_1132445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132445).length < 2 ^ (prefixWord ++ tailWord_1132445).sum := by decide
  have hdescent : baseEnd_1132445 < baseStart_1132445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132462 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1132462 : Nat := 118140960795 + 1132462 * 2 ^ 59
def prefixEnd_1132462 : Nat := 4983230072969 + 3 ^ 40 * 1132462 * 2
def baseEnd_1132462 : Nat := 387664885968035647277939

theorem tailTrace_1132462 : CollatzResearch.WordTrace tailWord_1132462 prefixEnd_1132462 387664885968035647277939 := by
  unfold tailWord_1132462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163035302911382244577955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27536188282194038637749093 5163035302911382244577955)
  ·
    refine ⟨7744552954367073366866933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163035302911382244577955 7744552954367073366866933)
    ·
      refine ⟨726051839471913128143775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7744552954367073366866933 726051839471913128143775)
      ·
        refine ⟨1089077759207869692215663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726051839471913128143775 1089077759207869692215663)
        ·
          refine ⟨1633616638811804538323495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089077759207869692215663 1633616638811804538323495)
          ·
            refine ⟨2450424958217706807485243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633616638811804538323495 2450424958217706807485243)
            ·
              refine ⟨3675637437326560211227865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450424958217706807485243 3675637437326560211227865)
              ·
                refine ⟨2756728077994920158420899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675637437326560211227865 2756728077994920158420899)
                ·
                  refine ⟨4135092116992380237631349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756728077994920158420899 4135092116992380237631349)
                  ·
                    refine ⟨387664885968035647277939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4135092116992380237631349 387664885968035647277939)
                    ·
                      rfl

theorem cell22_1132462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1132462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132462 prefixEnd_1132462 := by exact prefixLift 1132462
  have htrace : WordTrace (prefixWord ++ tailWord_1132462) baseStart_1132462 baseEnd_1132462 := by
    simpa [prefixWord, tailWord_1132462, baseEnd_1132462] using wordTrace_append hprefix tailTrace_1132462
  have hstable : (prefixWord ++ tailWord_1132462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132462).length < 2 ^ (prefixWord ++ tailWord_1132462).sum := by decide
  have hdescent : baseEnd_1132462 < baseStart_1132462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132501 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1132501 : Nat := 118140960795 + 1132501 * 2 ^ 59
def prefixEnd_1132501 : Nat := 4983230072969 + 3 ^ 40 * 1132501 * 2
def baseEnd_1132501 : Nat := 387678236465052545552819

theorem tailTrace_1132501 : CollatzResearch.WordTrace tailWord_1132501 prefixEnd_1132501 387678236465052545552819 := by
  unfold tailWord_1132501
  simp only [CollatzResearch.WordTrace]
  refine ⟨41305704870149767617293357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27537136580099845078195571 41305704870149767617293357)
  ·
    refine ⟨15489639326306162856485009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41305704870149767617293357 15489639326306162856485009)
    ·
      refine ⟨11617229494729622142363757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489639326306162856485009 11617229494729622142363757)
      ·
        refine ⟨4356461060523608303386409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11617229494729622142363757 4356461060523608303386409)
        ·
          refine ⟨3267345795392706227539807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356461060523608303386409 3267345795392706227539807)
          ·
            refine ⟨4901018693089059341309711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267345795392706227539807 4901018693089059341309711)
            ·
              refine ⟨7351528039633589011964567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901018693089059341309711 7351528039633589011964567)
              ·
                refine ⟨11027292059450383517946851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7351528039633589011964567 11027292059450383517946851)
                ·
                  refine ⟨16540938089175575276920277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11027292059450383517946851 16540938089175575276920277)
                  ·
                    refine ⟨387678236465052545552819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16540938089175575276920277 387678236465052545552819)
                    ·
                      rfl

theorem cell22_1132501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1132501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132501 prefixEnd_1132501 := by exact prefixLift 1132501
  have htrace : WordTrace (prefixWord ++ tailWord_1132501) baseStart_1132501 baseEnd_1132501 := by
    simpa [prefixWord, tailWord_1132501, baseEnd_1132501] using wordTrace_append hprefix tailTrace_1132501
  have hstable : (prefixWord ++ tailWord_1132501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132501).length < 2 ^ (prefixWord ++ tailWord_1132501).sum := by decide
  have hdescent : baseEnd_1132501 < baseStart_1132501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132516 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1132516 : Nat := 118140960795 + 1132516 * 2 ^ 59
def prefixEnd_1132516 : Nat := 4983230072969 + 3 ^ 40 * 1132516 * 2
def baseEnd_1132516 : Nat := 387683371271597506427773

theorem tailTrace_1132516 : CollatzResearch.WordTrace tailWord_1132516 prefixEnd_1132516 387683371271597506427773 := by
  unfold tailWord_1132516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20653125982547712589544701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27537501310063616786059601 20653125982547712589544701)
  ·
    refine ⟨7744922243455392221079263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20653125982547712589544701 7744922243455392221079263)
    ·
      refine ⟨11617383365183088331618895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7744922243455392221079263 11617383365183088331618895)
      ·
        refine ⟨17426075047774632497428343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617383365183088331618895 17426075047774632497428343)
        ·
          refine ⟨26139112571661948746142515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17426075047774632497428343 26139112571661948746142515)
          ·
            refine ⟨39208668857492923119213773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26139112571661948746142515 39208668857492923119213773)
            ·
              refine ⟨14703250821559846169705165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39208668857492923119213773 14703250821559846169705165)
              ·
                refine ⟨5513719058084942313639437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14703250821559846169705165 5513719058084942313639437)
                ·
                  refine ⟨2067644646781853367614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5513719058084942313639437 2067644646781853367614789)
                  ·
                    refine ⟨387683371271597506427773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067644646781853367614789 387683371271597506427773)
                    ·
                      rfl

theorem cell22_1132516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1132516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132516 prefixEnd_1132516 := by exact prefixLift 1132516
  have htrace : WordTrace (prefixWord ++ tailWord_1132516) baseStart_1132516 baseEnd_1132516 := by
    simpa [prefixWord, tailWord_1132516, baseEnd_1132516] using wordTrace_append hprefix tailTrace_1132516
  have hstable : (prefixWord ++ tailWord_1132516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132516).length < 2 ^ (prefixWord ++ tailWord_1132516).sum := by decide
  have hdescent : baseEnd_1132516 < baseStart_1132516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132563 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 2, 3]
def baseStart_1132563 : Nat := 118140960795 + 1132563 * 2 ^ 59
def prefixEnd_1132563 : Nat := 4983230072969 + 3 ^ 40 * 1132563 * 2
def baseEnd_1132563 : Nat := 387699460332105050502629

theorem tailTrace_1132563 : CollatzResearch.WordTrace tailWord_1132563 prefixEnd_1132563 387699460332105050502629 := by
  unfold tailWord_1132563
  simp only [CollatzResearch.WordTrace]
  refine ⟨41307966195925152206050343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27538644130616768137366895 41307966195925152206050343)
  ·
    refine ⟨61961949293887728309075515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41307966195925152206050343 61961949293887728309075515)
    ·
      refine ⟨92942923940831592463613273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61961949293887728309075515 92942923940831592463613273)
      ·
        refine ⟨69707192955623694347709955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92942923940831592463613273 69707192955623694347709955)
        ·
          refine ⟨104560789433435541521564933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69707192955623694347709955 104560789433435541521564933)
          ·
            refine ⟨19605148018769164035293425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104560789433435541521564933 19605148018769164035293425)
            ·
              refine ⟨14703861014076873026470069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19605148018769164035293425 14703861014076873026470069)
              ·
                refine ⟨1378486970069706846231569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14703861014076873026470069 1378486970069706846231569)
                ·
                  refine ⟨1033865227552280134673677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378486970069706846231569 1033865227552280134673677)
                  ·
                    refine ⟨387699460332105050502629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033865227552280134673677 387699460332105050502629)
                    ·
                      rfl

theorem cell22_1132563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3].length) (baseStart_1132563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132563 prefixEnd_1132563 := by exact prefixLift 1132563
  have htrace : WordTrace (prefixWord ++ tailWord_1132563) baseStart_1132563 baseEnd_1132563 := by
    simpa [prefixWord, tailWord_1132563, baseEnd_1132563] using wordTrace_append hprefix tailTrace_1132563
  have hstable : (prefixWord ++ tailWord_1132563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132563).length < 2 ^ (prefixWord ++ tailWord_1132563).sum := by decide
  have hdescent : baseEnd_1132563 < baseStart_1132563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132578 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1132578 : Nat := 118140960795 + 1132578 * 2 ^ 59
def prefixEnd_1132578 : Nat := 4983230072969 + 3 ^ 40 * 1132578 * 2
def baseEnd_1132578 : Nat := 387704595138650011377583

theorem tailTrace_1132578 : CollatzResearch.WordTrace tailWord_1132578 prefixEnd_1132578 387704595138650011377583 := by
  unfold tailWord_1132578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327128322717702441961597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27539008860580539845230925 10327128322717702441961597)
  ·
    refine ⟨3872673121019138415735599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10327128322717702441961597 3872673121019138415735599)
    ·
      refine ⟨5809009681528707623603399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872673121019138415735599 5809009681528707623603399)
      ·
        refine ⟨8713514522293061435405099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809009681528707623603399 8713514522293061435405099)
        ·
          refine ⟨13070271783439592153107649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8713514522293061435405099 13070271783439592153107649)
          ·
            refine ⟨9802703837579694114830737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13070271783439592153107649 9802703837579694114830737)
            ·
              refine ⟨7352027878184770586123053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9802703837579694114830737 7352027878184770586123053)
              ·
                refine ⟨2757010454319288969796145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7352027878184770586123053 2757010454319288969796145)
                ·
                  refine ⟨2067757840739466727347109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757010454319288969796145 2067757840739466727347109)
                  ·
                    refine ⟨387704595138650011377583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067757840739466727347109 387704595138650011377583)
                    ·
                      rfl

theorem cell22_1132578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1132578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132578 prefixEnd_1132578 := by exact prefixLift 1132578
  have htrace : WordTrace (prefixWord ++ tailWord_1132578) baseStart_1132578 baseEnd_1132578 := by
    simpa [prefixWord, tailWord_1132578, baseEnd_1132578] using wordTrace_append hprefix tailTrace_1132578
  have hstable : (prefixWord ++ tailWord_1132578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132578).length < 2 ^ (prefixWord ++ tailWord_1132578).sum := by decide
  have hdescent : baseEnd_1132578 < baseStart_1132578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132653 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1132653 : Nat := 118140960795 + 1132653 * 2 ^ 59
def prefixEnd_1132653 : Nat := 4983230072969 + 3 ^ 40 * 1132653 * 2
def baseEnd_1132653 : Nat := 387730269171374815752353

theorem tailTrace_1132653 : CollatzResearch.WordTrace tailWord_1132653 prefixEnd_1132653 387730269171374815752353 := by
  unfold tailWord_1132653
  simp only [CollatzResearch.WordTrace]
  refine ⟨41311248765599097576826613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27540832510399398384551075 41311248765599097576826613)
  ·
    refine ⟨3872929571774915397827495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41311248765599097576826613 3872929571774915397827495)
    ·
      refine ⟨5809394357662373096741243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872929571774915397827495 5809394357662373096741243)
      ·
        refine ⟨8714091536493559645111865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809394357662373096741243 8714091536493559645111865)
        ·
          refine ⟨6535568652370169733833899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8714091536493559645111865 6535568652370169733833899)
          ·
            refine ⟨9803352978555254600750849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535568652370169733833899 9803352978555254600750849)
            ·
              refine ⟨7352514733916440950563137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9803352978555254600750849 7352514733916440950563137)
              ·
                refine ⟨5514386050437330712922353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352514733916440950563137 5514386050437330712922353)
                ·
                  refine ⟨4135789537827998034691765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514386050437330712922353 4135789537827998034691765)
                  ·
                    refine ⟨387730269171374815752353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4135789537827998034691765 387730269171374815752353)
                    ·
                      rfl

theorem cell22_1132653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1132653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132653 prefixEnd_1132653 := by exact prefixLift 1132653
  have htrace : WordTrace (prefixWord ++ tailWord_1132653) baseStart_1132653 baseEnd_1132653 := by
    simpa [prefixWord, tailWord_1132653, baseEnd_1132653] using wordTrace_append hprefix tailTrace_1132653
  have hstable : (prefixWord ++ tailWord_1132653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132653).length < 2 ^ (prefixWord ++ tailWord_1132653).sum := by decide
  have hdescent : baseEnd_1132653 < baseStart_1132653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132666 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_1132666 : Nat := 118140960795 + 1132666 * 2 ^ 59
def prefixEnd_1132666 : Nat := 4983230072969 + 3 ^ 40 * 1132666 * 2
def baseEnd_1132666 : Nat := 129244906445682371725771

theorem tailTrace_1132666 : CollatzResearch.WordTrace tailWord_1132666 prefixEnd_1132666 129244906445682371725771 := by
  unfold tailWord_1132666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327930728638000199262463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27541148609701333864699901 10327930728638000199262463)
  ·
    refine ⟨15491896092957000298893695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10327930728638000199262463 15491896092957000298893695)
    ·
      refine ⟨23237844139435500448340543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15491896092957000298893695 23237844139435500448340543)
      ·
        refine ⟨34856766209153250672510815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23237844139435500448340543 34856766209153250672510815)
        ·
          refine ⟨52285149313729876008766223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34856766209153250672510815 52285149313729876008766223)
          ·
            refine ⟨78427723970594814013149335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52285149313729876008766223 78427723970594814013149335)
            ·
              refine ⟨117641585955892221019724003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78427723970594814013149335 117641585955892221019724003)
              ·
                refine ⟨176462378933838331529586005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117641585955892221019724003 176462378933838331529586005)
                ·
                  refine ⟨129244906445682371725771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 176462378933838331529586005 129244906445682371725771)
                  ·
                    rfl

theorem cell22_1132666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_1132666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132666 prefixEnd_1132666 := by exact prefixLift 1132666
  have htrace : WordTrace (prefixWord ++ tailWord_1132666) baseStart_1132666 baseEnd_1132666 := by
    simpa [prefixWord, tailWord_1132666, baseEnd_1132666] using wordTrace_append hprefix tailTrace_1132666
  have hstable : (prefixWord ++ tailWord_1132666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132666).length < 2 ^ (prefixWord ++ tailWord_1132666).sum := by decide
  have hdescent : baseEnd_1132666 < baseStart_1132666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132668 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1132668 : Nat := 118140960795 + 1132668 * 2 ^ 59
def prefixEnd_1132668 : Nat := 4983230072969 + 3 ^ 40 * 1132668 * 2
def baseEnd_1132668 : Nat := 387735403977919776627307

theorem tailTrace_1132668 : CollatzResearch.WordTrace tailWord_1132668 prefixEnd_1132668 387735403977919776627307 := by
  unfold tailWord_1132668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20655897930272377569311329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27541197240363170092415105 20655897930272377569311329)
  ·
    refine ⟨15491923447704283176983497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20655897930272377569311329 15491923447704283176983497)
    ·
      refine ⟨11618942585778212382737623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15491923447704283176983497 11618942585778212382737623)
      ·
        refine ⟨17428413878667318574106435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11618942585778212382737623 17428413878667318574106435)
        ·
          refine ⟨26142620818000977861159653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17428413878667318574106435 26142620818000977861159653)
          ·
            refine ⟨4901741403375183348967435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26142620818000977861159653 4901741403375183348967435)
            ·
              refine ⟨7352612105062775023451153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901741403375183348967435 7352612105062775023451153)
              ·
                refine ⟨5514459078797081267588365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352612105062775023451153 5514459078797081267588365)
                ·
                  refine ⟨2067922154548905475345637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5514459078797081267588365 2067922154548905475345637)
                  ·
                    refine ⟨387735403977919776627307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067922154548905475345637 387735403977919776627307)
                    ·
                      rfl

theorem cell22_1132668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1132668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132668 prefixEnd_1132668 := by exact prefixLift 1132668
  have htrace : WordTrace (prefixWord ++ tailWord_1132668) baseStart_1132668 baseEnd_1132668 := by
    simpa [prefixWord, tailWord_1132668, baseEnd_1132668] using wordTrace_append hprefix tailTrace_1132668
  have hstable : (prefixWord ++ tailWord_1132668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132668).length < 2 ^ (prefixWord ++ tailWord_1132668).sum := by decide
  have hdescent : baseEnd_1132668 < baseStart_1132668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132717 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1132717 : Nat := 118140960795 + 1132717 * 2 ^ 59
def prefixEnd_1132717 : Nat := 4983230072969 + 3 ^ 40 * 1132717 * 2
def baseEnd_1132717 : Nat := 129250725893099994050719

theorem tailTrace_1132717 : CollatzResearch.WordTrace tailWord_1132717 prefixEnd_1132717 129250725893099994050719 := by
  unfold tailWord_1132717
  simp only [CollatzResearch.WordTrace]
  refine ⟨41313583037367236507156405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27542388691578157671437603 41313583037367236507156405)
  ·
    refine ⟨3873148409753178422545913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41313583037367236507156405 3873148409753178422545913)
    ·
      refine ⟨2904861307314883816909435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3873148409753178422545913 2904861307314883816909435)
      ·
        refine ⟨4357291960972325725364153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904861307314883816909435 4357291960972325725364153)
        ·
          refine ⟨3267968970729244294023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357291960972325725364153 3267968970729244294023115)
          ·
            refine ⟨4901953456093866441034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267968970729244294023115 4901953456093866441034673)
            ·
              refine ⟨3676465092070399830776005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4901953456093866441034673 3676465092070399830776005)
              ·
                refine ⟨689337204763199968270501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3676465092070399830776005 689337204763199968270501)
                ·
                  refine ⟨129250725893099994050719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689337204763199968270501 129250725893099994050719)
                  ·
                    rfl

theorem cell22_1132717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1132717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132717 prefixEnd_1132717 := by exact prefixLift 1132717
  have htrace : WordTrace (prefixWord ++ tailWord_1132717) baseStart_1132717 baseEnd_1132717 := by
    simpa [prefixWord, tailWord_1132717, baseEnd_1132717] using wordTrace_append hprefix tailTrace_1132717
  have hstable : (prefixWord ++ tailWord_1132717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132717).length < 2 ^ (prefixWord ++ tailWord_1132717).sum := by decide
  have hdescent : baseEnd_1132717 < baseStart_1132717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132732 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1132732 : Nat := 118140960795 + 1132732 * 2 ^ 59
def prefixEnd_1132732 : Nat := 4983230072969 + 3 ^ 40 * 1132732 * 2
def baseEnd_1132732 : Nat := 387757312485844943027111

theorem tailTrace_1132732 : CollatzResearch.WordTrace tailWord_1132732 prefixEnd_1132732 387757312485844943027111 := by
  unfold tailWord_1132732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657065066156447034476225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27542753421541929379301633 20657065066156447034476225)
  ·
    refine ⟨15492798799617335275857169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20657065066156447034476225 15492798799617335275857169)
    ·
      refine ⟨11619599099713001456892877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15492798799617335275857169 11619599099713001456892877)
      ·
        refine ⟨4357349662392375546334829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11619599099713001456892877 4357349662392375546334829)
        ·
          refine ⟨1634006123397140829875561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4357349662392375546334829 1634006123397140829875561)
          ·
            refine ⟨1225504592547855622406671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1634006123397140829875561 1225504592547855622406671)
            ·
              refine ⟨1838256888821783433610007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225504592547855622406671 1838256888821783433610007)
              ·
                refine ⟨2757385333232675150415011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838256888821783433610007 2757385333232675150415011)
                ·
                  refine ⟨4136077999849012725622517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757385333232675150415011 4136077999849012725622517)
                  ·
                    refine ⟨387757312485844943027111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4136077999849012725622517 387757312485844943027111)
                    ·
                      rfl

theorem cell22_1132732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1132732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132732 prefixEnd_1132732 := by exact prefixLift 1132732
  have htrace : WordTrace (prefixWord ++ tailWord_1132732) baseStart_1132732 baseEnd_1132732 := by
    simpa [prefixWord, tailWord_1132732, baseEnd_1132732] using wordTrace_append hprefix tailTrace_1132732
  have hstable : (prefixWord ++ tailWord_1132732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132732).length < 2 ^ (prefixWord ++ tailWord_1132732).sum := by decide
  have hdescent : baseEnd_1132732 < baseStart_1132732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132764 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1132764 : Nat := 118140960795 + 1132764 * 2 ^ 59
def prefixEnd_1132764 : Nat := 4983230072969 + 3 ^ 40 * 1132764 * 2
def baseEnd_1132764 : Nat := 387768266739807526227013

theorem tailTrace_1132764 : CollatzResearch.WordTrace tailWord_1132764 prefixEnd_1132764 387768266739807526227013 := by
  unfold tailWord_1132764
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657648634098481767058673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27543531512131309022744897 20657648634098481767058673)
  ·
    refine ⟨15493236475573861325294005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20657648634098481767058673 15493236475573861325294005)
    ·
      refine ⟨1452490919585049499246313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15493236475573861325294005 1452490919585049499246313)
      ·
        refine ⟨1089368189688787124434735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452490919585049499246313 1089368189688787124434735)
        ·
          refine ⟨1634052284533180686652103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089368189688787124434735 1634052284533180686652103)
          ·
            refine ⟨2451078426799771029978155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634052284533180686652103 2451078426799771029978155)
            ·
              refine ⟨3676617640199656544967233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451078426799771029978155 3676617640199656544967233)
              ·
                refine ⟨2757463230149742408725425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3676617640199656544967233 2757463230149742408725425)
                ·
                  refine ⟨2068097422612306806544069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757463230149742408725425 2068097422612306806544069)
                  ·
                    refine ⟨387768266739807526227013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068097422612306806544069 387768266739807526227013)
                    ·
                      rfl

theorem cell22_1132764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1132764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132764 prefixEnd_1132764 := by exact prefixLift 1132764
  have htrace : WordTrace (prefixWord ++ tailWord_1132764) baseStart_1132764 baseEnd_1132764 := by
    simpa [prefixWord, tailWord_1132764, baseEnd_1132764] using wordTrace_append hprefix tailTrace_1132764
  have hstable : (prefixWord ++ tailWord_1132764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132764).length < 2 ^ (prefixWord ++ tailWord_1132764).sum := by decide
  have hdescent : baseEnd_1132764 < baseStart_1132764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132852 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1132852 : Nat := 118140960795 + 1132852 * 2 ^ 59
def prefixEnd_1132852 : Nat := 4983230072969 + 3 ^ 40 * 1132852 * 2
def baseEnd_1132852 : Nat := 129266130312734876675581

theorem tailTrace_1132852 : CollatzResearch.WordTrace tailWord_1132852 prefixEnd_1132852 129266130312734876675581 := by
  unfold tailWord_1132852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20659253445939077281660405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27545671261252103042213873 20659253445939077281660405)
  ·
    refine ⟨1936805010556788495155663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20659253445939077281660405 1936805010556788495155663)
    ·
      refine ⟨2905207515835182742733495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936805010556788495155663 2905207515835182742733495)
      ·
        refine ⟨4357811273752774114100243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905207515835182742733495 4357811273752774114100243)
        ·
          refine ⟨6536716910629161171150365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357811273752774114100243 6536716910629161171150365)
          ·
            refine ⟨2451268841485935439181387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6536716910629161171150365 2451268841485935439181387)
            ·
              refine ⟨3676903262228903158772081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451268841485935439181387 3676903262228903158772081)
              ·
                refine ⟨2757677446671677369079061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3676903262228903158772081 2757677446671677369079061)
                ·
                  refine ⟨129266130312734876675581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2757677446671677369079061 129266130312734876675581)
                  ·
                    rfl

theorem cell22_1132852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1132852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132852 prefixEnd_1132852 := by exact prefixLift 1132852
  have htrace : WordTrace (prefixWord ++ tailWord_1132852) baseStart_1132852 baseEnd_1132852 := by
    simpa [prefixWord, tailWord_1132852, baseEnd_1132852] using wordTrace_append hprefix tailTrace_1132852
  have hstable : (prefixWord ++ tailWord_1132852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132852).length < 2 ^ (prefixWord ++ tailWord_1132852).sum := by decide
  have hdescent : baseEnd_1132852 < baseStart_1132852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132884 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1132884 : Nat := 118140960795 + 1132884 * 2 ^ 59
def prefixEnd_1132884 : Nat := 4983230072969 + 3 ^ 40 * 1132884 * 2
def baseEnd_1132884 : Nat := 387809345192167213226645

theorem tailTrace_1132884 : CollatzResearch.WordTrace tailWord_1132884 prefixEnd_1132884 387809345192167213226645 := by
  unfold tailWord_1132884
  simp only [CollatzResearch.WordTrace]
  refine ⟨20659837013881112014242853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27546449351841482685657137 20659837013881112014242853)
  ·
    refine ⟨3873719440102708502670535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20659837013881112014242853 3873719440102708502670535)
    ·
      refine ⟨5810579160154062754005803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873719440102708502670535 5810579160154062754005803)
      ·
        refine ⟨8715868740231094131008705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810579160154062754005803 8715868740231094131008705)
        ·
          refine ⟨6536901555173320598256529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8715868740231094131008705 6536901555173320598256529)
          ·
            refine ⟨4902676166379990448692397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536901555173320598256529 4902676166379990448692397)
            ·
              refine ⟨1838503562392496418259649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4902676166379990448692397 1838503562392496418259649)
              ·
                refine ⟨1378877671794372313694737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838503562392496418259649 1378877671794372313694737)
                ·
                  refine ⟨1034158253845779235271053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378877671794372313694737 1034158253845779235271053)
                  ·
                    refine ⟨387809345192167213226645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034158253845779235271053 387809345192167213226645)
                    ·
                      rfl

theorem cell22_1132884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1132884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132884 prefixEnd_1132884 := by exact prefixLift 1132884
  have htrace : WordTrace (prefixWord ++ tailWord_1132884) baseStart_1132884 baseEnd_1132884 := by
    simpa [prefixWord, tailWord_1132884, baseEnd_1132884] using wordTrace_append hprefix tailTrace_1132884
  have hstable : (prefixWord ++ tailWord_1132884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132884).length < 2 ^ (prefixWord ++ tailWord_1132884).sum := by decide
  have hdescent : baseEnd_1132884 < baseStart_1132884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132912 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_1132912 : Nat := 118140960795 + 1132912 * 2 ^ 59
def prefixEnd_1132912 : Nat := 4983230072969 + 3 ^ 40 * 1132912 * 2
def baseEnd_1132912 : Nat := 387818930164384473526559

theorem tailTrace_1132912 : CollatzResearch.WordTrace tailWord_1132912 prefixEnd_1132912 387818930164384473526559 := by
  unfold tailWord_1132912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20660347635830392405252495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27547130181107189873669993 20660347635830392405252495)
  ·
    refine ⟨30990521453745588607878743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20660347635830392405252495 30990521453745588607878743)
    ·
      refine ⟨46485782180618382911818115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30990521453745588607878743 46485782180618382911818115)
      ·
        refine ⟨69728673270927574367727173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46485782180618382911818115 69728673270927574367727173)
        ·
          refine ⟨13074126238298920193948845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69728673270927574367727173 13074126238298920193948845)
          ·
            refine ⟨4902797339362095072730817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13074126238298920193948845 4902797339362095072730817)
            ·
              refine ⟨3677098004521571304548113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902797339362095072730817 3677098004521571304548113)
              ·
                refine ⟨2757823503391178478411085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3677098004521571304548113 2757823503391178478411085)
                ·
                  refine ⟨1034183813771691929404157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2757823503391178478411085 1034183813771691929404157)
                  ·
                    refine ⟨387818930164384473526559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034183813771691929404157 387818930164384473526559)
                    ·
                      rfl

theorem cell22_1132912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_1132912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132912 prefixEnd_1132912 := by exact prefixLift 1132912
  have htrace : WordTrace (prefixWord ++ tailWord_1132912) baseStart_1132912 baseEnd_1132912 := by
    simpa [prefixWord, tailWord_1132912, baseEnd_1132912] using wordTrace_append hprefix tailTrace_1132912
  have hstable : (prefixWord ++ tailWord_1132912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132912).length < 2 ^ (prefixWord ++ tailWord_1132912).sum := by decide
  have hdescent : baseEnd_1132912 < baseStart_1132912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132925 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 7]
def baseStart_1132925 : Nat := 118140960795 + 1132925 * 2 ^ 59
def prefixEnd_1132925 : Nat := 4983230072969 + 3 ^ 40 * 1132925 * 2
def baseEnd_1132925 : Nat := 129274460110018924317173

theorem tailTrace_1132925 : CollatzResearch.WordTrace tailWord_1132925 prefixEnd_1132925 129274460110018924317173 := by
  unfold tailWord_1132925
  simp only [CollatzResearch.WordTrace]
  refine ⟨41321169420613688030728229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27547446280409125353818819 41321169420613688030728229)
  ·
    refine ⟨7747719266365066505761543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41321169420613688030728229 7747719266365066505761543)
    ·
      refine ⟨11621578899547599758642315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747719266365066505761543 11621578899547599758642315)
      ·
        refine ⟨17432368349321399637963473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11621578899547599758642315 17432368349321399637963473)
        ·
          refine ⟨13074276261991049728472605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17432368349321399637963473 13074276261991049728472605)
          ·
            refine ⟨4902853598246643648177227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13074276261991049728472605 4902853598246643648177227)
            ·
              refine ⟨7354280397369965472265841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902853598246643648177227 7354280397369965472265841)
              ·
                refine ⟨5515710298027474104199381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7354280397369965472265841 5515710298027474104199381)
                ·
                  refine ⟨129274460110018924317173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5515710298027474104199381 129274460110018924317173)
                  ·
                    rfl

theorem cell22_1132925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_1132925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132925 prefixEnd_1132925 := by exact prefixLift 1132925
  have htrace : WordTrace (prefixWord ++ tailWord_1132925) baseStart_1132925 baseEnd_1132925 := by
    simpa [prefixWord, tailWord_1132925, baseEnd_1132925] using wordTrace_append hprefix tailTrace_1132925
  have hstable : (prefixWord ++ tailWord_1132925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132925).length < 2 ^ (prefixWord ++ tailWord_1132925).sum := by decide
  have hdescent : baseEnd_1132925 < baseStart_1132925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132942 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1132942 : Nat := 118140960795 + 1132942 * 2 ^ 59
def prefixEnd_1132942 : Nat := 4983230072969 + 3 ^ 40 * 1132942 * 2
def baseEnd_1132942 : Nat := 129276399925824798425489

theorem tailTrace_1132942 : CollatzResearch.WordTrace tailWord_1132942 prefixEnd_1132942 129276399925824798425489 := by
  unfold tailWord_1132942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165223682694012491762135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27547859641034733289398053 5165223682694012491762135)
  ·
    refine ⟨7747835524041018737643203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165223682694012491762135 7747835524041018737643203)
    ·
      refine ⟨11621753286061528106464805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747835524041018737643203 11621753286061528106464805)
      ·
        refine ⟨2179078741136536519962151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11621753286061528106464805 2179078741136536519962151)
        ·
          refine ⟨3268618111704804779943227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179078741136536519962151 3268618111704804779943227)
          ·
            refine ⟨4902927167557207169914841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268618111704804779943227 4902927167557207169914841)
            ·
              refine ⟨3677195375667905377436131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902927167557207169914841 3677195375667905377436131)
              ·
                refine ⟨5515793063501858066154197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677195375667905377436131 5515793063501858066154197)
                ·
                  refine ⟨129276399925824798425489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5515793063501858066154197 129276399925824798425489)
                  ·
                    rfl

theorem cell22_1132942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1132942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132942 prefixEnd_1132942 := by exact prefixLift 1132942
  have htrace : WordTrace (prefixWord ++ tailWord_1132942) baseStart_1132942 baseEnd_1132942 := by
    simpa [prefixWord, tailWord_1132942, baseEnd_1132942] using wordTrace_append hprefix tailTrace_1132942
  have hstable : (prefixWord ++ tailWord_1132942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132942).length < 2 ^ (prefixWord ++ tailWord_1132942).sum := by decide
  have hdescent : baseEnd_1132942 < baseStart_1132942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132993 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 5]
def baseStart_1132993 : Nat := 118140960795 + 1132993 * 2 ^ 59
def prefixEnd_1132993 : Nat := 4983230072969 + 3 ^ 40 * 1132993 * 2
def baseEnd_1132993 : Nat := 129282219373242420750437

theorem tailTrace_1132993 : CollatzResearch.WordTrace tailWord_1132993 prefixEnd_1132993 129282219373242420750437 := by
  unfold tailWord_1132993
  simp only [CollatzResearch.WordTrace]
  refine ⟨41323649584367335644203633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27549099722911557096135755 41323649584367335644203633)
  ·
    refine ⟨30992737188275501733152725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41323649584367335644203633 30992737188275501733152725)
    ·
      refine ⟨726392277850207071870767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30992737188275501733152725 726392277850207071870767)
      ·
        refine ⟨1089588416775310607806151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726392277850207071870767 1089588416775310607806151)
        ·
          refine ⟨1634382625162965911709227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089588416775310607806151 1634382625162965911709227)
          ·
            refine ⟨2451573937744448867563841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634382625162965911709227 2451573937744448867563841)
            ·
              refine ⟨1838680453308336650672881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451573937744448867563841 1838680453308336650672881)
              ·
                refine ⟨1379010339981252488004661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838680453308336650672881 1379010339981252488004661)
                ·
                  refine ⟨129282219373242420750437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1379010339981252488004661 129282219373242420750437)
                  ·
                    rfl

theorem cell22_1132993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_1132993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1132993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1132993 prefixEnd_1132993 := by exact prefixLift 1132993
  have htrace : WordTrace (prefixWord ++ tailWord_1132993) baseStart_1132993 baseEnd_1132993 := by
    simpa [prefixWord, tailWord_1132993, baseEnd_1132993] using wordTrace_append hprefix tailTrace_1132993
  have hstable : (prefixWord ++ tailWord_1132993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132993).length < 2 ^ (prefixWord ++ tailWord_1132993).sum := by decide
  have hdescent : baseEnd_1132993 < baseStart_1132993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133034 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1133034 : Nat := 118140960795 + 1133034 * 2 ^ 59
def prefixEnd_1133034 : Nat := 4983230072969 + 3 ^ 40 * 1133034 * 2
def baseEnd_1133034 : Nat := 387860693257616821976185

theorem tailTrace_1133034 : CollatzResearch.WordTrace tailWord_1133034 prefixEnd_1133034 387860693257616821976185 := by
  unfold tailWord_1133034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331286244304699911611539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27550096651479199764297437 10331286244304699911611539)
  ·
    refine ⟨15496929366457049867417309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10331286244304699911611539 15496929366457049867417309)
    ·
      refine ⟨5811348512421393700281491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15496929366457049867417309 5811348512421393700281491)
      ·
        refine ⟨8717022768632090550422237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811348512421393700281491 8717022768632090550422237)
        ·
          refine ⟨3268883538237033956408339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8717022768632090550422237 3268883538237033956408339)
          ·
            refine ⟨4903325307355550934612509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268883538237033956408339 4903325307355550934612509)
            ·
              refine ⟨1838746990258331600479691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4903325307355550934612509 1838746990258331600479691)
              ·
                refine ⟨2758120485387497400719537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838746990258331600479691 2758120485387497400719537)
                ·
                  refine ⟨2068590364040623050539653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758120485387497400719537 2068590364040623050539653)
                  ·
                    refine ⟨387860693257616821976185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068590364040623050539653 387860693257616821976185)
                    ·
                      rfl

theorem cell22_1133034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1133034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133034 prefixEnd_1133034 := by exact prefixLift 1133034
  have htrace : WordTrace (prefixWord ++ tailWord_1133034) baseStart_1133034 baseEnd_1133034 := by
    simpa [prefixWord, tailWord_1133034, baseEnd_1133034] using wordTrace_append hprefix tailTrace_1133034
  have hstable : (prefixWord ++ tailWord_1133034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133034).length < 2 ^ (prefixWord ++ tailWord_1133034).sum := by decide
  have hdescent : baseEnd_1133034 < baseStart_1133034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133098 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1133098 : Nat := 118140960795 + 1133098 * 2 ^ 59
def prefixEnd_1133098 : Nat := 4983230072969 + 3 ^ 40 * 1133098 * 2
def baseEnd_1133098 : Nat := 387882601765541988375989

theorem tailTrace_1133098 : CollatzResearch.WordTrace tailWord_1133098 prefixEnd_1133098 387882601765541988375989 := by
  unfold tailWord_1133098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331869812246734644193987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27551652832657959051183965 10331869812246734644193987)
  ·
    refine ⟨15497804718370101966290981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10331869812246734644193987 15497804718370101966290981)
    ·
      refine ⟨2905838384694394118679559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15497804718370101966290981 2905838384694394118679559)
      ·
        refine ⟨4358757577041591178019339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905838384694394118679559 4358757577041591178019339)
        ·
          refine ⟨6538136365562386767029009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358757577041591178019339 6538136365562386767029009)
          ·
            refine ⟨4903602274171790075271757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6538136365562386767029009 4903602274171790075271757)
            ·
              refine ⟨1838850852814421278226909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4903602274171790075271757 1838850852814421278226909)
              ·
                refine ⟨689569069805407979335091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838850852814421278226909 689569069805407979335091)
                ·
                  refine ⟨1034353604708111969002637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689569069805407979335091 1034353604708111969002637)
                  ·
                    refine ⟨387882601765541988375989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034353604708111969002637 387882601765541988375989)
                    ·
                      rfl

theorem cell22_1133098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1133098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133098 prefixEnd_1133098 := by exact prefixLift 1133098
  have htrace : WordTrace (prefixWord ++ tailWord_1133098) baseStart_1133098 baseEnd_1133098 := by
    simpa [prefixWord, tailWord_1133098, baseEnd_1133098] using wordTrace_append hprefix tailTrace_1133098
  have hstable : (prefixWord ++ tailWord_1133098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133098).length < 2 ^ (prefixWord ++ tailWord_1133098).sum := by decide
  have hdescent : baseEnd_1133098 < baseStart_1133098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133152 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_1133152 : Nat := 118140960795 + 1133152 * 2 ^ 59
def prefixEnd_1133152 : Nat := 4983230072969 + 3 ^ 40 * 1133152 * 2
def baseEnd_1133152 : Nat := 387901087069103847525823

theorem tailTrace_1133152 : CollatzResearch.WordTrace tailWord_1133152 prefixEnd_1133152 387901087069103847525823 := by
  unfold tailWord_1133152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664724395395652899620855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27552965860527537199494473 20664724395395652899620855)
  ·
    refine ⟨30997086593093479349431283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20664724395395652899620855 30997086593093479349431283)
    ·
      refine ⟨46495629889640219024146925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30997086593093479349431283 46495629889640219024146925)
      ·
        refine ⟨17435861208615082134055097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46495629889640219024146925 17435861208615082134055097)
        ·
          refine ⟨13076895906461311600541323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17435861208615082134055097 13076895906461311600541323)
          ·
            refine ⟨19615343859691967400811985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13076895906461311600541323 19615343859691967400811985)
            ·
              refine ⟨14711507894768975550608989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19615343859691967400811985 14711507894768975550608989)
              ·
                refine ⟨5516815460538365831478371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14711507894768975550608989 5516815460538365831478371)
                ·
                  refine ⟨8275223190807548747217557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516815460538365831478371 8275223190807548747217557)
                  ·
                    refine ⟨387901087069103847525823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8275223190807548747217557 387901087069103847525823)
                    ·
                      rfl

theorem cell22_1133152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_1133152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133152 prefixEnd_1133152 := by exact prefixLift 1133152
  have htrace : WordTrace (prefixWord ++ tailWord_1133152) baseStart_1133152 baseEnd_1133152 := by
    simpa [prefixWord, tailWord_1133152, baseEnd_1133152] using wordTrace_append hprefix tailTrace_1133152
  have hstable : (prefixWord ++ tailWord_1133152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133152).length < 2 ^ (prefixWord ++ tailWord_1133152).sum := by decide
  have hdescent : baseEnd_1133152 < baseStart_1133152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133173 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 4]
def baseStart_1133173 : Nat := 118140960795 + 1133173 * 2 ^ 59
def prefixEnd_1133173 : Nat := 4983230072969 + 3 ^ 40 * 1133173 * 2
def baseEnd_1133173 : Nat := 129302758599422264250253

theorem tailTrace_1133173 : CollatzResearch.WordTrace tailWord_1133173 prefixEnd_1133173 129302758599422264250253 := by
  unfold tailWord_1133173
  simp only [CollatzResearch.WordTrace]
  refine ⟨41330214723715226385756173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27553476482476817590504115 41330214723715226385756173)
  ·
    refine ⟨15498830521393209894658565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41330214723715226385756173 15498830521393209894658565)
    ·
      refine ⟨2906030722761226855248481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15498830521393209894658565 2906030722761226855248481)
      ·
        refine ⟨2179523042070920141436361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2906030722761226855248481 2179523042070920141436361)
        ·
          refine ⟨1634642281553190106077271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2179523042070920141436361 1634642281553190106077271)
          ·
            refine ⟨2451963422329785159115907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634642281553190106077271 2451963422329785159115907)
            ·
              refine ⟨3677945133494677738673861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451963422329785159115907 3677945133494677738673861)
              ·
                refine ⟨689614712530252076001349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3677945133494677738673861 689614712530252076001349)
                ·
                  refine ⟨129302758599422264250253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689614712530252076001349 129302758599422264250253)
                  ·
                    rfl

theorem cell22_1133173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_1133173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133173 prefixEnd_1133173 := by exact prefixLift 1133173
  have htrace : WordTrace (prefixWord ++ tailWord_1133173) baseStart_1133173 baseEnd_1133173 := by
    simpa [prefixWord, tailWord_1133173, baseEnd_1133173] using wordTrace_append hprefix tailTrace_1133173
  have hstable : (prefixWord ++ tailWord_1133173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133173).length < 2 ^ (prefixWord ++ tailWord_1133173).sum := by decide
  have hdescent : baseEnd_1133173 < baseStart_1133173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133184 : List Nat := [2, 1, 1, 2, 1, 7, 1, 7]
def baseStart_1133184 : Nat := 118140960795 + 1133184 * 2 ^ 59
def prefixEnd_1133184 : Nat := 4983230072969 + 3 ^ 40 * 1133184 * 2
def baseEnd_1133184 : Nat := 43101337924785158969525

theorem tailTrace_1133184 : CollatzResearch.WordTrace tailWord_1133184 prefixEnd_1133184 43101337924785158969525 := by
  unfold tailWord_1133184
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665307963337687632203303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27553743951116916842937737 20665307963337687632203303)
  ·
    refine ⟨30997961945006531448304955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20665307963337687632203303 30997961945006531448304955)
    ·
      refine ⟨46496942917509797172457433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30997961945006531448304955 46496942917509797172457433)
      ·
        refine ⟨34872707188132347879343075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46496942917509797172457433 34872707188132347879343075)
        ·
          refine ⟨52309060782198521819014613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34872707188132347879343075 52309060782198521819014613)
          ·
            refine ⟨1225993612082777855133155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52309060782198521819014613 1225993612082777855133155)
            ·
              refine ⟨1838990418124166782699733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225993612082777855133155 1838990418124166782699733)
              ·
                refine ⟨43101337924785158969525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1838990418124166782699733 43101337924785158969525)
                ·
                  rfl

theorem cell22_1133184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_1133184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133184 prefixEnd_1133184 := by exact prefixLift 1133184
  have htrace : WordTrace (prefixWord ++ tailWord_1133184) baseStart_1133184 baseEnd_1133184 := by
    simpa [prefixWord, tailWord_1133184, baseEnd_1133184] using wordTrace_append hprefix tailTrace_1133184
  have hstable : (prefixWord ++ tailWord_1133184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133184).length < 2 ^ (prefixWord ++ tailWord_1133184).sum := by decide
  have hdescent : baseEnd_1133184 < baseStart_1133184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133199 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 3, 3]
def baseStart_1133199 : Nat := 118140960795 + 1133199 * 2 ^ 59
def prefixEnd_1133199 : Nat := 4983230072969 + 3 ^ 40 * 1133199 * 2
def baseEnd_1133199 : Nat := 387917176129611391600679

theorem tailTrace_1133199 : CollatzResearch.WordTrace tailWord_1133199 prefixEnd_1133199 387917176129611391600679 := by
  unfold tailWord_1133199
  simp only [CollatzResearch.WordTrace]
  refine ⟨41331163021621032826202651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27554108681080688550801767 41331163021621032826202651)
  ·
    refine ⟨61996744532431549239303977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41331163021621032826202651 61996744532431549239303977)
    ·
      refine ⟨46497558399323661929477983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61996744532431549239303977 46497558399323661929477983)
      ·
        refine ⟨69746337598985492894216975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46497558399323661929477983 69746337598985492894216975)
        ·
          refine ⟨104619506398478239341325463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69746337598985492894216975 104619506398478239341325463)
          ·
            refine ⟨156929259597717359011988195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104619506398478239341325463 156929259597717359011988195)
            ·
              refine ⟨235393889396576038517982293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156929259597717359011988195 235393889396576038517982293)
              ·
                refine ⟨2758522141366125451382605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 235393889396576038517982293 2758522141366125451382605)
                ·
                  refine ⟨1034445803012297044268477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2758522141366125451382605 1034445803012297044268477)
                  ·
                    refine ⟨387917176129611391600679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034445803012297044268477 387917176129611391600679)
                    ·
                      rfl

theorem cell22_1133199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_1133199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133199 prefixEnd_1133199 := by exact prefixLift 1133199
  have htrace : WordTrace (prefixWord ++ tailWord_1133199) baseStart_1133199 baseEnd_1133199 := by
    simpa [prefixWord, tailWord_1133199, baseEnd_1133199] using wordTrace_append hprefix tailTrace_1133199
  have hstable : (prefixWord ++ tailWord_1133199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133199).length < 2 ^ (prefixWord ++ tailWord_1133199).sum := by decide
  have hdescent : baseEnd_1133199 < baseStart_1133199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133244 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1133244 : Nat := 118140960795 + 1133244 * 2 ^ 59
def prefixEnd_1133244 : Nat := 4983230072969 + 3 ^ 40 * 1133244 * 2
def baseEnd_1133244 : Nat := 387932580549246274225541

theorem tailTrace_1133244 : CollatzResearch.WordTrace tailWord_1133244 prefixEnd_1133244 387932580549246274225541 := by
  unfold tailWord_1133244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20666402153229002755795393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27555202870972003674393857 20666402153229002755795393)
  ·
    refine ⟨15499801614921752066846545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20666402153229002755795393 15499801614921752066846545)
    ·
      refine ⟨11624851211191314050134909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15499801614921752066846545 11624851211191314050134909)
      ·
        refine ⟨4359319204196742768800591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11624851211191314050134909 4359319204196742768800591)
        ·
          refine ⟨6538978806295114153200887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359319204196742768800591 6538978806295114153200887)
          ·
            refine ⟨9808468209442671229801331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6538978806295114153200887 9808468209442671229801331)
            ·
              refine ⟨14712702314164006844701997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9808468209442671229801331 14712702314164006844701997)
              ·
                refine ⟨5517263367811502566763249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14712702314164006844701997 5517263367811502566763249)
                ·
                  refine ⟨4137947525858626925072437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5517263367811502566763249 4137947525858626925072437)
                  ·
                    refine ⟨387932580549246274225541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4137947525858626925072437 387932580549246274225541)
                    ·
                      rfl

theorem cell22_1133244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1133244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133244 prefixEnd_1133244 := by exact prefixLift 1133244
  have htrace : WordTrace (prefixWord ++ tailWord_1133244) baseStart_1133244 baseEnd_1133244 := by
    simpa [prefixWord, tailWord_1133244, baseEnd_1133244] using wordTrace_append hprefix tailTrace_1133244
  have hstable : (prefixWord ++ tailWord_1133244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133244).length < 2 ^ (prefixWord ++ tailWord_1133244).sum := by decide
  have hdescent : baseEnd_1133244 < baseStart_1133244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133304 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1133304 : Nat := 118140960795 + 1133304 * 2 ^ 59
def prefixEnd_1133304 : Nat := 4983230072969 + 3 ^ 40 * 1133304 * 2
def baseEnd_1133304 : Nat := 387953119775426117725357

theorem tailTrace_1133304 : CollatzResearch.WordTrace tailWord_1133304 prefixEnd_1133304 387953119775426117725357 := by
  unfold tailWord_1133304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667496343120317879387483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27556661790827090505849977 20667496343120317879387483)
  ·
    refine ⟨31001244514680476819081225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20667496343120317879387483 31001244514680476819081225)
    ·
      refine ⟨23250933386010357614310919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31001244514680476819081225 23250933386010357614310919)
      ·
        refine ⟨34876400079015536421466379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23250933386010357614310919 34876400079015536421466379)
        ·
          refine ⟨52314600118523304632199569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34876400079015536421466379 52314600118523304632199569)
          ·
            refine ⟨39235950088892478474149677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52314600118523304632199569 39235950088892478474149677)
            ·
              refine ⟨14713481283334679427806129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39235950088892478474149677 14713481283334679427806129)
              ·
                refine ⟨11035110962501009570854597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14713481283334679427806129 11035110962501009570854597)
                ·
                  refine ⟨2069083305468939294535237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11035110962501009570854597 2069083305468939294535237)
                  ·
                    refine ⟨387953119775426117725357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069083305468939294535237 387953119775426117725357)
                    ·
                      rfl

theorem cell22_1133304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1133304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133304 prefixEnd_1133304 := by exact prefixLift 1133304
  have htrace : WordTrace (prefixWord ++ tailWord_1133304) baseStart_1133304 baseEnd_1133304 := by
    simpa [prefixWord, tailWord_1133304, baseEnd_1133304] using wordTrace_append hprefix tailTrace_1133304
  have hstable : (prefixWord ++ tailWord_1133304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133304).length < 2 ^ (prefixWord ++ tailWord_1133304).sum := by decide
  have hdescent : baseEnd_1133304 < baseStart_1133304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133310 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1133310 : Nat := 118140960795 + 1133310 * 2 ^ 59
def prefixEnd_1133310 : Nat := 4983230072969 + 3 ^ 40 * 1133310 * 2
def baseEnd_1133310 : Nat := 387955173698044102075339

theorem tailTrace_1133310 : CollatzResearch.WordTrace tailWord_1133310 prefixEnd_1133310 387955173698044102075339 := by
  unfold tailWord_1133310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5166901440527362347936673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27556807682812599188995589 5166901440527362347936673)
  ·
    refine ⟨3875176080395521760952505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5166901440527362347936673 3875176080395521760952505)
    ·
      refine ⟨2906382060296641320714379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3875176080395521760952505 2906382060296641320714379)
      ·
        refine ⟨4359573090444961981071569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906382060296641320714379 4359573090444961981071569)
        ·
          refine ⟨3269679817833721485803677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4359573090444961981071569 3269679817833721485803677)
          ·
            refine ⟨1226129931687645557176379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3269679817833721485803677 1226129931687645557176379)
            ·
              refine ⟨1839194897531468335764569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226129931687645557176379 1839194897531468335764569)
              ·
                refine ⟨1379396173148601251823427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839194897531468335764569 1379396173148601251823427)
                ·
                  refine ⟨2069094259722901877735141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379396173148601251823427 2069094259722901877735141)
                  ·
                    refine ⟨387955173698044102075339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069094259722901877735141 387955173698044102075339)
                    ·
                      rfl

theorem cell22_1133310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1133310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133310 prefixEnd_1133310 := by exact prefixLift 1133310
  have htrace : WordTrace (prefixWord ++ tailWord_1133310) baseStart_1133310 baseEnd_1133310 := by
    simpa [prefixWord, tailWord_1133310, baseEnd_1133310] using wordTrace_append hprefix tailTrace_1133310
  have hstable : (prefixWord ++ tailWord_1133310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133310).length < 2 ^ (prefixWord ++ tailWord_1133310).sum := by decide
  have hdescent : baseEnd_1133310 < baseStart_1133310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133349 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1133349 : Nat := 118140960795 + 1133349 * 2 ^ 59
def prefixEnd_1133349 : Nat := 4983230072969 + 3 ^ 40 * 1133349 * 2
def baseEnd_1133349 : Nat := 387968524195061000350219

theorem tailTrace_1133349 : CollatzResearch.WordTrace tailWord_1133349 prefixEnd_1133349 387968524195061000350219 := by
  unfold tailWord_1133349
  simp only [CollatzResearch.WordTrace]
  refine ⟨41336633971077608444163101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27557755980718405629442067 41336633971077608444163101)
  ·
    refine ⟨15501237739154103166561163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41336633971077608444163101 15501237739154103166561163)
    ·
      refine ⟨23251856608731154749841745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15501237739154103166561163 23251856608731154749841745)
      ·
        refine ⟨17438892456548366062381309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23251856608731154749841745 17438892456548366062381309)
        ·
          refine ⟨6539584671205637273392991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17438892456548366062381309 6539584671205637273392991)
          ·
            refine ⟨9809377006808455910089487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6539584671205637273392991 9809377006808455910089487)
            ·
              refine ⟨14714065510212683865134231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9809377006808455910089487 14714065510212683865134231)
              ·
                refine ⟨22071098265319025797701347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14714065510212683865134231 22071098265319025797701347)
                ·
                  refine ⟨33106647397978538696552021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22071098265319025797701347 33106647397978538696552021)
                  ·
                    refine ⟨387968524195061000350219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33106647397978538696552021 387968524195061000350219)
                    ·
                      rfl

theorem cell22_1133349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1133349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133349 prefixEnd_1133349 := by exact prefixLift 1133349
  have htrace : WordTrace (prefixWord ++ tailWord_1133349) baseStart_1133349 baseEnd_1133349 := by
    simpa [prefixWord, tailWord_1133349, baseEnd_1133349] using wordTrace_append hprefix tailTrace_1133349
  have hstable : (prefixWord ++ tailWord_1133349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133349).length < 2 ^ (prefixWord ++ tailWord_1133349).sum := by decide
  have hdescent : baseEnd_1133349 < baseStart_1133349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133379 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_1133379 : Nat := 118140960795 + 1133379 * 2 ^ 59
def prefixEnd_1133379 : Nat := 4983230072969 + 3 ^ 40 * 1133379 * 2
def baseEnd_1133379 : Nat := 387978793808150922100127

theorem tailTrace_1133379 : CollatzResearch.WordTrace tailWord_1133379 prefixEnd_1133379 387978793808150922100127 := by
  unfold tailWord_1133379
  simp only [CollatzResearch.WordTrace]
  refine ⟨41337728160968923567755191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27558485440645949045170127 41337728160968923567755191)
  ·
    refine ⟨62006592241453385351632787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41337728160968923567755191 62006592241453385351632787)
    ·
      refine ⟨93009888362180078027449181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62006592241453385351632787 93009888362180078027449181)
      ·
        refine ⟨34878708135817529260293443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93009888362180078027449181 34878708135817529260293443)
        ·
          refine ⟨52318062203726293890440165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34878708135817529260293443 52318062203726293890440165)
          ·
            refine ⟨9809636663198680104457531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52318062203726293890440165 9809636663198680104457531)
            ·
              refine ⟨14714454994798020156686297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9809636663198680104457531 14714454994798020156686297)
              ·
                refine ⟨11035841246098515117514723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14714454994798020156686297 11035841246098515117514723)
                ·
                  refine ⟨16553761869147772676272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11035841246098515117514723 16553761869147772676272085)
                  ·
                    refine ⟨387978793808150922100127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16553761869147772676272085 387978793808150922100127)
                    ·
                      rfl

theorem cell22_1133379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_1133379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133379 prefixEnd_1133379 := by exact prefixLift 1133379
  have htrace : WordTrace (prefixWord ++ tailWord_1133379) baseStart_1133379 baseEnd_1133379 := by
    simpa [prefixWord, tailWord_1133379, baseEnd_1133379] using wordTrace_append hprefix tailTrace_1133379
  have hstable : (prefixWord ++ tailWord_1133379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133379).length < 2 ^ (prefixWord ++ tailWord_1133379).sum := by decide
  have hdescent : baseEnd_1133379 < baseStart_1133379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133385 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 1, 3]
def baseStart_1133385 : Nat := 118140960795 + 1133385 * 2 ^ 59
def prefixEnd_1133385 : Nat := 4983230072969 + 3 ^ 40 * 1133385 * 2
def baseEnd_1133385 : Nat := 387980847730768906450109

theorem tailTrace_1133385 : CollatzResearch.WordTrace tailWord_1133385 prefixEnd_1133385 387980847730768906450109 := by
  unfold tailWord_1133385
  simp only [CollatzResearch.WordTrace]
  refine ⟨41337946998947186592473609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27558631332631457728315739 41337946998947186592473609)
  ·
    refine ⟨31003460249210389944355207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41337946998947186592473609 31003460249210389944355207)
    ·
      refine ⟨46505190373815584916532811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31003460249210389944355207 46505190373815584916532811)
      ·
        refine ⟨69757785560723377374799217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46505190373815584916532811 69757785560723377374799217)
        ·
          refine ⟨52318339170542533031099413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69757785560723377374799217 52318339170542533031099413)
          ·
            refine ⟨2452422148619181235832785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52318339170542533031099413 2452422148619181235832785)
            ·
              refine ⟨1839316611464385926874589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452422148619181235832785 1839316611464385926874589)
              ·
                refine ⟨689743729299144722577971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1839316611464385926874589 689743729299144722577971)
                ·
                  refine ⟨1034615593948717083866957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689743729299144722577971 1034615593948717083866957)
                  ·
                    refine ⟨387980847730768906450109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034615593948717083866957 387980847730768906450109)
                    ·
                      rfl

theorem cell22_1133385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_1133385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133385 prefixEnd_1133385 := by exact prefixLift 1133385
  have htrace : WordTrace (prefixWord ++ tailWord_1133385) baseStart_1133385 baseEnd_1133385 := by
    simpa [prefixWord, tailWord_1133385, baseEnd_1133385] using wordTrace_append hprefix tailTrace_1133385
  have hstable : (prefixWord ++ tailWord_1133385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133385).length < 2 ^ (prefixWord ++ tailWord_1133385).sum := by decide
  have hdescent : baseEnd_1133385 < baseStart_1133385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133426 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1133426 : Nat := 118140960795 + 1133426 * 2 ^ 59
def prefixEnd_1133426 : Nat := 4983230072969 + 3 ^ 40 * 1133426 * 2
def baseEnd_1133426 : Nat := 129331627622886155391661

theorem tailTrace_1133426 : CollatzResearch.WordTrace tailWord_1133426 prefixEnd_1133426 129331627622886155391661 := by
  unfold tailWord_1133426
  simp only [CollatzResearch.WordTrace]
  refine ⟨10334860597949662648679033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27559628261199100396477421 10334860597949662648679033)
  ·
    refine ⟨7751145448462246986509275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10334860597949662648679033 7751145448462246986509275)
    ·
      refine ⟨11626718172693370479763913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7751145448462246986509275 11626718172693370479763913)
      ·
        refine ⟨8720038629520027859822935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11626718172693370479763913 8720038629520027859822935)
        ·
          refine ⟨13080057944280041789734403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8720038629520027859822935 13080057944280041789734403)
          ·
            refine ⟨19620086916420062684601605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13080057944280041789734403 19620086916420062684601605)
            ·
              refine ⟨3678766296828761753362801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19620086916420062684601605 3678766296828761753362801)
              ·
                refine ⟨2759074722621571315022101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3678766296828761753362801 2759074722621571315022101)
                ·
                  refine ⟨129331627622886155391661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2759074722621571315022101 129331627622886155391661)
                  ·
                    rfl

theorem cell22_1133426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1133426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133426 prefixEnd_1133426 := by exact prefixLift 1133426
  have htrace : WordTrace (prefixWord ++ tailWord_1133426) baseStart_1133426 baseEnd_1133426 := by
    simpa [prefixWord, tailWord_1133426, baseEnd_1133426] using wordTrace_append hprefix tailTrace_1133426
  have hstable : (prefixWord ++ tailWord_1133426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133426).length < 2 ^ (prefixWord ++ tailWord_1133426).sum := by decide
  have hdescent : baseEnd_1133426 < baseStart_1133426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133471 : List Nat := [1, 1, 2, 5, 2, 1, 1, 9]
def baseStart_1133471 : Nat := 118140960795 + 1133471 * 2 ^ 59
def prefixEnd_1133471 : Nat := 4983230072969 + 3 ^ 40 * 1133471 * 2
def baseEnd_1133471 : Nat := 43112254143143705422205

theorem tailTrace_1133471 : CollatzResearch.WordTrace tailWord_1133471 prefixEnd_1133471 43112254143143705422205 := by
  unfold tailWord_1133471
  simp only [CollatzResearch.WordTrace]
  refine ⟨41341083676635623280104267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27560722451090415520069511 41341083676635623280104267)
  ·
    refine ⟨62011625514953434920156401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41341083676635623280104267 62011625514953434920156401)
    ·
      refine ⟨46508719136215076190117301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62011625514953434920156401 46508719136215076190117301)
      ·
        refine ⟨4360192419020163392823497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46508719136215076190117301 4360192419020163392823497)
        ·
          refine ⟨3270144314265122544617623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360192419020163392823497 3270144314265122544617623)
          ·
            refine ⟨4905216471397683816926435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270144314265122544617623 4905216471397683816926435)
            ·
              refine ⟨7357824707096525725389653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905216471397683816926435 7357824707096525725389653)
              ·
                refine ⟨43112254143143705422205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7357824707096525725389653 43112254143143705422205)
                ·
                  rfl

theorem cell22_1133471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 9].length) (baseStart_1133471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133471 prefixEnd_1133471 := by exact prefixLift 1133471
  have htrace : WordTrace (prefixWord ++ tailWord_1133471) baseStart_1133471 baseEnd_1133471 := by
    simpa [prefixWord, tailWord_1133471, baseEnd_1133471] using wordTrace_append hprefix tailTrace_1133471
  have hstable : (prefixWord ++ tailWord_1133471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133471).length < 2 ^ (prefixWord ++ tailWord_1133471).sum := by decide
  have hdescent : baseEnd_1133471 < baseStart_1133471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133475 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 2, 3]
def baseStart_1133475 : Nat := 118140960795 + 1133475 * 2 ^ 59
def prefixEnd_1133475 : Nat := 4983230072969 + 3 ^ 40 * 1133475 * 2
def baseEnd_1133475 : Nat := 388011656570038671699833

theorem tailTrace_1133475 : CollatzResearch.WordTrace tailWord_1133475 prefixEnd_1133475 388011656570038671699833 := by
  unfold tailWord_1133475
  simp only [CollatzResearch.WordTrace]
  refine ⟨41341229568621131963249879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27560819712414087975499919 41341229568621131963249879)
  ·
    refine ⟨62011844352931697944874819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41341229568621131963249879 62011844352931697944874819)
    ·
      refine ⟨93017766529397546917312229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62011844352931697944874819 93017766529397546917312229)
      ·
        refine ⟨17440831224262040046996043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93017766529397546917312229 17440831224262040046996043)
        ·
          refine ⟨26161246836393060070494065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17440831224262040046996043 26161246836393060070494065)
          ·
            refine ⟨19620935127294795052870549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26161246836393060070494065 19620935127294795052870549)
            ·
              refine ⟨919731334091943518103307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19620935127294795052870549 919731334091943518103307)
              ·
                refine ⟨1379597001137915277154961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919731334091943518103307 1379597001137915277154961)
                ·
                  refine ⟨1034697750853436457866221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379597001137915277154961 1034697750853436457866221)
                  ·
                    refine ⟨388011656570038671699833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034697750853436457866221 388011656570038671699833)
                    ·
                      rfl

theorem cell22_1133475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 3].length) (baseStart_1133475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133475 prefixEnd_1133475 := by exact prefixLift 1133475
  have htrace : WordTrace (prefixWord ++ tailWord_1133475) baseStart_1133475 baseEnd_1133475 := by
    simpa [prefixWord, tailWord_1133475, baseEnd_1133475] using wordTrace_append hprefix tailTrace_1133475
  have hstable : (prefixWord ++ tailWord_1133475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133475).length < 2 ^ (prefixWord ++ tailWord_1133475).sum := by decide
  have hdescent : baseEnd_1133475 < baseStart_1133475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133561 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 8]
def baseStart_1133561 : Nat := 118140960795 + 1133561 * 2 ^ 59
def prefixEnd_1133561 : Nat := 4983230072969 + 3 ^ 40 * 1133561 * 2
def baseEnd_1133561 : Nat := 129347032042521038016523

theorem tailTrace_1133561 : CollatzResearch.WordTrace tailWord_1133561 prefixEnd_1133561 129347032042521038016523 := by
  unfold tailWord_1133561
  simp only [CollatzResearch.WordTrace]
  refine ⟨41344366246309568650880537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27562910830873045767253691 41344366246309568650880537)
  ·
    refine ⟨31008274684732176488160403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41344366246309568650880537 31008274684732176488160403)
    ·
      refine ⟨46512412027098264732240605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31008274684732176488160403 46512412027098264732240605)
      ·
        refine ⟨17442154510161849274590227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46512412027098264732240605 17442154510161849274590227)
        ·
          refine ⟨26163231765242773911885341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17442154510161849274590227 26163231765242773911885341)
          ·
            refine ⟨9811211911966040216957003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26163231765242773911885341 9811211911966040216957003)
            ·
              refine ⟨14716817867949060325435505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811211911966040216957003 14716817867949060325435505)
              ·
                refine ⟨11037613400961795244076629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14716817867949060325435505 11037613400961795244076629)
                ·
                  refine ⟨129347032042521038016523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11037613400961795244076629 129347032042521038016523)
                  ·
                    rfl

theorem cell22_1133561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_1133561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133561 prefixEnd_1133561 := by exact prefixLift 1133561
  have htrace : WordTrace (prefixWord ++ tailWord_1133561) baseStart_1133561 baseEnd_1133561 := by
    simpa [prefixWord, tailWord_1133561, baseEnd_1133561] using wordTrace_append hprefix tailTrace_1133561
  have hstable : (prefixWord ++ tailWord_1133561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133561).length < 2 ^ (prefixWord ++ tailWord_1133561).sum := by decide
  have hdescent : baseEnd_1133561 < baseStart_1133561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133578 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_1133578 : Nat := 118140960795 + 1133578 * 2 ^ 59
def prefixEnd_1133578 : Nat := 4983230072969 + 3 ^ 40 * 1133578 * 2
def baseEnd_1133578 : Nat := 129348971858326912124839

theorem tailTrace_1133578 : CollatzResearch.WordTrace tailWord_1133578 prefixEnd_1133578 129348971858326912124839 := by
  unfold tailWord_1133578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336246571811995138562347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27563324191498653702832925 10336246571811995138562347)
  ·
    refine ⟨15504369857717992707843521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10336246571811995138562347 15504369857717992707843521)
    ·
      refine ⟨11628277393288494530882641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15504369857717992707843521 11628277393288494530882641)
      ·
        refine ⟨8721208044966370898161981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11628277393288494530882641 8721208044966370898161981)
        ·
          refine ⟨3270453016862389086810743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8721208044966370898161981 3270453016862389086810743)
          ·
            refine ⟨4905679525293583630216115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270453016862389086810743 4905679525293583630216115)
            ·
              refine ⟨7358519287940375445324173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905679525293583630216115 7358519287940375445324173)
              ·
                refine ⟨2759444732977640791996565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7358519287940375445324173 2759444732977640791996565)
                ·
                  refine ⟨129348971858326912124839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2759444732977640791996565 129348971858326912124839)
                  ·
                    rfl

theorem cell22_1133578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_1133578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133578 prefixEnd_1133578 := by exact prefixLift 1133578
  have htrace : WordTrace (prefixWord ++ tailWord_1133578) baseStart_1133578 baseEnd_1133578 := by
    simpa [prefixWord, tailWord_1133578, baseEnd_1133578] using wordTrace_append hprefix tailTrace_1133578
  have hstable : (prefixWord ++ tailWord_1133578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133578).length < 2 ^ (prefixWord ++ tailWord_1133578).sum := by decide
  have hdescent : baseEnd_1133578 < baseStart_1133578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133593 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_1133593 : Nat := 118140960795 + 1133593 * 2 ^ 59
def prefixEnd_1133593 : Nat := 4983230072969 + 3 ^ 40 * 1133593 * 2
def baseEnd_1133593 : Nat := 388052050381525697249471

theorem tailTrace_1133593 : CollatzResearch.WordTrace tailWord_1133593 prefixEnd_1133593 388052050381525697249471 := by
  unfold tailWord_1133593
  simp only [CollatzResearch.WordTrace]
  refine ⟨41345533382193638116045433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27563688921462425410696955 41345533382193638116045433)
  ·
    refine ⟨31009150036645228587034075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41345533382193638116045433 31009150036645228587034075)
    ·
      refine ⟨46513725054967842880551113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31009150036645228587034075 46513725054967842880551113)
      ·
        refine ⟨34885293791225882160413335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46513725054967842880551113 34885293791225882160413335)
        ·
          refine ⟨52327940686838823240620003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34885293791225882160413335 52327940686838823240620003)
          ·
            refine ⟨78491911030258234860930005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52327940686838823240620003 78491911030258234860930005)
            ·
              refine ⟨1839654164771677379553047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78491911030258234860930005 1839654164771677379553047)
              ·
                refine ⟨2759481247157516069329571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839654164771677379553047 2759481247157516069329571)
                ·
                  refine ⟨4139221870736274103994357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759481247157516069329571 4139221870736274103994357)
                  ·
                    refine ⟨388052050381525697249471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4139221870736274103994357 388052050381525697249471)
                    ·
                      rfl

theorem cell22_1133593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_1133593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133593 prefixEnd_1133593 := by exact prefixLift 1133593
  have htrace : WordTrace (prefixWord ++ tailWord_1133593) baseStart_1133593 baseEnd_1133593 := by
    simpa [prefixWord, tailWord_1133593, baseEnd_1133593] using wordTrace_append hprefix tailTrace_1133593
  have hstable : (prefixWord ++ tailWord_1133593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133593).length < 2 ^ (prefixWord ++ tailWord_1133593).sum := by decide
  have hdescent : baseEnd_1133593 < baseStart_1133593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133597 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1133597 : Nat := 118140960795 + 1133597 * 2 ^ 59
def prefixEnd_1133597 : Nat := 4983230072969 + 3 ^ 40 * 1133597 * 2
def baseEnd_1133597 : Nat := 388053419663271020149459

theorem tailTrace_1133597 : CollatzResearch.WordTrace tailWord_1133597 prefixEnd_1133597 388053419663271020149459 := by
  unfold tailWord_1133597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41345679274179146799191045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27563786182786097866127363 41345679274179146799191045)
  ·
    refine ⟨7752314863908590024848321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41345679274179146799191045 7752314863908590024848321)
    ·
      refine ⟨5814236147931442518636241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7752314863908590024848321 5814236147931442518636241)
      ·
        refine ⟨4360677110948581888977181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5814236147931442518636241 4360677110948581888977181)
        ·
          refine ⟨1635253916605718208366443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4360677110948581888977181 1635253916605718208366443)
          ·
            refine ⟨2452880874908577312549665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635253916605718208366443 2452880874908577312549665)
            ·
              refine ⟨1839660656181432984412249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452880874908577312549665 1839660656181432984412249)
              ·
                refine ⟨1379745492136074738309187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839660656181432984412249 1379745492136074738309187)
                ·
                  refine ⟨2069618238204112107463781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379745492136074738309187 2069618238204112107463781)
                  ·
                    refine ⟨388053419663271020149459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069618238204112107463781 388053419663271020149459)
                    ·
                      rfl

theorem cell22_1133597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1133597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133597 prefixEnd_1133597 := by exact prefixLift 1133597
  have htrace : WordTrace (prefixWord ++ tailWord_1133597) baseStart_1133597 baseEnd_1133597 := by
    simpa [prefixWord, tailWord_1133597, baseEnd_1133597] using wordTrace_append hprefix tailTrace_1133597
  have hstable : (prefixWord ++ tailWord_1133597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133597).length < 2 ^ (prefixWord ++ tailWord_1133597).sum := by decide
  have hdescent : baseEnd_1133597 < baseStart_1133597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133625 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_1133625 : Nat := 118140960795 + 1133625 * 2 ^ 59
def prefixEnd_1133625 : Nat := 4983230072969 + 3 ^ 40 * 1133625 * 2
def baseEnd_1133625 : Nat := 388063004635488280449373

theorem tailTrace_1133625 : CollatzResearch.WordTrace tailWord_1133625 prefixEnd_1133625 388063004635488280449373 := by
  unfold tailWord_1133625
  simp only [CollatzResearch.WordTrace]
  refine ⟨41346700518077707581210329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27564467012051805054140219 41346700518077707581210329)
  ·
    refine ⟨31010025388558280685907747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41346700518077707581210329 31010025388558280685907747)
    ·
      refine ⟨46515038082837421028861621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31010025388558280685907747 46515038082837421028861621)
      ·
        refine ⟨4360784820266008221455777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46515038082837421028861621 4360784820266008221455777)
        ·
          refine ⟨3270588615199506166091833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360784820266008221455777 3270588615199506166091833)
          ·
            refine ⟨2452941461399629624568875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270588615199506166091833 2452941461399629624568875)
            ·
              refine ⟨3679412192099444436853313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452941461399629624568875 3679412192099444436853313)
              ·
                refine ⟨2759559144074583327639985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679412192099444436853313 2759559144074583327639985)
                ·
                  refine ⟨2069669358055937495729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759559144074583327639985 2069669358055937495729989)
                  ·
                    refine ⟨388063004635488280449373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069669358055937495729989 388063004635488280449373)
                    ·
                      rfl

theorem cell22_1133625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_1133625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133625 prefixEnd_1133625 := by exact prefixLift 1133625
  have htrace : WordTrace (prefixWord ++ tailWord_1133625) baseStart_1133625 baseEnd_1133625 := by
    simpa [prefixWord, tailWord_1133625, baseEnd_1133625] using wordTrace_append hprefix tailTrace_1133625
  have hstable : (prefixWord ++ tailWord_1133625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133625).length < 2 ^ (prefixWord ++ tailWord_1133625).sum := by decide
  have hdescent : baseEnd_1133625 < baseStart_1133625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133689 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 1, 3]
def baseStart_1133689 : Nat := 118140960795 + 1133689 * 2 ^ 59
def prefixEnd_1133689 : Nat := 4983230072969 + 3 ^ 40 * 1133689 * 2
def baseEnd_1133689 : Nat := 388084913143413446849177

theorem tailTrace_1133689 : CollatzResearch.WordTrace tailWord_1133689 prefixEnd_1133689 388084913143413446849177 := by
  unfold tailWord_1133689
  simp only [CollatzResearch.WordTrace]
  refine ⟨41349034789845846511540121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27566023193230564341026747 41349034789845846511540121)
  ·
    refine ⟨31011776092384384883655091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41349034789845846511540121 31011776092384384883655091)
    ·
      refine ⟨46517664138576577325482637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31011776092384384883655091 46517664138576577325482637)
      ·
        refine ⟨17444124051966216497055989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46517664138576577325482637 17444124051966216497055989)
        ·
          refine ⟨1635386629871832796598999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17444124051966216497055989 1635386629871832796598999)
          ·
            refine ⟨2453079944807749194898499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635386629871832796598999 2453079944807749194898499)
            ·
              refine ⟨3679619917211623792347749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453079944807749194898499 3679619917211623792347749)
              ·
                refine ⟨689928734477179461065203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3679619917211623792347749 689928734477179461065203)
                ·
                  refine ⟨1034893101715769191597805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689928734477179461065203 1034893101715769191597805)
                  ·
                    refine ⟨388084913143413446849177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034893101715769191597805 388084913143413446849177)
                    ·
                      rfl

theorem cell22_1133689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_1133689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133689 prefixEnd_1133689 := by exact prefixLift 1133689
  have htrace : WordTrace (prefixWord ++ tailWord_1133689) baseStart_1133689 baseEnd_1133689 := by
    simpa [prefixWord, tailWord_1133689, baseEnd_1133689] using wordTrace_append hprefix tailTrace_1133689
  have hstable : (prefixWord ++ tailWord_1133689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133689).length < 2 ^ (prefixWord ++ tailWord_1133689).sum := by decide
  have hdescent : baseEnd_1133689 < baseStart_1133689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133700 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1133700 : Nat := 118140960795 + 1133700 * 2 ^ 59
def prefixEnd_1133700 : Nat := 4983230072969 + 3 ^ 40 * 1133700 * 2
def baseEnd_1133700 : Nat := 388088678668213084824143

theorem tailTrace_1133700 : CollatzResearch.WordTrace tailWord_1133700 prefixEnd_1133700 388088678668213084824143 := by
  unfold tailWord_1133700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674717996402997695095277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27566290661870663593460369 20674717996402997695095277)
  ·
    refine ⟨7753019248651124135660729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20674717996402997695095277 7753019248651124135660729)
    ·
      refine ⟨5814764436488343101745547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7753019248651124135660729 5814764436488343101745547)
      ·
        refine ⟨8722146654732514652618321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814764436488343101745547 8722146654732514652618321)
        ·
          refine ⟨6541609991049385989463741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8722146654732514652618321 6541609991049385989463741)
          ·
            refine ⟨2453103746643519746048903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6541609991049385989463741 2453103746643519746048903)
            ·
              refine ⟨3679655619965279619073355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453103746643519746048903 3679655619965279619073355)
              ·
                refine ⟨5519483429947919428610033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679655619965279619073355 5519483429947919428610033)
                ·
                  refine ⟨4139612572460939571457525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519483429947919428610033 4139612572460939571457525)
                  ·
                    refine ⟨388088678668213084824143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4139612572460939571457525 388088678668213084824143)
                    ·
                      rfl

theorem cell22_1133700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1133700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133700 prefixEnd_1133700 := by exact prefixLift 1133700
  have htrace : WordTrace (prefixWord ++ tailWord_1133700) baseStart_1133700 baseEnd_1133700 := by
    simpa [prefixWord, tailWord_1133700, baseEnd_1133700] using wordTrace_append hprefix tailTrace_1133700
  have hstable : (prefixWord ++ tailWord_1133700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133700).length < 2 ^ (prefixWord ++ tailWord_1133700).sum := by decide
  have hdescent : baseEnd_1133700 < baseStart_1133700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133732 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1133732 : Nat := 118140960795 + 1133732 * 2 ^ 59
def prefixEnd_1133732 : Nat := 4983230072969 + 3 ^ 40 * 1133732 * 2
def baseEnd_1133732 : Nat := 388099632922175668024045

theorem tailTrace_1133732 : CollatzResearch.WordTrace tailWord_1133732 prefixEnd_1133732 388099632922175668024045 := by
  unfold tailWord_1133732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20675301564345032427677725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27567068752460043236903633 20675301564345032427677725)
  ·
    refine ⟨7753238086629387160379147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20675301564345032427677725 7753238086629387160379147)
    ·
      refine ⟨11629857129944080740568721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7753238086629387160379147 11629857129944080740568721)
      ·
        refine ⟨8722392847458060555426541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11629857129944080740568721 8722392847458060555426541)
        ·
          refine ⟨3270897317796772708284953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8722392847458060555426541 3270897317796772708284953)
          ·
            refine ⟨2453172988347579531213715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270897317796772708284953 2453172988347579531213715)
            ·
              refine ⟨3679759482521369296820573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453172988347579531213715 3679759482521369296820573)
              ·
                refine ⟨1379909805945513486307715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3679759482521369296820573 1379909805945513486307715)
                ·
                  refine ⟨2069864708918270229461573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379909805945513486307715 2069864708918270229461573)
                  ·
                    refine ⟨388099632922175668024045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069864708918270229461573 388099632922175668024045)
                    ·
                      rfl

theorem cell22_1133732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1133732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133732 prefixEnd_1133732 := by exact prefixLift 1133732
  have htrace : WordTrace (prefixWord ++ tailWord_1133732) baseStart_1133732 baseEnd_1133732 := by
    simpa [prefixWord, tailWord_1133732, baseEnd_1133732] using wordTrace_append hprefix tailTrace_1133732
  have hstable : (prefixWord ++ tailWord_1133732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133732).length < 2 ^ (prefixWord ++ tailWord_1133732).sum := by decide
  have hdescent : baseEnd_1133732 < baseStart_1133732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133869 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1133869 : Nat := 118140960795 + 1133869 * 2 ^ 59
def prefixEnd_1133869 : Nat := 4983230072969 + 3 ^ 40 * 1133869 * 2
def baseEnd_1133869 : Nat := 388146530821952977348625

theorem tailTrace_1133869 : CollatzResearch.WordTrace tailWord_1133869 prefixEnd_1133869 388146530821952977348625 := by
  unfold tailWord_1133869
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355599929193737253092661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27570399952795824835395107 41355599929193737253092661)
  ·
    refine ⟨3877087493361912867477437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41355599929193737253092661 3877087493361912867477437)
    ·
      refine ⟨1453907810010717325304039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3877087493361912867477437 1453907810010717325304039)
      ·
        refine ⟨2180861715016075987956059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453907810010717325304039 2180861715016075987956059)
        ·
          refine ⟨3271292572524113981934089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180861715016075987956059 3271292572524113981934089)
          ·
            refine ⟨2453469429393085486450567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271292572524113981934089 2453469429393085486450567)
            ·
              refine ⟨3680204144089628229675851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453469429393085486450567 3680204144089628229675851)
              ·
                refine ⟨5520306216134442344513777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680204144089628229675851 5520306216134442344513777)
                ·
                  refine ⟨4140229662100831758385333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520306216134442344513777 4140229662100831758385333)
                  ·
                    refine ⟨388146530821952977348625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4140229662100831758385333 388146530821952977348625)
                    ·
                      rfl

theorem cell22_1133869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1133869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133869 prefixEnd_1133869 := by exact prefixLift 1133869
  have htrace : WordTrace (prefixWord ++ tailWord_1133869) baseStart_1133869 baseEnd_1133869 := by
    simpa [prefixWord, tailWord_1133869, baseEnd_1133869] using wordTrace_append hprefix tailTrace_1133869
  have hstable : (prefixWord ++ tailWord_1133869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133869).length < 2 ^ (prefixWord ++ tailWord_1133869).sum := by decide
  have hdescent : baseEnd_1133869 < baseStart_1133869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133914 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_1133914 : Nat := 118140960795 + 1133914 * 2 ^ 59
def prefixEnd_1133914 : Nat := 4983230072969 + 3 ^ 40 * 1133914 * 2
def baseEnd_1133914 : Nat := 388161935241587859973487

theorem tailTrace_1133914 : CollatzResearch.WordTrace tailWord_1133914 prefixEnd_1133914 388161935241587859973487 := by
  unfold tailWord_1133914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339310303507677484620199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27571494142687139958987197 10339310303507677484620199)
  ·
    refine ⟨15508965455261516226930299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10339310303507677484620199 15508965455261516226930299)
    ·
      refine ⟨23263448182892274340395449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15508965455261516226930299 23263448182892274340395449)
      ·
        refine ⟨17447586137169205755296587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23263448182892274340395449 17447586137169205755296587)
        ·
          refine ⟨26171379205753808632944881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17447586137169205755296587 26171379205753808632944881)
          ·
            refine ⟨19628534404315356474708661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26171379205753808632944881 19628534404315356474708661)
            ·
              refine ⟨1840175100404564669503937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19628534404315356474708661 1840175100404564669503937)
              ·
                refine ⟨1380131325303423502127953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840175100404564669503937 1380131325303423502127953)
                ·
                  refine ⟨1035098493977567626595965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380131325303423502127953 1035098493977567626595965)
                  ·
                    refine ⟨388161935241587859973487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035098493977567626595965 388161935241587859973487)
                    ·
                      rfl

theorem cell22_1133914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_1133914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133914 prefixEnd_1133914 := by exact prefixLift 1133914
  have htrace : WordTrace (prefixWord ++ tailWord_1133914) baseStart_1133914 baseEnd_1133914 := by
    simpa [prefixWord, tailWord_1133914, baseEnd_1133914] using wordTrace_append hprefix tailTrace_1133914
  have hstable : (prefixWord ++ tailWord_1133914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133914).length < 2 ^ (prefixWord ++ tailWord_1133914).sum := by decide
  have hdescent : baseEnd_1133914 < baseStart_1133914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133950 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1133950 : Nat := 118140960795 + 1133950 * 2 ^ 59
def prefixEnd_1133950 : Nat := 4983230072969 + 3 ^ 40 * 1133950 * 2
def baseEnd_1133950 : Nat := 129391419592431922024459

theorem tailTrace_1133950 : CollatzResearch.WordTrace tailWord_1133950 prefixEnd_1133950 129391419592431922024459 := by
  unfold tailWord_1133950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169819280237536010848913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27572369494600192057860869 5169819280237536010848913)
  ·
    refine ⟨3877364460178152008136685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5169819280237536010848913 3877364460178152008136685)
    ·
      refine ⟨1454011672566807003051257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3877364460178152008136685 1454011672566807003051257)
      ·
        refine ⟨1090508754425105252288443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1454011672566807003051257 1090508754425105252288443)
        ·
          refine ⟨1635763131637657878432665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090508754425105252288443 1635763131637657878432665)
          ·
            refine ⟨1226822348728243408824499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635763131637657878432665 1226822348728243408824499)
            ·
              refine ⟨1840233523092365113236749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226822348728243408824499 1840233523092365113236749)
              ·
                refine ⟨690087571159636917463781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1840233523092365113236749 690087571159636917463781)
                ·
                  refine ⟨129391419592431922024459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690087571159636917463781 129391419592431922024459)
                  ·
                    rfl

theorem cell22_1133950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1133950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133950 prefixEnd_1133950 := by exact prefixLift 1133950
  have htrace : WordTrace (prefixWord ++ tailWord_1133950) baseStart_1133950 baseEnd_1133950 := by
    simpa [prefixWord, tailWord_1133950, baseEnd_1133950] using wordTrace_append hprefix tailTrace_1133950
  have hstable : (prefixWord ++ tailWord_1133950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133950).length < 2 ^ (prefixWord ++ tailWord_1133950).sum := by decide
  have hdescent : baseEnd_1133950 < baseStart_1133950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133982 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1133982 : Nat := 118140960795 + 1133982 * 2 ^ 59
def prefixEnd_1133982 : Nat := 4983230072969 + 3 ^ 40 * 1133982 * 2
def baseEnd_1133982 : Nat := 388185213031258349273279

theorem tailTrace_1133982 : CollatzResearch.WordTrace tailWord_1133982 prefixEnd_1133982 388185213031258349273279 := by
  unfold tailWord_1133982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169965172223044693994525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27573147585189571701304133 5169965172223044693994525)
  ·
    refine ⟨1938736939583641760247947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5169965172223044693994525 1938736939583641760247947)
    ·
      refine ⟨2908105409375462640371921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938736939583641760247947 2908105409375462640371921)
      ·
        refine ⟨2181079057031596980278941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2908105409375462640371921 2181079057031596980278941)
        ·
          refine ⟨817904646386848867604603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2181079057031596980278941 817904646386848867604603)
          ·
            refine ⟨1226856969580273301406905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817904646386848867604603 1226856969580273301406905)
            ·
              refine ⟨920142727185204976055179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226856969580273301406905 920142727185204976055179)
              ·
                refine ⟨1380214090777807464082769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920142727185204976055179 1380214090777807464082769)
                ·
                  refine ⟨1035160568083355598062077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380214090777807464082769 1035160568083355598062077)
                  ·
                    refine ⟨388185213031258349273279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035160568083355598062077 388185213031258349273279)
                    ·
                      rfl

theorem cell22_1133982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1133982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1133982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1133982 prefixEnd_1133982 := by exact prefixLift 1133982
  have htrace : WordTrace (prefixWord ++ tailWord_1133982) baseStart_1133982 baseEnd_1133982 := by
    simpa [prefixWord, tailWord_1133982, baseEnd_1133982] using wordTrace_append hprefix tailTrace_1133982
  have hstable : (prefixWord ++ tailWord_1133982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133982).length < 2 ^ (prefixWord ++ tailWord_1133982).sum := by decide
  have hdescent : baseEnd_1133982 < baseStart_1133982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134047 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1134047 : Nat := 118140960795 + 1134047 * 2 ^ 59
def prefixEnd_1134047 : Nat := 4983230072969 + 3 ^ 40 * 1134047 * 2
def baseEnd_1134047 : Nat := 388207463859619846398079

theorem tailTrace_1134047 : CollatzResearch.WordTrace tailWord_1134047 prefixEnd_1134047 388207463859619846398079 := by
  unfold tailWord_1134047
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362092122548873653072395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27574728081699249102048263 41362092122548873653072395)
  ·
    refine ⟨62043138183823310479608593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41362092122548873653072395 62043138183823310479608593)
    ·
      refine ⟨46532353637867482859706445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62043138183823310479608593 46532353637867482859706445)
      ·
        refine ⟨17449632614200306072389917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46532353637867482859706445 17449632614200306072389917)
        ·
          refine ⟨6543612230325114777146219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17449632614200306072389917 6543612230325114777146219)
          ·
            refine ⟨9815418345487672165719329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543612230325114777146219 9815418345487672165719329)
            ·
              refine ⟨7361563759115754124289497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9815418345487672165719329 7361563759115754124289497)
              ·
                refine ⟨5521172819336815593217123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361563759115754124289497 5521172819336815593217123)
                ·
                  refine ⟨8281759229005223389825685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521172819336815593217123 8281759229005223389825685)
                  ·
                    refine ⟨388207463859619846398079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8281759229005223389825685 388207463859619846398079)
                    ·
                      rfl

theorem cell22_1134047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1134047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134047 prefixEnd_1134047 := by exact prefixLift 1134047
  have htrace : WordTrace (prefixWord ++ tailWord_1134047) baseStart_1134047 baseEnd_1134047 := by
    simpa [prefixWord, tailWord_1134047, baseEnd_1134047] using wordTrace_append hprefix tailTrace_1134047
  have hstable : (prefixWord ++ tailWord_1134047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134047).length < 2 ^ (prefixWord ++ tailWord_1134047).sum := by decide
  have hdescent : baseEnd_1134047 < baseStart_1134047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134049 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1134049 : Nat := 118140960795 + 1134049 * 2 ^ 59
def prefixEnd_1134049 : Nat := 4983230072969 + 3 ^ 40 * 1134049 * 2
def baseEnd_1134049 : Nat := 388208148500492507848073

theorem tailTrace_1134049 : CollatzResearch.WordTrace tailWord_1134049 prefixEnd_1134049 388208148500492507848073 := by
  unfold tailWord_1134049
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362165068541627994645201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27574776712361085329763467 41362165068541627994645201)
  ·
    refine ⟨31021623801406220995983901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41362165068541627994645201 31021623801406220995983901)
    ·
      refine ⟨11633108925527332873493963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31021623801406220995983901 11633108925527332873493963)
      ·
        refine ⟨17449663388290999310240945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11633108925527332873493963 17449663388290999310240945)
        ·
          refine ⟨13087247541218249482680709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17449663388290999310240945 13087247541218249482680709)
          ·
            refine ⟨2453858913978421778002633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13087247541218249482680709 2453858913978421778002633)
            ·
              refine ⟨1840394185483816333501975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453858913978421778002633 1840394185483816333501975)
              ·
                refine ⟨2760591278225724500252963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840394185483816333501975 2760591278225724500252963)
                ·
                  refine ⟨4140886917338586750379445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760591278225724500252963 4140886917338586750379445)
                  ·
                    refine ⟨388208148500492507848073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4140886917338586750379445 388208148500492507848073)
                    ·
                      rfl

theorem cell22_1134049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1134049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134049 prefixEnd_1134049 := by exact prefixLift 1134049
  have htrace : WordTrace (prefixWord ++ tailWord_1134049) baseStart_1134049 baseEnd_1134049 := by
    simpa [prefixWord, tailWord_1134049, baseEnd_1134049] using wordTrace_append hprefix tailTrace_1134049
  have hstable : (prefixWord ++ tailWord_1134049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134049).length < 2 ^ (prefixWord ++ tailWord_1134049).sum := by decide
  have hdescent : baseEnd_1134049 < baseStart_1134049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134064 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_1134064 : Nat := 118140960795 + 1134064 * 2 ^ 59
def prefixEnd_1134064 : Nat := 4983230072969 + 3 ^ 40 * 1134064 * 2
def baseEnd_1134064 : Nat := 388213283307037468723027

theorem tailTrace_1134064 : CollatzResearch.WordTrace tailWord_1134064 prefixEnd_1134064 388213283307037468723027 := by
  unfold tailWord_1134064
  simp only [CollatzResearch.WordTrace]
  refine ⟨20681356081743642778220623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27575141442324857037627497 20681356081743642778220623)
  ·
    refine ⟨31022034122615464167330935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20681356081743642778220623 31022034122615464167330935)
    ·
      refine ⟨46533051183923196250996403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31022034122615464167330935 46533051183923196250996403)
      ·
        refine ⟨69799576775884794376494605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46533051183923196250996403 69799576775884794376494605)
        ·
          refine ⟨26174841290956797891185477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69799576775884794376494605 26174841290956797891185477)
          ·
            refine ⟨4907782742054399604597277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26174841290956797891185477 4907782742054399604597277)
            ·
              refine ⟨1840418528270399851723979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4907782742054399604597277 1840418528270399851723979)
              ·
                refine ⟨2760627792405599777585969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840418528270399851723979 2760627792405599777585969)
                ·
                  refine ⟨2070470844304199833189477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760627792405599777585969 2070470844304199833189477)
                  ·
                    refine ⟨388213283307037468723027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2070470844304199833189477 388213283307037468723027)
                    ·
                      rfl

theorem cell22_1134064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_1134064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134064 prefixEnd_1134064 := by exact prefixLift 1134064
  have htrace : WordTrace (prefixWord ++ tailWord_1134064) baseStart_1134064 baseEnd_1134064 := by
    simpa [prefixWord, tailWord_1134064, baseEnd_1134064] using wordTrace_append hprefix tailTrace_1134064
  have hstable : (prefixWord ++ tailWord_1134064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134064).length < 2 ^ (prefixWord ++ tailWord_1134064).sum := by decide
  have hdescent : baseEnd_1134064 < baseStart_1134064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134100 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1134100 : Nat := 118140960795 + 1134100 * 2 ^ 59
def prefixEnd_1134100 : Nat := 4983230072969 + 3 ^ 40 * 1134100 * 2
def baseEnd_1134100 : Nat := 388225606842745374822917

theorem tailTrace_1134100 : CollatzResearch.WordTrace tailWord_1134100 prefixEnd_1134100 388225606842745374822917 := by
  unfold tailWord_1134100
  simp only [CollatzResearch.WordTrace]
  refine ⟨20682012595678431852375877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27576016794237909136501169 20682012595678431852375877)
  ·
    refine ⟨3877877361689705972320477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20682012595678431852375877 3877877361689705972320477)
    ·
      refine ⟨1454204010633639739620179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3877877361689705972320477 1454204010633639739620179)
      ·
        refine ⟨2181306015950459609430269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454204010633639739620179 2181306015950459609430269)
        ·
          refine ⟨817989755981422353536351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2181306015950459609430269 817989755981422353536351)
          ·
            refine ⟨1226984633972133530304527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817989755981422353536351 1226984633972133530304527)
            ·
              refine ⟨1840476950958200295456791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226984633972133530304527 1840476950958200295456791)
              ·
                refine ⟨2760715426437300443185187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840476950958200295456791 2760715426437300443185187)
                ·
                  refine ⟨4141073139655950664777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760715426437300443185187 4141073139655950664777781)
                  ·
                    refine ⟨388225606842745374822917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4141073139655950664777781 388225606842745374822917)
                    ·
                      rfl

theorem cell22_1134100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1134100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134100 prefixEnd_1134100 := by exact prefixLift 1134100
  have htrace : WordTrace (prefixWord ++ tailWord_1134100) baseStart_1134100 baseEnd_1134100 := by
    simpa [prefixWord, tailWord_1134100, baseEnd_1134100] using wordTrace_append hprefix tailTrace_1134100
  have hstable : (prefixWord ++ tailWord_1134100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134100).length < 2 ^ (prefixWord ++ tailWord_1134100).sum := by decide
  have hdescent : baseEnd_1134100 < baseStart_1134100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134145 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1134145 : Nat := 118140960795 + 1134145 * 2 ^ 59
def prefixEnd_1134145 : Nat := 4983230072969 + 3 ^ 40 * 1134145 * 2
def baseEnd_1134145 : Nat := 388241011262380257447779

theorem tailTrace_1134145 : CollatzResearch.WordTrace tailWord_1134145 prefixEnd_1134145 388241011262380257447779 := by
  unfold tailWord_1134145
  simp only [CollatzResearch.WordTrace]
  refine ⟨41365666476193836390139889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27577110984129224260093259 41365666476193836390139889)
  ·
    refine ⟨31024249857145377292604917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41365666476193836390139889 31024249857145377292604917)
    ·
      refine ⟨2908523424107379121181711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31024249857145377292604917 2908523424107379121181711)
      ·
        refine ⟨4362785136161068681772567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908523424107379121181711 4362785136161068681772567)
        ·
          refine ⟨6544177704241603022658851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362785136161068681772567 6544177704241603022658851)
          ·
            refine ⟨9816266556362404533988277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6544177704241603022658851 9816266556362404533988277)
            ·
              refine ⟨920274989658975425061401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9816266556362404533988277 920274989658975425061401)
              ·
                refine ⟨690206242244231568796051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920274989658975425061401 690206242244231568796051)
                ·
                  refine ⟨1035309363366347353194077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690206242244231568796051 1035309363366347353194077)
                  ·
                    refine ⟨388241011262380257447779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035309363366347353194077 388241011262380257447779)
                    ·
                      rfl

theorem cell22_1134145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1134145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134145 prefixEnd_1134145 := by exact prefixLift 1134145
  have htrace : WordTrace (prefixWord ++ tailWord_1134145) baseStart_1134145 baseEnd_1134145 := by
    simpa [prefixWord, tailWord_1134145, baseEnd_1134145] using wordTrace_append hprefix tailTrace_1134145
  have hstable : (prefixWord ++ tailWord_1134145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134145).length < 2 ^ (prefixWord ++ tailWord_1134145).sum := by decide
  have hdescent : baseEnd_1134145 < baseStart_1134145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134154 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1134154 : Nat := 118140960795 + 1134154 * 2 ^ 59
def prefixEnd_1134154 : Nat := 4983230072969 + 3 ^ 40 * 1134154 * 2
def baseEnd_1134154 : Nat := 388244092146307233972751

theorem tailTrace_1134154 : CollatzResearch.WordTrace tailWord_1134154 prefixEnd_1134154 388244092146307233972751 := by
  unfold tailWord_1134154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341498683290307731804379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27577329822107487284811677 10341498683290307731804379)
  ·
    refine ⟨15512248024935461597706569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10341498683290307731804379 15512248024935461597706569)
    ·
      refine ⟨11634186018701596198279927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15512248024935461597706569 11634186018701596198279927)
      ·
        refine ⟨17451279028052394297419891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11634186018701596198279927 17451279028052394297419891)
        ·
          refine ⟨26176918542078591446129837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17451279028052394297419891 26176918542078591446129837)
          ·
            refine ⟨9816344453279471792298689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26176918542078591446129837 9816344453279471792298689)
            ·
              refine ⟨7362258339959603844224017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9816344453279471792298689 7362258339959603844224017)
              ·
                refine ⟨5521693754969702883168013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7362258339959603844224017 5521693754969702883168013)
                ·
                  refine ⟨2070635158113638581188005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5521693754969702883168013 2070635158113638581188005)
                  ·
                    refine ⟨388244092146307233972751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2070635158113638581188005 388244092146307233972751)
                    ·
                      rfl

theorem cell22_1134154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1134154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134154 prefixEnd_1134154 := by exact prefixLift 1134154
  have htrace : WordTrace (prefixWord ++ tailWord_1134154) baseStart_1134154 baseEnd_1134154 := by
    simpa [prefixWord, tailWord_1134154, baseEnd_1134154] using wordTrace_append hprefix tailTrace_1134154
  have hstable : (prefixWord ++ tailWord_1134154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134154).length < 2 ^ (prefixWord ++ tailWord_1134154).sum := by decide
  have hdescent : baseEnd_1134154 < baseStart_1134154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134218 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_1134218 : Nat := 118140960795 + 1134218 * 2 ^ 59
def prefixEnd_1134218 : Nat := 4983230072969 + 3 ^ 40 * 1134218 * 2
def baseEnd_1134218 : Nat := 388266000654232400372555

theorem tailTrace_1134218 : CollatzResearch.WordTrace tailWord_1134218 prefixEnd_1134218 388266000654232400372555 := by
  unfold tailWord_1134218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342082251232342464386827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27578886003286246571698205 10342082251232342464386827)
  ·
    refine ⟨15513123376848513696580241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10342082251232342464386827 15513123376848513696580241)
    ·
      refine ⟨11634842532636385272435181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15513123376848513696580241 11634842532636385272435181)
      ·
        refine ⟨4363065949738644477163193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11634842532636385272435181 4363065949738644477163193)
        ·
          refine ⟨3272299462303983357872395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363065949738644477163193 3272299462303983357872395)
          ·
            refine ⟨4908449193455975036808593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272299462303983357872395 4908449193455975036808593)
            ·
              refine ⟨3681336895091981277606445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4908449193455975036808593 3681336895091981277606445)
              ·
                refine ⟨1380501335659492979102417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3681336895091981277606445 1380501335659492979102417)
                ·
                  refine ⟨1035376001744619734326813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380501335659492979102417 1035376001744619734326813)
                  ·
                    refine ⟨388266000654232400372555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035376001744619734326813 388266000654232400372555)
                    ·
                      rfl

theorem cell22_1134218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_1134218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134218 prefixEnd_1134218 := by exact prefixLift 1134218
  have htrace : WordTrace (prefixWord ++ tailWord_1134218) baseStart_1134218 baseEnd_1134218 := by
    simpa [prefixWord, tailWord_1134218, baseEnd_1134218] using wordTrace_append hprefix tailTrace_1134218
  have hstable : (prefixWord ++ tailWord_1134218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134218).length < 2 ^ (prefixWord ++ tailWord_1134218).sum := by decide
  have hdescent : baseEnd_1134218 < baseStart_1134218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134231 : List Nat := [1, 1, 3, 3, 2, 3, 3, 6]
def baseStart_1134231 : Nat := 118140960795 + 1134231 * 2 ^ 59
def prefixEnd_1134231 : Nat := 4983230072969 + 3 ^ 40 * 1134231 * 2
def baseEnd_1134231 : Nat := 43141161202211633310835

theorem tailTrace_1134231 : CollatzResearch.WordTrace tailWord_1134231 prefixEnd_1134231 43141161202211633310835 := by
  unfold tailWord_1134231
  simp only [CollatzResearch.WordTrace]
  refine ⟨41368803153882273077770547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27579202102588182051847031 41368803153882273077770547)
  ·
    refine ⟨62053204730823409616655821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41368803153882273077770547 62053204730823409616655821)
    ·
      refine ⟨23269951774058778606245933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62053204730823409616655821 23269951774058778606245933)
      ·
        refine ⟨8726231915272041977342225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23269951774058778606245933 8726231915272041977342225)
        ·
          refine ⟨6544673936454031483006669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8726231915272041977342225 6544673936454031483006669)
          ·
            refine ⟨2454252726170261806127501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6544673936454031483006669 2454252726170261806127501)
            ·
              refine ⟨920344772313848177297813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2454252726170261806127501 920344772313848177297813)
              ·
                refine ⟨43141161202211633310835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 920344772313848177297813 43141161202211633310835)
                ·
                  rfl

theorem cell22_1134231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 6].length) (baseStart_1134231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134231 prefixEnd_1134231 := by exact prefixLift 1134231
  have htrace : WordTrace (prefixWord ++ tailWord_1134231) baseStart_1134231 baseEnd_1134231 := by
    simpa [prefixWord, tailWord_1134231, baseEnd_1134231] using wordTrace_append hprefix tailTrace_1134231
  have hstable : (prefixWord ++ tailWord_1134231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134231).length < 2 ^ (prefixWord ++ tailWord_1134231).sum := by decide
  have hdescent : baseEnd_1134231 < baseStart_1134231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134259 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 7]
def baseStart_1134259 : Nat := 118140960795 + 1134259 * 2 ^ 59
def prefixEnd_1134259 : Nat := 4983230072969 + 3 ^ 40 * 1134259 * 2
def baseEnd_1134259 : Nat := 129426678597373986699143

theorem tailTrace_1134259 : CollatzResearch.WordTrace tailWord_1134259 prefixEnd_1134259 129426678597373986699143 := by
  unfold tailWord_1134259
  simp only [CollatzResearch.WordTrace]
  refine ⟨41369824397780833859789831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27579882931853889239859887 41369824397780833859789831)
  ·
    refine ⟨62054736596671250789684747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41369824397780833859789831 62054736596671250789684747)
    ·
      refine ⟨93082104895006876184527121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62054736596671250789684747 93082104895006876184527121)
      ·
        refine ⟨69811578671255157138395341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93082104895006876184527121 69811578671255157138395341)
        ·
          refine ⟨26179342001720683926898253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69811578671255157138395341 26179342001720683926898253)
          ·
            refine ⟨9817253250645256472586845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26179342001720683926898253 9817253250645256472586845)
            ·
              refine ⟨3681469968991971177220067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9817253250645256472586845 3681469968991971177220067)
              ·
                refine ⟨5522204953487956765830101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681469968991971177220067 5522204953487956765830101)
                ·
                  refine ⟨129426678597373986699143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5522204953487956765830101 129426678597373986699143)
                  ·
                    rfl

theorem cell22_1134259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_1134259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134259 prefixEnd_1134259 := by exact prefixLift 1134259
  have htrace : WordTrace (prefixWord ++ tailWord_1134259) baseStart_1134259 baseEnd_1134259 := by
    simpa [prefixWord, tailWord_1134259, baseEnd_1134259] using wordTrace_append hprefix tailTrace_1134259
  have hstable : (prefixWord ++ tailWord_1134259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134259).length < 2 ^ (prefixWord ++ tailWord_1134259).sum := by decide
  have hdescent : baseEnd_1134259 < baseStart_1134259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134263 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 3, 3]
def baseStart_1134263 : Nat := 118140960795 + 1134263 * 2 ^ 59
def prefixEnd_1134263 : Nat := 4983230072969 + 3 ^ 40 * 1134263 * 2
def baseEnd_1134263 : Nat := 388281405073867282997417

theorem tailTrace_1134263 : CollatzResearch.WordTrace tailWord_1134263 prefixEnd_1134263 388281405073867282997417 := by
  unfold tailWord_1134263
  simp only [CollatzResearch.WordTrace]
  refine ⟨41369970289766342542935443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27579980193177561695290295 41369970289766342542935443)
  ·
    refine ⟨62054955434649513814403165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41369970289766342542935443 62054955434649513814403165)
    ·
      refine ⟨23270608287993567680401187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62054955434649513814403165 23270608287993567680401187)
      ·
        refine ⟨34905912431990351520601781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23270608287993567680401187 34905912431990351520601781)
        ·
          refine ⟨3272429290499095455056417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34905912431990351520601781 3272429290499095455056417)
          ·
            refine ⟨2454321967874321591292313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272429290499095455056417 2454321967874321591292313)
            ·
              refine ⟨1840741475905741193469235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454321967874321591292313 1840741475905741193469235)
              ·
                refine ⟨2761112213858611790203853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840741475905741193469235 2761112213858611790203853)
                ·
                  refine ⟨1035417080196979421326445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2761112213858611790203853 1035417080196979421326445)
                  ·
                    refine ⟨388281405073867282997417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035417080196979421326445 388281405073867282997417)
                    ·
                      rfl

theorem cell22_1134263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_1134263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134263 prefixEnd_1134263 := by exact prefixLift 1134263
  have htrace : WordTrace (prefixWord ++ tailWord_1134263) baseStart_1134263 baseEnd_1134263 := by
    simpa [prefixWord, tailWord_1134263, baseEnd_1134263] using wordTrace_append hprefix tailTrace_1134263
  have hstable : (prefixWord ++ tailWord_1134263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134263).length < 2 ^ (prefixWord ++ tailWord_1134263).sum := by decide
  have hdescent : baseEnd_1134263 < baseStart_1134263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134304 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_1134304 : Nat := 118140960795 + 1134304 * 2 ^ 59
def prefixEnd_1134304 : Nat := 4983230072969 + 3 ^ 40 * 1134304 * 2
def baseEnd_1134304 : Nat := 129431813403918947574097

theorem tailTrace_1134304 : CollatzResearch.WordTrace tailWord_1134304 prefixEnd_1134304 129431813403918947574097 := by
  unfold tailWord_1134304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20685732841308903272588983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27580977121745204363451977 20685732841308903272588983)
  ·
    refine ⟨31028599261963354908883475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20685732841308903272588983 31028599261963354908883475)
    ·
      refine ⟨46542898892945032363325213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31028599261963354908883475 46542898892945032363325213)
      ·
        refine ⟨17453587084854387136246955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46542898892945032363325213 17453587084854387136246955)
        ·
          refine ⟨26180380627281580704370433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17453587084854387136246955 26180380627281580704370433)
          ·
            refine ⟨19635285470461185528277825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26180380627281580704370433 19635285470461185528277825)
            ·
              refine ⟨14726464102845889146208369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19635285470461185528277825 14726464102845889146208369)
              ·
                refine ⟨11044848077134416859656277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14726464102845889146208369 11044848077134416859656277)
                ·
                  refine ⟨129431813403918947574097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11044848077134416859656277 129431813403918947574097)
                  ·
                    rfl

theorem cell22_1134304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_1134304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134304 prefixEnd_1134304 := by exact prefixLift 1134304
  have htrace : WordTrace (prefixWord ++ tailWord_1134304) baseStart_1134304 baseEnd_1134304 := by
    simpa [prefixWord, tailWord_1134304, baseEnd_1134304] using wordTrace_append hprefix tailTrace_1134304
  have hstable : (prefixWord ++ tailWord_1134304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134304).length < 2 ^ (prefixWord ++ tailWord_1134304).sum := by decide
  have hdescent : baseEnd_1134304 < baseStart_1134304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134321 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 6]
def baseStart_1134321 : Nat := 118140960795 + 1134321 * 2 ^ 59
def prefixEnd_1134321 : Nat := 4983230072969 + 3 ^ 40 * 1134321 * 2
def baseEnd_1134321 : Nat := 129433753219724821682413

theorem tailTrace_1134321 : CollatzResearch.WordTrace tailWord_1134321 prefixEnd_1134321 129433753219724821682413 := by
  unfold tailWord_1134321
  simp only [CollatzResearch.WordTrace]
  refine ⟨41372085723556218448546817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27581390482370812299031211 41372085723556218448546817)
  ·
    refine ⟨31029064292667163836410113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41372085723556218448546817 31029064292667163836410113)
    ·
      refine ⟨23271798219500372877307585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31029064292667163836410113 23271798219500372877307585)
      ·
        refine ⟨17453848664625279657980689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23271798219500372877307585 17453848664625279657980689)
        ·
          refine ⟨13090386498468959743485517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17453848664625279657980689 13090386498468959743485517)
          ·
            refine ⟨4908894936925859903807069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13090386498468959743485517 4908894936925859903807069)
            ·
              refine ⟨1840835601347197463927651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4908894936925859903807069 1840835601347197463927651)
              ·
                refine ⟨2761253402020796195891477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840835601347197463927651 2761253402020796195891477)
                ·
                  refine ⟨129433753219724821682413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2761253402020796195891477 129433753219724821682413)
                  ·
                    rfl

theorem cell22_1134321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_1134321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134321 prefixEnd_1134321 := by exact prefixLift 1134321
  have htrace : WordTrace (prefixWord ++ tailWord_1134321) baseStart_1134321 baseEnd_1134321 := by
    simpa [prefixWord, tailWord_1134321, baseEnd_1134321] using wordTrace_append hprefix tailTrace_1134321
  have hstable : (prefixWord ++ tailWord_1134321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134321).length < 2 ^ (prefixWord ++ tailWord_1134321).sum := by decide
  have hdescent : baseEnd_1134321 < baseStart_1134321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134340 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1134340 : Nat := 118140960795 + 1134340 * 2 ^ 59
def prefixEnd_1134340 : Nat := 4983230072969 + 3 ^ 40 * 1134340 * 2
def baseEnd_1134340 : Nat := 388307763747464748822181

theorem tailTrace_1134340 : CollatzResearch.WordTrace tailWord_1134340 prefixEnd_1134340 388307763747464748822181 := by
  unfold tailWord_1134340
  simp only [CollatzResearch.WordTrace]
  refine ⟨20686389355243692346744237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27581852473658256462325649 20686389355243692346744237)
  ·
    refine ⟨7757396008216384630029089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20686389355243692346744237 7757396008216384630029089)
    ·
      refine ⟨5818047006162288472521817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7757396008216384630029089 5818047006162288472521817)
      ·
        refine ⟨4363535254621716354391363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5818047006162288472521817 4363535254621716354391363)
        ·
          refine ⟨6545302881932574531587045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4363535254621716354391363 6545302881932574531587045)
          ·
            refine ⟨1227244290362357724672571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6545302881932574531587045 1227244290362357724672571)
            ·
              refine ⟨1840866435543536587008857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227244290362357724672571 1840866435543536587008857)
              ·
                refine ⟨1380649826657652440256643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840866435543536587008857 1380649826657652440256643)
                ·
                  refine ⟨2070974739986478660384965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380649826657652440256643 2070974739986478660384965)
                  ·
                    refine ⟨388307763747464748822181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2070974739986478660384965 388307763747464748822181)
                    ·
                      rfl

theorem cell22_1134340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1134340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134340 prefixEnd_1134340 := by exact prefixLift 1134340
  have htrace : WordTrace (prefixWord ++ tailWord_1134340) baseStart_1134340 baseEnd_1134340 := by
    simpa [prefixWord, tailWord_1134340, baseEnd_1134340] using wordTrace_append hprefix tailTrace_1134340
  have hstable : (prefixWord ++ tailWord_1134340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134340).length < 2 ^ (prefixWord ++ tailWord_1134340).sum := by decide
  have hdescent : baseEnd_1134340 < baseStart_1134340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134370 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1134370 : Nat := 118140960795 + 1134370 * 2 ^ 59
def prefixEnd_1134370 : Nat := 4983230072969 + 3 ^ 40 * 1134370 * 2
def baseEnd_1134370 : Nat := 388318033360554670572089

theorem tailTrace_1134370 : CollatzResearch.WordTrace tailWord_1134370 prefixEnd_1134370 388318033360554670572089 := by
  unfold tailWord_1134370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343468225094674954270141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27582581933585799878053709 10343468225094674954270141)
  ·
    refine ⟨3878800584410503107851303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10343468225094674954270141 3878800584410503107851303)
    ·
      refine ⟨5818200876615754661776955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3878800584410503107851303 5818200876615754661776955)
      ·
        refine ⟨8727301314923631992665433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5818200876615754661776955 8727301314923631992665433)
        ·
          refine ⟨6545475986192723994499075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8727301314923631992665433 6545475986192723994499075)
          ·
            refine ⟨9818213979289085991748613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545475986192723994499075 9818213979289085991748613)
            ·
              refine ⟨1840915121116703623452865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9818213979289085991748613 1840915121116703623452865)
              ·
                refine ⟨1380686340837527717589649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840915121116703623452865 1380686340837527717589649)
                ·
                  refine ⟨1035514755628145788192237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380686340837527717589649 1035514755628145788192237)
                  ·
                    refine ⟨388318033360554670572089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035514755628145788192237 388318033360554670572089)
                    ·
                      rfl

theorem cell22_1134370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1134370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134370 prefixEnd_1134370 := by exact prefixLift 1134370
  have htrace : WordTrace (prefixWord ++ tailWord_1134370) baseStart_1134370 baseEnd_1134370 := by
    simpa [prefixWord, tailWord_1134370, baseEnd_1134370] using wordTrace_append hprefix tailTrace_1134370
  have hstable : (prefixWord ++ tailWord_1134370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134370).length < 2 ^ (prefixWord ++ tailWord_1134370).sum := by decide
  have hdescent : baseEnd_1134370 < baseStart_1134370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134372 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_1134372 : Nat := 118140960795 + 1134372 * 2 ^ 59
def prefixEnd_1134372 : Nat := 4983230072969 + 3 ^ 40 * 1134372 * 2
def baseEnd_1134372 : Nat := 129439572667142444007361

theorem tailTrace_1134372 : CollatzResearch.WordTrace tailWord_1134372 prefixEnd_1134372 129439572667142444007361 := by
  unfold tailWord_1134372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20686972923185727079326685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27582630564247636105768913 20686972923185727079326685)
  ·
    refine ⟨7757614846194647654747507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20686972923185727079326685 7757614846194647654747507)
    ·
      refine ⟨11636422269291971482121261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757614846194647654747507 11636422269291971482121261)
      ·
        refine ⟨4363658350984489305795473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11636422269291971482121261 4363658350984489305795473)
        ·
          refine ⟨3272743763238366979346605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363658350984489305795473 3272743763238366979346605)
          ·
            refine ⟨1227278911214387617254977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3272743763238366979346605 1227278911214387617254977)
            ·
              refine ⟨920459183410790712941233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227278911214387617254977 920459183410790712941233)
              ·
                refine ⟨690344387558093034705925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920459183410790712941233 690344387558093034705925)
                ·
                  refine ⟨129439572667142444007361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690344387558093034705925 129439572667142444007361)
                  ·
                    rfl

theorem cell22_1134372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_1134372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134372 prefixEnd_1134372 := by exact prefixLift 1134372
  have htrace : WordTrace (prefixWord ++ tailWord_1134372) baseStart_1134372 baseEnd_1134372 := by
    simpa [prefixWord, tailWord_1134372, baseEnd_1134372] using wordTrace_append hprefix tailTrace_1134372
  have hstable : (prefixWord ++ tailWord_1134372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134372).length < 2 ^ (prefixWord ++ tailWord_1134372).sum := by decide
  have hdescent : baseEnd_1134372 < baseStart_1134372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134426 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1134426 : Nat := 118140960795 + 1134426 * 2 ^ 59
def prefixEnd_1134426 : Nat := 4983230072969 + 3 ^ 40 * 1134426 * 2
def baseEnd_1134426 : Nat := 388337203304989191171917

theorem tailTrace_1134426 : CollatzResearch.WordTrace tailWord_1134426 prefixEnd_1134426 388337203304989191171917 := by
  unfold tailWord_1134426
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343978847043955345279783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27583943592117214254079421 10343978847043955345279783)
  ·
    refine ⟨15515968270565933017919675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10343978847043955345279783 15515968270565933017919675)
    ·
      refine ⟨23273952405848899526879513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15515968270565933017919675 23273952405848899526879513)
      ·
        refine ⟨17455464304386674645159635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23273952405848899526879513 17455464304386674645159635)
        ·
          refine ⟨26183196456580011967739453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17455464304386674645159635 26183196456580011967739453)
          ·
            refine ⟨9818698671217504487902295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26183196456580011967739453 9818698671217504487902295)
            ·
              refine ⟨14728048006826256731853443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9818698671217504487902295 14728048006826256731853443)
              ·
                refine ⟨22092072010239385097780165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14728048006826256731853443 22092072010239385097780165)
                ·
                  refine ⟨4142263501919884705833781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22092072010239385097780165 4142263501919884705833781)
                  ·
                    refine ⟨388337203304989191171917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4142263501919884705833781 388337203304989191171917)
                    ·
                      rfl

theorem cell22_1134426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1134426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134426 prefixEnd_1134426 := by exact prefixLift 1134426
  have htrace : WordTrace (prefixWord ++ tailWord_1134426) baseStart_1134426 baseEnd_1134426 := by
    simpa [prefixWord, tailWord_1134426, baseEnd_1134426] using wordTrace_append hprefix tailTrace_1134426
  have hstable : (prefixWord ++ tailWord_1134426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134426).length < 2 ^ (prefixWord ++ tailWord_1134426).sum := by decide
  have hdescent : baseEnd_1134426 < baseStart_1134426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_1134441 : Nat := 118140960795 + 1134441 * 2 ^ 59
def prefixEnd_1134441 : Nat := 4983230072969 + 3 ^ 40 * 1134441 * 2
def baseEnd_1134441 : Nat := 388342338111534152046871

theorem tailTrace_1134441 : CollatzResearch.WordTrace tailWord_1134441 prefixEnd_1134441 388342338111534152046871 := by
  unfold tailWord_1134441
  simp only [CollatzResearch.WordTrace]
  refine ⟨41376462483121478942915177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27584308322080985961943451 41376462483121478942915177)
  ·
    refine ⟨31032346862341109207186383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41376462483121478942915177 31032346862341109207186383)
    ·
      refine ⟨46548520293511663810779575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31032346862341109207186383 46548520293511663810779575)
      ·
        refine ⟨69822780440267495716169363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46548520293511663810779575 69822780440267495716169363)
        ·
          refine ⟨104734170660401243574254045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69822780440267495716169363 104734170660401243574254045)
          ·
            refine ⟨39275313997650466340345267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104734170660401243574254045 39275313997650466340345267)
            ·
              refine ⟨58912970996475699510517901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39275313997650466340345267 58912970996475699510517901)
              ·
                refine ⟨22092364123678387316444213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58912970996475699510517901 22092364123678387316444213)
                ·
                  refine ⟨2071159136594848810916645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22092364123678387316444213 2071159136594848810916645)
                  ·
                    refine ⟨388342338111534152046871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071159136594848810916645 388342338111534152046871)
                    ·
                      rfl

theorem cell22_1134441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_1134441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134441 prefixEnd_1134441 := by exact prefixLift 1134441
  have htrace : WordTrace (prefixWord ++ tailWord_1134441) baseStart_1134441 baseEnd_1134441 := by
    simpa [prefixWord, tailWord_1134441, baseEnd_1134441] using wordTrace_append hprefix tailTrace_1134441
  have hstable : (prefixWord ++ tailWord_1134441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134441).length < 2 ^ (prefixWord ++ tailWord_1134441).sum := by decide
  have hdescent : baseEnd_1134441 < baseStart_1134441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134458 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_1134458 : Nat := 118140960795 + 1134458 * 2 ^ 59
def prefixEnd_1134458 : Nat := 4983230072969 + 3 ^ 40 * 1134458 * 2
def baseEnd_1134458 : Nat := 388348157558951774371819

theorem tailTrace_1134458 : CollatzResearch.WordTrace tailWord_1134458 prefixEnd_1134458 388348157558951774371819 := by
  unfold tailWord_1134458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344270631014972711571007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27584721682706593897522685 10344270631014972711571007)
  ·
    refine ⟨15516405946522459067356511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10344270631014972711571007 15516405946522459067356511)
    ·
      refine ⟨23274608919783688601034767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15516405946522459067356511 23274608919783688601034767)
      ·
        refine ⟨34911913379675532901552151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23274608919783688601034767 34911913379675532901552151)
        ·
          refine ⟨52367870069513299352328227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34911913379675532901552151 52367870069513299352328227)
          ·
            refine ⟨78551805104269949028492341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52367870069513299352328227 78551805104269949028492341)
            ·
              refine ⟨7364231728525307721421157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78551805104269949028492341 7364231728525307721421157)
              ·
                refine ⟨1380793449098495197766467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7364231728525307721421157 1380793449098495197766467)
                ·
                  refine ⟨2071190173647742796649701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380793449098495197766467 2071190173647742796649701)
                  ·
                    refine ⟨388348157558951774371819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071190173647742796649701 388348157558951774371819)
                    ·
                      rfl

theorem cell22_1134458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_1134458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134458 prefixEnd_1134458 := by exact prefixLift 1134458
  have htrace : WordTrace (prefixWord ++ tailWord_1134458) baseStart_1134458 baseEnd_1134458 := by
    simpa [prefixWord, tailWord_1134458, baseEnd_1134458] using wordTrace_append hprefix tailTrace_1134458
  have hstable : (prefixWord ++ tailWord_1134458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134458).length < 2 ^ (prefixWord ++ tailWord_1134458).sum := by decide
  have hdescent : baseEnd_1134458 < baseStart_1134458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134490 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_1134490 : Nat := 118140960795 + 1134490 * 2 ^ 59
def prefixEnd_1134490 : Nat := 4983230072969 + 3 ^ 40 * 1134490 * 2
def baseEnd_1134490 : Nat := 129453037270971452523907

theorem tailTrace_1134490 : CollatzResearch.WordTrace tailWord_1134490 prefixEnd_1134490 129453037270971452523907 := by
  unfold tailWord_1134490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344562414985990077862231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27585499773295973540965949 10344562414985990077862231)
  ·
    refine ⟨15516843622478985116793347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10344562414985990077862231 15516843622478985116793347)
    ·
      refine ⟨23275265433718477675190021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15516843622478985116793347 23275265433718477675190021)
      ·
        refine ⟨4364112268822214564098129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23275265433718477675190021 4364112268822214564098129)
        ·
          refine ⟨3273084201616660923073597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4364112268822214564098129 3273084201616660923073597)
          ·
            refine ⟨1227406575606247846152599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3273084201616660923073597 1227406575606247846152599)
            ·
              refine ⟨1841109863409371769228899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227406575606247846152599 1841109863409371769228899)
              ·
                refine ⟨2761664795114057653843349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841109863409371769228899 2761664795114057653843349)
                ·
                  refine ⟨129453037270971452523907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2761664795114057653843349 129453037270971452523907)
                  ·
                    rfl

theorem cell22_1134490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_1134490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134490 prefixEnd_1134490 := by exact prefixLift 1134490
  have htrace : WordTrace (prefixWord ++ tailWord_1134490) baseStart_1134490 baseEnd_1134490 := by
    simpa [prefixWord, tailWord_1134490, baseEnd_1134490] using wordTrace_append hprefix tailTrace_1134490
  have hstable : (prefixWord ++ tailWord_1134490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134490).length < 2 ^ (prefixWord ++ tailWord_1134490).sum := by decide
  have hdescent : baseEnd_1134490 < baseStart_1134490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134531 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_1134531 : Nat := 118140960795 + 1134531 * 2 ^ 59
def prefixEnd_1134531 : Nat := 4983230072969 + 3 ^ 40 * 1134531 * 2
def baseEnd_1134531 : Nat := 388373146950803917296595

theorem tailTrace_1134531 : CollatzResearch.WordTrace tailWord_1134531 prefixEnd_1134531 388373146950803917296595 := by
  unfold tailWord_1134531
  simp only [CollatzResearch.WordTrace]
  refine ⟨41379745052795424313691447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27586496701863616209127631 41379745052795424313691447)
  ·
    refine ⟨62069617579193136470537171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41379745052795424313691447 62069617579193136470537171)
    ·
      refine ⟨93104426368789704705805757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62069617579193136470537171 93104426368789704705805757)
      ·
        refine ⟨34914159888296139264677159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93104426368789704705805757 34914159888296139264677159)
        ·
          refine ⟨52371239832444208897015739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34914159888296139264677159 52371239832444208897015739)
          ·
            refine ⟨78556859748666313345523609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52371239832444208897015739 78556859748666313345523609)
            ·
              refine ⟨58917644811499735009142707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78556859748666313345523609 58917644811499735009142707)
              ·
                refine ⟨88376467217249602513714061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58917644811499735009142707 88376467217249602513714061)
                ·
                  refine ⟨33141175206468600942642773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88376467217249602513714061 33141175206468600942642773)
                  ·
                    refine ⟨388373146950803917296595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33141175206468600942642773 388373146950803917296595)
                    ·
                      rfl

theorem cell22_1134531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_1134531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134531 prefixEnd_1134531 := by exact prefixLift 1134531
  have htrace : WordTrace (prefixWord ++ tailWord_1134531) baseStart_1134531 baseEnd_1134531 := by
    simpa [prefixWord, tailWord_1134531, baseEnd_1134531] using wordTrace_append hprefix tailTrace_1134531
  have hstable : (prefixWord ++ tailWord_1134531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134531).length < 2 ^ (prefixWord ++ tailWord_1134531).sum := by decide
  have hdescent : baseEnd_1134531 < baseStart_1134531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134533 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_1134533 : Nat := 118140960795 + 1134533 * 2 ^ 59
def prefixEnd_1134533 : Nat := 4983230072969 + 3 ^ 40 * 1134533 * 2
def baseEnd_1134533 : Nat := 388373831591676578746589

theorem tailTrace_1134533 : CollatzResearch.WordTrace tailWord_1134533 prefixEnd_1134533 388373831591676578746589 := by
  unfold tailWord_1134533
  simp only [CollatzResearch.WordTrace]
  refine ⟨41379817998788178655264253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27586545332525452436842835 41379817998788178655264253)
  ·
    refine ⟨15517431749545566995724095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41379817998788178655264253 15517431749545566995724095)
    ·
      refine ⟨23276147624318350493586143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15517431749545566995724095 23276147624318350493586143)
      ·
        refine ⟨34914221436477525740379215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23276147624318350493586143 34914221436477525740379215)
        ·
          refine ⟨52371332154716288610568823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34914221436477525740379215 52371332154716288610568823)
          ·
            refine ⟨78556998232074432915853235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52371332154716288610568823 78556998232074432915853235)
            ·
              refine ⟨117835497348111649373779853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78556998232074432915853235 117835497348111649373779853)
              ·
                refine ⟨44188311505541868515167445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117835497348111649373779853 44188311505541868515167445)
                ·
                  refine ⟨1035663550911137543324237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44188311505541868515167445 1035663550911137543324237)
                  ·
                    refine ⟨388373831591676578746589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035663550911137543324237 388373831591676578746589)
                    ·
                      rfl

theorem cell22_1134533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_1134533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134533 prefixEnd_1134533 := by exact prefixLift 1134533
  have htrace : WordTrace (prefixWord ++ tailWord_1134533) baseStart_1134533 baseEnd_1134533 := by
    simpa [prefixWord, tailWord_1134533, baseEnd_1134533] using wordTrace_append hprefix tailTrace_1134533
  have hstable : (prefixWord ++ tailWord_1134533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134533).length < 2 ^ (prefixWord ++ tailWord_1134533).sum := by decide
  have hdescent : baseEnd_1134533 < baseStart_1134533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134548 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1134548 : Nat := 118140960795 + 1134548 * 2 ^ 59
def prefixEnd_1134548 : Nat := 4983230072969 + 3 ^ 40 * 1134548 * 2
def baseEnd_1134548 : Nat := 388378966398221539621543

theorem tailTrace_1134548 : CollatzResearch.WordTrace tailWord_1134548 prefixEnd_1134548 388378966398221539621543 := by
  unfold tailWord_1134548
  simp only [CollatzResearch.WordTrace]
  refine ⟨20690182546866918108530149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27586910062489224144706865 20690182546866918108530149)
  ·
    refine ⟨3879409227537547145349403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20690182546866918108530149 3879409227537547145349403)
    ·
      refine ⟨5819113841306320718024105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879409227537547145349403 5819113841306320718024105)
      ·
        refine ⟨4364335380979740538518079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5819113841306320718024105 4364335380979740538518079)
        ·
          refine ⟨6546503071469610807777119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364335380979740538518079 6546503071469610807777119)
          ·
            refine ⟨9819754607204416211665679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6546503071469610807777119 9819754607204416211665679)
            ·
              refine ⟨14729631910806624317498519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9819754607204416211665679 14729631910806624317498519)
              ·
                refine ⟨22094447866209936476247779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14729631910806624317498519 22094447866209936476247779)
                ·
                  refine ⟨33141671799314904714371669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22094447866209936476247779 33141671799314904714371669)
                  ·
                    refine ⟨388378966398221539621543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33141671799314904714371669 388378966398221539621543)
                    ·
                      rfl

theorem cell22_1134548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1134548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134548 prefixEnd_1134548 := by exact prefixLift 1134548
  have htrace : WordTrace (prefixWord ++ tailWord_1134548) baseStart_1134548 baseEnd_1134548 := by
    simpa [prefixWord, tailWord_1134548, baseEnd_1134548] using wordTrace_append hprefix tailTrace_1134548
  have hstable : (prefixWord ++ tailWord_1134548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134548).length < 2 ^ (prefixWord ++ tailWord_1134548).sum := by decide
  have hdescent : baseEnd_1134548 < baseStart_1134548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134567 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1134567 : Nat := 118140960795 + 1134567 * 2 ^ 59
def prefixEnd_1134567 : Nat := 4983230072969 + 3 ^ 40 * 1134567 * 2
def baseEnd_1134567 : Nat := 388385470486511823396485

theorem tailTrace_1134567 : CollatzResearch.WordTrace tailWord_1134567 prefixEnd_1134567 388385470486511823396485 := by
  unfold tailWord_1134567
  simp only [CollatzResearch.WordTrace]
  refine ⟨41381058080665002462001955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27587372053776668308001303 41381058080665002462001955)
  ·
    refine ⟨62071587120997503693002933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41381058080665002462001955 62071587120997503693002933)
    ·
      refine ⟨5819211292593515971219025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62071587120997503693002933 5819211292593515971219025)
      ·
        refine ⟨4364408469445136978414269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5819211292593515971219025 4364408469445136978414269)
        ·
          refine ⟨1636653176041926366905351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4364408469445136978414269 1636653176041926366905351)
          ·
            refine ⟨2454979764062889550358027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636653176041926366905351 2454979764062889550358027)
            ·
              refine ⟨3682469646094334325537041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454979764062889550358027 3682469646094334325537041)
              ·
                refine ⟨2761852234570750744152781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3682469646094334325537041 2761852234570750744152781)
                ·
                  refine ⟨1035694587964031529057293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2761852234570750744152781 1035694587964031529057293)
                  ·
                    refine ⟨388385470486511823396485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035694587964031529057293 388385470486511823396485)
                    ·
                      rfl

theorem cell22_1134567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1134567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134567 prefixEnd_1134567 := by exact prefixLift 1134567
  have htrace : WordTrace (prefixWord ++ tailWord_1134567) baseStart_1134567 baseEnd_1134567 := by
    simpa [prefixWord, tailWord_1134567, baseEnd_1134567] using wordTrace_append hprefix tailTrace_1134567
  have hstable : (prefixWord ++ tailWord_1134567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134567).length < 2 ^ (prefixWord ++ tailWord_1134567).sum := by decide
  have hdescent : baseEnd_1134567 < baseStart_1134567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134640 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_1134640 : Nat := 118140960795 + 1134640 * 2 ^ 59
def prefixEnd_1134640 : Nat := 4983230072969 + 3 ^ 40 * 1134640 * 2
def baseEnd_1134640 : Nat := 388410459878363966321261

theorem tailTrace_1134640 : CollatzResearch.WordTrace tailWord_1134640 prefixEnd_1134640 388410459878363966321261 := by
  unfold tailWord_1134640
  simp only [CollatzResearch.WordTrace]
  refine ⟨20691860304700267964704687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27589147072933690619606249 20691860304700267964704687)
  ·
    refine ⟨31037790457050401947057031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20691860304700267964704687 31037790457050401947057031)
    ·
      refine ⟨46556685685575602920585547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31037790457050401947057031 46556685685575602920585547)
      ·
        refine ⟨69835028528363404380878321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46556685685575602920585547 69835028528363404380878321)
        ·
          refine ⟨52376271396272553285658741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69835028528363404380878321 52376271396272553285658741)
          ·
            refine ⟨4910275443400551870530507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52376271396272553285658741 4910275443400551870530507)
            ·
              refine ⟨7365413165100827805795761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910275443400551870530507 7365413165100827805795761)
              ·
                refine ⟨5524059873825620854346821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7365413165100827805795761 5524059873825620854346821)
                ·
                  refine ⟨1035761226342303910190029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5524059873825620854346821 1035761226342303910190029)
                  ·
                    refine ⟨388410459878363966321261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035761226342303910190029 388410459878363966321261)
                    ·
                      rfl

theorem cell22_1134640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_1134640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134640 prefixEnd_1134640 := by exact prefixLift 1134640
  have htrace : WordTrace (prefixWord ++ tailWord_1134640) baseStart_1134640 baseEnd_1134640 := by
    simpa [prefixWord, tailWord_1134640, baseEnd_1134640] using wordTrace_append hprefix tailTrace_1134640
  have hstable : (prefixWord ++ tailWord_1134640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134640).length < 2 ^ (prefixWord ++ tailWord_1134640).sum := by decide
  have hdescent : baseEnd_1134640 < baseStart_1134640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134642 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_1134642 : Nat := 118140960795 + 1134642 * 2 ^ 59
def prefixEnd_1134642 : Nat := 4983230072969 + 3 ^ 40 * 1134642 * 2
def baseEnd_1134642 : Nat := 129470381506412209257085

theorem tailTrace_1134642 : CollatzResearch.WordTrace tailWord_1134642 prefixEnd_1134642 129470381506412209257085 := by
  unfold tailWord_1134642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10345948388848322567745545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27589195703595526847321453 10345948388848322567745545)
  ·
    refine ⟨7759461291636241925809159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10345948388848322567745545 7759461291636241925809159)
    ·
      refine ⟨11639191937454362888713739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759461291636241925809159 11639191937454362888713739)
      ·
        refine ⟨17458787906181544333070609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639191937454362888713739 17458787906181544333070609)
        ·
          refine ⟨13094090929636158249802957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17458787906181544333070609 13094090929636158249802957)
          ·
            refine ⟨4910284098613559343676109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13094090929636158249802957 4910284098613559343676109)
            ·
              refine ⟨1841356536980084753878541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4910284098613559343676109 1841356536980084753878541)
              ·
                refine ⟨690508701367531782704453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1841356536980084753878541 690508701367531782704453)
                ·
                  refine ⟨129470381506412209257085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690508701367531782704453 129470381506412209257085)
                  ·
                    rfl

theorem cell22_1134642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_1134642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134642 prefixEnd_1134642 := by exact prefixLift 1134642
  have htrace : WordTrace (prefixWord ++ tailWord_1134642) baseStart_1134642 baseEnd_1134642 := by
    simpa [prefixWord, tailWord_1134642, baseEnd_1134642] using wordTrace_append hprefix tailTrace_1134642
  have hstable : (prefixWord ++ tailWord_1134642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134642).length < 2 ^ (prefixWord ++ tailWord_1134642).sum := by decide
  have hdescent : baseEnd_1134642 < baseStart_1134642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134657 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1134657 : Nat := 118140960795 + 1134657 * 2 ^ 59
def prefixEnd_1134657 : Nat := 4983230072969 + 3 ^ 40 * 1134657 * 2
def baseEnd_1134657 : Nat := 388416279325781588646209

theorem tailTrace_1134657 : CollatzResearch.WordTrace tailWord_1134657 prefixEnd_1134657 388416279325781588646209 := by
  unfold tailWord_1134657
  simp only [CollatzResearch.WordTrace]
  refine ⟨41384340650338947832778225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27589560433559298555185483 41384340650338947832778225)
  ·
    refine ⟨31038255487754210874583669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41384340650338947832778225 31038255487754210874583669)
    ·
      refine ⟨2909836451976957269492219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31038255487754210874583669 2909836451976957269492219)
      ·
        refine ⟨4364754677965435904238329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909836451976957269492219 4364754677965435904238329)
        ·
          refine ⟨3273566008474076928178747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4364754677965435904238329 3273566008474076928178747)
          ·
            refine ⟨4910349012711115392268121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273566008474076928178747 4910349012711115392268121)
            ·
              refine ⟨3682761759533336544201091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4910349012711115392268121 3682761759533336544201091)
              ·
                refine ⟨5524142639300004816301637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682761759533336544201091 5524142639300004816301637)
                ·
                  refine ⟨1035776744868750903056557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5524142639300004816301637 1035776744868750903056557)
                  ·
                    refine ⟨388416279325781588646209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035776744868750903056557 388416279325781588646209)
                    ·
                      rfl

theorem cell22_1134657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1134657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134657 prefixEnd_1134657 := by exact prefixLift 1134657
  have htrace : WordTrace (prefixWord ++ tailWord_1134657) baseStart_1134657 baseEnd_1134657 := by
    simpa [prefixWord, tailWord_1134657, baseEnd_1134657] using wordTrace_append hprefix tailTrace_1134657
  have hstable : (prefixWord ++ tailWord_1134657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134657).length < 2 ^ (prefixWord ++ tailWord_1134657).sum := by decide
  have hdescent : baseEnd_1134657 < baseStart_1134657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134670 : List Nat := [4, 1, 1, 1, 1, 5, 2, 7]
def baseStart_1134670 : Nat := 118140960795 + 1134670 * 2 ^ 59
def prefixEnd_1134670 : Nat := 4983230072969 + 3 ^ 40 * 1134670 * 2
def baseEnd_1134670 : Nat := 43157858832383765341241

theorem tailTrace_1134670 : CollatzResearch.WordTrace tailWord_1134670 prefixEnd_1134670 43157858832383765341241 := by
  unfold tailWord_1134670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173101849911481381625183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27589876532861234035334309 5173101849911481381625183)
  ·
    refine ⟨7759652774867222072437775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5173101849911481381625183 7759652774867222072437775)
    ·
      refine ⟨11639479162300833108656663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759652774867222072437775 11639479162300833108656663)
      ·
        refine ⟨17459218743451249662984995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639479162300833108656663 17459218743451249662984995)
        ·
          refine ⟨26188828115176874494477493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17459218743451249662984995 26188828115176874494477493)
          ·
            refine ⟨2455202635797831983857265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26188828115176874494477493 2455202635797831983857265)
            ·
              refine ⟨1841401976848373987892949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455202635797831983857265 1841401976848373987892949)
              ·
                refine ⟨43157858832383765341241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1841401976848373987892949 43157858832383765341241)
                ·
                  rfl

theorem cell22_1134670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_1134670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134670 prefixEnd_1134670 := by exact prefixLift 1134670
  have htrace : WordTrace (prefixWord ++ tailWord_1134670) baseStart_1134670 baseEnd_1134670 := by
    simpa [prefixWord, tailWord_1134670, baseEnd_1134670] using wordTrace_append hprefix tailTrace_1134670
  have hstable : (prefixWord ++ tailWord_1134670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134670).length < 2 ^ (prefixWord ++ tailWord_1134670).sum := by decide
  have hdescent : baseEnd_1134670 < baseStart_1134670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134674 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1134674 : Nat := 118140960795 + 1134674 * 2 ^ 59
def prefixEnd_1134674 : Nat := 4983230072969 + 3 ^ 40 * 1134674 * 2
def baseEnd_1134674 : Nat := 388422098773199210971157

theorem tailTrace_1134674 : CollatzResearch.WordTrace tailWord_1134674 prefixEnd_1134674 388422098773199210971157 := by
  unfold tailWord_1134674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346240172819339934036769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27589973794184906490764717 10346240172819339934036769)
  ·
    refine ⟨7759680129614504950527577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10346240172819339934036769 7759680129614504950527577)
    ·
      refine ⟨5819760097210878712895683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7759680129614504950527577 5819760097210878712895683)
      ·
        refine ⟨8729640145816318069343525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5819760097210878712895683 8729640145816318069343525)
        ·
          refine ⟨1636807527340559638001911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8729640145816318069343525 1636807527340559638001911)
          ·
            refine ⟨2455211291010839457002867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636807527340559638001911 2455211291010839457002867)
            ·
              refine ⟨3682816936516259185504301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455211291010839457002867 3682816936516259185504301)
              ·
                refine ⟨1381056351193597194564113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3682816936516259185504301 1381056351193597194564113)
                ·
                  refine ⟨1035792263395197895923085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381056351193597194564113 1035792263395197895923085)
                  ·
                    refine ⟨388422098773199210971157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035792263395197895923085 388422098773199210971157)
                    ·
                      rfl

theorem cell22_1134674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1134674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134674 prefixEnd_1134674 := by exact prefixLift 1134674
  have htrace : WordTrace (prefixWord ++ tailWord_1134674) baseStart_1134674 baseEnd_1134674 := by
    simpa [prefixWord, tailWord_1134674, baseEnd_1134674] using wordTrace_append hprefix tailTrace_1134674
  have hstable : (prefixWord ++ tailWord_1134674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134674).length < 2 ^ (prefixWord ++ tailWord_1134674).sum := by decide
  have hdescent : baseEnd_1134674 < baseStart_1134674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134730 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1134730 : Nat := 118140960795 + 1134730 * 2 ^ 59
def prefixEnd_1134730 : Nat := 4983230072969 + 3 ^ 40 * 1134730 * 2
def baseEnd_1134730 : Nat := 388441268717633731570985

theorem tailTrace_1134730 : CollatzResearch.WordTrace tailWord_1134730 prefixEnd_1134730 388441268717633731570985 := by
  unfold tailWord_1134730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346750794768620325046411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27591335452716320866790429 10346750794768620325046411)
  ·
    refine ⟨15520126192152930487569617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10346750794768620325046411 15520126192152930487569617)
    ·
      refine ⟨11640094644114697865677213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15520126192152930487569617 11640094644114697865677213)
      ·
        refine ⟨4365035491543011699628955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11640094644114697865677213 4365035491543011699628955)
        ·
          refine ⟨6547553237314517549443433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365035491543011699628955 6547553237314517549443433)
          ·
            refine ⟨4910664927985888162082575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6547553237314517549443433 4910664927985888162082575)
            ·
              refine ⟨7365997391978832243123863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910664927985888162082575 7365997391978832243123863)
              ·
                refine ⟨11048996087968248364685795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7365997391978832243123863 11048996087968248364685795)
                ·
                  refine ⟨16573494131952372547028693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11048996087968248364685795 16573494131952372547028693)
                  ·
                    refine ⟨388441268717633731570985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16573494131952372547028693 388441268717633731570985)
                    ·
                      rfl

theorem cell22_1134730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1134730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134730 prefixEnd_1134730 := by exact prefixLift 1134730
  have htrace : WordTrace (prefixWord ++ tailWord_1134730) baseStart_1134730 baseEnd_1134730 := by
    simpa [prefixWord, tailWord_1134730, baseEnd_1134730] using wordTrace_append hprefix tailTrace_1134730
  have hstable : (prefixWord ++ tailWord_1134730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134730).length < 2 ^ (prefixWord ++ tailWord_1134730).sum := by decide
  have hdescent : baseEnd_1134730 < baseStart_1134730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134777 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 4]
def baseStart_1134777 : Nat := 118140960795 + 1134777 * 2 ^ 59
def prefixEnd_1134777 : Nat := 4983230072969 + 3 ^ 40 * 1134777 * 2
def baseEnd_1134777 : Nat := 129485785926047091881947

theorem tailTrace_1134777 : CollatzResearch.WordTrace tailWord_1134777 prefixEnd_1134777 129485785926047091881947 := by
  unfold tailWord_1134777
  simp only [CollatzResearch.WordTrace]
  refine ⟨41388717409904208327146585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27592478273269472218097723 41388717409904208327146585)
  ·
    refine ⟨31041538057428156245359939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41388717409904208327146585 31041538057428156245359939)
    ·
      refine ⟨46562307086142234368039909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31041538057428156245359939 46562307086142234368039909)
      ·
        refine ⟨8730432578651668944007483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46562307086142234368039909 8730432578651668944007483)
        ·
          refine ⟨13095648867977503416011225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730432578651668944007483 13095648867977503416011225)
          ·
            refine ⟨9821736650983127562008419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13095648867977503416011225 9821736650983127562008419)
            ·
              refine ⟨14732604976474691343012629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9821736650983127562008419 14732604976474691343012629)
              ·
                refine ⟨690590858272251156703717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14732604976474691343012629 690590858272251156703717)
                ·
                  refine ⟨129485785926047091881947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690590858272251156703717 129485785926047091881947)
                  ·
                    rfl

theorem cell22_1134777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_1134777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134777 prefixEnd_1134777 := by exact prefixLift 1134777
  have htrace : WordTrace (prefixWord ++ tailWord_1134777) baseStart_1134777 baseEnd_1134777 := by
    simpa [prefixWord, tailWord_1134777, baseEnd_1134777] using wordTrace_append hprefix tailTrace_1134777
  have hstable : (prefixWord ++ tailWord_1134777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134777).length < 2 ^ (prefixWord ++ tailWord_1134777).sum := by decide
  have hdescent : baseEnd_1134777 < baseStart_1134777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134796 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_1134796 : Nat := 118140960795 + 1134796 * 2 ^ 59
def prefixEnd_1134796 : Nat := 4983230072969 + 3 ^ 40 * 1134796 * 2
def baseEnd_1134796 : Nat := 388463861866431559420783

theorem tailTrace_1134796 : CollatzResearch.WordTrace tailWord_1134796 prefixEnd_1134796 388463861866431559420783 := by
  unfold tailWord_1134796
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694705198417687286044121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27592940264556916381392161 20694705198417687286044121)
  ·
    refine ⟨15521028898813265464533091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20694705198417687286044121 15521028898813265464533091)
    ·
      refine ⟨23281543348219898196799637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15521028898813265464533091 23281543348219898196799637)
      ·
        refine ⟨1091322344447807727974983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23281543348219898196799637 1091322344447807727974983)
        ·
          refine ⟨1636983516671711591962475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091322344447807727974983 1636983516671711591962475)
          ·
            refine ⟨2455475275007567387943713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636983516671711591962475 2455475275007567387943713)
            ·
              refine ⟨1841606456255675540957785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455475275007567387943713 1841606456255675540957785)
              ·
                refine ⟨1381204842191756655718339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841606456255675540957785 1381204842191756655718339)
                ·
                  refine ⟨2071807263287634983577509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381204842191756655718339 2071807263287634983577509)
                  ·
                    refine ⟨388463861866431559420783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071807263287634983577509 388463861866431559420783)
                    ·
                      rfl

theorem cell22_1134796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_1134796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134796 prefixEnd_1134796 := by exact prefixLift 1134796
  have htrace : WordTrace (prefixWord ++ tailWord_1134796) baseStart_1134796 baseEnd_1134796 := by
    simpa [prefixWord, tailWord_1134796, baseEnd_1134796] using wordTrace_append hprefix tailTrace_1134796
  have hstable : (prefixWord ++ tailWord_1134796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134796).length < 2 ^ (prefixWord ++ tailWord_1134796).sum := by decide
  have hdescent : baseEnd_1134796 < baseStart_1134796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134835 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_1134835 : Nat := 118140960795 + 1134835 * 2 ^ 59
def prefixEnd_1134835 : Nat := 4983230072969 + 3 ^ 40 * 1134835 * 2
def baseEnd_1134835 : Nat := 388477212363448457695663

theorem tailTrace_1134835 : CollatzResearch.WordTrace tailWord_1134835 prefixEnd_1134835 388477212363448457695663 := by
  unfold tailWord_1134835
  simp only [CollatzResearch.WordTrace]
  refine ⟨41390832843694084232757959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27593888562462722821838639 41390832843694084232757959)
  ·
    refine ⟨62086249265541126349136939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41390832843694084232757959 62086249265541126349136939)
    ·
      refine ⟨93129373898311689523705409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62086249265541126349136939 93129373898311689523705409)
      ·
        refine ⟨69847030423733767142779057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93129373898311689523705409 69847030423733767142779057)
        ·
          refine ⟨52385272817800325357084293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69847030423733767142779057 52385272817800325357084293)
          ·
            refine ⟨9822238653337561004453305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52385272817800325357084293 9822238653337561004453305)
            ·
              refine ⟨7366678990003170753339979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9822238653337561004453305 7366678990003170753339979)
              ·
                refine ⟨11050018485004756130009969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7366678990003170753339979 11050018485004756130009969)
                ·
                  refine ⟨8287513863753567097507477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11050018485004756130009969 8287513863753567097507477)
                  ·
                    refine ⟨388477212363448457695663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8287513863753567097507477 388477212363448457695663)
                    ·
                      rfl

theorem cell22_1134835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_1134835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134835 prefixEnd_1134835 := by exact prefixLift 1134835
  have htrace : WordTrace (prefixWord ++ tailWord_1134835) baseStart_1134835 baseEnd_1134835 := by
    simpa [prefixWord, tailWord_1134835, baseEnd_1134835] using wordTrace_append hprefix tailTrace_1134835
  have hstable : (prefixWord ++ tailWord_1134835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134835).length < 2 ^ (prefixWord ++ tailWord_1134835).sum := by decide
  have hdescent : baseEnd_1134835 < baseStart_1134835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134884 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1134884 : Nat := 118140960795 + 1134884 * 2 ^ 59
def prefixEnd_1134884 : Nat := 4983230072969 + 3 ^ 40 * 1134884 * 2
def baseEnd_1134884 : Nat := 129497995354942887740171

theorem tailTrace_1134884 : CollatzResearch.WordTrace tailWord_1134884 prefixEnd_1134884 129497995354942887740171 := by
  unfold tailWord_1134884
  simp only [CollatzResearch.WordTrace]
  refine ⟨20696310010258282800645853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27595080013677710400861137 20696310010258282800645853)
  ·
    refine ⟨7761116253846856050242195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20696310010258282800645853 7761116253846856050242195)
    ·
      refine ⟨11641674380770284075363293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761116253846856050242195 11641674380770284075363293)
      ·
        refine ⟨4365627892788856528261235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11641674380770284075363293 4365627892788856528261235)
        ·
          refine ⟨6548441839183284792391853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365627892788856528261235 6548441839183284792391853)
          ·
            refine ⟨2455665689693731797146945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6548441839183284792391853 2455665689693731797146945)
            ·
              refine ⟨1841749267270298847860209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455665689693731797146945 1841749267270298847860209)
              ·
                refine ⟨1381311950452724135895157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841749267270298847860209 1381311950452724135895157)
                ·
                  refine ⟨129497995354942887740171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1381311950452724135895157 129497995354942887740171)
                  ·
                    rfl

theorem cell22_1134884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1134884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134884 prefixEnd_1134884 := by exact prefixLift 1134884
  have htrace : WordTrace (prefixWord ++ tailWord_1134884) baseStart_1134884 baseEnd_1134884 := by
    simpa [prefixWord, tailWord_1134884, baseEnd_1134884] using wordTrace_append hprefix tailTrace_1134884
  have hstable : (prefixWord ++ tailWord_1134884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134884).length < 2 ^ (prefixWord ++ tailWord_1134884).sum := by decide
  have hdescent : baseEnd_1134884 < baseStart_1134884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134888 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1134888 : Nat := 118140960795 + 1134888 * 2 ^ 59
def prefixEnd_1134888 : Nat := 4983230072969 + 3 ^ 40 * 1134888 * 2
def baseEnd_1134888 : Nat := 388495355346573986120501

theorem tailTrace_1134888 : CollatzResearch.WordTrace tailWord_1134888 prefixEnd_1134888 388495355346573986120501 := by
  unfold tailWord_1134888
  simp only [CollatzResearch.WordTrace]
  refine ⟨20696382956251037142218659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27595177275001382856291545 20696382956251037142218659)
  ·
    refine ⟨31044574434376555713327989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20696382956251037142218659 31044574434376555713327989)
    ·
      refine ⟨2910428853222802098124499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31044574434376555713327989 2910428853222802098124499)
      ·
        refine ⟨4365643279834203147186749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910428853222802098124499 4365643279834203147186749)
        ·
          refine ⟨1637116229937826180195031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4365643279834203147186749 1637116229937826180195031)
          ·
            refine ⟨2455674344906739270292547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637116229937826180195031 2455674344906739270292547)
            ·
              refine ⟨3683511517360108905438821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455674344906739270292547 3683511517360108905438821)
              ·
                refine ⟨690658409505020419769779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3683511517360108905438821 690658409505020419769779)
                ·
                  refine ⟨1035987614257530629654669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690658409505020419769779 1035987614257530629654669)
                  ·
                    refine ⟨388495355346573986120501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035987614257530629654669 388495355346573986120501)
                    ·
                      rfl

theorem cell22_1134888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1134888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134888 prefixEnd_1134888 := by exact prefixLift 1134888
  have htrace : WordTrace (prefixWord ++ tailWord_1134888) baseStart_1134888 baseEnd_1134888 := by
    simpa [prefixWord, tailWord_1134888, baseEnd_1134888] using wordTrace_append hprefix tailTrace_1134888
  have hstable : (prefixWord ++ tailWord_1134888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134888).length < 2 ^ (prefixWord ++ tailWord_1134888).sum := by decide
  have hdescent : baseEnd_1134888 < baseStart_1134888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134929 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 4]
def baseStart_1134929 : Nat := 118140960795 + 1134929 * 2 ^ 59
def prefixEnd_1134929 : Nat := 4983230072969 + 3 ^ 40 * 1134929 * 2
def baseEnd_1134929 : Nat := 129503130161487848615125

theorem tailTrace_1134929 : CollatzResearch.WordTrace tailWord_1134929 prefixEnd_1134929 129503130161487848615125 := by
  unfold tailWord_1134929
  simp only [CollatzResearch.WordTrace]
  refine ⟨41394261305353538286679841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27596174203569025524453227 41394261305353538286679841)
  ·
    refine ⟨31045695979015153715009881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41394261305353538286679841 31045695979015153715009881)
    ·
      refine ⟨23284271984261365286257411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31045695979015153715009881 23284271984261365286257411)
      ·
        refine ⟨34926407976392047929386117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23284271984261365286257411 34926407976392047929386117)
        ·
          refine ⟨6548701495573508986759897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34926407976392047929386117 6548701495573508986759897)
          ·
            refine ⟨4911526121680131740069923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6548701495573508986759897 4911526121680131740069923)
            ·
              refine ⟨7367289182520197610104885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911526121680131740069923 7367289182520197610104885)
              ·
                refine ⟨690683360861268525947333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7367289182520197610104885 690683360861268525947333)
                ·
                  refine ⟨129503130161487848615125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690683360861268525947333 129503130161487848615125)
                  ·
                    rfl

theorem cell22_1134929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_1134929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134929 prefixEnd_1134929 := by exact prefixLift 1134929
  have htrace : WordTrace (prefixWord ++ tailWord_1134929) baseStart_1134929 baseEnd_1134929 := by
    simpa [prefixWord, tailWord_1134929, baseEnd_1134929] using wordTrace_append hprefix tailTrace_1134929
  have hstable : (prefixWord ++ tailWord_1134929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134929).length < 2 ^ (prefixWord ++ tailWord_1134929).sum := by decide
  have hdescent : baseEnd_1134929 < baseStart_1134929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134946 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1134946 : Nat := 118140960795 + 1134946 * 2 ^ 59
def prefixEnd_1134946 : Nat := 4983230072969 + 3 ^ 40 * 1134946 * 2
def baseEnd_1134946 : Nat := 129505069977293722723441

theorem tailTrace_1134946 : CollatzResearch.WordTrace tailWord_1134946 prefixEnd_1134946 129505069977293722723441 := by
  unfold tailWord_1134946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348720336572987547512173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27596587564194633460032461 10348720336572987547512173)
  ·
    refine ⟨3880770126214870330317065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10348720336572987547512173 3880770126214870330317065)
    ·
      refine ⟨2910577594661152747737799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3880770126214870330317065 2910577594661152747737799)
      ·
        refine ⟨4365866391991729121606699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910577594661152747737799 4365866391991729121606699)
        ·
          refine ⟨6548799587987593682410049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365866391991729121606699 6548799587987593682410049)
          ·
            refine ⟨4911599690990695261807537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6548799587987593682410049 4911599690990695261807537)
            ·
              refine ⟨3683699768243021446355653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911599690990695261807537 3683699768243021446355653)
              ·
                refine ⟨690693706545566521191685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3683699768243021446355653 690693706545566521191685)
                ·
                  refine ⟨129505069977293722723441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690693706545566521191685 129505069977293722723441)
                  ·
                    rfl

theorem cell22_1134946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1134946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134946 prefixEnd_1134946 := by exact prefixLift 1134946
  have htrace : WordTrace (prefixWord ++ tailWord_1134946) baseStart_1134946 baseEnd_1134946 := by
    simpa [prefixWord, tailWord_1134946, baseEnd_1134946] using wordTrace_append hprefix tailTrace_1134946
  have hstable : (prefixWord ++ tailWord_1134946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134946).length < 2 ^ (prefixWord ++ tailWord_1134946).sum := by decide
  have hdescent : baseEnd_1134946 < baseStart_1134946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134957 : List Nat := [1, 5, 1, 1, 1, 2, 2, 9]
def baseStart_1134957 : Nat := 118140960795 + 1134957 * 2 ^ 59
def prefixEnd_1134957 : Nat := 4983230072969 + 3 ^ 40 * 1134957 * 2
def baseEnd_1134957 : Nat := 43168775050742311793921

theorem tailTrace_1134957 : CollatzResearch.WordTrace tailWord_1134957 prefixEnd_1134957 43168775050742311793921 := by
  unfold tailWord_1134957
  simp only [CollatzResearch.WordTrace]
  refine ⟨41395282549252099068699125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27596855032834732712466083 41395282549252099068699125)
  ·
    refine ⟨3880807738992384287690543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41395282549252099068699125 3880807738992384287690543)
    ·
      refine ⟨5821211608488576431535815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880807738992384287690543 5821211608488576431535815)
      ·
        refine ⟨8731817412732864647303723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821211608488576431535815 8731817412732864647303723)
        ·
          refine ⟨13097726119099296970955585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731817412732864647303723 13097726119099296970955585)
          ·
            refine ⟨9823294589324472728216689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13097726119099296970955585 9823294589324472728216689)
            ·
              refine ⟨7367470941993354546162517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9823294589324472728216689 7367470941993354546162517)
              ·
                refine ⟨43168775050742311793921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7367470941993354546162517 43168775050742311793921)
                ·
                  rfl

theorem cell22_1134957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 9].length) (baseStart_1134957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1134957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1134957 prefixEnd_1134957 := by exact prefixLift 1134957
  have htrace : WordTrace (prefixWord ++ tailWord_1134957) baseStart_1134957 baseEnd_1134957 := by
    simpa [prefixWord, tailWord_1134957, baseEnd_1134957] using wordTrace_append hprefix tailTrace_1134957
  have hstable : (prefixWord ++ tailWord_1134957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134957).length < 2 ^ (prefixWord ++ tailWord_1134957).sum := by decide
  have hdescent : baseEnd_1134957 < baseStart_1134957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135017 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1135017 : Nat := 118140960795 + 1135017 * 2 ^ 59
def prefixEnd_1135017 : Nat := 4983230072969 + 3 ^ 40 * 1135017 * 2
def baseEnd_1135017 : Nat := 388539514682860649645105

theorem tailTrace_1135017 : CollatzResearch.WordTrace tailWord_1135017 prefixEnd_1135017 388539514682860649645105 := by
  unfold tailWord_1135017
  simp only [CollatzResearch.WordTrace]
  refine ⟨41397470929034729315883305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27598313952689819543922203 41397470929034729315883305)
  ·
    refine ⟨31048103196776046986912479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41397470929034729315883305 31048103196776046986912479)
    ·
      refine ⟨46572154795164070480368719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31048103196776046986912479 46572154795164070480368719)
      ·
        refine ⟨69858232192746105720553079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46572154795164070480368719 69858232192746105720553079)
        ·
          refine ⟨104787348289119158580829619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69858232192746105720553079 104787348289119158580829619)
          ·
            refine ⟨157181022433678737871244429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104787348289119158580829619 157181022433678737871244429)
            ·
              refine ⟨58942883412629526701716661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157181022433678737871244429 58942883412629526701716661)
              ·
                refine ⟨5525895319934018128285937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58942883412629526701716661 5525895319934018128285937)
                ·
                  refine ⟨4144421489950513596214453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5525895319934018128285937 4144421489950513596214453)
                  ·
                    refine ⟨388539514682860649645105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4144421489950513596214453 388539514682860649645105)
                    ·
                      rfl

theorem cell22_1135017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1135017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135017 prefixEnd_1135017 := by exact prefixLift 1135017
  have htrace : WordTrace (prefixWord ++ tailWord_1135017) baseStart_1135017 baseEnd_1135017 := by
    simpa [prefixWord, tailWord_1135017, baseEnd_1135017] using wordTrace_append hprefix tailTrace_1135017
  have hstable : (prefixWord ++ tailWord_1135017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135017).length < 2 ^ (prefixWord ++ tailWord_1135017).sum := by decide
  have hdescent : baseEnd_1135017 < baseStart_1135017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135049 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_1135049 : Nat := 118140960795 + 1135049 * 2 ^ 59
def prefixEnd_1135049 : Nat := 4983230072969 + 3 ^ 40 * 1135049 * 2
def baseEnd_1135049 : Nat := 388550468936823232845007

theorem tailTrace_1135049 : CollatzResearch.WordTrace tailWord_1135049 prefixEnd_1135049 388550468936823232845007 := by
  unfold tailWord_1135049
  simp only [CollatzResearch.WordTrace]
  refine ⟨41398638064918798781048201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27599092043279199187365467 41398638064918798781048201)
  ·
    refine ⟨31048978548689099085786151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41398638064918798781048201 31048978548689099085786151)
    ·
      refine ⟨46573467823033648628679227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31048978548689099085786151 46573467823033648628679227)
      ·
        refine ⟨69860201734550472943018841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46573467823033648628679227 69860201734550472943018841)
        ·
          refine ⟨52395151300912854707264131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69860201734550472943018841 52395151300912854707264131)
          ·
            refine ⟨78592726951369282060896197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52395151300912854707264131 78592726951369282060896197)
            ·
              refine ⟨14736136303381740386418037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78592726951369282060896197 14736136303381740386418037)
              ·
                refine ⟨1381512778442038161226691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14736136303381740386418037 1381512778442038161226691)
                ·
                  refine ⟨2072269167663057241840037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381512778442038161226691 2072269167663057241840037)
                  ·
                    refine ⟨388550468936823232845007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2072269167663057241840037 388550468936823232845007)
                    ·
                      rfl

theorem cell22_1135049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_1135049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135049 prefixEnd_1135049 := by exact prefixLift 1135049
  have htrace : WordTrace (prefixWord ++ tailWord_1135049) baseStart_1135049 baseEnd_1135049 := by
    simpa [prefixWord, tailWord_1135049, baseEnd_1135049] using wordTrace_append hprefix tailTrace_1135049
  have hstable : (prefixWord ++ tailWord_1135049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135049).length < 2 ^ (prefixWord ++ tailWord_1135049).sum := by decide
  have hdescent : baseEnd_1135049 < baseStart_1135049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135141 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_1135141 : Nat := 118140960795 + 1135141 * 2 ^ 59
def prefixEnd_1135141 : Nat := 4983230072969 + 3 ^ 40 * 1135141 * 2
def baseEnd_1135141 : Nat := 388581962416965659544725

theorem tailTrace_1135141 : CollatzResearch.WordTrace tailWord_1135141 prefixEnd_1135141 388581962416965659544725 := by
  unfold tailWord_1135141
  simp only [CollatzResearch.WordTrace]
  refine ⟨41401993580585498493397277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27601329053723665662264851 41401993580585498493397277)
  ·
    refine ⟨15525747592719561935023979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41401993580585498493397277 15525747592719561935023979)
    ·
      refine ⟨23288621389079342902535969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15525747592719561935023979 23288621389079342902535969)
      ·
        refine ⟨17466466041809507176901977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23288621389079342902535969 17466466041809507176901977)
        ·
          refine ⟨13099849531357130382676483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17466466041809507176901977 13099849531357130382676483)
          ·
            refine ⟨19649774297035695574014725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13099849531357130382676483 19649774297035695574014725)
            ·
              refine ⟨3684332680694192920127761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19649774297035695574014725 3684332680694192920127761)
              ·
                refine ⟨2763249510520644690095821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684332680694192920127761 2763249510520644690095821)
                ·
                  refine ⟨1036218566445241758785933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2763249510520644690095821 1036218566445241758785933)
                  ·
                    refine ⟨388581962416965659544725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1036218566445241758785933 388581962416965659544725)
                    ·
                      rfl

theorem cell22_1135141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_1135141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135141 prefixEnd_1135141 := by exact prefixLift 1135141
  have htrace : WordTrace (prefixWord ++ tailWord_1135141) baseStart_1135141 baseEnd_1135141 := by
    simpa [prefixWord, tailWord_1135141, baseEnd_1135141] using wordTrace_append hprefix tailTrace_1135141
  have hstable : (prefixWord ++ tailWord_1135141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135141).length < 2 ^ (prefixWord ++ tailWord_1135141).sum := by decide
  have hdescent : baseEnd_1135141 < baseStart_1135141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135143 : List Nat := [1, 1, 7, 2, 1, 1, 1, 8]
def baseStart_1135143 : Nat := 118140960795 + 1135143 * 2 ^ 59
def prefixEnd_1135143 : Nat := 4983230072969 + 3 ^ 40 * 1135143 * 2
def baseEnd_1135143 : Nat := 43175849673093146777191

theorem tailTrace_1135143 : CollatzResearch.WordTrace tailWord_1135143 prefixEnd_1135143 43175849673093146777191 := by
  unfold tailWord_1135143
  simp only [CollatzResearch.WordTrace]
  refine ⟨41402066526578252834970083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27601377684385501889980055 41402066526578252834970083)
  ·
    refine ⟨62103099789867379252455125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41402066526578252834970083 62103099789867379252455125)
    ·
      refine ⟨1455541401325016701229417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62103099789867379252455125 1455541401325016701229417)
      ·
        refine ⟨1091656050993762525922063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1455541401325016701229417 1091656050993762525922063)
        ·
          refine ⟨1637484076490643788883095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091656050993762525922063 1637484076490643788883095)
          ·
            refine ⟨2456226114735965683324643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637484076490643788883095 2456226114735965683324643)
            ·
              refine ⟨3684339172103948524986965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456226114735965683324643 3684339172103948524986965)
              ·
                refine ⟨43175849673093146777191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3684339172103948524986965 43175849673093146777191)
                ·
                  rfl

theorem cell22_1135143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 8].length) (baseStart_1135143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135143 prefixEnd_1135143 := by exact prefixLift 1135143
  have htrace : WordTrace (prefixWord ++ tailWord_1135143) baseStart_1135143 baseEnd_1135143 := by
    simpa [prefixWord, tailWord_1135143, baseEnd_1135143] using wordTrace_append hprefix tailTrace_1135143
  have hstable : (prefixWord ++ tailWord_1135143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135143).length < 2 ^ (prefixWord ++ tailWord_1135143).sum := by decide
  have hdescent : baseEnd_1135143 < baseStart_1135143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135149 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1135149 : Nat := 118140960795 + 1135149 * 2 ^ 59
def prefixEnd_1135149 : Nat := 4983230072969 + 3 ^ 40 * 1135149 * 2
def baseEnd_1135149 : Nat := 129528233660152101781567

theorem tailTrace_1135149 : CollatzResearch.WordTrace tailWord_1135149 prefixEnd_1135149 129528233660152101781567 := by
  unfold tailWord_1135149
  simp only [CollatzResearch.WordTrace]
  refine ⟨41402285364556515859688501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27601523576371010573125667 41402285364556515859688501)
  ·
    refine ⟨3881464252927173361845797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41402285364556515859688501 3881464252927173361845797)
    ·
      refine ⟨727774547423845005346087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3881464252927173361845797 727774547423845005346087)
      ·
        refine ⟨1091661821135767508019131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727774547423845005346087 1091661821135767508019131)
        ·
          refine ⟨1637492731703651262028697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091661821135767508019131 1637492731703651262028697)
          ·
            refine ⟨1228119548777738446521523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637492731703651262028697 1228119548777738446521523)
            ·
              refine ⟨1842179323166607669782285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228119548777738446521523 1842179323166607669782285)
              ·
                refine ⟨690817246187477876168357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842179323166607669782285 690817246187477876168357)
                ·
                  refine ⟨129528233660152101781567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690817246187477876168357 129528233660152101781567)
                  ·
                    rfl

theorem cell22_1135149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1135149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135149 prefixEnd_1135149 := by exact prefixLift 1135149
  have htrace : WordTrace (prefixWord ++ tailWord_1135149) baseStart_1135149 baseEnd_1135149 := by
    simpa [prefixWord, tailWord_1135149, baseEnd_1135149] using wordTrace_append hprefix tailTrace_1135149
  have hstable : (prefixWord ++ tailWord_1135149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135149).length < 2 ^ (prefixWord ++ tailWord_1135149).sum := by decide
  have hdescent : baseEnd_1135149 < baseStart_1135149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135154 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1135154 : Nat := 118140960795 + 1135154 * 2 ^ 59
def prefixEnd_1135154 : Nat := 4983230072969 + 3 ^ 40 * 1135154 * 2
def baseEnd_1135154 : Nat := 129528804194212652989895

theorem tailTrace_1135154 : CollatzResearch.WordTrace tailWord_1135154 prefixEnd_1135154 129528804194212652989895 := by
  unfold tailWord_1135154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350616932384600428405129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27601645153025601142413677 10350616932384600428405129)
  ·
    refine ⟨7762962699288450321303847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10350616932384600428405129 7762962699288450321303847)
    ·
      refine ⟨11644444048932675481955771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7762962699288450321303847 11644444048932675481955771)
      ·
        refine ⟨17466666073399013222933657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644444048932675481955771 17466666073399013222933657)
        ·
          refine ⟨13099999555049259917200243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17466666073399013222933657 13099999555049259917200243)
          ·
            refine ⟨19649999332573889875800365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13099999555049259917200243 19649999332573889875800365)
            ·
              refine ⟨7368749749715208703425137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19649999332573889875800365 7368749749715208703425137)
              ·
                refine ⟨5526562312286406527568853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7368749749715208703425137 5526562312286406527568853)
                ·
                  refine ⟨129528804194212652989895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5526562312286406527568853 129528804194212652989895)
                  ·
                    rfl

theorem cell22_1135154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1135154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135154 prefixEnd_1135154 := by exact prefixLift 1135154
  have htrace : WordTrace (prefixWord ++ tailWord_1135154) baseStart_1135154 baseEnd_1135154 := by
    simpa [prefixWord, tailWord_1135154, baseEnd_1135154] using wordTrace_append hprefix tailTrace_1135154
  have hstable : (prefixWord ++ tailWord_1135154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135154).length < 2 ^ (prefixWord ++ tailWord_1135154).sum := by decide
  have hdescent : baseEnd_1135154 < baseStart_1135154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135188 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1135188 : Nat := 118140960795 + 1135188 * 2 ^ 59
def prefixEnd_1135188 : Nat := 4983230072969 + 3 ^ 40 * 1135188 * 2
def baseEnd_1135188 : Nat := 129532683825824401206527

theorem tailTrace_1135188 : CollatzResearch.WordTrace tailWord_1135188 prefixEnd_1135188 129532683825824401206527 := by
  unfold tailWord_1135188
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701853905707612760179109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27602471874276817013572145 20701853905707612760179109)
  ·
    refine ⟨3881597607320177392533583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20701853905707612760179109 3881597607320177392533583)
    ·
      refine ⟨5822396410980266088800375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3881597607320177392533583 5822396410980266088800375)
      ·
        refine ⟨8733594616470399133200563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822396410980266088800375 8733594616470399133200563)
        ·
          refine ⟨13100391924705598699800845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733594616470399133200563 13100391924705598699800845)
          ·
            refine ⟨4912646971764599512425317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13100391924705598699800845 4912646971764599512425317)
            ·
              refine ⟨921121307205862408579747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4912646971764599512425317 921121307205862408579747)
              ·
                refine ⟨1381681960808793612869621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921121307205862408579747 1381681960808793612869621)
                ·
                  refine ⟨129532683825824401206527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1381681960808793612869621 129532683825824401206527)
                  ·
                    rfl

theorem cell22_1135188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1135188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135188 prefixEnd_1135188 := by exact prefixLift 1135188
  have htrace : WordTrace (prefixWord ++ tailWord_1135188) baseStart_1135188 baseEnd_1135188 := by
    simpa [prefixWord, tailWord_1135188, baseEnd_1135188] using wordTrace_append hprefix tailTrace_1135188
  have hstable : (prefixWord ++ tailWord_1135188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135188).length < 2 ^ (prefixWord ++ tailWord_1135188).sum := by decide
  have hdescent : baseEnd_1135188 < baseStart_1135188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135199 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 6]
def baseStart_1135199 : Nat := 118140960795 + 1135199 * 2 ^ 59
def prefixEnd_1135199 : Nat := 4983230072969 + 3 ^ 40 * 1135199 * 2
def baseEnd_1135199 : Nat := 129533939000757613864849

theorem tailTrace_1135199 : CollatzResearch.WordTrace tailWord_1135199 prefixEnd_1135199 129533939000757613864849 := by
  unfold tailWord_1135199
  simp only [CollatzResearch.WordTrace]
  refine ⟨41404109014375374399008651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27602739342916916266005767 41404109014375374399008651)
  ·
    refine ⟨62106163521563061598512977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41404109014375374399008651 62106163521563061598512977)
    ·
      refine ⟨46579622641172296198884733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62106163521563061598512977 46579622641172296198884733)
      ·
        refine ⟨17467358490439611074581775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46579622641172296198884733 17467358490439611074581775)
        ·
          refine ⟨26201037735659416611872663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17467358490439611074581775 26201037735659416611872663)
          ·
            refine ⟨39301556603489124917808995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26201037735659416611872663 39301556603489124917808995)
            ·
              refine ⟨58952334905233687376713493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39301556603489124917808995 58952334905233687376713493)
              ·
                refine ⟨2763390698682829095783445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58952334905233687376713493 2763390698682829095783445)
                ·
                  refine ⟨129533939000757613864849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2763390698682829095783445 129533939000757613864849)
                  ·
                    rfl

theorem cell22_1135199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_1135199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135199 prefixEnd_1135199 := by exact prefixLift 1135199
  have htrace : WordTrace (prefixWord ++ tailWord_1135199) baseStart_1135199 baseEnd_1135199 := by
    simpa [prefixWord, tailWord_1135199, baseEnd_1135199] using wordTrace_append hprefix tailTrace_1135199
  have hstable : (prefixWord ++ tailWord_1135199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135199).length < 2 ^ (prefixWord ++ tailWord_1135199).sum := by decide
  have hdescent : baseEnd_1135199 < baseStart_1135199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135201 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1135201 : Nat := 118140960795 + 1135201 * 2 ^ 59
def prefixEnd_1135201 : Nat := 4983230072969 + 3 ^ 40 * 1135201 * 2
def baseEnd_1135201 : Nat := 388602501643145503044541

theorem tailTrace_1135201 : CollatzResearch.WordTrace tailWord_1135201 prefixEnd_1135201 388602501643145503044541 := by
  unfold tailWord_1135201
  simp only [CollatzResearch.WordTrace]
  refine ⟨41404181960368128740581457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27602787973578752493720971 41404181960368128740581457)
  ·
    refine ⟨31053136470276096555436093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41404181960368128740581457 31053136470276096555436093)
    ·
      refine ⟨11644926176353536208288535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31053136470276096555436093 11644926176353536208288535)
      ·
        refine ⟨17467389264530304312432803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644926176353536208288535 17467389264530304312432803)
        ·
          refine ⟨26201083896795456468649205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17467389264530304312432803 26201083896795456468649205)
          ·
            refine ⟨2456351615324574043935863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26201083896795456468649205 2456351615324574043935863)
            ·
              refine ⟨3684527422986861065903795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456351615324574043935863 3684527422986861065903795)
              ·
                refine ⟨5526791134480291598855693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684527422986861065903795 5526791134480291598855693)
                ·
                  refine ⟨2072546675430109349570885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5526791134480291598855693 2072546675430109349570885)
                  ·
                    refine ⟨388602501643145503044541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2072546675430109349570885 388602501643145503044541)
                    ·
                      rfl

theorem cell22_1135201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1135201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135201 prefixEnd_1135201 := by exact prefixLift 1135201
  have htrace : WordTrace (prefixWord ++ tailWord_1135201) baseStart_1135201 baseEnd_1135201 := by
    simpa [prefixWord, tailWord_1135201, baseEnd_1135201] using wordTrace_append hprefix tailTrace_1135201
  have hstable : (prefixWord ++ tailWord_1135201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135201).length < 2 ^ (prefixWord ++ tailWord_1135201).sum := by decide
  have hdescent : baseEnd_1135201 < baseStart_1135201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135233 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 4]
def baseStart_1135233 : Nat := 118140960795 + 1135233 * 2 ^ 59
def prefixEnd_1135233 : Nat := 4983230072969 + 3 ^ 40 * 1135233 * 2
def baseEnd_1135233 : Nat := 129537818632369362081481

theorem tailTrace_1135233 : CollatzResearch.WordTrace tailWord_1135233 prefixEnd_1135233 129537818632369362081481 := by
  unfold tailWord_1135233
  simp only [CollatzResearch.WordTrace]
  refine ⟨41405349096252198205746353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27603566064168132137164235 41405349096252198205746353)
  ·
    refine ⟨31054011822189148654309765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41405349096252198205746353 31054011822189148654309765)
    ·
      refine ⟨5822627216660465372683081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31054011822189148654309765 5822627216660465372683081)
      ·
        refine ⟨4366970412495349029512311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5822627216660465372683081 4366970412495349029512311)
        ·
          refine ⟨6550455618743023544268467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366970412495349029512311 6550455618743023544268467)
          ·
            refine ⟨9825683428114535316402701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550455618743023544268467 9825683428114535316402701)
            ·
              refine ⟨3684631285542950743651013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9825683428114535316402701 3684631285542950743651013)
              ·
                refine ⟨690868366039303264434565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3684631285542950743651013 690868366039303264434565)
                ·
                  refine ⟨129537818632369362081481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690868366039303264434565 129537818632369362081481)
                  ·
                    rfl

theorem cell22_1135233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_1135233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135233 prefixEnd_1135233 := by exact prefixLift 1135233
  have htrace : WordTrace (prefixWord ++ tailWord_1135233) baseStart_1135233 baseEnd_1135233 := by
    simpa [prefixWord, tailWord_1135233, baseEnd_1135233] using wordTrace_append hprefix tailTrace_1135233
  have hstable : (prefixWord ++ tailWord_1135233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135233).length < 2 ^ (prefixWord ++ tailWord_1135233).sum := by decide
  have hdescent : baseEnd_1135233 < baseStart_1135233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135244 : List Nat := [2, 2, 1, 2, 1, 1, 2, 11]
def baseStart_1135244 : Nat := 118140960795 + 1135244 * 2 ^ 59
def prefixEnd_1135244 : Nat := 4983230072969 + 3 ^ 40 * 1135244 * 2
def baseEnd_1135244 : Nat := 43179691269100858246601

theorem tailTrace_1135244 : CollatzResearch.WordTrace tailWord_1135244 prefixEnd_1135244 43179691269100858246601 := by
  unfold tailWord_1135244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20702875149606173542198393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27603833532808231389597857 20702875149606173542198393)
  ·
    refine ⟨15527156362204630156648795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20702875149606173542198393 15527156362204630156648795)
    ·
      refine ⟨23290734543306945234973193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15527156362204630156648795 23290734543306945234973193)
      ·
        refine ⟨17468050907480208926229895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23290734543306945234973193 17468050907480208926229895)
        ·
          refine ⟨26202076361220313389344843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17468050907480208926229895 26202076361220313389344843)
          ·
            refine ⟨39303114541830470084017265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26202076361220313389344843 39303114541830470084017265)
            ·
              refine ⟨29477335906372852563012949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39303114541830470084017265 29477335906372852563012949)
              ·
                refine ⟨43179691269100858246601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29477335906372852563012949 43179691269100858246601)
                ·
                  rfl

theorem cell22_1135244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_1135244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135244 prefixEnd_1135244 := by exact prefixLift 1135244
  have htrace : WordTrace (prefixWord ++ tailWord_1135244) baseStart_1135244 baseEnd_1135244 := by
    simpa [prefixWord, tailWord_1135244, baseEnd_1135244] using wordTrace_append hprefix tailTrace_1135244
  have hstable : (prefixWord ++ tailWord_1135244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135244).length < 2 ^ (prefixWord ++ tailWord_1135244).sum := by decide
  have hdescent : baseEnd_1135244 < baseStart_1135244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135246 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1135246 : Nat := 118140960795 + 1135246 * 2 ^ 59
def prefixEnd_1135246 : Nat := 4983230072969 + 3 ^ 40 * 1135246 * 2
def baseEnd_1135246 : Nat := 388617906062780385669403

theorem tailTrace_1135246 : CollatzResearch.WordTrace tailWord_1135246 prefixEnd_1135246 388617906062780385669403 := by
  unfold tailWord_1135246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175727905650637678246199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27603882163470067617313061 5175727905650637678246199)
  ·
    refine ⟨7763591858475956517369299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5175727905650637678246199 7763591858475956517369299)
    ·
      refine ⟨11645387787713934776053949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763591858475956517369299 11645387787713934776053949)
      ·
        refine ⟨4367020420392725541020231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11645387787713934776053949 4367020420392725541020231)
        ·
          refine ⟨6550530630589088311530347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367020420392725541020231 6550530630589088311530347)
          ·
            refine ⟨9825795945883632467295521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550530630589088311530347 9825795945883632467295521)
            ·
              refine ⟨7369346959412724350471641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9825795945883632467295521 7369346959412724350471641)
              ·
                refine ⟨5527010219559543262853731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7369346959412724350471641 5527010219559543262853731)
                ·
                  refine ⟨8290515329339314894280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527010219559543262853731 8290515329339314894280597)
                  ·
                    refine ⟨388617906062780385669403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8290515329339314894280597 388617906062780385669403)
                    ·
                      rfl

theorem cell22_1135246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1135246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135246 prefixEnd_1135246 := by exact prefixLift 1135246
  have htrace : WordTrace (prefixWord ++ tailWord_1135246) baseStart_1135246 baseEnd_1135246 := by
    simpa [prefixWord, tailWord_1135246, baseEnd_1135246] using wordTrace_append hprefix tailTrace_1135246
  have hstable : (prefixWord ++ tailWord_1135246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135246).length < 2 ^ (prefixWord ++ tailWord_1135246).sum := by decide
  have hdescent : baseEnd_1135246 < baseStart_1135246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135278 : List Nat := [4, 1, 4, 1, 1, 2, 9]
def baseStart_1135278 : Nat := 118140960795 + 1135278 * 2 ^ 59
def prefixEnd_1135278 : Nat := 4983230072969 + 3 ^ 40 * 1135278 * 2
def baseEnd_1135278 : Nat := 14393661493212702550715

theorem tailTrace_1135278 : CollatzResearch.WordTrace tailWord_1135278 prefixEnd_1135278 14393661493212702550715 := by
  unfold tailWord_1135278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175873797636146361391811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27604660254059447260756325 5175873797636146361391811)
  ·
    refine ⟨7763810696454219542087717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5175873797636146361391811 7763810696454219542087717)
    ·
      refine ⟨1455714505585166164141447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7763810696454219542087717 1455714505585166164141447)
      ·
        refine ⟨2183571758377749246212171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455714505585166164141447 2183571758377749246212171)
        ·
          refine ⟨3275357637566623869318257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183571758377749246212171 3275357637566623869318257)
          ·
            refine ⟨2456518228174967901988693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275357637566623869318257 2456518228174967901988693)
            ·
              refine ⟨14393661493212702550715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2456518228174967901988693 14393661493212702550715)
              ·
                rfl

theorem cell22_1135278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 9].length) (baseStart_1135278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135278 prefixEnd_1135278 := by exact prefixLift 1135278
  have htrace : WordTrace (prefixWord ++ tailWord_1135278) baseStart_1135278 baseEnd_1135278 := by
    simpa [prefixWord, tailWord_1135278, baseEnd_1135278] using wordTrace_append hprefix tailTrace_1135278
  have hstable : (prefixWord ++ tailWord_1135278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135278).length < 2 ^ (prefixWord ++ tailWord_1135278).sum := by decide
  have hdescent : baseEnd_1135278 < baseStart_1135278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135293 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1135293 : Nat := 118140960795 + 1135293 * 2 ^ 59
def prefixEnd_1135293 : Nat := 4983230072969 + 3 ^ 40 * 1135293 * 2
def baseEnd_1135293 : Nat := 388633995123287929744259

theorem tailTrace_1135293 : CollatzResearch.WordTrace tailWord_1135293 prefixEnd_1135293 388633995123287929744259 := by
  unfold tailWord_1135293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41407537476034828452930533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27605024984023218968620355 41407537476034828452930533)
  ·
    refine ⟨7763913276756530334924475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41407537476034828452930533 7763913276756530334924475)
    ·
      refine ⟨11645869915134795502386713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763913276756530334924475 11645869915134795502386713)
      ·
        refine ⟨8734402436351096626790035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11645869915134795502386713 8734402436351096626790035)
        ·
          refine ⟨13101603654526644940185053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8734402436351096626790035 13101603654526644940185053)
          ·
            refine ⟨4913101370447491852569395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13101603654526644940185053 4913101370447491852569395)
            ·
              refine ⟨7369652055671237778854093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913101370447491852569395 7369652055671237778854093)
              ·
                refine ⟨2763619520876714167070285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7369652055671237778854093 2763619520876714167070285)
                ·
                  refine ⟨1036357320328767812651357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2763619520876714167070285 1036357320328767812651357)
                  ·
                    refine ⟨388633995123287929744259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1036357320328767812651357 388633995123287929744259)
                    ·
                      rfl

theorem cell22_1135293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1135293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135293 prefixEnd_1135293 := by exact prefixLift 1135293
  have htrace : WordTrace (prefixWord ++ tailWord_1135293) baseStart_1135293 baseEnd_1135293 := by
    simpa [prefixWord, tailWord_1135293, baseEnd_1135293] using wordTrace_append hprefix tailTrace_1135293
  have hstable : (prefixWord ++ tailWord_1135293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135293).length < 2 ^ (prefixWord ++ tailWord_1135293).sum := by decide
  have hdescent : baseEnd_1135293 < baseStart_1135293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135327 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 1, 3]
def baseStart_1135327 : Nat := 118140960795 + 1135327 * 2 ^ 59
def prefixEnd_1135327 : Nat := 4983230072969 + 3 ^ 40 * 1135327 * 2
def baseEnd_1135327 : Nat := 388645634018123174394155

theorem tailTrace_1135327 : CollatzResearch.WordTrace tailWord_1135327 prefixEnd_1135327 388645634018123174394155 := by
  unfold tailWord_1135327
  simp only [CollatzResearch.WordTrace]
  refine ⟨41408777557911652259668235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27605851705274434839778823 41408777557911652259668235)
  ·
    refine ⟨62113166336867478389502353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41408777557911652259668235 62113166336867478389502353)
    ·
      refine ⟨46584874752650608792126765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62113166336867478389502353 46584874752650608792126765)
      ·
        refine ⟨17469328032243978297047537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46584874752650608792126765 17469328032243978297047537)
        ·
          refine ⟨13101996024182983722785653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17469328032243978297047537 13101996024182983722785653)
          ·
            refine ⟨1228312127267154724011155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13101996024182983722785653 1228312127267154724011155)
            ·
              refine ⟨1842468190900732086016733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228312127267154724011155 1842468190900732086016733)
              ·
                refine ⟨690925571587774532256275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842468190900732086016733 690925571587774532256275)
                ·
                  refine ⟨1036388357381661798384413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690925571587774532256275 1036388357381661798384413)
                  ·
                    refine ⟨388645634018123174394155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1036388357381661798384413 388645634018123174394155)
                    ·
                      rfl

theorem cell22_1135327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_1135327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135327 prefixEnd_1135327 := by exact prefixLift 1135327
  have htrace : WordTrace (prefixWord ++ tailWord_1135327) baseStart_1135327 baseEnd_1135327 := by
    simpa [prefixWord, tailWord_1135327, baseEnd_1135327] using wordTrace_append hprefix tailTrace_1135327
  have hstable : (prefixWord ++ tailWord_1135327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135327).length < 2 ^ (prefixWord ++ tailWord_1135327).sum := by decide
  have hdescent : baseEnd_1135327 < baseStart_1135327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135396 : List Nat := [2, 3, 1, 3, 13]
def baseStart_1135396 : Nat := 118140960795 + 1135396 * 2 ^ 59
def prefixEnd_1135396 : Nat := 4983230072969 + 3 ^ 40 * 1135396 * 2
def baseEnd_1135396 : Nat := 1599461951144979400901

theorem tailTrace_1135396 : CollatzResearch.WordTrace tailWord_1135396 prefixEnd_1135396 1599461951144979400901 := by
  unfold tailWord_1135396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20705647097330838521965021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27607529463107784695953361 20705647097330838521965021)
  ·
    refine ⟨7764617661499064445736883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20705647097330838521965021 7764617661499064445736883)
    ·
      refine ⟨11646926492248596668605325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7764617661499064445736883 11646926492248596668605325)
      ·
        refine ⟨4367597434593223750726997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11646926492248596668605325 4367597434593223750726997)
        ·
          refine ⟨1599461951144979400901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4367597434593223750726997 1599461951144979400901)
          ·
            rfl

theorem cell22_1135396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 13].length) (baseStart_1135396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135396 prefixEnd_1135396 := by exact prefixLift 1135396
  have htrace : WordTrace (prefixWord ++ tailWord_1135396) baseStart_1135396 baseEnd_1135396 := by
    simpa [prefixWord, tailWord_1135396, baseEnd_1135396] using wordTrace_append hprefix tailTrace_1135396
  have hstable : (prefixWord ++ tailWord_1135396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135396).length < 2 ^ (prefixWord ++ tailWord_1135396).sum := by decide
  have hdescent : baseEnd_1135396 < baseStart_1135396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135413 : List Nat := [1, 3, 3, 1, 3, 1, 3, 7]
def baseStart_1135413 : Nat := 118140960795 + 1135413 * 2 ^ 59
def prefixEnd_1135413 : Nat := 4983230072969 + 3 ^ 40 * 1135413 * 2
def baseEnd_1135413 : Nat := 43186119286183068527099

theorem tailTrace_1135413 : CollatzResearch.WordTrace tailWord_1135413 prefixEnd_1135413 43186119286183068527099 := by
  unfold tailWord_1135413
  simp only [CollatzResearch.WordTrace]
  refine ⟨41411914235600088947298893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27607942823733392631532595 41411914235600088947298893)
  ·
    refine ⟨15529467838350033355237085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41411914235600088947298893 15529467838350033355237085)
    ·
      refine ⟨5823550439381262508213907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15529467838350033355237085 5823550439381262508213907)
      ·
        refine ⟨8735325659071893762320861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5823550439381262508213907 8735325659071893762320861)
        ·
          refine ⟨3275747122151960160870323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735325659071893762320861 3275747122151960160870323)
          ·
            refine ⟨4913620683227940241305485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275747122151960160870323 4913620683227940241305485)
            ·
              refine ⟨1842607756210477590489557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4913620683227940241305485 1842607756210477590489557)
              ·
                refine ⟨43186119286183068527099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1842607756210477590489557 43186119286183068527099)
                ·
                  rfl

theorem cell22_1135413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 7].length) (baseStart_1135413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135413 prefixEnd_1135413 := by exact prefixLift 1135413
  have htrace : WordTrace (prefixWord ++ tailWord_1135413) baseStart_1135413 baseEnd_1135413 := by
    simpa [prefixWord, tailWord_1135413, baseEnd_1135413] using wordTrace_append hprefix tailTrace_1135413
  have hstable : (prefixWord ++ tailWord_1135413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135413).length < 2 ^ (prefixWord ++ tailWord_1135413).sum := by decide
  have hdescent : baseEnd_1135413 < baseStart_1135413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135473 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1135473 : Nat := 118140960795 + 1135473 * 2 ^ 59
def prefixEnd_1135473 : Nat := 4983230072969 + 3 ^ 40 * 1135473 * 2
def baseEnd_1135473 : Nat := 388695612801827460243707

theorem tailTrace_1135473 : CollatzResearch.WordTrace tailWord_1135473 prefixEnd_1135473 388695612801827460243707 := by
  unfold tailWord_1135473
  simp only [CollatzResearch.WordTrace]
  refine ⟨41414102615382719194483073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27609401743588479462988715 41414102615382719194483073)
  ·
    refine ⟨31060576961537039395862305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41414102615382719194483073 31060576961537039395862305)
    ·
      refine ⟨23295432721152779546896729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31060576961537039395862305 23295432721152779546896729)
      ·
        refine ⟨17471574540864584660172547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23295432721152779546896729 17471574540864584660172547)
        ·
          refine ⟨26207361811296876990258821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17471574540864584660172547 26207361811296876990258821)
          ·
            refine ⟨4913880339618164435673529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26207361811296876990258821 4913880339618164435673529)
            ·
              refine ⟨3685410254713623326755147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913880339618164435673529 3685410254713623326755147)
              ·
                refine ⟨5528115382070434990132721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685410254713623326755147 5528115382070434990132721)
                ·
                  refine ⟨4146086536552826242599541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528115382070434990132721 4146086536552826242599541)
                  ·
                    refine ⟨388695612801827460243707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4146086536552826242599541 388695612801827460243707)
                    ·
                      rfl

theorem cell22_1135473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1135473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135473 prefixEnd_1135473 := by exact prefixLift 1135473
  have htrace : WordTrace (prefixWord ++ tailWord_1135473) baseStart_1135473 baseEnd_1135473 := by
    simpa [prefixWord, tailWord_1135473, baseEnd_1135473] using wordTrace_append hprefix tailTrace_1135473
  have hstable : (prefixWord ++ tailWord_1135473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135473).length < 2 ^ (prefixWord ++ tailWord_1135473).sum := by decide
  have hdescent : baseEnd_1135473 < baseStart_1135473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135520 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_1135520 : Nat := 118140960795 + 1135520 * 2 ^ 59
def prefixEnd_1135520 : Nat := 4983230072969 + 3 ^ 40 * 1135520 * 2
def baseEnd_1135520 : Nat := 129570567287445001439521

theorem tailTrace_1135520 : CollatzResearch.WordTrace tailWord_1135520 prefixEnd_1135520 129570567287445001439521 := by
  unfold tailWord_1135520
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707908423106223110722007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27610544564141630814296009 20707908423106223110722007)
  ·
    refine ⟨31061862634659334666083011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20707908423106223110722007 31061862634659334666083011)
    ·
      refine ⟨46592793951989001999124517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31061862634659334666083011 46592793951989001999124517)
      ·
        refine ⟨8736148865997937874835847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46592793951989001999124517 8736148865997937874835847)
        ·
          refine ⟨13104223298996906812253771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8736148865997937874835847 13104223298996906812253771)
          ·
            refine ⟨19656334948495360218380657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13104223298996906812253771 19656334948495360218380657)
            ·
              refine ⟨14742251211371520163785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19656334948495360218380657 14742251211371520163785493)
              ·
                refine ⟨691043025533040007677445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14742251211371520163785493 691043025533040007677445)
                ·
                  refine ⟨129570567287445001439521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691043025533040007677445 129570567287445001439521)
                  ·
                    rfl

theorem cell22_1135520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_1135520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135520 prefixEnd_1135520 := by exact prefixLift 1135520
  have htrace : WordTrace (prefixWord ++ tailWord_1135520) baseStart_1135520 baseEnd_1135520 := by
    simpa [prefixWord, tailWord_1135520, baseEnd_1135520] using wordTrace_append hprefix tailTrace_1135520
  have hstable : (prefixWord ++ tailWord_1135520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135520).length < 2 ^ (prefixWord ++ tailWord_1135520).sum := by decide
  have hdescent : baseEnd_1135520 < baseStart_1135520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135556 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1135556 : Nat := 118140960795 + 1135556 * 2 ^ 59
def prefixEnd_1135556 : Nat := 4983230072969 + 3 ^ 40 * 1135556 * 2
def baseEnd_1135556 : Nat := 388724025398042910418453

theorem tailTrace_1135556 : CollatzResearch.WordTrace tailWord_1135556 prefixEnd_1135556 388724025398042910418453 := by
  unfold tailWord_1135556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708564937041012184877261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27611419916054682913169681 20708564937041012184877261)
  ·
    refine ⟨7765711851390379569328973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20708564937041012184877261 7765711851390379569328973)
    ·
      refine ⟨2912141944271392338498365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7765711851390379569328973 2912141944271392338498365)
      ·
        refine ⟨1092053229101772126936887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2912141944271392338498365 1092053229101772126936887)
        ·
          refine ⟨1638079843652658190405331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092053229101772126936887 1638079843652658190405331)
          ·
            refine ⟨2457119765478987285607997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638079843652658190405331 2457119765478987285607997)
            ·
              refine ⟨921419912054620232102999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2457119765478987285607997 921419912054620232102999)
              ·
                refine ⟨1382129868081930348154499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921419912054620232102999 1382129868081930348154499)
                ·
                  refine ⟨2073194802122895522231749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382129868081930348154499 2073194802122895522231749)
                  ·
                    refine ⟨388724025398042910418453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073194802122895522231749 388724025398042910418453)
                    ·
                      rfl

theorem cell22_1135556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1135556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135556 prefixEnd_1135556 := by exact prefixLift 1135556
  have htrace : WordTrace (prefixWord ++ tailWord_1135556) baseStart_1135556 baseEnd_1135556 := by
    simpa [prefixWord, tailWord_1135556, baseEnd_1135556] using wordTrace_append hprefix tailTrace_1135556
  have hstable : (prefixWord ++ tailWord_1135556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135556).length < 2 ^ (prefixWord ++ tailWord_1135556).sum := by decide
  have hdescent : baseEnd_1135556 < baseStart_1135556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135608 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1135608 : Nat := 118140960795 + 1135608 * 2 ^ 59
def prefixEnd_1135608 : Nat := 4983230072969 + 3 ^ 40 * 1135608 * 2
def baseEnd_1135608 : Nat := 388741826060732108118293

theorem tailTrace_1135608 : CollatzResearch.WordTrace tailWord_1135608 prefixEnd_1135608 388741826060732108118293 := by
  unfold tailWord_1135608
  simp only [CollatzResearch.WordTrace]
  refine ⟨20709513234946818625323739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27612684313262424833764985 20709513234946818625323739)
  ·
    refine ⟨31064269852420227937985609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20709513234946818625323739 31064269852420227937985609)
    ·
      refine ⟨23298202389315170953489207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31064269852420227937985609 23298202389315170953489207)
      ·
        refine ⟨34947303583972756430233811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23298202389315170953489207 34947303583972756430233811)
        ·
          refine ⟨52420955375959134645350717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34947303583972756430233811 52420955375959134645350717)
          ·
            refine ⟨19657858265984675492006519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52420955375959134645350717 19657858265984675492006519)
            ·
              refine ⟨29486787398977013238009779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19657858265984675492006519 29486787398977013238009779)
              ·
                refine ⟨44230181098465519857014669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29486787398977013238009779 44230181098465519857014669)
                ·
                  refine ⟨16586317911924569946380501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44230181098465519857014669 16586317911924569946380501)
                  ·
                    refine ⟨388741826060732108118293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16586317911924569946380501 388741826060732108118293)
                    ·
                      rfl

theorem cell22_1135608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1135608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135608 prefixEnd_1135608 := by exact prefixLift 1135608
  have htrace : WordTrace (prefixWord ++ tailWord_1135608) baseStart_1135608 baseEnd_1135608 := by
    simpa [prefixWord, tailWord_1135608, baseEnd_1135608] using wordTrace_append hprefix tailTrace_1135608
  have hstable : (prefixWord ++ tailWord_1135608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135608).length < 2 ^ (prefixWord ++ tailWord_1135608).sum := by decide
  have hdescent : baseEnd_1135608 < baseStart_1135608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135627 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 5]
def baseStart_1135627 : Nat := 118140960795 + 1135627 * 2 ^ 59
def prefixEnd_1135627 : Nat := 4983230072969 + 3 ^ 40 * 1135627 * 2
def baseEnd_1135627 : Nat := 129582776716340797297745

theorem tailTrace_1135627 : CollatzResearch.WordTrace tailWord_1135627 prefixEnd_1135627 129582776716340797297745 := by
  unfold tailWord_1135627
  simp only [CollatzResearch.WordTrace]
  refine ⟨41419719456824803495589135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27613146304549868997059423 41419719456824803495589135)
  ·
    refine ⟨62129579185237205243383703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41419719456824803495589135 62129579185237205243383703)
    ·
      refine ⟨93194368777855807865075555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62129579185237205243383703 93194368777855807865075555)
      ·
        refine ⟨139791553166783711797613333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93194368777855807865075555 139791553166783711797613333)
        ·
          refine ⟨6552729054692986490513125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139791553166783711797613333 6552729054692986490513125)
          ·
            refine ⟨1228636697754934966971211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6552729054692986490513125 1228636697754934966971211)
            ·
              refine ⟨1842955046632402450456817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228636697754934966971211 1842955046632402450456817)
              ·
                refine ⟨1382216284974301837842613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842955046632402450456817 1382216284974301837842613)
                ·
                  refine ⟨129582776716340797297745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382216284974301837842613 129582776716340797297745)
                  ·
                    rfl

theorem cell22_1135627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 5].length) (baseStart_1135627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135627 prefixEnd_1135627 := by exact prefixLift 1135627
  have htrace : WordTrace (prefixWord ++ tailWord_1135627) baseStart_1135627 baseEnd_1135627 := by
    simpa [prefixWord, tailWord_1135627, baseEnd_1135627] using wordTrace_append hprefix tailTrace_1135627
  have hstable : (prefixWord ++ tailWord_1135627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135627).length < 2 ^ (prefixWord ++ tailWord_1135627).sum := by decide
  have hdescent : baseEnd_1135627 < baseStart_1135627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135644 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_1135644 : Nat := 118140960795 + 1135644 * 2 ^ 59
def prefixEnd_1135644 : Nat := 4983230072969 + 3 ^ 40 * 1135644 * 2
def baseEnd_1135644 : Nat := 129584716532146671406061

theorem tailTrace_1135644 : CollatzResearch.WordTrace tailWord_1135644 prefixEnd_1135644 129584716532146671406061 := by
  unfold tailWord_1135644
  simp only [CollatzResearch.WordTrace]
  refine ⟨20710169748881607699478993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27613559665175476932638657 20710169748881607699478993)
  ·
    refine ⟨15532627311661205774609245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20710169748881607699478993 15532627311661205774609245)
    ·
      refine ⟨5824735241872952165478467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15532627311661205774609245 5824735241872952165478467)
      ·
        refine ⟨8737102862809428248217701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824735241872952165478467 8737102862809428248217701)
        ·
          refine ⟨1638206786776767796540819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8737102862809428248217701 1638206786776767796540819)
          ·
            refine ⟨2457310180165151694811229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638206786776767796540819 2457310180165151694811229)
            ·
              refine ⟨921491317561931885554211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2457310180165151694811229 921491317561931885554211)
              ·
                refine ⟨1382236976342897828331317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921491317561931885554211 1382236976342897828331317)
                ·
                  refine ⟨129584716532146671406061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382236976342897828331317 129584716532146671406061)
                  ·
                    rfl

theorem cell22_1135644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_1135644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135644 prefixEnd_1135644 := by exact prefixLift 1135644
  have htrace : WordTrace (prefixWord ++ tailWord_1135644) baseStart_1135644 baseEnd_1135644 := by
    simpa [prefixWord, tailWord_1135644, baseEnd_1135644] using wordTrace_append hprefix tailTrace_1135644
  have hstable : (prefixWord ++ tailWord_1135644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135644).length < 2 ^ (prefixWord ++ tailWord_1135644).sum := by decide
  have hdescent : baseEnd_1135644 < baseStart_1135644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135685 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1135685 : Nat := 118140960795 + 1135685 * 2 ^ 59
def prefixEnd_1135685 : Nat := 4983230072969 + 3 ^ 40 * 1135685 * 2
def baseEnd_1135685 : Nat := 388768184734329573943057

theorem tailTrace_1135685 : CollatzResearch.WordTrace tailWord_1135685 prefixEnd_1135685 388768184734329573943057 := by
  unfold tailWord_1135685
  simp only [CollatzResearch.WordTrace]
  refine ⟨41421834890614679401200509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27614556593743119600800339 41421834890614679401200509)
  ·
    refine ⟨15533188083980504775450191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41421834890614679401200509 15533188083980504775450191)
    ·
      refine ⟨23299782125970757163175287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15533188083980504775450191 23299782125970757163175287)
      ·
        refine ⟨34949673188956135744762931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23299782125970757163175287 34949673188956135744762931)
        ·
          refine ⟨52424509783434203617144397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34949673188956135744762931 52424509783434203617144397)
          ·
            refine ⟨19659191168787826356429149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52424509783434203617144397 19659191168787826356429149)
            ·
              refine ⟨7372196688295434883660931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19659191168787826356429149 7372196688295434883660931)
              ·
                refine ⟨11058295032443152325491397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7372196688295434883660931 11058295032443152325491397)
                ·
                  refine ⟨2073430318583091061029637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11058295032443152325491397 2073430318583091061029637)
                  ·
                    refine ⟨388768184734329573943057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073430318583091061029637 388768184734329573943057)
                    ·
                      rfl

theorem cell22_1135685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1135685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135685 prefixEnd_1135685 := by exact prefixLift 1135685
  have htrace : WordTrace (prefixWord ++ tailWord_1135685) baseStart_1135685 baseEnd_1135685 := by
    simpa [prefixWord, tailWord_1135685, baseEnd_1135685] using wordTrace_append hprefix tailTrace_1135685
  have hstable : (prefixWord ++ tailWord_1135685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135685).length < 2 ^ (prefixWord ++ tailWord_1135685).sum := by decide
  have hdescent : baseEnd_1135685 < baseStart_1135685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135687 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1135687 : Nat := 118140960795 + 1135687 * 2 ^ 59
def prefixEnd_1135687 : Nat := 4983230072969 + 3 ^ 40 * 1135687 * 2
def baseEnd_1135687 : Nat := 388768869375202235393051

theorem tailTrace_1135687 : CollatzResearch.WordTrace tailWord_1135687 prefixEnd_1135687 388768869375202235393051 := by
  unfold tailWord_1135687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41421907836607433742773315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27614605224404955828515543 41421907836607433742773315)
  ·
    refine ⟨62132861754911150614159973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41421907836607433742773315 62132861754911150614159973)
    ·
      refine ⟨11649911579045840740154995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62132861754911150614159973 11649911579045840740154995)
      ·
        refine ⟨17474867368568761110232493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11649911579045840740154995 17474867368568761110232493)
        ·
          refine ⟨6553075263213285416337185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17474867368568761110232493 6553075263213285416337185)
          ·
            refine ⟨4914806447409964062252889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6553075263213285416337185 4914806447409964062252889)
            ·
              refine ⟨3686104835557473046689667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914806447409964062252889 3686104835557473046689667)
              ·
                refine ⟨5529157253336209570034501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686104835557473046689667 5529157253336209570034501)
                ·
                  refine ⟨1036716985000539294381469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5529157253336209570034501 1036716985000539294381469)
                  ·
                    refine ⟨388768869375202235393051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1036716985000539294381469 388768869375202235393051)
                    ·
                      rfl

theorem cell22_1135687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1135687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135687 prefixEnd_1135687 := by exact prefixLift 1135687
  have htrace : WordTrace (prefixWord ++ tailWord_1135687) baseStart_1135687 baseEnd_1135687 := by
    simpa [prefixWord, tailWord_1135687, baseEnd_1135687] using wordTrace_append hprefix tailTrace_1135687
  have hstable : (prefixWord ++ tailWord_1135687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135687).length < 2 ^ (prefixWord ++ tailWord_1135687).sum := by decide
  have hdescent : baseEnd_1135687 < baseStart_1135687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135700 : List Nat := [2, 4, 1, 1, 1, 1, 3, 9]
def baseStart_1135700 : Nat := 118140960795 + 1135700 * 2 ^ 59
def prefixEnd_1135700 : Nat := 4983230072969 + 3 ^ 40 * 1135700 * 2
def baseEnd_1135700 : Nat := 43197035504541614979779

theorem tailTrace_1135700 : CollatzResearch.WordTrace tailWord_1135700 prefixEnd_1135700 43197035504541614979779 := by
  unfold tailWord_1135700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20711190992780168481498277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27614921323706891308664369 20711190992780168481498277)
  ·
    refine ⟨3883348311146281590280927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20711190992780168481498277 3883348311146281590280927)
    ·
      refine ⟨5825022466719422385421391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883348311146281590280927 5825022466719422385421391)
      ·
        refine ⟨8737533700079133578132087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825022466719422385421391 8737533700079133578132087)
        ·
          refine ⟨13106300550118700367198131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8737533700079133578132087 13106300550118700367198131)
          ·
            refine ⟨19659450825178050550797197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13106300550118700367198131 19659450825178050550797197)
            ·
              refine ⟨7372294059441768956548949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19659450825178050550797197 7372294059441768956548949)
              ·
                refine ⟨43197035504541614979779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7372294059441768956548949 43197035504541614979779)
                ·
                  rfl

theorem cell22_1135700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_1135700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135700 prefixEnd_1135700 := by exact prefixLift 1135700
  have htrace : WordTrace (prefixWord ++ tailWord_1135700) baseStart_1135700 baseEnd_1135700 := by
    simpa [prefixWord, tailWord_1135700, baseEnd_1135700] using wordTrace_append hprefix tailTrace_1135700
  have hstable : (prefixWord ++ tailWord_1135700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135700).length < 2 ^ (prefixWord ++ tailWord_1135700).sum := by decide
  have hdescent : baseEnd_1135700 < baseStart_1135700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135783 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1135783 : Nat := 118140960795 + 1135783 * 2 ^ 59
def prefixEnd_1135783 : Nat := 4983230072969 + 3 ^ 40 * 1135783 * 2
def baseEnd_1135783 : Nat := 388801732137089984992757

theorem tailTrace_1135783 : CollatzResearch.WordTrace tailWord_1135783 prefixEnd_1135783 388801732137089984992757 := by
  unfold tailWord_1135783
  simp only [CollatzResearch.WordTrace]
  refine ⟨41425409244259642138268003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27616939496173094758845335 41425409244259642138268003)
  ·
    refine ⟨62138113866389463207402005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41425409244259642138268003 62138113866389463207402005)
    ·
      refine ⟨2912724087487006087846969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62138113866389463207402005 2912724087487006087846969)
      ·
        refine ⟨2184543065615254565885227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912724087487006087846969 2184543065615254565885227)
        ·
          refine ⟨3276814598422881848827841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184543065615254565885227 3276814598422881848827841)
          ·
            refine ⟨2457610948817161386620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276814598422881848827841 2457610948817161386620881)
            ·
              refine ⟨1843208211612871039965661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457610948817161386620881 1843208211612871039965661)
              ·
                refine ⟨691203079354826639987123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843208211612871039965661 691203079354826639987123)
                ·
                  refine ⟨1036804619032239959980685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691203079354826639987123 1036804619032239959980685)
                  ·
                    refine ⟨388801732137089984992757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1036804619032239959980685 388801732137089984992757)
                    ·
                      rfl

theorem cell22_1135783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1135783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135783 prefixEnd_1135783 := by exact prefixLift 1135783
  have htrace : WordTrace (prefixWord ++ tailWord_1135783) baseStart_1135783 baseEnd_1135783 := by
    simpa [prefixWord, tailWord_1135783, baseEnd_1135783] using wordTrace_append hprefix tailTrace_1135783
  have hstable : (prefixWord ++ tailWord_1135783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135783).length < 2 ^ (prefixWord ++ tailWord_1135783).sum := by decide
  have hdescent : baseEnd_1135783 < baseStart_1135783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135792 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_1135792 : Nat := 118140960795 + 1135792 * 2 ^ 59
def prefixEnd_1135792 : Nat := 4983230072969 + 3 ^ 40 * 1135792 * 2
def baseEnd_1135792 : Nat := 388804813021016961517729

theorem tailTrace_1135792 : CollatzResearch.WordTrace tailWord_1135792 prefixEnd_1135792 388804813021016961517729 := by
  unfold tailWord_1135792
  simp only [CollatzResearch.WordTrace]
  refine ⟨20712868750613518337672815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27617158334151357783563753 20712868750613518337672815)
  ·
    refine ⟨31069303125920277506509223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20712868750613518337672815 31069303125920277506509223)
    ·
      refine ⟨46603954688880416259763835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31069303125920277506509223 46603954688880416259763835)
      ·
        refine ⟨69905932033320624389645753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46603954688880416259763835 69905932033320624389645753)
        ·
          refine ⟨52429449024990468292234315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69905932033320624389645753 52429449024990468292234315)
          ·
            refine ⟨78644173537485702438351473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52429449024990468292234315 78644173537485702438351473)
            ·
              refine ⟨58983130153114276828763605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78644173537485702438351473 58983130153114276828763605)
              ·
                refine ⟨1382417112963615863174147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58983130153114276828763605 1382417112963615863174147)
                ·
                  refine ⟨2073625669445423794761221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382417112963615863174147 2073625669445423794761221)
                  ·
                    refine ⟨388804813021016961517729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073625669445423794761221 388804813021016961517729)
                    ·
                      rfl

theorem cell22_1135792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_1135792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135792 prefixEnd_1135792 := by exact prefixLift 1135792
  have htrace : WordTrace (prefixWord ++ tailWord_1135792) baseStart_1135792 baseEnd_1135792 := by
    simpa [prefixWord, tailWord_1135792, baseEnd_1135792] using wordTrace_append hprefix tailTrace_1135792
  have hstable : (prefixWord ++ tailWord_1135792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135792).length < 2 ^ (prefixWord ++ tailWord_1135792).sum := by decide
  have hdescent : baseEnd_1135792 < baseStart_1135792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135841 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 4]
def baseStart_1135841 : Nat := 118140960795 + 1135841 * 2 ^ 59
def prefixEnd_1135841 : Nat := 4983230072969 + 3 ^ 40 * 1135841 * 2
def baseEnd_1135841 : Nat := 129607195574132389014193

theorem tailTrace_1135841 : CollatzResearch.WordTrace tailWord_1135841 prefixEnd_1135841 129607195574132389014193 := by
  unfold tailWord_1135841
  simp only [CollatzResearch.WordTrace]
  refine ⟨41427524678049518043879377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27618349785366345362586251 41427524678049518043879377)
  ·
    refine ⟨31070643508537138532909533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41427524678049518043879377 31070643508537138532909533)
    ·
      refine ⟨11651491315701426949841075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31070643508537138532909533 11651491315701426949841075)
      ·
        refine ⟨17477236973552140424761613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11651491315701426949841075 17477236973552140424761613)
        ·
          refine ⟨6553963865082052659285605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17477236973552140424761613 6553963865082052659285605)
          ·
            refine ⟨1228868224702884873616051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6553963865082052659285605 1228868224702884873616051)
            ·
              refine ⟨1843302337054327310424077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228868224702884873616051 1843302337054327310424077)
              ·
                refine ⟨691238376395372741409029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843302337054327310424077 691238376395372741409029)
                ·
                  refine ⟨129607195574132389014193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691238376395372741409029 129607195574132389014193)
                  ·
                    rfl

theorem cell22_1135841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_1135841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135841 prefixEnd_1135841 := by exact prefixLift 1135841
  have htrace : WordTrace (prefixWord ++ tailWord_1135841) baseStart_1135841 baseEnd_1135841 := by
    simpa [prefixWord, tailWord_1135841, baseEnd_1135841] using wordTrace_append hprefix tailTrace_1135841
  have hstable : (prefixWord ++ tailWord_1135841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135841).length < 2 ^ (prefixWord ++ tailWord_1135841).sum := by decide
  have hdescent : baseEnd_1135841 < baseStart_1135841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135852 : List Nat := [2, 2, 1, 1, 2, 6, 8]
def baseStart_1135852 : Nat := 118140960795 + 1135852 * 2 ^ 59
def prefixEnd_1135852 : Nat := 4983230072969 + 3 ^ 40 * 1135852 * 2
def baseEnd_1135852 : Nat := 14400938972118400185835

theorem tailTrace_1135852 : CollatzResearch.WordTrace tailWord_1135852 prefixEnd_1135852 14400938972118400185835 := by
  unfold tailWord_1135852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20713962940504833461264905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27618617254006444615019873 20713962940504833461264905)
  ·
    refine ⟨15535472205378625095948679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20713962940504833461264905 15535472205378625095948679)
    ·
      refine ⟨23303208308067937643923019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15535472205378625095948679 23303208308067937643923019)
      ·
        refine ⟨34954812462101906465884529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23303208308067937643923019 34954812462101906465884529)
        ·
          refine ⟨26216109346576429849413397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34954812462101906465884529 26216109346576429849413397)
          ·
            refine ⟨1228880125620770149191253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26216109346576429849413397 1228880125620770149191253)
            ·
              refine ⟨14400938972118400185835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1228880125620770149191253 14400938972118400185835)
              ·
                rfl

theorem cell22_1135852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 8].length) (baseStart_1135852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135852 prefixEnd_1135852 := by exact prefixLift 1135852
  have htrace : WordTrace (prefixWord ++ tailWord_1135852) baseStart_1135852 baseEnd_1135852 := by
    simpa [prefixWord, tailWord_1135852, baseEnd_1135852] using wordTrace_append hprefix tailTrace_1135852
  have hstable : (prefixWord ++ tailWord_1135852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135852).length < 2 ^ (prefixWord ++ tailWord_1135852).sum := by decide
  have hdescent : baseEnd_1135852 < baseStart_1135852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135858 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1135858 : Nat := 118140960795 + 1135858 * 2 ^ 59
def prefixEnd_1135858 : Nat := 4983230072969 + 3 ^ 40 * 1135858 * 2
def baseEnd_1135858 : Nat := 129609135389938263122509

theorem tailTrace_1135858 : CollatzResearch.WordTrace tailWord_1135858 prefixEnd_1135858 129609135389938263122509 := by
  unfold tailWord_1135858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357036179746982486812057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27618763145991953298165485 10357036179746982486812057)
  ·
    refine ⟨7767777134810236865109043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10357036179746982486812057 7767777134810236865109043)
    ·
      refine ⟨11651665702215355297663565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7767777134810236865109043 11651665702215355297663565)
      ·
        refine ⟨4369374638330758236623837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11651665702215355297663565 4369374638330758236623837)
        ·
          refine ⟨1638515489374034338733939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4369374638330758236623837 1638515489374034338733939)
          ·
            refine ⟨2457773234061051508100909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638515489374034338733939 2457773234061051508100909)
            ·
              refine ⟨921664962772894315537841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2457773234061051508100909 921664962772894315537841)
              ·
                refine ⟨691248722079670736653381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921664962772894315537841 691248722079670736653381)
                ·
                  refine ⟨129609135389938263122509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691248722079670736653381 129609135389938263122509)
                  ·
                    rfl

theorem cell22_1135858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1135858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135858 prefixEnd_1135858 := by exact prefixLift 1135858
  have htrace : WordTrace (prefixWord ++ tailWord_1135858) baseStart_1135858 baseEnd_1135858 := by
    simpa [prefixWord, tailWord_1135858, baseEnd_1135858] using wordTrace_append hprefix tailTrace_1135858
  have hstable : (prefixWord ++ tailWord_1135858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135858).length < 2 ^ (prefixWord ++ tailWord_1135858).sum := by decide
  have hdescent : baseEnd_1135858 < baseStart_1135858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135873 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1135873 : Nat := 118140960795 + 1135873 * 2 ^ 59
def prefixEnd_1135873 : Nat := 4983230072969 + 3 ^ 40 * 1135873 * 2
def baseEnd_1135873 : Nat := 388832540976359750242481

theorem tailTrace_1135873 : CollatzResearch.WordTrace tailWord_1135873 prefixEnd_1135873 388832540976359750242481 := by
  unfold tailWord_1135873
  simp only [CollatzResearch.WordTrace]
  refine ⟨41428691813933587509044273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27619127875955725006029515 41428691813933587509044273)
  ·
    refine ⟨31071518860450190631783205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41428691813933587509044273 31071518860450190631783205)
    ·
      refine ⟨5825909786334410743459351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31071518860450190631783205 5825909786334410743459351)
      ·
        refine ⟨8738864679501616115189027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825909786334410743459351 8738864679501616115189027)
        ·
          refine ⟨13108297019252424172783541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738864679501616115189027 13108297019252424172783541)
          ·
            refine ⟨1228902845554914766198457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13108297019252424172783541 1228902845554914766198457)
            ·
              refine ⟨921677134166186074648843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228902845554914766198457 921677134166186074648843)
              ·
                refine ⟨1382515701249279111973265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921677134166186074648843 1382515701249279111973265)
                ·
                  refine ⟨1036886775936959333979949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1382515701249279111973265 1036886775936959333979949)
                  ·
                    refine ⟨388832540976359750242481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1036886775936959333979949 388832540976359750242481)
                    ·
                      rfl

theorem cell22_1135873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1135873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135873 prefixEnd_1135873 := by exact prefixLift 1135873
  have htrace : WordTrace (prefixWord ++ tailWord_1135873) baseStart_1135873 baseEnd_1135873 := by
    simpa [prefixWord, tailWord_1135873, baseEnd_1135873] using wordTrace_append hprefix tailTrace_1135873
  have hstable : (prefixWord ++ tailWord_1135873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135873).length < 2 ^ (prefixWord ++ tailWord_1135873).sum := by decide
  have hdescent : baseEnd_1135873 < baseStart_1135873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135944 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1135944 : Nat := 118140960795 + 1135944 * 2 ^ 59
def prefixEnd_1135944 : Nat := 4983230072969 + 3 ^ 40 * 1135944 * 2
def baseEnd_1135944 : Nat := 388856845727339231717263

theorem tailTrace_1135944 : CollatzResearch.WordTrace tailWord_1135944 prefixEnd_1135944 388856845727339231717263 := by
  unfold tailWord_1135944
  simp only [CollatzResearch.WordTrace]
  refine ⟨20715640698338183317439443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27620854264450911089919257 20715640698338183317439443)
  ·
    refine ⟨31073461047507274976159165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20715640698338183317439443 31073461047507274976159165)
    ·
      refine ⟨11652547892815228116059687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31073461047507274976159165 11652547892815228116059687)
      ·
        refine ⟨17478821839222842174089531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11652547892815228116059687 17478821839222842174089531)
        ·
          refine ⟨26218232758834263261134297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17478821839222842174089531 26218232758834263261134297)
          ·
            refine ⟨19663674569125697445850723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26218232758834263261134297 19663674569125697445850723)
            ·
              refine ⟨29495511853688546168776085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19663674569125697445850723 29495511853688546168776085)
              ·
                refine ⟨1382602118141650601661379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29495511853688546168776085 1382602118141650601661379)
                ·
                  refine ⟨2073903177212475902492069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382602118141650601661379 2073903177212475902492069)
                  ·
                    refine ⟨388856845727339231717263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073903177212475902492069 388856845727339231717263)
                    ·
                      rfl

theorem cell22_1135944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1135944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135944 prefixEnd_1135944 := by exact prefixLift 1135944
  have htrace : WordTrace (prefixWord ++ tailWord_1135944) baseStart_1135944 baseEnd_1135944 := by
    simpa [prefixWord, tailWord_1135944, baseEnd_1135944] using wordTrace_append hprefix tailTrace_1135944
  have hstable : (prefixWord ++ tailWord_1135944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135944).length < 2 ^ (prefixWord ++ tailWord_1135944).sum := by decide
  have hdescent : baseEnd_1135944 < baseStart_1135944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135961 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_1135961 : Nat := 118140960795 + 1135961 * 2 ^ 59
def prefixEnd_1135961 : Nat := 4983230072969 + 3 ^ 40 * 1135961 * 2
def baseEnd_1135961 : Nat := 388862665174756854042211

theorem tailTrace_1135961 : CollatzResearch.WordTrace tailWord_1135961 prefixEnd_1135961 388862665174756854042211 := by
  unfold tailWord_1135961
  simp only [CollatzResearch.WordTrace]
  refine ⟨41431901437614778538247737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27621267625076519025498491 41431901437614778538247737)
  ·
    refine ⟨31073926078211083903685803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41431901437614778538247737 31073926078211083903685803)
    ·
      refine ⟨46610889117316625855528705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31073926078211083903685803 46610889117316625855528705)
      ·
        refine ⟨34958166837987469391646529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46610889117316625855528705 34958166837987469391646529)
        ·
          refine ⟨26218625128490602043734897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34958166837987469391646529 26218625128490602043734897)
          ·
            refine ⟨19663968846367951532801173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26218625128490602043734897 19663968846367951532801173)
            ·
              refine ⟨921748539673497728100055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19663968846367951532801173 921748539673497728100055)
              ·
                refine ⟨1382622809510246592150083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921748539673497728100055 1382622809510246592150083)
                ·
                  refine ⟨2073934214265369888225125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382622809510246592150083 2073934214265369888225125)
                  ·
                    refine ⟨388862665174756854042211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073934214265369888225125 388862665174756854042211)
                    ·
                      rfl

theorem cell22_1135961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_1135961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135961 prefixEnd_1135961 := by exact prefixLift 1135961
  have htrace : WordTrace (prefixWord ++ tailWord_1135961) baseStart_1135961 baseEnd_1135961 := by
    simpa [prefixWord, tailWord_1135961, baseEnd_1135961] using wordTrace_append hprefix tailTrace_1135961
  have hstable : (prefixWord ++ tailWord_1135961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135961).length < 2 ^ (prefixWord ++ tailWord_1135961).sum := by decide
  have hdescent : baseEnd_1135961 < baseStart_1135961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135976 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_1135976 : Nat := 118140960795 + 1135976 * 2 ^ 59
def prefixEnd_1135976 : Nat := 4983230072969 + 3 ^ 40 * 1135976 * 2
def baseEnd_1135976 : Nat := 129622599993767271639055

theorem tailTrace_1135976 : CollatzResearch.WordTrace tailWord_1135976 prefixEnd_1135976 129622599993767271639055 := by
  unfold tailWord_1135976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716224266280218050021891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27621632355040290733362521 20716224266280218050021891)
  ·
    refine ⟨31074336399420327075032837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20716224266280218050021891 31074336399420327075032837)
    ·
      refine ⟨5826438074891311326568657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31074336399420327075032837 5826438074891311326568657)
      ·
        refine ⟨4369828556168483494926493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5826438074891311326568657 4369828556168483494926493)
        ·
          refine ⟨1638685708563181310597435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4369828556168483494926493 1638685708563181310597435)
          ·
            refine ⟨2458028562844771965896153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638685708563181310597435 2458028562844771965896153)
            ·
              refine ⟨1843521422133578974422115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458028562844771965896153 1843521422133578974422115)
              ·
                refine ⟨2765282133200368461633173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843521422133578974422115 2765282133200368461633173)
                ·
                  refine ⟨129622599993767271639055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2765282133200368461633173 129622599993767271639055)
                  ·
                    rfl

theorem cell22_1135976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_1135976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1135976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1135976 prefixEnd_1135976 := by exact prefixLift 1135976
  have htrace : WordTrace (prefixWord ++ tailWord_1135976) baseStart_1135976 baseEnd_1135976 := by
    simpa [prefixWord, tailWord_1135976, baseEnd_1135976] using wordTrace_append hprefix tailTrace_1135976
  have hstable : (prefixWord ++ tailWord_1135976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135976).length < 2 ^ (prefixWord ++ tailWord_1135976).sum := by decide
  have hdescent : baseEnd_1135976 < baseStart_1135976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136004 : List Nat := [2, 3, 2, 1, 1, 4, 1, 8]
def baseStart_1136004 : Nat := 118140960795 + 1136004 * 2 ^ 59
def prefixEnd_1136004 : Nat := 4983230072969 + 3 ^ 40 * 1136004 * 2
def baseEnd_1136004 : Nat := 43208598328168786135231

theorem tailTrace_1136004 : CollatzResearch.WordTrace tailWord_1136004 prefixEnd_1136004 43208598328168786135231 := by
  unfold tailWord_1136004
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716734888229498441031533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27622313184305997921375377 20716734888229498441031533)
  ·
    refine ⟨7768775583086061915386825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20716734888229498441031533 7768775583086061915386825)
    ·
      refine ⟨5826581687314546436540119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7768775583086061915386825 5826581687314546436540119)
      ·
        refine ⟨8739872530971819654810179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5826581687314546436540119 8739872530971819654810179)
        ·
          refine ⟨13109808796457729482215269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8739872530971819654810179 13109808796457729482215269)
          ·
            refine ⟨2458089149335824277915363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13109808796457729482215269 2458089149335824277915363)
            ·
              refine ⟨3687133724003736416873045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458089149335824277915363 3687133724003736416873045)
              ·
                refine ⟨43208598328168786135231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3687133724003736416873045 43208598328168786135231)
                ·
                  rfl

theorem cell22_1136004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_1136004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136004 prefixEnd_1136004 := by exact prefixLift 1136004
  have htrace : WordTrace (prefixWord ++ tailWord_1136004) baseStart_1136004 baseEnd_1136004 := by
    simpa [prefixWord, tailWord_1136004, baseEnd_1136004] using wordTrace_append hprefix tailTrace_1136004
  have hstable : (prefixWord ++ tailWord_1136004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136004).length < 2 ^ (prefixWord ++ tailWord_1136004).sum := by decide
  have hdescent : baseEnd_1136004 < baseStart_1136004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136130 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1136130 : Nat := 118140960795 + 1136130 * 2 ^ 59
def prefixEnd_1136130 : Nat := 4983230072969 + 3 ^ 40 * 1136130 * 2
def baseEnd_1136130 : Nat := 388920517328496746566693

theorem tailTrace_1136130 : CollatzResearch.WordTrace tailWord_1136130 prefixEnd_1136130 388920517328496746566693 := by
  unfold tailWord_1136130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359516343500630100287461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27625376916001680267433229 10359516343500630100287461)
  ·
    refine ⟨1942409314406368143803899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10359516343500630100287461 1942409314406368143803899)
    ·
      refine ⟨2913613971609552215705849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942409314406368143803899 2913613971609552215705849)
      ·
        refine ⟨2185210478707164161779387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913613971609552215705849 2185210478707164161779387)
        ·
          refine ⟨3277815718060746242669081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185210478707164161779387 3277815718060746242669081)
          ·
            refine ⟨2458361788545559682001811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3277815718060746242669081 2458361788545559682001811)
            ·
              refine ⟨3687542682818339523002717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458361788545559682001811 3687542682818339523002717)
              ·
                refine ⟨1382828506056877321126019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3687542682818339523002717 1382828506056877321126019)
                ·
                  refine ⟨2074242759085315981689029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382828506056877321126019 2074242759085315981689029)
                  ·
                    refine ⟨388920517328496746566693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074242759085315981689029 388920517328496746566693)
                    ·
                      rfl

theorem cell22_1136130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1136130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136130 prefixEnd_1136130 := by exact prefixLift 1136130
  have htrace : WordTrace (prefixWord ++ tailWord_1136130) baseStart_1136130 baseEnd_1136130 := by
    simpa [prefixWord, tailWord_1136130, baseEnd_1136130] using wordTrace_append hprefix tailTrace_1136130
  have hstable : (prefixWord ++ tailWord_1136130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136130).length < 2 ^ (prefixWord ++ tailWord_1136130).sum := by decide
  have hdescent : baseEnd_1136130 < baseStart_1136130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136134 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1136134 : Nat := 118140960795 + 1136134 * 2 ^ 59
def prefixEnd_1136134 : Nat := 4983230072969 + 3 ^ 40 * 1136134 * 2
def baseEnd_1136134 : Nat := 129640628870080689822227

theorem tailTrace_1136134 : CollatzResearch.WordTrace tailWord_1136134 prefixEnd_1136134 129640628870080689822227 := by
  unfold tailWord_1136134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294944102062125908884233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27625474177325352722863637 1294944102062125908884233)
  ·
    refine ⟨971208076546594431663175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1294944102062125908884233 971208076546594431663175)
    ·
      refine ⟨1456812114819891647494763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971208076546594431663175 1456812114819891647494763)
      ·
        refine ⟨2185218172229837471242145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456812114819891647494763 2185218172229837471242145)
        ·
          refine ⟨1638913629172378103431609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2185218172229837471242145 1638913629172378103431609)
          ·
            refine ⟨1229185221879283577573707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1638913629172378103431609 1229185221879283577573707)
            ·
              refine ⟨1843777832818925366360561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229185221879283577573707 1843777832818925366360561)
              ·
                refine ⟨1382833374614194024770421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843777832818925366360561 1382833374614194024770421)
                ·
                  refine ⟨129640628870080689822227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382833374614194024770421 129640628870080689822227)
                  ·
                    rfl

theorem cell22_1136134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1136134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136134 prefixEnd_1136134 := by exact prefixLift 1136134
  have htrace : WordTrace (prefixWord ++ tailWord_1136134) baseStart_1136134 baseEnd_1136134 := by
    simpa [prefixWord, tailWord_1136134, baseEnd_1136134] using wordTrace_append hprefix tailTrace_1136134
  have hstable : (prefixWord ++ tailWord_1136134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136134).length < 2 ^ (prefixWord ++ tailWord_1136134).sum := by decide
  have hdescent : baseEnd_1136134 < baseStart_1136134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136261 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1136261 : Nat := 118140960795 + 1136261 * 2 ^ 59
def prefixEnd_1136261 : Nat := 4983230072969 + 3 ^ 40 * 1136261 * 2
def baseEnd_1136261 : Nat := 388965361305656071541291

theorem tailTrace_1136261 : CollatzResearch.WordTrace tailWord_1136261 prefixEnd_1136261 388965361305656071541291 := by
  unfold tailWord_1136261
  simp only [CollatzResearch.WordTrace]
  refine ⟨41442843336527929774168637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27628562224351953182779091 41442843336527929774168637)
  ·
    refine ⟨15541066251197973665313239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41442843336527929774168637 15541066251197973665313239)
    ·
      refine ⟨23311599376796960497969859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541066251197973665313239 23311599376796960497969859)
      ·
        refine ⟨34967399065195440746954789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23311599376796960497969859 34967399065195440746954789)
        ·
          refine ⟨6556387324724145140054023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34967399065195440746954789 6556387324724145140054023)
          ·
            refine ⟨9834580987086217710081035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6556387324724145140054023 9834580987086217710081035)
            ·
              refine ⟨14751871480629326565121553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9834580987086217710081035 14751871480629326565121553)
              ·
                refine ⟨11063903610471994923841165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14751871480629326565121553 11063903610471994923841165)
                ·
                  refine ⟨4148963853926998096440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11063903610471994923841165 4148963853926998096440437)
                  ·
                    refine ⟨388965361305656071541291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4148963853926998096440437 388965361305656071541291)
                    ·
                      rfl

theorem cell22_1136261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1136261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136261 prefixEnd_1136261 := by exact prefixLift 1136261
  have htrace : WordTrace (prefixWord ++ tailWord_1136261) baseStart_1136261 baseEnd_1136261 := by
    simpa [prefixWord, tailWord_1136261, baseEnd_1136261] using wordTrace_append hprefix tailTrace_1136261
  have hstable : (prefixWord ++ tailWord_1136261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136261).length < 2 ^ (prefixWord ++ tailWord_1136261).sum := by decide
  have hdescent : baseEnd_1136261 < baseStart_1136261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136293 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1136293 : Nat := 118140960795 + 1136293 * 2 ^ 59
def prefixEnd_1136293 : Nat := 4983230072969 + 3 ^ 40 * 1136293 * 2
def baseEnd_1136293 : Nat := 388976315559618654741193

theorem tailTrace_1136293 : CollatzResearch.WordTrace tailWord_1136293 prefixEnd_1136293 388976315559618654741193 := by
  unfold tailWord_1136293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41444010472411999239333533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27629340314941332826222355 41444010472411999239333533)
  ·
    refine ⟨15541503927154499714750075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41444010472411999239333533 15541503927154499714750075)
    ·
      refine ⟨23312255890731749572125113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541503927154499714750075 23312255890731749572125113)
      ·
        refine ⟨17484191918048812179093835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23312255890731749572125113 17484191918048812179093835)
        ·
          refine ⟨26226287877073218268640753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17484191918048812179093835 26226287877073218268640753)
          ·
            refine ⟨19669715907804913701480565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26226287877073218268640753 19669715907804913701480565)
            ·
              refine ⟨1844035866356710659513803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19669715907804913701480565 1844035866356710659513803)
              ·
                refine ⟨2766053799535065989270705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844035866356710659513803 2766053799535065989270705)
                ·
                  refine ⟨2074540349651299491953029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2766053799535065989270705 2074540349651299491953029)
                  ·
                    refine ⟨388976315559618654741193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074540349651299491953029 388976315559618654741193)
                    ·
                      rfl

theorem cell22_1136293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1136293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136293 prefixEnd_1136293 := by exact prefixLift 1136293
  have htrace : WordTrace (prefixWord ++ tailWord_1136293) baseStart_1136293 baseEnd_1136293 := by
    simpa [prefixWord, tailWord_1136293, baseEnd_1136293] using wordTrace_append hprefix tailTrace_1136293
  have hstable : (prefixWord ++ tailWord_1136293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136293).length < 2 ^ (prefixWord ++ tailWord_1136293).sum := by decide
  have hdescent : baseEnd_1136293 < baseStart_1136293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136342 : List Nat := [5, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1136342 : Nat := 118140960795 + 1136342 * 2 ^ 59
def prefixEnd_1136342 : Nat := 4983230072969 + 3 ^ 40 * 1136342 * 2
def baseEnd_1136342 : Nat := 43221454362333206696227

theorem tailTrace_1136342 : CollatzResearch.WordTrace tailWord_1136342 prefixEnd_1136342 43221454362333206696227 := by
  unfold tailWord_1136342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590362353077155037991705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27630531766156320405244853 2590362353077155037991705)
  ·
    refine ⟨1942771764807866278493779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2590362353077155037991705 1942771764807866278493779)
    ·
      refine ⟨2914157647211799417740669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942771764807866278493779 2914157647211799417740669)
      ·
        refine ⟨1092809117704424781652751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2914157647211799417740669 1092809117704424781652751)
        ·
          refine ⟨1639213676556637172479127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092809117704424781652751 1639213676556637172479127)
          ·
            refine ⟨2458820514834955758718691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639213676556637172479127 2458820514834955758718691)
            ·
              refine ⟨3688230772252433638078037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458820514834955758718691 3688230772252433638078037)
              ·
                refine ⟨43221454362333206696227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3688230772252433638078037 43221454362333206696227)
                ·
                  rfl

theorem cell22_1136342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1136342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136342 prefixEnd_1136342 := by exact prefixLift 1136342
  have htrace : WordTrace (prefixWord ++ tailWord_1136342) baseStart_1136342 baseEnd_1136342 := by
    simpa [prefixWord, tailWord_1136342, baseEnd_1136342] using wordTrace_append hprefix tailTrace_1136342
  have hstable : (prefixWord ++ tailWord_1136342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136342).length < 2 ^ (prefixWord ++ tailWord_1136342).sum := by decide
  have hdescent : baseEnd_1136342 < baseStart_1136342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
