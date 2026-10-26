import V185TrunkScan22Chunk323

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2891678 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2891678 : Nat := 118140960795 + 2891678 * 2 ^ 59
def prefixEnd_2891678 : Nat := 4983230072969 + 3 ^ 40 * 2891678 * 2
def baseEnd_2891678 : Nat := 989880474688028353484281

theorem tailTrace_2891678 : CollatzResearch.WordTrace tailWord_2891678 prefixEnd_2891678 989880474688028353484281 := by
  unfold tailWord_2891678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183520152243992516170461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70312107478634626752909125 13183520152243992516170461)
  ·
    refine ⟨4943820057091497193563923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13183520152243992516170461 4943820057091497193563923)
    ·
      refine ⟨7415730085637245790345885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943820057091497193563923 7415730085637245790345885)
      ·
        refine ⟨2780898782113967171379707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7415730085637245790345885 2780898782113967171379707)
        ·
          refine ⟨4171348173170950757069561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780898782113967171379707 4171348173170950757069561)
          ·
            refine ⟨3128511129878213067802171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4171348173170950757069561 3128511129878213067802171)
            ·
              refine ⟨4692766694817319601703257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128511129878213067802171 4692766694817319601703257)
              ·
                refine ⟨3519575021112989701277443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692766694817319601703257 3519575021112989701277443)
                ·
                  refine ⟨5279362531669484551916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519575021112989701277443 5279362531669484551916165)
                  ·
                    refine ⟨989880474688028353484281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279362531669484551916165 989880474688028353484281)
                    ·
                      rfl

theorem cell22_2891678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2891678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891678 prefixEnd_2891678 := by exact prefixLift 2891678
  have htrace : WordTrace (prefixWord ++ tailWord_2891678) baseStart_2891678 baseEnd_2891678 := by
    simpa [prefixWord, tailWord_2891678, baseEnd_2891678] using wordTrace_append hprefix tailTrace_2891678
  have hstable : (prefixWord ++ tailWord_2891678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891678).length < 2 ^ (prefixWord ++ tailWord_2891678).sum := by decide
  have hdescent : baseEnd_2891678 < baseStart_2891678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891732 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2891732 : Nat := 118140960795 + 2891732 * 2 ^ 59
def prefixEnd_2891732 : Nat := 4983230072969 + 3 ^ 40 * 2891732 * 2
def baseEnd_2891732 : Nat := 329966319997196737544705

theorem tailTrace_2891732 : CollatzResearch.WordTrace tailWord_2891732 prefixEnd_2891732 329966319997196737544705 := by
  unfold tailWord_2891732
  simp only [CollatzResearch.WordTrace]
  refine ⟨52735065379878153675914725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70313420506504204901219633 52735065379878153675914725)
  ·
    refine ⟨9887824758727153814234011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52735065379878153675914725 9887824758727153814234011)
    ·
      refine ⟨14831737138090730721351017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887824758727153814234011 14831737138090730721351017)
      ·
        refine ⟨11123802853568048041013263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14831737138090730721351017 11123802853568048041013263)
        ·
          refine ⟨16685704280352072061519895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11123802853568048041013263 16685704280352072061519895)
          ·
            refine ⟨25028556420528108092279843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16685704280352072061519895 25028556420528108092279843)
            ·
              refine ⟨37542834630792162138419765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25028556420528108092279843 37542834630792162138419765)
              ·
                refine ⟨3519640746636765200476853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37542834630792162138419765 3519640746636765200476853)
                ·
                  refine ⟨329966319997196737544705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3519640746636765200476853 329966319997196737544705)
                  ·
                    rfl

theorem cell22_2891732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2891732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891732 prefixEnd_2891732 := by exact prefixLift 2891732
  have htrace : WordTrace (prefixWord ++ tailWord_2891732) baseStart_2891732 baseEnd_2891732 := by
    simpa [prefixWord, tailWord_2891732, baseEnd_2891732] using wordTrace_append hprefix tailTrace_2891732
  have hstable : (prefixWord ++ tailWord_2891732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891732).length < 2 ^ (prefixWord ++ tailWord_2891732).sum := by decide
  have hdescent : baseEnd_2891732 < baseStart_2891732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891740 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2891740 : Nat := 118140960795 + 2891740 * 2 ^ 59
def prefixEnd_2891740 : Nat := 4983230072969 + 3 ^ 40 * 2891740 * 2
def baseEnd_2891740 : Nat := 989901698555080858434091

theorem tailTrace_2891740 : CollatzResearch.WordTrace tailWord_2891740 prefixEnd_2891740 989901698555080858434091 := by
  unfold tailWord_2891740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52735211271863662359060337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70313615029151549812080449 52735211271863662359060337)
  ·
    refine ⟨39551408453897746769295253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52735211271863662359060337 39551408453897746769295253)
    ·
      refine ⟨1853972271276456879810715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39551408453897746769295253 1853972271276456879810715)
      ·
        refine ⟨2780958406914685319716073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853972271276456879810715 2780958406914685319716073)
        ·
          refine ⟨2085718805186013989787055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780958406914685319716073 2085718805186013989787055)
          ·
            refine ⟨3128578207779020984680583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085718805186013989787055 3128578207779020984680583)
            ·
              refine ⟨4692867311668531477020875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128578207779020984680583 4692867311668531477020875)
              ·
                refine ⟨7039300967502797215531313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692867311668531477020875 7039300967502797215531313)
                ·
                  refine ⟨5279475725627097911648485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7039300967502797215531313 5279475725627097911648485)
                  ·
                    refine ⟨989901698555080858434091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279475725627097911648485 989901698555080858434091)
                    ·
                      rfl

theorem cell22_2891740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2891740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891740 prefixEnd_2891740 := by exact prefixLift 2891740
  have htrace : WordTrace (prefixWord ++ tailWord_2891740) baseStart_2891740 baseEnd_2891740 := by
    simpa [prefixWord, tailWord_2891740, baseEnd_2891740] using wordTrace_append hprefix tailTrace_2891740
  have hstable : (prefixWord ++ tailWord_2891740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891740).length < 2 ^ (prefixWord ++ tailWord_2891740).sum := by decide
  have hdescent : baseEnd_2891740 < baseStart_2891740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891766 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2891766 : Nat := 118140960795 + 2891766 * 2 ^ 59
def prefixEnd_2891766 : Nat := 4983230072969 + 3 ^ 40 * 2891766 * 2
def baseEnd_2891766 : Nat := 329970199628808485761337

theorem tailTrace_2891766 : CollatzResearch.WordTrace tailWord_2891766 prefixEnd_2891766 329970199628808485761337 := by
  unfold tailWord_2891766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591960677602070697410447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70314247227755420772378101 6591960677602070697410447)
  ·
    refine ⟨9887941016403106046115671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6591960677602070697410447 9887941016403106046115671)
    ·
      refine ⟨14831911524604659069173507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887941016403106046115671 14831911524604659069173507)
      ·
        refine ⟨22247867286906988603760261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14831911524604659069173507 22247867286906988603760261)
        ·
          refine ⟨4171475116295060363205049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22247867286906988603760261 4171475116295060363205049)
          ·
            refine ⟨3128606337221295272403787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4171475116295060363205049 3128606337221295272403787)
            ·
              refine ⟨4692909505831942908605681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128606337221295272403787 4692909505831942908605681)
              ·
                refine ⟨3519682129373957181454261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692909505831942908605681 3519682129373957181454261)
                ·
                  refine ⟨329970199628808485761337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3519682129373957181454261 329970199628808485761337)
                  ·
                    rfl

theorem cell22_2891766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2891766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891766 prefixEnd_2891766 := by exact prefixLift 2891766
  have htrace : WordTrace (prefixWord ++ tailWord_2891766) baseStart_2891766 baseEnd_2891766 := by
    simpa [prefixWord, tailWord_2891766, baseEnd_2891766] using wordTrace_append hprefix tailTrace_2891766
  have hstable : (prefixWord ++ tailWord_2891766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891766).length < 2 ^ (prefixWord ++ tailWord_2891766).sum := by decide
  have hdescent : baseEnd_2891766 < baseStart_2891766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891775 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_2891775 : Nat := 118140960795 + 2891775 * 2 ^ 59
def prefixEnd_2891775 : Nat := 4983230072969 + 3 ^ 40 * 2891775 * 2
def baseEnd_2891775 : Nat := 989913679770352433808983

theorem tailTrace_2891775 : CollatzResearch.WordTrace tailWord_2891775 prefixEnd_2891775 989913679770352433808983 := by
  unfold tailWord_2891775
  simp only [CollatzResearch.WordTrace]
  refine ⟨105471699098600525695644779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70314466065733683797096519 105471699098600525695644779)
  ·
    refine ⟨158207548647900788543467169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105471699098600525695644779 158207548647900788543467169)
    ·
      refine ⟨118655661485925591407600377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158207548647900788543467169 118655661485925591407600377)
      ·
        refine ⟨88991746114444193555700283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118655661485925591407600377 88991746114444193555700283)
        ·
          refine ⟨133487619171666290333550425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88991746114444193555700283 133487619171666290333550425)
          ·
            refine ⟨100115714378749717750162819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133487619171666290333550425 100115714378749717750162819)
            ·
              refine ⟨150173571568124576625244229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100115714378749717750162819 150173571568124576625244229)
              ·
                refine ⟨28157544669023358117233293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150173571568124576625244229 28157544669023358117233293)
                ·
                  refine ⟨10559079250883759293962485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28157544669023358117233293 10559079250883759293962485)
                  ·
                    refine ⟨989913679770352433808983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10559079250883759293962485 989913679770352433808983)
                    ·
                      rfl

theorem cell22_2891775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_2891775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891775 prefixEnd_2891775 := by exact prefixLift 2891775
  have htrace : WordTrace (prefixWord ++ tailWord_2891775) baseStart_2891775 baseEnd_2891775 := by
    simpa [prefixWord, tailWord_2891775, baseEnd_2891775] using wordTrace_append hprefix tailTrace_2891775
  have hstable : (prefixWord ++ tailWord_2891775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891775).length < 2 ^ (prefixWord ++ tailWord_2891775).sum := by decide
  have hdescent : baseEnd_2891775 < baseStart_2891775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891777 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 6]
def baseStart_2891777 : Nat := 118140960795 + 2891777 * 2 ^ 59
def prefixEnd_2891777 : Nat := 4983230072969 + 3 ^ 40 * 2891777 * 2
def baseEnd_2891777 : Nat := 329971454803741698419659

theorem tailTrace_2891777 : CollatzResearch.WordTrace tailWord_2891777 prefixEnd_2891777 329971454803741698419659 := by
  unfold tailWord_2891777
  simp only [CollatzResearch.WordTrace]
  refine ⟨105471772044593280037217585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70314514696395520024811723 105471772044593280037217585)
  ·
    refine ⟨79103829033444960027913189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105471772044593280037217585 79103829033444960027913189)
    ·
      refine ⟨14831967943770930005233723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79103829033444960027913189 14831967943770930005233723)
      ·
        refine ⟨22247951915656395007850585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14831967943770930005233723 22247951915656395007850585)
        ·
          refine ⟨16685963936742296255887939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22247951915656395007850585 16685963936742296255887939)
          ·
            refine ⟨25028945905113444383831909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16685963936742296255887939 25028945905113444383831909)
            ·
              refine ⟨4692927357208770821968483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25028945905113444383831909 4692927357208770821968483)
              ·
                refine ⟨7039391035813156232952725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692927357208770821968483 7039391035813156232952725)
                ·
                  refine ⟨329971454803741698419659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7039391035813156232952725 329971454803741698419659)
                  ·
                    rfl

theorem cell22_2891777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_2891777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891777 prefixEnd_2891777 := by exact prefixLift 2891777
  have htrace : WordTrace (prefixWord ++ tailWord_2891777) baseStart_2891777 baseEnd_2891777 := by
    simpa [prefixWord, tailWord_2891777, baseEnd_2891777] using wordTrace_append hprefix tailTrace_2891777
  have hstable : (prefixWord ++ tailWord_2891777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891777).length < 2 ^ (prefixWord ++ tailWord_2891777).sum := by decide
  have hdescent : baseEnd_2891777 < baseStart_2891777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891807 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_2891807 : Nat := 118140960795 + 2891807 * 2 ^ 59
def prefixEnd_2891807 : Nat := 4983230072969 + 3 ^ 40 * 2891807 * 2
def baseEnd_2891807 : Nat := 989924634024315017008885

theorem tailTrace_2891807 : CollatzResearch.WordTrace tailWord_2891807 prefixEnd_2891807 989924634024315017008885 := by
  unfold tailWord_2891807
  simp only [CollatzResearch.WordTrace]
  refine ⟨105472866234484595160809675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70315244156323063440539783 105472866234484595160809675)
  ·
    refine ⟨158209299351726892741214513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105472866234484595160809675 158209299351726892741214513)
    ·
      refine ⟨118656974513795169555910885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158209299351726892741214513 118656974513795169555910885)
      ·
        refine ⟨22248182721336594291733291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118656974513795169555910885 22248182721336594291733291)
        ·
          refine ⟨33372274082004891437599937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22248182721336594291733291 33372274082004891437599937)
          ·
            refine ⟨25029205561503668578199953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33372274082004891437599937 25029205561503668578199953)
            ·
              refine ⟨18771904171127751433649965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25029205561503668578199953 18771904171127751433649965)
              ·
                refine ⟨7039464064172906787618737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18771904171127751433649965 7039464064172906787618737)
                ·
                  refine ⟨5279598048129680090714053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7039464064172906787618737 5279598048129680090714053)
                  ·
                    refine ⟨989924634024315017008885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279598048129680090714053 989924634024315017008885)
                    ·
                      rfl

theorem cell22_2891807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_2891807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891807 prefixEnd_2891807 := by exact prefixLift 2891807
  have htrace : WordTrace (prefixWord ++ tailWord_2891807) baseStart_2891807 baseEnd_2891807 := by
    simpa [prefixWord, tailWord_2891807, baseEnd_2891807] using wordTrace_append hprefix tailTrace_2891807
  have hstable : (prefixWord ++ tailWord_2891807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891807).length < 2 ^ (prefixWord ++ tailWord_2891807).sum := by decide
  have hdescent : baseEnd_2891807 < baseStart_2891807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891822 : List Nat := [4, 1, 3, 1, 1, 2, 10]
def baseStart_2891822 : Nat := 118140960795 + 2891822 * 2 ^ 59
def prefixEnd_2891822 : Nat := 4983230072969 + 3 ^ 40 * 2891822 * 2
def baseEnd_2891822 : Nat := 36664065512254073254957

theorem tailTrace_2891822 : CollatzResearch.WordTrace tailWord_2891822 prefixEnd_2891822 36664065512254073254957 := by
  unfold tailWord_2891822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13184176666178781590325715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70315608886286835148403813 13184176666178781590325715)
  ·
    refine ⟨19776264999268172385488573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13184176666178781590325715 19776264999268172385488573)
    ·
      refine ⟨7416099374725564644558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19776264999268172385488573 7416099374725564644558215)
      ·
        refine ⟨11124149062088346966837323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416099374725564644558215 11124149062088346966837323)
        ·
          refine ⟨16686223593132520450255985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124149062088346966837323 16686223593132520450255985)
          ·
            refine ⟨12514667694849390337691989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16686223593132520450255985 12514667694849390337691989)
            ·
              refine ⟨36664065512254073254957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12514667694849390337691989 36664065512254073254957)
              ·
                rfl

theorem cell22_2891822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 10].length) (baseStart_2891822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891822 prefixEnd_2891822 := by exact prefixLift 2891822
  have htrace : WordTrace (prefixWord ++ tailWord_2891822) baseStart_2891822 baseEnd_2891822 := by
    simpa [prefixWord, tailWord_2891822, baseEnd_2891822] using wordTrace_append hprefix tailTrace_2891822
  have hstable : (prefixWord ++ tailWord_2891822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891822).length < 2 ^ (prefixWord ++ tailWord_2891822).sum := by decide
  have hdescent : baseEnd_2891822 < baseStart_2891822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891828 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2891828 : Nat := 118140960795 + 2891828 * 2 ^ 59
def prefixEnd_2891828 : Nat := 4983230072969 + 3 ^ 40 * 2891828 * 2
def baseEnd_2891828 : Nat := 329977274251159320744607

theorem tailTrace_2891828 : CollatzResearch.WordTrace tailWord_2891828 prefixEnd_2891828 329977274251159320744607 := by
  unfold tailWord_2891828
  simp only [CollatzResearch.WordTrace]
  refine ⟨52736816083704257873662069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70315754778272343831549425 52736816083704257873662069)
  ·
    refine ⟨4944076507847274175655819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52736816083704257873662069 4944076507847274175655819)
    ·
      refine ⟨7416114761770911263483729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944076507847274175655819 7416114761770911263483729)
      ·
        refine ⟨5562086071328183447612797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7416114761770911263483729 5562086071328183447612797)
        ·
          refine ⟨2085782276748068792854799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5562086071328183447612797 2085782276748068792854799)
          ·
            refine ⟨3128673415122103189282199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085782276748068792854799 3128673415122103189282199)
            ·
              refine ⟨4693010122683154783923299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128673415122103189282199 4693010122683154783923299)
              ·
                refine ⟨7039515184024732175884949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693010122683154783923299 7039515184024732175884949)
                ·
                  refine ⟨329977274251159320744607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7039515184024732175884949 329977274251159320744607)
                  ·
                    rfl

theorem cell22_2891828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2891828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891828 prefixEnd_2891828 := by exact prefixLift 2891828
  have htrace : WordTrace (prefixWord ++ tailWord_2891828) baseStart_2891828 baseEnd_2891828 := by
    simpa [prefixWord, tailWord_2891828, baseEnd_2891828] using wordTrace_append hprefix tailTrace_2891828
  have hstable : (prefixWord ++ tailWord_2891828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891828).length < 2 ^ (prefixWord ++ tailWord_2891828).sum := by decide
  have hdescent : baseEnd_2891828 < baseStart_2891828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891835 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_2891835 : Nat := 118140960795 + 2891835 * 2 ^ 59
def prefixEnd_2891835 : Nat := 4983230072969 + 3 ^ 40 * 2891835 * 2
def baseEnd_2891835 : Nat := 989934218996532277308799

theorem tailTrace_2891835 : CollatzResearch.WordTrace tailWord_2891835 prefixEnd_2891835 989934218996532277308799 := by
  unfold tailWord_2891835
  simp only [CollatzResearch.WordTrace]
  refine ⟨105473887478383155942828959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70315924985588770628552639 105473887478383155942828959)
  ·
    refine ⟨158210831217574733914243439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105473887478383155942828959 158210831217574733914243439)
    ·
      refine ⟨237316246826362100871365159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158210831217574733914243439 237316246826362100871365159)
      ·
        refine ⟨355974370239543151307047739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237316246826362100871365159 355974370239543151307047739)
        ·
          refine ⟨533961555359314726960571609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355974370239543151307047739 533961555359314726960571609)
          ·
            refine ⟨400471166519486045220428707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533961555359314726960571609 400471166519486045220428707)
            ·
              refine ⟨600706749779229067830643061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400471166519486045220428707 600706749779229067830643061)
              ·
                refine ⟨56316257791802725109122787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600706749779229067830643061 56316257791802725109122787)
                ·
                  refine ⟨84474386687704087663684181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56316257791802725109122787 84474386687704087663684181)
                  ·
                    refine ⟨989934218996532277308799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84474386687704087663684181 989934218996532277308799)
                    ·
                      rfl

theorem cell22_2891835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_2891835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891835 prefixEnd_2891835 := by exact prefixLift 2891835
  have htrace : WordTrace (prefixWord ++ tailWord_2891835) baseStart_2891835 baseEnd_2891835 := by
    simpa [prefixWord, tailWord_2891835, baseEnd_2891835] using wordTrace_append hprefix tailTrace_2891835
  have hstable : (prefixWord ++ tailWord_2891835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891835).length < 2 ^ (prefixWord ++ tailWord_2891835).sum := by decide
  have hdescent : baseEnd_2891835 < baseStart_2891835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891884 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_2891884 : Nat := 118140960795 + 2891884 * 2 ^ 59
def prefixEnd_2891884 : Nat := 4983230072969 + 3 ^ 40 * 2891884 * 2
def baseEnd_2891884 : Nat := 329983664232637494277883

theorem tailTrace_2891884 : CollatzResearch.WordTrace tailWord_2891884 prefixEnd_2891884 329983664232637494277883 := by
  unfold tailWord_2891884
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737837327602818655681353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70317116436803758207575137 52737837327602818655681353)
  ·
    refine ⟨39553377995702113991761015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52737837327602818655681353 39553377995702113991761015)
    ·
      refine ⟨59330066993553170987641523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39553377995702113991761015 59330066993553170987641523)
      ·
        refine ⟨88995100490329756481462285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59330066993553170987641523 88995100490329756481462285)
        ·
          refine ⟨33373162683873658680548357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88995100490329756481462285 33373162683873658680548357)
          ·
            refine ⟨6257468003226311002602817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33373162683873658680548357 6257468003226311002602817)
            ·
              refine ⟨4693101002419733251952113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6257468003226311002602817 4693101002419733251952113)
              ·
                refine ⟨3519825751814799938964085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693101002419733251952113 3519825751814799938964085)
                ·
                  refine ⟨329983664232637494277883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3519825751814799938964085 329983664232637494277883)
                  ·
                    rfl

theorem cell22_2891884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_2891884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891884 prefixEnd_2891884 := by exact prefixLift 2891884
  have htrace : WordTrace (prefixWord ++ tailWord_2891884) baseStart_2891884 baseEnd_2891884 := by
    simpa [prefixWord, tailWord_2891884, baseEnd_2891884] using wordTrace_append hprefix tailTrace_2891884
  have hstable : (prefixWord ++ tailWord_2891884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891884).length < 2 ^ (prefixWord ++ tailWord_2891884).sum := by decide
  have hdescent : baseEnd_2891884 < baseStart_2891884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891888 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 1, 3]
def baseStart_2891888 : Nat := 118140960795 + 2891888 * 2 ^ 59
def prefixEnd_2891888 : Nat := 4983230072969 + 3 ^ 40 * 2891888 * 2
def baseEnd_2891888 : Nat := 989952361979657805733637

theorem tailTrace_2891888 : CollatzResearch.WordTrace tailWord_2891888 prefixEnd_2891888 989952361979657805733637 := by
  unfold tailWord_2891888
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737910273595572997254159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70317213698127430663005545 52737910273595572997254159)
  ·
    refine ⟨79106865410393359495881239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52737910273595572997254159 79106865410393359495881239)
    ·
      refine ⟨118660298115590039243821859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79106865410393359495881239 118660298115590039243821859)
      ·
        refine ⟨177990447173385058865732789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118660298115590039243821859 177990447173385058865732789)
        ·
          refine ⟨16686604422504849268662449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177990447173385058865732789 16686604422504849268662449)
          ·
            refine ⟨12514953316878636951496837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16686604422504849268662449 12514953316878636951496837)
            ·
              refine ⟨2346553746914744428405657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12514953316878636951496837 2346553746914744428405657)
              ·
                refine ⟨1759915310186058321304243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346553746914744428405657 1759915310186058321304243)
                ·
                  refine ⟨2639872965279087481956365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759915310186058321304243 2639872965279087481956365)
                  ·
                    refine ⟨989952361979657805733637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639872965279087481956365 989952361979657805733637)
                    ·
                      rfl

theorem cell22_2891888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_2891888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891888 prefixEnd_2891888 := by exact prefixLift 2891888
  have htrace : WordTrace (prefixWord ++ tailWord_2891888) baseStart_2891888 baseEnd_2891888 := by
    simpa [prefixWord, tailWord_2891888, baseEnd_2891888] using wordTrace_append hprefix tailTrace_2891888
  have hstable : (prefixWord ++ tailWord_2891888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891888).length < 2 ^ (prefixWord ++ tailWord_2891888).sum := by decide
  have hdescent : baseEnd_2891888 < baseStart_2891888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891914 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2891914 : Nat := 118140960795 + 2891914 * 2 ^ 59
def prefixEnd_2891914 : Nat := 4983230072969 + 3 ^ 40 * 2891914 * 2
def baseEnd_2891914 : Nat := 989961262311002404583557

theorem tailTrace_2891914 : CollatzResearch.WordTrace tailWord_2891914 prefixEnd_2891914 989961262311002404583557 := by
  unfold tailWord_2891914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26369192211274238108738699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70317845896731301623303197 26369192211274238108738699)
  ·
    refine ⟨39553788316911357163108049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26369192211274238108738699 39553788316911357163108049)
    ·
      refine ⟨29665341237683517872331037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39553788316911357163108049 29665341237683517872331037)
      ·
        refine ⟨11124502964131319202124139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29665341237683517872331037 11124502964131319202124139)
        ·
          refine ⟨16686754446196978803186209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124502964131319202124139 16686754446196978803186209)
          ·
            refine ⟨12515065834647734102389657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16686754446196978803186209 12515065834647734102389657)
            ·
              refine ⟨9386299375985800576792243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12515065834647734102389657 9386299375985800576792243)
              ·
                refine ⟨14079449063978700865188365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9386299375985800576792243 14079449063978700865188365)
                ·
                  refine ⟨5279793398992012824445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14079449063978700865188365 5279793398992012824445637)
                  ·
                    refine ⟨989961262311002404583557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279793398992012824445637 989961262311002404583557)
                    ·
                      rfl

theorem cell22_2891914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2891914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891914 prefixEnd_2891914 := by exact prefixLift 2891914
  have htrace : WordTrace (prefixWord ++ tailWord_2891914) baseStart_2891914 baseEnd_2891914 := by
    simpa [prefixWord, tailWord_2891914, baseEnd_2891914] using wordTrace_append hprefix tailTrace_2891914
  have hstable : (prefixWord ++ tailWord_2891914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891914).length < 2 ^ (prefixWord ++ tailWord_2891914).sum := by decide
  have hdescent : baseEnd_2891914 < baseStart_2891914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891980 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_2891980 : Nat := 118140960795 + 2891980 * 2 ^ 59
def prefixEnd_2891980 : Nat := 4983230072969 + 3 ^ 40 * 2891980 * 2
def baseEnd_2891980 : Nat := 329994618486600077477785

theorem tailTrace_2891980 : CollatzResearch.WordTrace tailWord_2891980 prefixEnd_2891980 329994618486600077477785 := by
  unfold tailWord_2891980
  simp only [CollatzResearch.WordTrace]
  refine ⟨52739588031428922853428697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70319450708571897137904929 52739588031428922853428697)
  ·
    refine ⟨39554691023571692140071523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52739588031428922853428697 39554691023571692140071523)
    ·
      refine ⟨59332036535357538210107285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39554691023571692140071523 59332036535357538210107285)
      ·
        refine ⟨2781189212594884603598779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59332036535357538210107285 2781189212594884603598779)
        ·
          refine ⟨4171783818892326905398169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781189212594884603598779 4171783818892326905398169)
          ·
            refine ⟨3128837864169245179048627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4171783818892326905398169 3128837864169245179048627)
            ·
              refine ⟨4693256796253867768572941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128837864169245179048627 4693256796253867768572941)
              ·
                refine ⟨1759971298595200413214853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4693256796253867768572941 1759971298595200413214853)
                ·
                  refine ⟨329994618486600077477785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759971298595200413214853 329994618486600077477785)
                  ·
                    rfl

theorem cell22_2891980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_2891980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891980 prefixEnd_2891980 := by exact prefixLift 2891980
  have htrace : WordTrace (prefixWord ++ tailWord_2891980) baseStart_2891980 baseEnd_2891980 := by
    simpa [prefixWord, tailWord_2891980, baseEnd_2891980] using wordTrace_append hprefix tailTrace_2891980
  have hstable : (prefixWord ++ tailWord_2891980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891980).length < 2 ^ (prefixWord ++ tailWord_2891980).sum := by decide
  have hdescent : baseEnd_2891980 < baseStart_2891980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892019 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 5]
def baseStart_2892019 : Nat := 118140960795 + 2892019 * 2 ^ 59
def prefixEnd_2892019 : Nat := 4983230072969 + 3 ^ 40 * 2892019 * 2
def baseEnd_2892019 : Nat := 329999068652272376902745

theorem tailTrace_2892019 : CollatzResearch.WordTrace tailWord_2892019 prefixEnd_2892019 329999068652272376902745 := by
  unfold tailWord_2892019
  simp only [CollatzResearch.WordTrace]
  refine ⟨105480598509716555367527111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70320399006477703578351407 105480598509716555367527111)
  ·
    refine ⟨158220897764574833051290667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105480598509716555367527111 158220897764574833051290667)
    ·
      refine ⟨237331346646862249576936001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158220897764574833051290667 237331346646862249576936001)
      ·
        refine ⟨177998509985146687182702001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237331346646862249576936001 177998509985146687182702001)
        ·
          refine ⟨133498882488860015387026501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177998509985146687182702001 133498882488860015387026501)
          ·
            refine ⟨25031040466661252885067469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133498882488860015387026501 25031040466661252885067469)
            ·
              refine ⟨9386640174997969831900301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25031040466661252885067469 9386640174997969831900301)
              ·
                refine ⟨3519990065624238686962613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9386640174997969831900301 3519990065624238686962613)
                ·
                  refine ⟨329999068652272376902745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3519990065624238686962613 329999068652272376902745)
                  ·
                    rfl

theorem cell22_2892019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 5].length) (baseStart_2892019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892019 prefixEnd_2892019 := by exact prefixLift 2892019
  have htrace : WordTrace (prefixWord ++ tailWord_2892019) baseStart_2892019 baseEnd_2892019 := by
    simpa [prefixWord, tailWord_2892019, baseEnd_2892019] using wordTrace_append hprefix tailTrace_2892019
  have hstable : (prefixWord ++ tailWord_2892019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892019).length < 2 ^ (prefixWord ++ tailWord_2892019).sum := by decide
  have hdescent : baseEnd_2892019 < baseStart_2892019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892066 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2892066 : Nat := 118140960795 + 2892066 * 2 ^ 59
def prefixEnd_2892066 : Nat := 4983230072969 + 3 ^ 40 * 2892066 * 2
def baseEnd_2892066 : Nat := 990013295017324674783091

theorem tailTrace_2892066 : CollatzResearch.WordTrace tailWord_2892066 prefixEnd_2892066 990013295017324674783091 := by
  unfold tailWord_2892066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26370578185136570598622013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70321541827030854929658701 26370578185136570598622013)
  ·
    refine ⟨9888966819426213974483255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26370578185136570598622013 9888966819426213974483255)
    ·
      refine ⟨14833450229139320961724883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9888966819426213974483255 14833450229139320961724883)
      ·
        refine ⟨22250175343708981442587325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14833450229139320961724883 22250175343708981442587325)
        ·
          refine ⟨8343815753890868040970247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22250175343708981442587325 8343815753890868040970247)
          ·
            refine ⟨12515723630836302061455371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343815753890868040970247 12515723630836302061455371)
            ·
              refine ⟨18773585446254453092183057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12515723630836302061455371 18773585446254453092183057)
              ·
                refine ⟨14080189084690839819137293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18773585446254453092183057 14080189084690839819137293)
                ·
                  refine ⟨5280070906759064932176485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14080189084690839819137293 5280070906759064932176485)
                  ·
                    refine ⟨990013295017324674783091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280070906759064932176485 990013295017324674783091)
                    ·
                      rfl

theorem cell22_2892066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2892066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892066 prefixEnd_2892066 := by exact prefixLift 2892066
  have htrace : WordTrace (prefixWord ++ tailWord_2892066) baseStart_2892066 baseEnd_2892066 := by
    simpa [prefixWord, tailWord_2892066, baseEnd_2892066] using wordTrace_append hprefix tailTrace_2892066
  have hstable : (prefixWord ++ tailWord_2892066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892066).length < 2 ^ (prefixWord ++ tailWord_2892066).sum := by decide
  have hdescent : baseEnd_2892066 < baseStart_2892066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892079 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_2892079 : Nat := 118140960795 + 2892079 * 2 ^ 59
def prefixEnd_2892079 : Nat := 4983230072969 + 3 ^ 40 * 2892079 * 2
def baseEnd_2892079 : Nat := 990017745182996974208051

theorem tailTrace_2892079 : CollatzResearch.WordTrace tailWord_2892079 prefixEnd_2892079 990017745182996974208051 := by
  unfold tailWord_2892079
  simp only [CollatzResearch.WordTrace]
  refine ⟨105482786889499185614711291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70321857926332790409807527 105482786889499185614711291)
  ·
    refine ⟨158224180334248778422066937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105482786889499185614711291 158224180334248778422066937)
    ·
      refine ⟨118668135250686583816550203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158224180334248778422066937 118668135250686583816550203)
      ·
        refine ⟨178002202876029875724825305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118668135250686583816550203 178002202876029875724825305)
        ·
          refine ⟨133501652157022406793618979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178002202876029875724825305 133501652157022406793618979)
          ·
            refine ⟨200252478235533610190428469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133501652157022406793618979 200252478235533610190428469)
            ·
              refine ⟨18773669834581275955352669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200252478235533610190428469 18773669834581275955352669)
              ·
                refine ⟨7040126187967978483257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18773669834581275955352669 7040126187967978483257251)
                ·
                  refine ⟨10560189281951967724885877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7040126187967978483257251 10560189281951967724885877)
                  ·
                    refine ⟨990017745182996974208051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10560189281951967724885877 990017745182996974208051)
                    ·
                      rfl

theorem cell22_2892079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_2892079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892079 prefixEnd_2892079 := by exact prefixLift 2892079
  have htrace : WordTrace (prefixWord ++ tailWord_2892079) baseStart_2892079 baseEnd_2892079 := by
    simpa [prefixWord, tailWord_2892079, baseEnd_2892079] using wordTrace_append hprefix tailTrace_2892079
  have hstable : (prefixWord ++ tailWord_2892079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892079).length < 2 ^ (prefixWord ++ tailWord_2892079).sum := by decide
  have hdescent : baseEnd_2892079 < baseStart_2892079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892081 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 6]
def baseStart_2892081 : Nat := 118140960795 + 2892081 * 2 ^ 59
def prefixEnd_2892081 : Nat := 4983230072969 + 3 ^ 40 * 2892081 * 2
def baseEnd_2892081 : Nat := 330006143274623211886015

theorem tailTrace_2892081 : CollatzResearch.WordTrace tailWord_2892081 prefixEnd_2892081 330006143274623211886015 := by
  unfold tailWord_2892081
  simp only [CollatzResearch.WordTrace]
  refine ⟨105482859835491939956284097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70321906556994626637522731 105482859835491939956284097)
  ·
    refine ⟨79112144876618954967213073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105482859835491939956284097 79112144876618954967213073)
    ·
      refine ⟨59334108657464216225409805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79112144876618954967213073 59334108657464216225409805)
      ·
        refine ⟨22250290746549081084528677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59334108657464216225409805 22250290746549081084528677)
        ·
          refine ⟨4171929514977952703349127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22250290746549081084528677 4171929514977952703349127)
          ·
            refine ⟨6257894272466929055023691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171929514977952703349127 6257894272466929055023691)
            ·
              refine ⟨9386841408700393582535537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257894272466929055023691 9386841408700393582535537)
              ·
                refine ⟨7040131056525295186901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9386841408700393582535537 7040131056525295186901653)
                ·
                  refine ⟨330006143274623211886015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7040131056525295186901653 330006143274623211886015)
                  ·
                    rfl

theorem cell22_2892081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_2892081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892081 prefixEnd_2892081 := by exact prefixLift 2892081
  have htrace : WordTrace (prefixWord ++ tailWord_2892081) baseStart_2892081 baseEnd_2892081 := by
    simpa [prefixWord, tailWord_2892081, baseEnd_2892081] using wordTrace_append hprefix tailTrace_2892081
  have hstable : (prefixWord ++ tailWord_2892081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892081).length < 2 ^ (prefixWord ++ tailWord_2892081).sum := by decide
  have hdescent : baseEnd_2892081 < baseStart_2892081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892100 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2892100 : Nat := 118140960795 + 2892100 * 2 ^ 59
def prefixEnd_2892100 : Nat := 4983230072969 + 3 ^ 40 * 2892100 * 2
def baseEnd_2892100 : Nat := 990024933912159919432987

theorem tailTrace_2892100 : CollatzResearch.WordTrace tailWord_2892100 prefixEnd_2892100 990024933912159919432987 := by
  unfold tailWord_2892100
  simp only [CollatzResearch.WordTrace]
  refine ⟨52741776411211553100612877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70322368548282070800817169 52741776411211553100612877)
  ·
    refine ⟨19778166154204332412729829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52741776411211553100612877 19778166154204332412729829)
    ·
      refine ⟨3708406153913312327386843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19778166154204332412729829 3708406153913312327386843)
      ·
        refine ⟨5562609230869968491080265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708406153913312327386843 5562609230869968491080265)
        ·
          refine ⟨4171956923152476368310199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5562609230869968491080265 4171956923152476368310199)
          ·
            refine ⟨6257935384728714552465299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171956923152476368310199 6257935384728714552465299)
            ·
              refine ⟨9386903077093071828697949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257935384728714552465299 9386903077093071828697949)
              ·
                refine ⟨3520088653909901935761731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9386903077093071828697949 3520088653909901935761731)
                ·
                  refine ⟨5280132980864852903642597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520088653909901935761731 5280132980864852903642597)
                  ·
                    refine ⟨990024933912159919432987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280132980864852903642597 990024933912159919432987)
                    ·
                      rfl

theorem cell22_2892100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2892100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892100 prefixEnd_2892100 := by exact prefixLift 2892100
  have htrace : WordTrace (prefixWord ++ tailWord_2892100) baseStart_2892100 baseEnd_2892100 := by
    simpa [prefixWord, tailWord_2892100, baseEnd_2892100] using wordTrace_append hprefix tailTrace_2892100
  have hstable : (prefixWord ++ tailWord_2892100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892100).length < 2 ^ (prefixWord ++ tailWord_2892100).sum := by decide
  have hdescent : baseEnd_2892100 < baseStart_2892100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892113 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_2892113 : Nat := 118140960795 + 2892113 * 2 ^ 59
def prefixEnd_2892113 : Nat := 4983230072969 + 3 ^ 40 * 2892113 * 2
def baseEnd_2892113 : Nat := 990029384077832218857947

theorem tailTrace_2892113 : CollatzResearch.WordTrace tailWord_2892113 prefixEnd_2892113 990029384077832218857947 := by
  unfold tailWord_2892113
  simp only [CollatzResearch.WordTrace]
  refine ⟨105484026971376009421448993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70322684647584006280965995 105484026971376009421448993)
  ·
    refine ⟨79113020228532007066086745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105484026971376009421448993 79113020228532007066086745)
    ·
      refine ⟨59334765171399005299565059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79113020228532007066086745 59334765171399005299565059)
      ·
        refine ⟨89002147757098507949347589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59334765171399005299565059 89002147757098507949347589)
        ·
          refine ⟨16687902704455970240502673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89002147757098507949347589 16687902704455970240502673)
          ·
            refine ⟨12515927028341977680377005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16687902704455970240502673 12515927028341977680377005)
            ·
              refine ⟨4693472635628241630141377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12515927028341977680377005 4693472635628241630141377)
              ·
                refine ⟨3520104476721181222606033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693472635628241630141377 3520104476721181222606033)
                ·
                  refine ⟨2640078357540885916954525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3520104476721181222606033 2640078357540885916954525)
                  ·
                    refine ⟨990029384077832218857947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640078357540885916954525 990029384077832218857947)
                    ·
                      rfl

theorem cell22_2892113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_2892113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892113 prefixEnd_2892113 := by exact prefixLift 2892113
  have htrace : WordTrace (prefixWord ++ tailWord_2892113) baseStart_2892113 baseEnd_2892113 := by
    simpa [prefixWord, tailWord_2892113, baseEnd_2892113] using wordTrace_append hprefix tailTrace_2892113
  have hstable : (prefixWord ++ tailWord_2892113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892113).length < 2 ^ (prefixWord ++ tailWord_2892113).sum := by decide
  have hdescent : baseEnd_2892113 < baseStart_2892113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892293 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_2892293 : Nat := 118140960795 + 2892293 * 2 ^ 59
def prefixEnd_2892293 : Nat := 4983230072969 + 3 ^ 40 * 2892293 * 2
def baseEnd_2892293 : Nat := 990091001756371749357395

theorem tailTrace_2892293 : CollatzResearch.WordTrace tailWord_2892293 prefixEnd_2892293 990091001756371749357395 := by
  unfold tailWord_2892293
  simp only [CollatzResearch.WordTrace]
  refine ⟨105490592110723900163001533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70327061407149266775334355 105490592110723900163001533)
  ·
    refine ⟨39558972041521462561125575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105490592110723900163001533 39558972041521462561125575)
    ·
      refine ⟨59338458062282193841688363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39558972041521462561125575 59338458062282193841688363)
      ·
        refine ⟨89007687093423290762532545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59338458062282193841688363 89007687093423290762532545)
        ·
          refine ⟨66755765320067468071899409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89007687093423290762532545 66755765320067468071899409)
          ·
            refine ⟨50066823990050601053924557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66755765320067468071899409 50066823990050601053924557)
            ·
              refine ⟨18775058996268975395221709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50066823990050601053924557 18775058996268975395221709)
              ·
                refine ⟨7040647123600865773208141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18775058996268975395221709 7040647123600865773208141)
                ·
                  refine ⟨2640242671350324664953053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7040647123600865773208141 2640242671350324664953053)
                  ·
                    refine ⟨990091001756371749357395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640242671350324664953053 990091001756371749357395)
                    ·
                      rfl

theorem cell22_2892293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_2892293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892293 prefixEnd_2892293 := by exact prefixLift 2892293
  have htrace : WordTrace (prefixWord ++ tailWord_2892293) baseStart_2892293 baseEnd_2892293 := by
    simpa [prefixWord, tailWord_2892293, baseEnd_2892293] using wordTrace_append hprefix tailTrace_2892293
  have hstable : (prefixWord ++ tailWord_2892293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892293).length < 2 ^ (prefixWord ++ tailWord_2892293).sum := by decide
  have hdescent : baseEnd_2892293 < baseStart_2892293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892383 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 6, 3]
def baseStart_2892383 : Nat := 118140960795 + 2892383 * 2 ^ 59
def prefixEnd_2892383 : Nat := 4983230072969 + 3 ^ 40 * 2892383 * 2
def baseEnd_2892383 : Nat := 990121810595641514607119

theorem tailTrace_2892383 : CollatzResearch.WordTrace tailWord_2892383 prefixEnd_2892383 990121810595641514607119 := by
  unfold tailWord_2892383
  simp only [CollatzResearch.WordTrace]
  refine ⟨105493874680397845533777803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70329249786931897022518535 105493874680397845533777803)
  ·
    refine ⟨158240812020596768300666705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105493874680397845533777803 158240812020596768300666705)
    ·
      refine ⟨118680609015447576225500029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158240812020596768300666705 118680609015447576225500029)
      ·
        refine ⟨44505228380792841084562511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118680609015447576225500029 44505228380792841084562511)
        ·
          refine ⟨66757842571189261626843767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44505228380792841084562511 66757842571189261626843767)
          ·
            refine ⟨100136763856783892440265651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66757842571189261626843767 100136763856783892440265651)
            ·
              refine ⟨150205145785175838660398477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100136763856783892440265651 150205145785175838660398477)
              ·
                refine ⟨56326929669440939497649429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150205145785175838660398477 56326929669440939497649429)
                ·
                  refine ⟨2640324828255044038952317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56326929669440939497649429 2640324828255044038952317)
                  ·
                    refine ⟨990121810595641514607119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640324828255044038952317 990121810595641514607119)
                    ·
                      rfl

theorem cell22_2892383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_2892383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892383 prefixEnd_2892383 := by exact prefixLift 2892383
  have htrace : WordTrace (prefixWord ++ tailWord_2892383) baseStart_2892383 baseEnd_2892383 := by
    simpa [prefixWord, tailWord_2892383, baseEnd_2892383] using wordTrace_append hprefix tailTrace_2892383
  have hstable : (prefixWord ++ tailWord_2892383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892383).length < 2 ^ (prefixWord ++ tailWord_2892383).sum := by decide
  have hdescent : baseEnd_2892383 < baseStart_2892383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892402 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_2892402 : Nat := 118140960795 + 2892402 * 2 ^ 59
def prefixEnd_2892402 : Nat := 4983230072969 + 3 ^ 40 * 2892402 * 2
def baseEnd_2892402 : Nat := 330042771561310599460687

theorem tailTrace_2892402 : CollatzResearch.WordTrace tailWord_2892402 prefixEnd_2892402 330042771561310599460687 := by
  unfold tailWord_2892402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26373641916832252944679865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70329711778219341185812973 26373641916832252944679865)
  ·
    refine ⟨19780231437624189708509899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26373641916832252944679865 19780231437624189708509899)
    ·
      refine ⟨29670347156436284562764849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19780231437624189708509899 29670347156436284562764849)
      ·
        refine ⟨22252760367327213422073637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29670347156436284562764849 22252760367327213422073637)
        ·
          refine ⟨4172392568873852516638807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22252760367327213422073637 4172392568873852516638807)
          ·
            refine ⟨6258588853310778774958211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172392568873852516638807 6258588853310778774958211)
            ·
              refine ⟨9387883279966168162437317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258588853310778774958211 9387883279966168162437317)
              ·
                refine ⟨1760228114993656530456997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9387883279966168162437317 1760228114993656530456997)
                ·
                  refine ⟨330042771561310599460687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760228114993656530456997 330042771561310599460687)
                  ·
                    rfl

theorem cell22_2892402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_2892402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892402 prefixEnd_2892402 := by exact prefixLift 2892402
  have htrace : WordTrace (prefixWord ++ tailWord_2892402) baseStart_2892402 baseEnd_2892402 := by
    simpa [prefixWord, tailWord_2892402, baseEnd_2892402] using wordTrace_append hprefix tailTrace_2892402
  have hstable : (prefixWord ++ tailWord_2892402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892402).length < 2 ^ (prefixWord ++ tailWord_2892402).sum := by decide
  have hdescent : baseEnd_2892402 < baseStart_2892402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892430 : List Nat := [4, 1, 1, 3, 1, 1, 5, 6]
def baseStart_2892430 : Nat := 118140960795 + 2892430 * 2 ^ 59
def prefixEnd_2892430 : Nat := 4983230072969 + 3 ^ 40 * 2892430 * 2
def baseEnd_2892430 : Nat := 110015322184016562075775

theorem tailTrace_2892430 : CollatzResearch.WordTrace tailWord_2892430 prefixEnd_2892430 110015322184016562075775 := by
  unfold tailWord_2892430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186948613903446570092343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70330392607485048373825829 13186948613903446570092343)
  ·
    refine ⟨19780422920855169855138515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13186948613903446570092343 19780422920855169855138515)
    ·
      refine ⟨29670634381282754782707773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19780422920855169855138515 29670634381282754782707773)
      ·
        refine ⟨11126487892981033043515415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29670634381282754782707773 11126487892981033043515415)
        ·
          refine ⟨16689731839471549565273123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11126487892981033043515415 16689731839471549565273123)
          ·
            refine ⟨25034597759207324347909685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16689731839471549565273123 25034597759207324347909685)
            ·
              refine ⟨2346993539925686657616533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25034597759207324347909685 2346993539925686657616533)
              ·
                refine ⟨110015322184016562075775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2346993539925686657616533 110015322184016562075775)
                ·
                  rfl

theorem cell22_2892430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_2892430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892430 prefixEnd_2892430 := by exact prefixLift 2892430
  have htrace : WordTrace (prefixWord ++ tailWord_2892430) baseStart_2892430 baseEnd_2892430 := by
    simpa [prefixWord, tailWord_2892430, baseEnd_2892430] using wordTrace_append hprefix tailTrace_2892430
  have hstable : (prefixWord ++ tailWord_2892430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892430).length < 2 ^ (prefixWord ++ tailWord_2892430).sum := by decide
  have hdescent : baseEnd_2892430 < baseStart_2892430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892481 : List Nat := [1, 2, 6, 2, 2, 1, 2, 6]
def baseStart_2892481 : Nat := 118140960795 + 2892481 * 2 ^ 59
def prefixEnd_2892481 : Nat := 4983230072969 + 3 ^ 40 * 2892481 * 2
def baseEnd_2892481 : Nat := 110017261999822436184091

theorem tailTrace_2892481 : CollatzResearch.WordTrace tailWord_2892481 prefixEnd_2892481 110017261999822436184091 := by
  unfold tailWord_2892481
  simp only [CollatzResearch.WordTrace]
  refine ⟨105497449034042808270845297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70331632689361872180563531 105497449034042808270845297)
  ·
    refine ⟨79123086775532106203133973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105497449034042808270845297 79123086775532106203133973)
    ·
      refine ⟨3708894692603067478271905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79123086775532106203133973 3708894692603067478271905)
      ·
        refine ⟨2781671019452300608703929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3708894692603067478271905 2781671019452300608703929)
        ·
          refine ⟨2086253264589225456527947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781671019452300608703929 2086253264589225456527947)
          ·
            refine ⟨3129379896883838184791921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086253264589225456527947 3129379896883838184791921)
            ·
              refine ⟨2347034922662878638593941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129379896883838184791921 2347034922662878638593941)
              ·
                refine ⟨110017261999822436184091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2347034922662878638593941 110017261999822436184091)
                ·
                  rfl

theorem cell22_2892481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 6].length) (baseStart_2892481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892481 prefixEnd_2892481 := by exact prefixLift 2892481
  have htrace : WordTrace (prefixWord ++ tailWord_2892481) baseStart_2892481 baseEnd_2892481 := by
    simpa [prefixWord, tailWord_2892481, baseEnd_2892481] using wordTrace_append hprefix tailTrace_2892481
  have hstable : (prefixWord ++ tailWord_2892481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892481).length < 2 ^ (prefixWord ++ tailWord_2892481).sum := by decide
  have hdescent : baseEnd_2892481 < baseStart_2892481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892505 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_2892505 : Nat := 118140960795 + 2892505 * 2 ^ 59
def prefixEnd_2892505 : Nat := 4983230072969 + 3 ^ 40 * 2892505 * 2
def baseEnd_2892505 : Nat := 990163573688873863056745

theorem tailTrace_2892505 : CollatzResearch.WordTrace tailWord_2892505 prefixEnd_2892505 990163573688873863056745 := by
  unfold tailWord_2892505
  simp only [CollatzResearch.WordTrace]
  refine ⟨105498324385955860369718969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70332216257303906913145979 105498324385955860369718969)
  ·
    refine ⟨79123743289466895277289227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105498324385955860369718969 79123743289466895277289227)
    ·
      refine ⟨118685614934200342915933841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79123743289466895277289227 118685614934200342915933841)
      ·
        refine ⟨89014211200650257186950381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118685614934200342915933841 89014211200650257186950381)
        ·
          refine ⟨33380329200243846445106393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89014211200650257186950381 33380329200243846445106393)
          ·
            refine ⟨25035246900182884833829795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33380329200243846445106393 25035246900182884833829795)
            ·
              refine ⟨37552870350274327250744693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25035246900182884833829795 37552870350274327250744693)
              ·
                refine ⟨3520581595338218179757315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37552870350274327250744693 3520581595338218179757315)
                ·
                  refine ⟨5280872393007327269635973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520581595338218179757315 5280872393007327269635973)
                  ·
                    refine ⟨990163573688873863056745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280872393007327269635973 990163573688873863056745)
                    ·
                      rfl

theorem cell22_2892505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_2892505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892505 prefixEnd_2892505 := by exact prefixLift 2892505
  have htrace : WordTrace (prefixWord ++ tailWord_2892505) baseStart_2892505 baseEnd_2892505 := by
    simpa [prefixWord, tailWord_2892505, baseEnd_2892505] using wordTrace_append hprefix tailTrace_2892505
  have hstable : (prefixWord ++ tailWord_2892505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892505).length < 2 ^ (prefixWord ++ tailWord_2892505).sum := by decide
  have hdescent : baseEnd_2892505 < baseStart_2892505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892597 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2892597 : Nat := 118140960795 + 2892597 * 2 ^ 59
def prefixEnd_2892597 : Nat := 4983230072969 + 3 ^ 40 * 2892597 * 2
def baseEnd_2892597 : Nat := 990195067169016289756463

theorem tailTrace_2892597 : CollatzResearch.WordTrace tailWord_2892597 prefixEnd_2892597 990195067169016289756463 := by
  unfold tailWord_2892597
  simp only [CollatzResearch.WordTrace]
  refine ⟨105501679901622560082068045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70334453267748373388045363 105501679901622560082068045)
  ·
    refine ⟨39563129963108460030775517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105501679901622560082068045 39563129963108460030775517)
    ·
      refine ⟨14836173736165672511540819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39563129963108460030775517 14836173736165672511540819)
      ·
        refine ⟨22254260604248508767311229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14836173736165672511540819 22254260604248508767311229)
        ·
          refine ⟨8345347726593190787741711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22254260604248508767311229 8345347726593190787741711)
          ·
            refine ⟨12518021589889786181612567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345347726593190787741711 12518021589889786181612567)
            ·
              refine ⟨18777032384834679272418851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518021589889786181612567 18777032384834679272418851)
              ·
                refine ⟨28165548577252018908628277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18777032384834679272418851 28165548577252018908628277)
                ·
                  refine ⟨2640520179117376772683901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28165548577252018908628277 2640520179117376772683901)
                  ·
                    refine ⟨990195067169016289756463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640520179117376772683901 990195067169016289756463)
                    ·
                      rfl

theorem cell22_2892597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2892597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892597 prefixEnd_2892597 := by exact prefixLift 2892597
  have htrace : WordTrace (prefixWord ++ tailWord_2892597) baseStart_2892597 baseEnd_2892597 := by
    simpa [prefixWord, tailWord_2892597, baseEnd_2892597] using wordTrace_append hprefix tailTrace_2892597
  have hstable : (prefixWord ++ tailWord_2892597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892597).length < 2 ^ (prefixWord ++ tailWord_2892597).sum := by decide
  have hdescent : baseEnd_2892597 < baseStart_2892597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892644 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2892644 : Nat := 118140960795 + 2892644 * 2 ^ 59
def prefixEnd_2892644 : Nat := 4983230072969 + 3 ^ 40 * 2892644 * 2
def baseEnd_2892644 : Nat := 330070385409841277943773

theorem tailTrace_2892644 : CollatzResearch.WordTrace tailWord_2892644 prefixEnd_2892644 330070385409841277943773 := by
  unfold tailWord_2892644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751697066226143554514493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70335596088301524739352657 52751697066226143554514493)
  ·
    refine ⟨19781886399834803832942935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52751697066226143554514493 19781886399834803832942935)
    ·
      refine ⟨29672829599752205749414403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19781886399834803832942935 29672829599752205749414403)
      ·
        refine ⟨44509244399628308624121605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29672829599752205749414403 44509244399628308624121605)
        ·
          refine ⟨8345483324930307867022801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44509244399628308624121605 8345483324930307867022801)
          ·
            refine ⟨6259112493697730900267101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345483324930307867022801 6259112493697730900267101)
            ·
              refine ⟨2347167185136649087600163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6259112493697730900267101 2347167185136649087600163)
              ·
                refine ⟨3520750777704973631400245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347167185136649087600163 3520750777704973631400245)
                ·
                  refine ⟨330070385409841277943773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3520750777704973631400245 330070385409841277943773)
                  ·
                    rfl

theorem cell22_2892644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2892644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892644 prefixEnd_2892644 := by exact prefixLift 2892644
  have htrace : WordTrace (prefixWord ++ tailWord_2892644) baseStart_2892644 baseEnd_2892644 := by
    simpa [prefixWord, tailWord_2892644, baseEnd_2892644] using wordTrace_append hprefix tailTrace_2892644
  have hstable : (prefixWord ++ tailWord_2892644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892644).length < 2 ^ (prefixWord ++ tailWord_2892644).sum := by decide
  have hdescent : baseEnd_2892644 < baseStart_2892644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892657 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_2892657 : Nat := 118140960795 + 2892657 * 2 ^ 59
def prefixEnd_2892657 : Nat := 4983230072969 + 3 ^ 40 * 2892657 * 2
def baseEnd_2892657 : Nat := 990215606395196133256279

theorem tailTrace_2892657 : CollatzResearch.WordTrace tailWord_2892657 prefixEnd_2892657 990215606395196133256279 := by
  unfold tailWord_2892657
  simp only [CollatzResearch.WordTrace]
  refine ⟨105503868281405190329252225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70335912187603460219501483 105503868281405190329252225)
  ·
    refine ⟨79127901211053892746939169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105503868281405190329252225 79127901211053892746939169)
    ·
      refine ⟨59345925908290419560204377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79127901211053892746939169 59345925908290419560204377)
      ·
        refine ⟨44509444431217814670153283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59345925908290419560204377 44509444431217814670153283)
        ·
          refine ⟨66764166646826722005229925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44509444431217814670153283 66764166646826722005229925)
          ·
            refine ⟨12518281246280010375980611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66764166646826722005229925 12518281246280010375980611)
            ·
              refine ⟨18777421869420015563970917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518281246280010375980611 18777421869420015563970917)
              ·
                refine ⟨3520766600516252918244547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18777421869420015563970917 3520766600516252918244547)
                ·
                  refine ⟨5281149900774379377366821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520766600516252918244547 5281149900774379377366821)
                  ·
                    refine ⟨990215606395196133256279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5281149900774379377366821 990215606395196133256279)
                    ·
                      rfl

theorem cell22_2892657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_2892657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892657 prefixEnd_2892657 := by exact prefixLift 2892657
  have htrace : WordTrace (prefixWord ++ tailWord_2892657) baseStart_2892657 baseEnd_2892657 := by
    simpa [prefixWord, tailWord_2892657, baseEnd_2892657] using wordTrace_append hprefix tailTrace_2892657
  have hstable : (prefixWord ++ tailWord_2892657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892657).length < 2 ^ (prefixWord ++ tailWord_2892657).sum := by decide
  have hdescent : baseEnd_2892657 < baseStart_2892657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892672 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_2892672 : Nat := 118140960795 + 2892672 * 2 ^ 59
def prefixEnd_2892672 : Nat := 4983230072969 + 3 ^ 40 * 2892672 * 2
def baseEnd_2892672 : Nat := 330073580400580364710411

theorem tailTrace_2892672 : CollatzResearch.WordTrace tailWord_2892672 prefixEnd_2892672 330073580400580364710411 := by
  unfold tailWord_2892672
  simp only [CollatzResearch.WordTrace]
  refine ⟨52752207688175423945524135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70336276917567231927365513 52752207688175423945524135)
  ·
    refine ⟨79128311532263135918286203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52752207688175423945524135 79128311532263135918286203)
    ·
      refine ⟨118692467298394703877429305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79128311532263135918286203 118692467298394703877429305)
      ·
        refine ⟨89019350473796027908071979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118692467298394703877429305 89019350473796027908071979)
        ·
          refine ⟨133529025710694041862107969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89019350473796027908071979 133529025710694041862107969)
          ·
            refine ⟨100146769283020531396580977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133529025710694041862107969 100146769283020531396580977)
            ·
              refine ⟨75110076962265398547435733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100146769283020531396580977 75110076962265398547435733)
              ·
                refine ⟨1760392428803095278455525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75110076962265398547435733 1760392428803095278455525)
                ·
                  refine ⟨330073580400580364710411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760392428803095278455525 330073580400580364710411)
                  ·
                    rfl

theorem cell22_2892672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_2892672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892672 prefixEnd_2892672 := by exact prefixLift 2892672
  have htrace : WordTrace (prefixWord ++ tailWord_2892672) baseStart_2892672 baseEnd_2892672 := by
    simpa [prefixWord, tailWord_2892672, baseEnd_2892672] using wordTrace_append hprefix tailTrace_2892672
  have hstable : (prefixWord ++ tailWord_2892672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892672).length < 2 ^ (prefixWord ++ tailWord_2892672).sum := by decide
  have hdescent : baseEnd_2892672 < baseStart_2892672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892740 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_2892740 : Nat := 118140960795 + 2892740 * 2 ^ 59
def prefixEnd_2892740 : Nat := 4983230072969 + 3 ^ 40 * 2892740 * 2
def baseEnd_2892740 : Nat := 330081339663803861143675

theorem tailTrace_2892740 : CollatzResearch.WordTrace tailWord_2892740 prefixEnd_2892740 330081339663803861143675 := by
  unfold tailWord_2892740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52753447770052247752261837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70337930360069663669682449 52753447770052247752261837)
  ·
    refine ⟨19782542913769592907098189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52753447770052247752261837 19782542913769592907098189)
    ·
      refine ⟨7418453592663597340161821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19782542913769592907098189 7418453592663597340161821)
      ·
        refine ⟨2781920097248849002560683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7418453592663597340161821 2781920097248849002560683)
        ·
          refine ⟨4172880145873273503841025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781920097248849002560683 4172880145873273503841025)
          ·
            refine ⟨3129660109404955127880769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4172880145873273503841025 3129660109404955127880769)
            ·
              refine ⟨2347245082053716345910577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129660109404955127880769 2347245082053716345910577)
              ·
                refine ⟨1760433811540287259432933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347245082053716345910577 1760433811540287259432933)
                ·
                  refine ⟨330081339663803861143675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760433811540287259432933 330081339663803861143675)
                  ·
                    rfl

theorem cell22_2892740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_2892740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892740 prefixEnd_2892740 := by exact prefixLift 2892740
  have htrace : WordTrace (prefixWord ++ tailWord_2892740) baseStart_2892740 baseEnd_2892740 := by
    simpa [prefixWord, tailWord_2892740, baseEnd_2892740] using wordTrace_append hprefix tailTrace_2892740
  have hstable : (prefixWord ++ tailWord_2892740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892740).length < 2 ^ (prefixWord ++ tailWord_2892740).sum := by decide
  have hdescent : baseEnd_2892740 < baseStart_2892740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892837 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2892837 : Nat := 118140960795 + 2892837 * 2 ^ 59
def prefixEnd_2892837 : Nat := 4983230072969 + 3 ^ 40 * 2892837 * 2
def baseEnd_2892837 : Nat := 990277224073735663755727

theorem tailTrace_2892837 : CollatzResearch.WordTrace tailWord_2892837 prefixEnd_2892837 990277224073735663755727 := by
  unfold tailWord_2892837
  simp only [CollatzResearch.WordTrace]
  refine ⟨105510433420753081070804765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70340288947168720713869843 105510433420753081070804765)
  ·
    refine ⟨39566412532782405401551787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105510433420753081070804765 39566412532782405401551787)
    ·
      refine ⟨59349618799173608102327681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39566412532782405401551787 59349618799173608102327681)
      ·
        refine ⟨44512214099380206076745761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59349618799173608102327681 44512214099380206076745761)
        ·
          refine ⟨33384160574535154557559321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44512214099380206076745761 33384160574535154557559321)
          ·
            refine ⟨25038120430901365918169491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33384160574535154557559321 25038120430901365918169491)
            ·
              refine ⟨37557180646352048877254237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25038120430901365918169491 37557180646352048877254237)
              ·
                refine ⟨14083942742382018328970339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37557180646352048877254237 14083942742382018328970339)
                ·
                  refine ⟨21125914113573027493455509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14083942742382018328970339 21125914113573027493455509)
                  ·
                    refine ⟨990277224073735663755727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21125914113573027493455509 990277224073735663755727)
                    ·
                      rfl

theorem cell22_2892837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2892837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892837 prefixEnd_2892837 := by exact prefixLift 2892837
  have htrace : WordTrace (prefixWord ++ tailWord_2892837) baseStart_2892837 baseEnd_2892837 := by
    simpa [prefixWord, tailWord_2892837, baseEnd_2892837] using wordTrace_append hprefix tailTrace_2892837
  have hstable : (prefixWord ++ tailWord_2892837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892837).length < 2 ^ (prefixWord ++ tailWord_2892837).sum := by decide
  have hdescent : baseEnd_2892837 < baseStart_2892837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892897 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 9]
def baseStart_2892897 : Nat := 118140960795 + 2892897 * 2 ^ 59
def prefixEnd_2892897 : Nat := 4983230072969 + 3 ^ 40 * 2892897 * 2
def baseEnd_2892897 : Nat := 330099254433305169085181

theorem tailTrace_2892897 : CollatzResearch.WordTrace tailWord_2892897 prefixEnd_2892897 330099254433305169085181 := by
  unfold tailWord_2892897
  simp only [CollatzResearch.WordTrace]
  refine ⟨105512621800535711317988945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70341747867023807545325963 105512621800535711317988945)
  ·
    refine ⟨79134466350401783488491709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105512621800535711317988945 79134466350401783488491709)
    ·
      refine ⟨29675424881400668808184391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79134466350401783488491709 29675424881400668808184391)
      ·
        refine ⟨44513137322101003212276587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29675424881400668808184391 44513137322101003212276587)
        ·
          refine ⟨66769705983151504818414881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44513137322101003212276587 66769705983151504818414881)
          ·
            refine ⟨50077279487363628613811161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66769705983151504818414881 50077279487363628613811161)
            ·
              refine ⟨37557959615522721460358371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50077279487363628613811161 37557959615522721460358371)
              ·
                refine ⟨56336939423284082190537557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37557959615522721460358371 56336939423284082190537557)
                ·
                  refine ⟨330099254433305169085181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56336939423284082190537557 330099254433305169085181)
                  ·
                    rfl

theorem cell22_2892897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_2892897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892897 prefixEnd_2892897 := by exact prefixLift 2892897
  have htrace : WordTrace (prefixWord ++ tailWord_2892897) baseStart_2892897 baseEnd_2892897 := by
    simpa [prefixWord, tailWord_2892897, baseEnd_2892897] using wordTrace_append hprefix tailTrace_2892897
  have hstable : (prefixWord ++ tailWord_2892897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892897).length < 2 ^ (prefixWord ++ tailWord_2892897).sum := by decide
  have hdescent : baseEnd_2892897 < baseStart_2892897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892929 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2892929 : Nat := 118140960795 + 2892929 * 2 ^ 59
def prefixEnd_2892929 : Nat := 4983230072969 + 3 ^ 40 * 2892929 * 2
def baseEnd_2892929 : Nat := 990308717553878090455445

theorem tailTrace_2892929 : CollatzResearch.WordTrace tailWord_2892929 prefixEnd_2892929 990308717553878090455445 := by
  unfold tailWord_2892929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105513788936419780783153841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70342525957613187188769227 105513788936419780783153841)
  ·
    refine ⟨79135341702314835587365381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105513788936419780783153841 79135341702314835587365381)
    ·
      refine ⟨14837876569184031672631009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79135341702314835587365381 14837876569184031672631009)
      ·
        refine ⟨11128407426888023754473257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14837876569184031672631009 11128407426888023754473257)
        ·
          refine ⟨8346305570166017815854943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11128407426888023754473257 8346305570166017815854943)
          ·
            refine ⟨12519458355249026723782415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346305570166017815854943 12519458355249026723782415)
            ·
              refine ⟨18779187532873540085673623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519458355249026723782415 18779187532873540085673623)
              ·
                refine ⟨28168781299310310128510435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18779187532873540085673623 28168781299310310128510435)
                ·
                  refine ⟨42253171948965465192765653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28168781299310310128510435 42253171948965465192765653)
                  ·
                    refine ⟨990308717553878090455445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42253171948965465192765653 990308717553878090455445)
                    ·
                      rfl

theorem cell22_2892929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2892929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892929 prefixEnd_2892929 := by exact prefixLift 2892929
  have htrace : WordTrace (prefixWord ++ tailWord_2892929) baseStart_2892929 baseEnd_2892929 := by
    simpa [prefixWord, tailWord_2892929, baseEnd_2892929] using wordTrace_append hprefix tailTrace_2892929
  have hstable : (prefixWord ++ tailWord_2892929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892929).length < 2 ^ (prefixWord ++ tailWord_2892929).sum := by decide
  have hdescent : baseEnd_2892929 < baseStart_2892929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892961 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2892961 : Nat := 118140960795 + 2892961 * 2 ^ 59
def prefixEnd_2892961 : Nat := 4983230072969 + 3 ^ 40 * 2892961 * 2
def baseEnd_2892961 : Nat := 990319671807840673655347

theorem tailTrace_2892961 : CollatzResearch.WordTrace tailWord_2892961 prefixEnd_2892961 990319671807840673655347 := by
  unfold tailWord_2892961
  simp only [CollatzResearch.WordTrace]
  refine ⟨105514956072303850248318737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70343304048202566832212491 105514956072303850248318737)
  ·
    refine ⟨79136217054227887686239053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105514956072303850248318737 79136217054227887686239053)
    ·
      refine ⟨29676081395335457882339645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79136217054227887686239053 29676081395335457882339645)
      ·
        refine ⟨11128530523250796705877367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29676081395335457882339645 11128530523250796705877367)
        ·
          refine ⟨16692795784876195058816051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11128530523250796705877367 16692795784876195058816051)
          ·
            refine ⟨25039193677314292588224077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16692795784876195058816051 25039193677314292588224077)
            ·
              refine ⟨9389697628992859720584029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25039193677314292588224077 9389697628992859720584029)
              ·
                refine ⟨3521136610872322395219011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9389697628992859720584029 3521136610872322395219011)
                ·
                  refine ⟨5281704916308483592828517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521136610872322395219011 5281704916308483592828517)
                  ·
                    refine ⟨990319671807840673655347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5281704916308483592828517 990319671807840673655347)
                    ·
                      rfl

theorem cell22_2892961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2892961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892961 prefixEnd_2892961 := by exact prefixLift 2892961
  have htrace : WordTrace (prefixWord ++ tailWord_2892961) baseStart_2892961 baseEnd_2892961 := by
    simpa [prefixWord, tailWord_2892961, baseEnd_2892961] using wordTrace_append hprefix tailTrace_2892961
  have hstable : (prefixWord ++ tailWord_2892961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892961).length < 2 ^ (prefixWord ++ tailWord_2892961).sum := by decide
  have hdescent : baseEnd_2892961 < baseStart_2892961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892982 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2892982 : Nat := 118140960795 + 2892982 * 2 ^ 59
def prefixEnd_2892982 : Nat := 4983230072969 + 3 ^ 40 * 2892982 * 2
def baseEnd_2892982 : Nat := 330108953512334539626761

theorem tailTrace_2892982 : CollatzResearch.WordTrace tailWord_2892982 prefixEnd_2892982 330108953512334539626761 := by
  unfold tailWord_2892982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594732625326735677177075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70343814670151847223222133 6594732625326735677177075)
  ·
    refine ⟨9892098937990103515765613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6594732625326735677177075 9892098937990103515765613)
    ·
      refine ⟨3709537101746288818412105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9892098937990103515765613 3709537101746288818412105)
      ·
        refine ⟨2782152826309716613809079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3709537101746288818412105 2782152826309716613809079)
        ·
          refine ⟨4173229239464574920713619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782152826309716613809079 4173229239464574920713619)
          ·
            refine ⟨6259843859196862381070429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173229239464574920713619 6259843859196862381070429)
            ·
              refine ⟨2347441447198823392901411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6259843859196862381070429 2347441447198823392901411)
              ·
                refine ⟨3521162170798235089352117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347441447198823392901411 3521162170798235089352117)
                ·
                  refine ⟨330108953512334539626761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521162170798235089352117 330108953512334539626761)
                  ·
                    rfl

theorem cell22_2892982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2892982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892982 prefixEnd_2892982 := by exact prefixLift 2892982
  have htrace : WordTrace (prefixWord ++ tailWord_2892982) baseStart_2892982 baseEnd_2892982 := by
    simpa [prefixWord, tailWord_2892982, baseEnd_2892982] using wordTrace_append hprefix tailTrace_2892982
  have hstable : (prefixWord ++ tailWord_2892982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892982).length < 2 ^ (prefixWord ++ tailWord_2892982).sum := by decide
  have hdescent : baseEnd_2892982 < baseStart_2892982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892989 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2892989 : Nat := 118140960795 + 2892989 * 2 ^ 59
def prefixEnd_2892989 : Nat := 4983230072969 + 3 ^ 40 * 2892989 * 2
def baseEnd_2892989 : Nat := 990329256780057933955261

theorem tailTrace_2892989 : CollatzResearch.WordTrace tailWord_2892989 prefixEnd_2892989 990329256780057933955261 := by
  unfold tailWord_2892989
  simp only [CollatzResearch.WordTrace]
  refine ⟨105515977316202411030338021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70343984877468274020225347 105515977316202411030338021)
  ·
    refine ⟨19784245746787952068188379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105515977316202411030338021 19784245746787952068188379)
    ·
      refine ⟨29676368620181928102282569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19784245746787952068188379 29676368620181928102282569)
      ·
        refine ⟨22257276465136446076711927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29676368620181928102282569 22257276465136446076711927)
        ·
          refine ⟨33385914697704669115067891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22257276465136446076711927 33385914697704669115067891)
          ·
            refine ⟨50078872046557003672601837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33385914697704669115067891 50078872046557003672601837)
            ·
              refine ⟨18779577017458876377225689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50078872046557003672601837 18779577017458876377225689)
              ·
                refine ⟨14084682763094157282919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18779577017458876377225689 14084682763094157282919267)
                ·
                  refine ⟨21127024144641235924378901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14084682763094157282919267 21127024144641235924378901)
                  ·
                    refine ⟨990329256780057933955261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21127024144641235924378901 990329256780057933955261)
                    ·
                      rfl

theorem cell22_2892989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2892989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892989 prefixEnd_2892989 := by exact prefixLift 2892989
  have htrace : WordTrace (prefixWord ++ tailWord_2892989) baseStart_2892989 baseEnd_2892989 := by
    simpa [prefixWord, tailWord_2892989, baseEnd_2892989] using wordTrace_append hprefix tailTrace_2892989
  have hstable : (prefixWord ++ tailWord_2892989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892989).length < 2 ^ (prefixWord ++ tailWord_2892989).sum := by decide
  have hdescent : baseEnd_2892989 < baseStart_2892989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892991 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 2, 3]
def baseStart_2892991 : Nat := 118140960795 + 2892991 * 2 ^ 59
def prefixEnd_2892991 : Nat := 4983230072969 + 3 ^ 40 * 2892991 * 2
def baseEnd_2892991 : Nat := 990329941420930595405255

theorem tailTrace_2892991 : CollatzResearch.WordTrace tailWord_2892991 prefixEnd_2892991 990329941420930595405255 := by
  unfold tailWord_2892991
  simp only [CollatzResearch.WordTrace]
  refine ⟨105516050262195165371910827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70344033508130110247940551 105516050262195165371910827)
  ·
    refine ⟨158274075393292748057866241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105516050262195165371910827 158274075393292748057866241)
    ·
      refine ⟨118705556544969561043399681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158274075393292748057866241 118705556544969561043399681)
      ·
        refine ⟨89029167408727170782549761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118705556544969561043399681 89029167408727170782549761)
        ·
          refine ⟨66771875556545378086912321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89029167408727170782549761 66771875556545378086912321)
          ·
            refine ⟨50078906667409033565184241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66771875556545378086912321 50078906667409033565184241)
            ·
              refine ⟨37559180000556775173888181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50078906667409033565184241 37559180000556775173888181)
              ·
                refine ⟨3521173125052197672552017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37559180000556775173888181 3521173125052197672552017)
                ·
                  refine ⟨2640879843789148254414013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521173125052197672552017 2640879843789148254414013)
                  ·
                    refine ⟨990329941420930595405255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640879843789148254414013 990329941420930595405255)
                    ·
                      rfl

theorem cell22_2892991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_2892991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2892991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2892991 prefixEnd_2892991 := by exact prefixLift 2892991
  have htrace : WordTrace (prefixWord ++ tailWord_2892991) baseStart_2892991 baseEnd_2892991 := by
    simpa [prefixWord, tailWord_2892991, baseEnd_2892991] using wordTrace_append hprefix tailTrace_2892991
  have hstable : (prefixWord ++ tailWord_2892991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892991).length < 2 ^ (prefixWord ++ tailWord_2892991).sum := by decide
  have hdescent : baseEnd_2892991 < baseStart_2892991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893042 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_2893042 : Nat := 118140960795 + 2893042 * 2 ^ 59
def prefixEnd_2893042 : Nat := 4983230072969 + 3 ^ 40 * 2893042 * 2
def baseEnd_2893042 : Nat := 990347399763183462380099

theorem tailTrace_2893042 : CollatzResearch.WordTrace tailWord_2893042 prefixEnd_2893042 990347399763183462380099 := by
  unfold tailWord_2893042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379477596252600270504345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70345273590006934054678253 26379477596252600270504345)
  ·
    refine ⟨19784608197189450202878259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26379477596252600270504345 19784608197189450202878259)
    ·
      refine ⟨29676912295784175304317389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19784608197189450202878259 29676912295784175304317389)
      ·
        refine ⟨11128842110919065739119021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29676912295784175304317389 11128842110919065739119021)
        ·
          refine ⟨4173315791594649652169633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11128842110919065739119021 4173315791594649652169633)
          ·
            refine ⟨3129986843695987239127225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173315791594649652169633 3129986843695987239127225)
            ·
              refine ⟨2347490132771990429345419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129986843695987239127225 2347490132771990429345419)
              ·
                refine ⟨3521235199157985644018129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347490132771990429345419 3521235199157985644018129)
                ·
                  refine ⟨2640926399368489233013597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521235199157985644018129 2640926399368489233013597)
                  ·
                    refine ⟨990347399763183462380099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640926399368489233013597 990347399763183462380099)
                    ·
                      rfl

theorem cell22_2893042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_2893042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893042 prefixEnd_2893042 := by exact prefixLift 2893042
  have htrace : WordTrace (prefixWord ++ tailWord_2893042) baseStart_2893042 baseEnd_2893042 := by
    simpa [prefixWord, tailWord_2893042, baseEnd_2893042] using wordTrace_append hprefix tailTrace_2893042
  have hstable : (prefixWord ++ tailWord_2893042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893042).length < 2 ^ (prefixWord ++ tailWord_2893042).sum := by decide
  have hdescent : baseEnd_2893042 < baseStart_2893042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893098 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2893098 : Nat := 118140960795 + 2893098 * 2 ^ 59
def prefixEnd_2893098 : Nat := 4983230072969 + 3 ^ 40 * 2893098 * 2
def baseEnd_2893098 : Nat := 990366569707617982979927

theorem tailTrace_2893098 : CollatzResearch.WordTrace tailWord_2893098 prefixEnd_2893098 990366569707617982979927 := by
  unfold tailWord_2893098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379988218201880661513987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70346635248538348430703965 26379988218201880661513987)
  ·
    refine ⟨39569982327302820992270981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26379988218201880661513987 39569982327302820992270981)
    ·
      refine ⟨7419371686369278936050809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39569982327302820992270981 7419371686369278936050809)
      ·
        refine ⟨5564528764776959202038107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7419371686369278936050809 5564528764776959202038107)
        ·
          refine ⟨8346793147165438803057161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564528764776959202038107 8346793147165438803057161)
          ·
            refine ⟨6260094860374079102292871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8346793147165438803057161 6260094860374079102292871)
            ·
              refine ⟨9390142290561118653439307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260094860374079102292871 9390142290561118653439307)
              ·
                refine ⟨14085213435841677980158961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390142290561118653439307 14085213435841677980158961)
                ·
                  refine ⟨10563910076881258485119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14085213435841677980158961 10563910076881258485119221)
                  ·
                    refine ⟨990366569707617982979927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10563910076881258485119221 990366569707617982979927)
                    ·
                      rfl

theorem cell22_2893098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2893098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893098 prefixEnd_2893098 := by exact prefixLift 2893098
  have htrace : WordTrace (prefixWord ++ tailWord_2893098) baseStart_2893098 baseEnd_2893098 := by
    simpa [prefixWord, tailWord_2893098, baseEnd_2893098] using wordTrace_append hprefix tailTrace_2893098
  have hstable : (prefixWord ++ tailWord_2893098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893098).length < 2 ^ (prefixWord ++ tailWord_2893098).sum := by decide
  have hdescent : baseEnd_2893098 < baseStart_2893098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893139 : List Nat := [1, 1, 1, 2, 1, 1, 15]
def baseStart_2893139 : Nat := 118140960795 + 2893139 * 2 ^ 59
def prefixEnd_2893139 : Nat := 4983230072969 + 3 ^ 40 * 2893139 * 2
def baseEnd_2893139 : Nat := 36680763142426205285363

theorem tailTrace_2893139 : CollatzResearch.WordTrace tailWord_2893139 prefixEnd_2893139 36680763142426205285363 := by
  unfold tailWord_2893139
  simp only [CollatzResearch.WordTrace]
  refine ⟨105521448265658986648298471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70347632177105991098865647 105521448265658986648298471)
  ·
    refine ⟨158282172398488479972447707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105521448265658986648298471 158282172398488479972447707)
    ·
      refine ⟨237423258597732719958671561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158282172398488479972447707 237423258597732719958671561)
      ·
        refine ⟨178067443948299539969003671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237423258597732719958671561 178067443948299539969003671)
        ·
          refine ⟨267101165922449309953505507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178067443948299539969003671 267101165922449309953505507)
          ·
            refine ⟨400651748883673964930258261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267101165922449309953505507 400651748883673964930258261)
            ·
              refine ⟨36680763142426205285363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 400651748883673964930258261 36680763142426205285363)
              ·
                rfl

theorem cell22_2893139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 15].length) (baseStart_2893139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893139 prefixEnd_2893139 := by exact prefixLift 2893139
  have htrace : WordTrace (prefixWord ++ tailWord_2893139) baseStart_2893139 baseEnd_2893139 := by
    simpa [prefixWord, tailWord_2893139, baseEnd_2893139] using wordTrace_append hprefix tailTrace_2893139
  have hstable : (prefixWord ++ tailWord_2893139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893139).length < 2 ^ (prefixWord ++ tailWord_2893139).sum := by decide
  have hdescent : baseEnd_2893139 < baseStart_2893139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893143 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 4, 3]
def baseStart_2893143 : Nat := 118140960795 + 2893143 * 2 ^ 59
def prefixEnd_2893143 : Nat := 4983230072969 + 3 ^ 40 * 2893143 * 2
def baseEnd_2893143 : Nat := 990381974127252865604789

theorem tailTrace_2893143 : CollatzResearch.WordTrace tailWord_2893143 prefixEnd_2893143 990381974127252865604789 := by
  unfold tailWord_2893143
  simp only [CollatzResearch.WordTrace]
  refine ⟨105521594157644495331444083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70347729438429663554296055 105521594157644495331444083)
  ·
    refine ⟨158282391236466742997166125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105521594157644495331444083 158282391236466742997166125)
    ·
      refine ⟨59355896713675028623937297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158282391236466742997166125 59355896713675028623937297)
      ·
        refine ⟨44516922535256271467952973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59355896713675028623937297 44516922535256271467952973)
        ·
          refine ⟨16693845950721101800482365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44516922535256271467952973 16693845950721101800482365)
          ·
            refine ⟨6260192231520413175180887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16693845950721101800482365 6260192231520413175180887)
            ·
              refine ⟨9390288347280619762771331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260192231520413175180887 9390288347280619762771331)
              ·
                refine ⟨14085432520920929644156997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390288347280619762771331 14085432520920929644156997)
                ·
                  refine ⟨2641018597672674308279437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14085432520920929644156997 2641018597672674308279437)
                  ·
                    refine ⟨990381974127252865604789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641018597672674308279437 990381974127252865604789)
                    ·
                      rfl

theorem cell22_2893143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_2893143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893143 prefixEnd_2893143 := by exact prefixLift 2893143
  have htrace : WordTrace (prefixWord ++ tailWord_2893143) baseStart_2893143 baseEnd_2893143 := by
    simpa [prefixWord, tailWord_2893143, baseEnd_2893143] using wordTrace_append hprefix tailTrace_2893143
  have hstable : (prefixWord ++ tailWord_2893143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893143).length < 2 ^ (prefixWord ++ tailWord_2893143).sum := by decide
  have hdescent : baseEnd_2893143 < baseStart_2893143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893160 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2893160 : Nat := 118140960795 + 2893160 * 2 ^ 59
def prefixEnd_2893160 : Nat := 4983230072969 + 3 ^ 40 * 2893160 * 2
def baseEnd_2893160 : Nat := 990387793574670487929737

theorem tailTrace_2893160 : CollatzResearch.WordTrace tailWord_2893160 prefixEnd_2893160 990387793574670487929737 := by
  unfold tailWord_2893160
  simp only [CollatzResearch.WordTrace]
  refine ⟨52761107099291453617406467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70348142799055271489875289 52761107099291453617406467)
  ·
    refine ⟨79141660648937180426109701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52761107099291453617406467 79141660648937180426109701)
    ·
      refine ⟨14839061371675721329895569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79141660648937180426109701 14839061371675721329895569)
      ·
        refine ⟨11129296028756790997421677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14839061371675721329895569 11129296028756790997421677)
        ·
          refine ⟨4173486010783796624033129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11129296028756790997421677 4173486010783796624033129)
          ·
            refine ⟨3130114508087847468024847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173486010783796624033129 3130114508087847468024847)
            ·
              refine ⟨4695171762131771202037271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130114508087847468024847 4695171762131771202037271)
              ·
                refine ⟨7042757643197656803055907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695171762131771202037271 7042757643197656803055907)
                ·
                  refine ⟨10564136464796485204583861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042757643197656803055907 10564136464796485204583861)
                  ·
                    refine ⟨990387793574670487929737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10564136464796485204583861 990387793574670487929737)
                    ·
                      rfl

theorem cell22_2893160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2893160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893160 prefixEnd_2893160 := by exact prefixLift 2893160
  have htrace : WordTrace (prefixWord ++ tailWord_2893160) baseStart_2893160 baseEnd_2893160 := by
    simpa [prefixWord, tailWord_2893160, baseEnd_2893160] using wordTrace_append hprefix tailTrace_2893160
  have hstable : (prefixWord ++ tailWord_2893160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893160).length < 2 ^ (prefixWord ++ tailWord_2893160).sum := by decide
  have hdescent : baseEnd_2893160 < baseStart_2893160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893173 : List Nat := [1, 3, 4, 1, 3, 1, 1, 8]
def baseStart_2893173 : Nat := 118140960795 + 2893173 * 2 ^ 59
def prefixEnd_2893173 : Nat := 4983230072969 + 3 ^ 40 * 2893173 * 2
def baseEnd_2893173 : Nat := 110043582637815865261633

theorem tailTrace_2893173 : CollatzResearch.WordTrace tailWord_2893173 prefixEnd_2893173 110043582637815865261633 := by
  unfold tailWord_2893173
  simp only [CollatzResearch.WordTrace]
  refine ⟨105522688347535810455036173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70348458898357206970024115 105522688347535810455036173)
  ·
    refine ⟨39571008130325928920638565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105522688347535810455036173 39571008130325928920638565)
    ·
      refine ⟨7419564024436111672619731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39571008130325928920638565 7419564024436111672619731)
      ·
        refine ⟨11129346036654167508929597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419564024436111672619731 11129346036654167508929597)
        ·
          refine ⟨4173504763745312815848599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11129346036654167508929597 4173504763745312815848599)
          ·
            refine ⟨6260257145617969223772899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173504763745312815848599 6260257145617969223772899)
            ·
              refine ⟨9390385718426953835659349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260257145617969223772899 9390385718426953835659349)
              ·
                refine ⟨110043582637815865261633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9390385718426953835659349 110043582637815865261633)
                ·
                  rfl

theorem cell22_2893173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 8].length) (baseStart_2893173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893173 prefixEnd_2893173 := by exact prefixLift 2893173
  have htrace : WordTrace (prefixWord ++ tailWord_2893173) baseStart_2893173 baseEnd_2893173 := by
    simpa [prefixWord, tailWord_2893173, baseEnd_2893173] using wordTrace_append hprefix tailTrace_2893173
  have hstable : (prefixWord ++ tailWord_2893173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893173).length < 2 ^ (prefixWord ++ tailWord_2893173).sum := by decide
  have hdescent : baseEnd_2893173 < baseStart_2893173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893205 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2893205 : Nat := 118140960795 + 2893205 * 2 ^ 59
def prefixEnd_2893205 : Nat := 4983230072969 + 3 ^ 40 * 2893205 * 2
def baseEnd_2893205 : Nat := 990403197994305370554599

theorem tailTrace_2893205 : CollatzResearch.WordTrace tailWord_2893205 prefixEnd_2893205 990403197994305370554599 := by
  unfold tailWord_2893205
  simp only [CollatzResearch.WordTrace]
  refine ⟨105523855483419879920201069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70349236988946586613467379 105523855483419879920201069)
  ·
    refine ⟨39571445806282454970075401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105523855483419879920201069 39571445806282454970075401)
    ·
      refine ⟨29678584354711841227556551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39571445806282454970075401 29678584354711841227556551)
      ·
        refine ⟨44517876532067761841334827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29678584354711841227556551 44517876532067761841334827)
        ·
          refine ⟨66776814798101642762002241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44517876532067761841334827 66776814798101642762002241)
          ·
            refine ⟨50082611098576232071501681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66776814798101642762002241 50082611098576232071501681)
            ·
              refine ⟨37561958323932174053626261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50082611098576232071501681 37561958323932174053626261)
              ·
                refine ⟨1760716796434320658763731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37561958323932174053626261 1760716796434320658763731)
                ·
                  refine ⟨2641075194651480988145597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760716796434320658763731 2641075194651480988145597)
                  ·
                    refine ⟨990403197994305370554599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641075194651480988145597 990403197994305370554599)
                    ·
                      rfl

theorem cell22_2893205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2893205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893205 prefixEnd_2893205 := by exact prefixLift 2893205
  have htrace : WordTrace (prefixWord ++ tailWord_2893205) baseStart_2893205 baseEnd_2893205 := by
    simpa [prefixWord, tailWord_2893205, baseEnd_2893205] using wordTrace_append hprefix tailTrace_2893205
  have hstable : (prefixWord ++ tailWord_2893205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893205).length < 2 ^ (prefixWord ++ tailWord_2893205).sum := by decide
  have hdescent : baseEnd_2893205 < baseStart_2893205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893216 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_2893216 : Nat := 118140960795 + 2893216 * 2 ^ 59
def prefixEnd_2893216 : Nat := 4983230072969 + 3 ^ 40 * 2893216 * 2
def baseEnd_2893216 : Nat := 990406963519105008529565

theorem tailTrace_2893216 : CollatzResearch.WordTrace tailWord_2893216 prefixEnd_2893216 990406963519105008529565 := by
  unfold tailWord_2893216
  simp only [CollatzResearch.WordTrace]
  refine ⟨52762128343190014399425751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70349504457586685865901001 52762128343190014399425751)
  ·
    refine ⟨79143192514785021599138627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52762128343190014399425751 79143192514785021599138627)
    ·
      refine ⟨118714788772177532398707941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79143192514785021599138627 118714788772177532398707941)
      ·
        refine ⟨22259022894783287324757739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118714788772177532398707941 22259022894783287324757739)
        ·
          refine ⟨33388534342174930987136609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22259022894783287324757739 33388534342174930987136609)
          ·
            refine ⟨25041400756631198240352457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33388534342174930987136609 25041400756631198240352457)
            ·
              refine ⟨18781050567473398680264343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25041400756631198240352457 18781050567473398680264343)
              ·
                refine ⟨28171575851210098020396515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18781050567473398680264343 28171575851210098020396515)
                ·
                  refine ⟨42257363776815147030594773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28171575851210098020396515 42257363776815147030594773)
                  ·
                    refine ⟨990406963519105008529565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42257363776815147030594773 990406963519105008529565)
                    ·
                      rfl

theorem cell22_2893216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_2893216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893216 prefixEnd_2893216 := by exact prefixLift 2893216
  have htrace : WordTrace (prefixWord ++ tailWord_2893216) baseStart_2893216 baseEnd_2893216 := by
    simpa [prefixWord, tailWord_2893216, baseEnd_2893216] using wordTrace_append hprefix tailTrace_2893216
  have hstable : (prefixWord ++ tailWord_2893216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893216).length < 2 ^ (prefixWord ++ tailWord_2893216).sum := by decide
  have hdescent : baseEnd_2893216 < baseStart_2893216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893248 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_2893248 : Nat := 118140960795 + 2893248 * 2 ^ 59
def prefixEnd_2893248 : Nat := 4983230072969 + 3 ^ 40 * 2893248 * 2
def baseEnd_2893248 : Nat := 990417917773067591729467

theorem tailTrace_2893248 : CollatzResearch.WordTrace tailWord_2893248 prefixEnd_2893248 990417917773067591729467 := by
  unfold tailWord_2893248
  simp only [CollatzResearch.WordTrace]
  refine ⟨52762711911132049132008199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70350282548176065509344265 52762711911132049132008199)
  ·
    refine ⟨79144067866698073698012299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52762711911132049132008199 79144067866698073698012299)
    ·
      refine ⟨118716101800047110547018449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79144067866698073698012299 118716101800047110547018449)
      ·
        refine ⟨89037076350035332910263837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118716101800047110547018449 89037076350035332910263837)
        ·
          refine ⟨33388903631263249841348939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89037076350035332910263837 33388903631263249841348939)
          ·
            refine ⟨50083355446894874762023409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33388903631263249841348939 50083355446894874762023409)
            ·
              refine ⟨37562516585171156071517557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50083355446894874762023409 37562516585171156071517557)
              ·
                refine ⟨3521485929859795881704771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37562516585171156071517557 3521485929859795881704771)
                ·
                  refine ⟨5282228894789693822557157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521485929859795881704771 5282228894789693822557157)
                  ·
                    refine ⟨990417917773067591729467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5282228894789693822557157 990417917773067591729467)
                    ·
                      rfl

theorem cell22_2893248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_2893248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893248 prefixEnd_2893248 := by exact prefixLift 2893248
  have htrace : WordTrace (prefixWord ++ tailWord_2893248) baseStart_2893248 baseEnd_2893248 := by
    simpa [prefixWord, tailWord_2893248, baseEnd_2893248] using wordTrace_append hprefix tailTrace_2893248
  have hstable : (prefixWord ++ tailWord_2893248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893248).length < 2 ^ (prefixWord ++ tailWord_2893248).sum := by decide
  have hdescent : baseEnd_2893248 < baseStart_2893248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893340 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2893340 : Nat := 118140960795 + 2893340 * 2 ^ 59
def prefixEnd_2893340 : Nat := 4983230072969 + 3 ^ 40 * 2893340 * 2
def baseEnd_2893340 : Nat := 990449411253210018429185

theorem tailTrace_2893340 : CollatzResearch.WordTrace tailWord_2893340 prefixEnd_2893340 990449411253210018429185 := by
  unfold tailWord_2893340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52764389668965398988182737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70352519558620531984243649 52764389668965398988182737)
  ·
    refine ⟨39573292251724049241137053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52764389668965398988182737 39573292251724049241137053)
    ·
      refine ⟨14839984594396518465426395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39573292251724049241137053 14839984594396518465426395)
      ·
        refine ⟨22259976891594777698139593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14839984594396518465426395 22259976891594777698139593)
        ·
          refine ⟨16694982668696083273604695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22259976891594777698139593 16694982668696083273604695)
          ·
            refine ⟨25042474003044124910407043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16694982668696083273604695 25042474003044124910407043)
            ·
              refine ⟨37563711004566187365610565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25042474003044124910407043 37563711004566187365610565)
              ·
                refine ⟨7043195813356160131051981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37563711004566187365610565 7043195813356160131051981)
                ·
                  refine ⟨2641198430008560049144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7043195813356160131051981 2641198430008560049144493)
                  ·
                    refine ⟨990449411253210018429185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641198430008560049144493 990449411253210018429185)
                    ·
                      rfl

theorem cell22_2893340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2893340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893340 prefixEnd_2893340 := by exact prefixLift 2893340
  have htrace : WordTrace (prefixWord ++ tailWord_2893340) baseStart_2893340 baseEnd_2893340 := by
    simpa [prefixWord, tailWord_2893340, baseEnd_2893340] using wordTrace_append hprefix tailTrace_2893340
  have hstable : (prefixWord ++ tailWord_2893340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893340).length < 2 ^ (prefixWord ++ tailWord_2893340).sum := by decide
  have hdescent : baseEnd_2893340 < baseStart_2893340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893447 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2893447 : Nat := 118140960795 + 2893447 * 2 ^ 59
def prefixEnd_2893447 : Nat := 4983230072969 + 3 ^ 40 * 2893447 * 2
def baseEnd_2893447 : Nat := 990486039539897406003857

theorem tailTrace_2893447 : CollatzResearch.WordTrace tailWord_2893447 prefixEnd_2893447 990486039539897406003857 := by
  unfold tailWord_2893447
  simp only [CollatzResearch.WordTrace]
  refine ⟨105532681948543155250510595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70355121299028770167007063 105532681948543155250510595)
  ·
    refine ⟨158299022922814732875765893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105532681948543155250510595 158299022922814732875765893)
    ·
      refine ⟨29681066798027762414206105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158299022922814732875765893 29681066798027762414206105)
      ·
        refine ⟨22260800098520821810654579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29681066798027762414206105 22260800098520821810654579)
        ·
          refine ⟨33391200147781232715981869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22260800098520821810654579 33391200147781232715981869)
          ·
            refine ⟨12521700055417962268493201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33391200147781232715981869 12521700055417962268493201)
            ·
              refine ⟨9391275041563471701369901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12521700055417962268493201 9391275041563471701369901)
              ·
                refine ⟨3521728140586301888013713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9391275041563471701369901 3521728140586301888013713)
                ·
                  refine ⟨2641296105439726416010285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521728140586301888013713 2641296105439726416010285)
                  ·
                    refine ⟨990486039539897406003857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641296105439726416010285 990486039539897406003857)
                    ·
                      rfl

theorem cell22_2893447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2893447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893447 prefixEnd_2893447 := by exact prefixLift 2893447
  have htrace : WordTrace (prefixWord ++ tailWord_2893447) baseStart_2893447 baseEnd_2893447 := by
    simpa [prefixWord, tailWord_2893447, baseEnd_2893447] using wordTrace_append hprefix tailTrace_2893447
  have hstable : (prefixWord ++ tailWord_2893447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893447).length < 2 ^ (prefixWord ++ tailWord_2893447).sum := by decide
  have hdescent : baseEnd_2893447 < baseStart_2893447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893475 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 5, 3]
def baseStart_2893475 : Nat := 118140960795 + 2893475 * 2 ^ 59
def prefixEnd_2893475 : Nat := 4983230072969 + 3 ^ 40 * 2893475 * 2
def baseEnd_2893475 : Nat := 990495624512114666303771

theorem tailTrace_2893475 : CollatzResearch.WordTrace tailWord_2893475 prefixEnd_2893475 990495624512114666303771 := by
  unfold tailWord_2893475
  simp only [CollatzResearch.WordTrace]
  refine ⟨105533703192441716032529879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70355802128294477355019919 105533703192441716032529879)
  ·
    refine ⟨158300554788662574048794819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105533703192441716032529879 158300554788662574048794819)
    ·
      refine ⟨237450832182993861073192229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158300554788662574048794819 237450832182993861073192229)
      ·
        refine ⟨44522031034311348951223543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237450832182993861073192229 44522031034311348951223543)
        ·
          refine ⟨66783046551467023426835315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44522031034311348951223543 66783046551467023426835315)
          ·
            refine ⟨100174569827200535140252973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66783046551467023426835315 100174569827200535140252973)
            ·
              refine ⟨37565463685200200677594865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100174569827200535140252973 37565463685200200677594865)
              ·
                refine ⟨28174097763900150508196149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37565463685200200677594865 28174097763900150508196149)
                ·
                  refine ⟨2641321665365639110143389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28174097763900150508196149 2641321665365639110143389)
                  ·
                    refine ⟨990495624512114666303771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641321665365639110143389 990495624512114666303771)
                    ·
                      rfl

theorem cell22_2893475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3].length) (baseStart_2893475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893475 prefixEnd_2893475 := by exact prefixLift 2893475
  have htrace : WordTrace (prefixWord ++ tailWord_2893475) baseStart_2893475 baseEnd_2893475 := by
    simpa [prefixWord, tailWord_2893475, baseEnd_2893475] using wordTrace_append hprefix tailTrace_2893475
  have hstable : (prefixWord ++ tailWord_2893475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893475).length < 2 ^ (prefixWord ++ tailWord_2893475).sum := by decide
  have hdescent : baseEnd_2893475 < baseStart_2893475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893543 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2893543 : Nat := 118140960795 + 2893543 * 2 ^ 59
def prefixEnd_2893543 : Nat := 4983230072969 + 3 ^ 40 * 2893543 * 2
def baseEnd_2893543 : Nat := 990518902301785155603563

theorem tailTrace_2893543 : CollatzResearch.WordTrace tailWord_2893543 prefixEnd_2893543 990518902301785155603563 := by
  unfold tailWord_2893543
  simp only [CollatzResearch.WordTrace]
  refine ⟨105536183356195363646005283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70357455570796909097336855 105536183356195363646005283)
  ·
    refine ⟨158304275034293045469007925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105536183356195363646005283 158304275034293045469007925)
    ·
      refine ⟨14841025784464973012719493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158304275034293045469007925 14841025784464973012719493)
      ·
        refine ⟨2782692334587182439884905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14841025784464973012719493 2782692334587182439884905)
        ·
          refine ⟨2087019250940386829913679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782692334587182439884905 2087019250940386829913679)
          ·
            refine ⟨3130528876410580244870519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087019250940386829913679 3130528876410580244870519)
            ·
              refine ⟨4695793314615870367305779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130528876410580244870519 4695793314615870367305779)
              ·
                refine ⟨7043689971923805550958669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695793314615870367305779 7043689971923805550958669)
                ·
                  refine ⟨2641383739471427081609501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7043689971923805550958669 2641383739471427081609501)
                  ·
                    refine ⟨990518902301785155603563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641383739471427081609501 990518902301785155603563)
                    ·
                      rfl

theorem cell22_2893543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2893543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893543 prefixEnd_2893543 := by exact prefixLift 2893543
  have htrace : WordTrace (prefixWord ++ tailWord_2893543) baseStart_2893543 baseEnd_2893543 := by
    simpa [prefixWord, tailWord_2893543, baseEnd_2893543] using wordTrace_append hprefix tailTrace_2893543
  have hstable : (prefixWord ++ tailWord_2893543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893543).length < 2 ^ (prefixWord ++ tailWord_2893543).sum := by decide
  have hdescent : baseEnd_2893543 < baseStart_2893543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893556 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2893556 : Nat := 118140960795 + 2893556 * 2 ^ 59
def prefixEnd_2893556 : Nat := 4983230072969 + 3 ^ 40 * 2893556 * 2
def baseEnd_2893556 : Nat := 330174450822485818342841

theorem tailTrace_2893556 : CollatzResearch.WordTrace tailWord_2893556 prefixEnd_2893556 330174450822485818342841 := by
  unfold tailWord_2893556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52768328752574133433114261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70357771670098844577485681 52768328752574133433114261)
  ·
    refine ⟨2473515410276912504677231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52768328752574133433114261 2473515410276912504677231)
    ·
      refine ⟨3710273115415368757015847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2473515410276912504677231 3710273115415368757015847)
      ·
        refine ⟨5565409673123053135523771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710273115415368757015847 5565409673123053135523771)
        ·
          refine ⟨8348114509684579703285657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565409673123053135523771 8348114509684579703285657)
          ·
            refine ⟨6261085882263434777464243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8348114509684579703285657 6261085882263434777464243)
            ·
              refine ⟨9391628823395152166196365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261085882263434777464243 9391628823395152166196365)
              ·
                refine ⟨3521860808773182062323637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9391628823395152166196365 3521860808773182062323637)
                ·
                  refine ⟨330174450822485818342841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521860808773182062323637 330174450822485818342841)
                  ·
                    rfl

theorem cell22_2893556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2893556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893556 prefixEnd_2893556 := by exact prefixLift 2893556
  have htrace : WordTrace (prefixWord ++ tailWord_2893556) baseStart_2893556 baseEnd_2893556 := by
    simpa [prefixWord, tailWord_2893556, baseEnd_2893556] using wordTrace_append hprefix tailTrace_2893556
  have hstable : (prefixWord ++ tailWord_2893556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893556).length < 2 ^ (prefixWord ++ tailWord_2893556).sum := by decide
  have hdescent : baseEnd_2893556 < baseStart_2893556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893580 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_2893580 : Nat := 118140960795 + 2893580 * 2 ^ 59
def prefixEnd_2893580 : Nat := 4983230072969 + 3 ^ 40 * 2893580 * 2
def baseEnd_2893580 : Nat := 990531568157929392428449

theorem tailTrace_2893580 : CollatzResearch.WordTrace tailWord_2893580 prefixEnd_2893580 990531568157929392428449 := by
  unfold tailWord_2893580
  simp only [CollatzResearch.WordTrace]
  refine ⟨52768766428530659482551097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70358355238040879310068129 52768766428530659482551097)
  ·
    refine ⟨39576574821397994611913323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52768766428530659482551097 39576574821397994611913323)
    ·
      refine ⟨59364862232096991917869985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39576574821397994611913323 59364862232096991917869985)
      ·
        refine ⟨44523646674072743938402489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59364862232096991917869985 44523646674072743938402489)
        ·
          refine ⟨33392735005554557953801867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44523646674072743938402489 33392735005554557953801867)
          ·
            refine ⟨50089102508331836930702801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33392735005554557953801867 50089102508331836930702801)
            ·
              refine ⟨37566826881248877698027101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50089102508331836930702801 37566826881248877698027101)
              ·
                refine ⟨14087560080468329136760163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37566826881248877698027101 14087560080468329136760163)
                ·
                  refine ⟨21131340120702493705140245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14087560080468329136760163 21131340120702493705140245)
                  ·
                    refine ⟨990531568157929392428449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21131340120702493705140245 990531568157929392428449)
                    ·
                      rfl

theorem cell22_2893580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_2893580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893580 prefixEnd_2893580 := by exact prefixLift 2893580
  have htrace : WordTrace (prefixWord ++ tailWord_2893580) baseStart_2893580 baseEnd_2893580 := by
    simpa [prefixWord, tailWord_2893580, baseEnd_2893580] using wordTrace_append hprefix tailTrace_2893580
  have hstable : (prefixWord ++ tailWord_2893580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893580).length < 2 ^ (prefixWord ++ tailWord_2893580).sum := by decide
  have hdescent : baseEnd_2893580 < baseStart_2893580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893582 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_2893582 : Nat := 118140960795 + 2893582 * 2 ^ 59
def prefixEnd_2893582 : Nat := 4983230072969 + 3 ^ 40 * 2893582 * 2
def baseEnd_2893582 : Nat := 990532252798802053878443

theorem tailTrace_2893582 : CollatzResearch.WordTrace tailWord_2893582 prefixEnd_2893582 990532252798802053878443 := by
  unfold tailWord_2893582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13192200725381759163334375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70358403868702715537783333 13192200725381759163334375)
  ·
    refine ⟨19788301088072638745001563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13192200725381759163334375 19788301088072638745001563)
    ·
      refine ⟨29682451632108958117502345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19788301088072638745001563 29682451632108958117502345)
      ·
        refine ⟨22261838724081718588126759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29682451632108958117502345 22261838724081718588126759)
        ·
          refine ⟨33392758086122577882190139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22261838724081718588126759 33392758086122577882190139)
          ·
            refine ⟨50089137129183866823285209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33392758086122577882190139 50089137129183866823285209)
            ·
              refine ⟨37566852846887900117463907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50089137129183866823285209 37566852846887900117463907)
              ·
                refine ⟨56350279270331850176195861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37566852846887900117463907 56350279270331850176195861)
                ·
                  refine ⟨2641419340796805477009181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56350279270331850176195861 2641419340796805477009181)
                  ·
                    refine ⟨990532252798802053878443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641419340796805477009181 990532252798802053878443)
                    ·
                      rfl

theorem cell22_2893582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_2893582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893582 prefixEnd_2893582 := by exact prefixLift 2893582
  have htrace : WordTrace (prefixWord ++ tailWord_2893582) baseStart_2893582 baseEnd_2893582 := by
    simpa [prefixWord, tailWord_2893582, baseEnd_2893582] using wordTrace_append hprefix tailTrace_2893582
  have hstable : (prefixWord ++ tailWord_2893582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893582).length < 2 ^ (prefixWord ++ tailWord_2893582).sum := by decide
  have hdescent : baseEnd_2893582 < baseStart_2893582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893599 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 2, 3]
def baseStart_2893599 : Nat := 118140960795 + 2893599 * 2 ^ 59
def prefixEnd_2893599 : Nat := 4983230072969 + 3 ^ 40 * 2893599 * 2
def baseEnd_2893599 : Nat := 990538072246219676203391

theorem tailTrace_2893599 : CollatzResearch.WordTrace tailWord_2893599 prefixEnd_2893599 990538072246219676203391 := by
  unfold tailWord_2893599
  simp only [CollatzResearch.WordTrace]
  refine ⟨105538225843992485210043851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70358817229328323473362567 105538225843992485210043851)
  ·
    refine ⟨158307338765988727815065777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105538225843992485210043851 158307338765988727815065777)
    ·
      refine ⟨118730504074491545861299333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158307338765988727815065777 118730504074491545861299333)
      ·
        refine ⟨22261969513967164848993625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118730504074491545861299333 22261969513967164848993625)
        ·
          refine ⟨16696477135475373636745219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22261969513967164848993625 16696477135475373636745219)
          ·
            refine ⟨25044715703213060455117829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16696477135475373636745219 25044715703213060455117829)
            ·
              refine ⟨4695884194352448835334593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25044715703213060455117829 4695884194352448835334593)
              ·
                refine ⟨3521913145764336626500945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4695884194352448835334593 3521913145764336626500945)
                ·
                  refine ⟨2641434859323252469875709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521913145764336626500945 2641434859323252469875709)
                  ·
                    refine ⟨990538072246219676203391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641434859323252469875709 990538072246219676203391)
                    ·
                      rfl

theorem cell22_2893599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_2893599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893599 prefixEnd_2893599 := by exact prefixLift 2893599
  have htrace : WordTrace (prefixWord ++ tailWord_2893599) baseStart_2893599 baseEnd_2893599 := by
    simpa [prefixWord, tailWord_2893599, baseEnd_2893599] using wordTrace_append hprefix tailTrace_2893599
  have hstable : (prefixWord ++ tailWord_2893599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893599).length < 2 ^ (prefixWord ++ tailWord_2893599).sum := by decide
  have hdescent : baseEnd_2893599 < baseStart_2893599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893601 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 4]
def baseStart_2893601 : Nat := 118140960795 + 2893601 * 2 ^ 59
def prefixEnd_2893601 : Nat := 4983230072969 + 3 ^ 40 * 2893601 * 2
def baseEnd_2893601 : Nat := 330179585629030779217795

theorem tailTrace_2893601 : CollatzResearch.WordTrace tailWord_2893601 prefixEnd_2893601 330179585629030779217795 := by
  unfold tailWord_2893601
  simp only [CollatzResearch.WordTrace]
  refine ⟨105538298789985239551616657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70358865859990159701077771 105538298789985239551616657)
  ·
    refine ⟨79153724092488929663712493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105538298789985239551616657 79153724092488929663712493)
    ·
      refine ⟨29682646534683348623892185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79153724092488929663712493 29682646534683348623892185)
      ·
        refine ⟨22261984901012511467919139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29682646534683348623892185 22261984901012511467919139)
        ·
          refine ⟨33392977351518767201878709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22261984901012511467919139 33392977351518767201878709)
          ·
            refine ⟨3130591626704884425176129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33392977351518767201878709 3130591626704884425176129)
            ·
              refine ⟨2347943720028663318882097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130591626704884425176129 2347943720028663318882097)
              ·
                refine ⟨1760957790021497489161573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347943720028663318882097 1760957790021497489161573)
                ·
                  refine ⟨330179585629030779217795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760957790021497489161573 330179585629030779217795)
                  ·
                    rfl

theorem cell22_2893601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_2893601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893601 prefixEnd_2893601 := by exact prefixLift 2893601
  have htrace : WordTrace (prefixWord ++ tailWord_2893601) baseStart_2893601 baseEnd_2893601 := by
    simpa [prefixWord, tailWord_2893601, baseEnd_2893601] using wordTrace_append hprefix tailTrace_2893601
  have hstable : (prefixWord ++ tailWord_2893601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893601).length < 2 ^ (prefixWord ++ tailWord_2893601).sum := by decide
  have hdescent : baseEnd_2893601 < baseStart_2893601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893612 : List Nat := [2, 2, 1, 1, 1, 7, 1, 7]
def baseStart_2893612 : Nat := 118140960795 + 2893612 * 2 ^ 59
def prefixEnd_2893612 : Nat := 4983230072969 + 3 ^ 40 * 2893612 * 2
def baseEnd_2893612 : Nat := 110060280267987997292039

theorem tailTrace_2893612 : CollatzResearch.WordTrace tailWord_2893612 prefixEnd_2893612 110060280267987997292039 := by
  unfold tailWord_2893612
  simp only [CollatzResearch.WordTrace]
  refine ⟨52769349996472694215133545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70359133328630258953511393 52769349996472694215133545)
  ·
    refine ⟨39577012497354520661350159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52769349996472694215133545 39577012497354520661350159)
    ·
      refine ⟨59365518746031780992025239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39577012497354520661350159 59365518746031780992025239)
      ·
        refine ⟨89048278119047671488037859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59365518746031780992025239 89048278119047671488037859)
        ·
          refine ⟨133572417178571507232056789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89048278119047671488037859 133572417178571507232056789)
          ·
            refine ⟨3130603527622769700751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 133572417178571507232056789 3130603527622769700751331)
            ·
              refine ⟨4695905291434154551126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130603527622769700751331 4695905291434154551126997)
              ·
                refine ⟨110060280267987997292039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4695905291434154551126997 110060280267987997292039)
                ·
                  rfl

theorem cell22_2893612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_2893612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893612 prefixEnd_2893612 := by exact prefixLift 2893612
  have htrace : WordTrace (prefixWord ++ tailWord_2893612) baseStart_2893612 baseEnd_2893612 := by
    simpa [prefixWord, tailWord_2893612, baseEnd_2893612] using wordTrace_append hprefix tailTrace_2893612
  have hstable : (prefixWord ++ tailWord_2893612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893612).length < 2 ^ (prefixWord ++ tailWord_2893612).sum := by decide
  have hdescent : baseEnd_2893612 < baseStart_2893612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893629 : List Nat := [1, 4, 1, 4, 1, 2, 3, 6]
def baseStart_2893629 : Nat := 118140960795 + 2893629 * 2 ^ 59
def prefixEnd_2893629 : Nat := 4983230072969 + 3 ^ 40 * 2893629 * 2
def baseEnd_2893629 : Nat := 110060926873256621994811

theorem tailTrace_2893629 : CollatzResearch.WordTrace tailWord_2893629 prefixEnd_2893629 110060926873256621994811 := by
  unfold tailWord_2893629
  simp only [CollatzResearch.WordTrace]
  refine ⟨105539320033883800333635941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70359546689255866889090627 105539320033883800333635941)
  ·
    refine ⟨19788622506353212562556739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105539320033883800333635941 19788622506353212562556739)
    ·
      refine ⟨29682933759529818843835109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19788622506353212562556739 29682933759529818843835109)
      ·
        refine ⟨5565550079911841033219083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29682933759529818843835109 5565550079911841033219083)
        ·
          refine ⟨8348325119867761549828625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565550079911841033219083 8348325119867761549828625)
          ·
            refine ⟨6261243839900821162371469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8348325119867761549828625 6261243839900821162371469)
            ·
              refine ⟨2347966439962807935889301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6261243839900821162371469 2347966439962807935889301)
              ·
                refine ⟨110060926873256621994811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2347966439962807935889301 110060926873256621994811)
                ·
                  rfl

theorem cell22_2893629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 6].length) (baseStart_2893629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893629 prefixEnd_2893629 := by exact prefixLift 2893629
  have htrace : WordTrace (prefixWord ++ tailWord_2893629) baseStart_2893629 baseEnd_2893629 := by
    simpa [prefixWord, tailWord_2893629, baseEnd_2893629] using wordTrace_append hprefix tailTrace_2893629
  have hstable : (prefixWord ++ tailWord_2893629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893629).length < 2 ^ (prefixWord ++ tailWord_2893629).sum := by decide
  have hdescent : baseEnd_2893629 < baseStart_2893629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893631 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 2, 4]
def baseStart_2893631 : Nat := 118140960795 + 2893631 * 2 ^ 59
def prefixEnd_2893631 : Nat := 4983230072969 + 3 ^ 40 * 2893631 * 2
def baseEnd_2893631 : Nat := 990549026500182259403293

theorem tailTrace_2893631 : CollatzResearch.WordTrace tailWord_2893631 prefixEnd_2893631 990549026500182259403293 := by
  unfold tailWord_2893631
  simp only [CollatzResearch.WordTrace]
  refine ⟨105539392979876554675208747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70359595319917703116805831 105539392979876554675208747)
  ·
    refine ⟨158309089469814832012813121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105539392979876554675208747 158309089469814832012813121)
    ·
      refine ⟨118731817102361124009609841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158309089469814832012813121 118731817102361124009609841)
      ·
        refine ⟨89048862826770843007207381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118731817102361124009609841 89048862826770843007207381)
        ·
          refine ⟨2087082722502441632981423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 89048862826770843007207381 2087082722502441632981423)
          ·
            refine ⟨3130624083753662449472135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087082722502441632981423 3130624083753662449472135)
            ·
              refine ⟨4695936125630493674208203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130624083753662449472135 4695936125630493674208203)
              ·
                refine ⟨7043904188445740511312305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695936125630493674208203 7043904188445740511312305)
                ·
                  refine ⟨5282928141334305383484229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043904188445740511312305 5282928141334305383484229)
                  ·
                    refine ⟨990549026500182259403293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5282928141334305383484229 990549026500182259403293)
                    ·
                      rfl

theorem cell22_2893631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_2893631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893631 prefixEnd_2893631 := by exact prefixLift 2893631
  have htrace : WordTrace (prefixWord ++ tailWord_2893631) baseStart_2893631 baseEnd_2893631 := by
    simpa [prefixWord, tailWord_2893631, baseEnd_2893631] using wordTrace_append hprefix tailTrace_2893631
  have hstable : (prefixWord ++ tailWord_2893631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893631).length < 2 ^ (prefixWord ++ tailWord_2893631).sum := by decide
  have hdescent : baseEnd_2893631 < baseStart_2893631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893672 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2893672 : Nat := 118140960795 + 2893672 * 2 ^ 59
def prefixEnd_2893672 : Nat := 4983230072969 + 3 ^ 40 * 2893672 * 2
def baseEnd_2893672 : Nat := 990563061638071819128167

theorem tailTrace_2893672 : CollatzResearch.WordTrace tailWord_2893672 prefixEnd_2893672 990563061638071819128167 := by
  unfold tailWord_2893672
  simp only [CollatzResearch.WordTrace]
  refine ⟨52770444186364009338725635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70360592248485345784967513 52770444186364009338725635)
  ·
    refine ⟨79155666279546014008088453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52770444186364009338725635 79155666279546014008088453)
    ·
      refine ⟨14841687427414877626516585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79155666279546014008088453 14841687427414877626516585)
      ·
        refine ⟨11131265570561158219887439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14841687427414877626516585 11131265570561158219887439)
        ·
          refine ⟨16696898355841737329831159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11131265570561158219887439 16696898355841737329831159)
          ·
            refine ⟨25045347533762605994746739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16696898355841737329831159 25045347533762605994746739)
            ·
              refine ⟨37568021300643908992120109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25045347533762605994746739 37568021300643908992120109)
              ·
                refine ⟨14088007987741465872045041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37568021300643908992120109 14088007987741465872045041)
                ·
                  refine ⟨10566005990806099404033781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14088007987741465872045041 10566005990806099404033781)
                  ·
                    refine ⟨990563061638071819128167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10566005990806099404033781 990563061638071819128167)
                    ·
                      rfl

theorem cell22_2893672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2893672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893672 prefixEnd_2893672 := by exact prefixLift 2893672
  have htrace : WordTrace (prefixWord ++ tailWord_2893672) baseStart_2893672 baseEnd_2893672 := by
    simpa [prefixWord, tailWord_2893672, baseEnd_2893672] using wordTrace_append hprefix tailTrace_2893672
  have hstable : (prefixWord ++ tailWord_2893672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893672).length < 2 ^ (prefixWord ++ tailWord_2893672).sum := by decide
  have hdescent : baseEnd_2893672 < baseStart_2893672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893719 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 6]
def baseStart_2893719 : Nat := 118140960795 + 2893719 * 2 ^ 59
def prefixEnd_2893719 : Nat := 4983230072969 + 3 ^ 40 * 2893719 * 2
def baseEnd_2893719 : Nat := 330193050232859787734341

theorem tailTrace_2893719 : CollatzResearch.WordTrace tailWord_2893719 prefixEnd_2893719 330193050232859787734341 := by
  unfold tailWord_2893719
  simp only [CollatzResearch.WordTrace]
  refine ⟨105542602603557745704412211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70361735069038497136274807 105542602603557745704412211)
  ·
    refine ⟨158313903905336618556618317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105542602603557745704412211 158313903905336618556618317)
    ·
      refine ⟨59367713964501231958731869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158313903905336618556618317 59367713964501231958731869)
      ·
        refine ⟨22262892736687961984524451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59367713964501231958731869 22262892736687961984524451)
        ·
          refine ⟨33394339105031942976786677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22262892736687961984524451 33394339105031942976786677)
          ·
            refine ⟨3130719291096744654073751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33394339105031942976786677 3130719291096744654073751)
            ·
              refine ⟨4696078936645116981110627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130719291096744654073751 4696078936645116981110627)
              ·
                refine ⟨7044118404967675471665941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696078936645116981110627 7044118404967675471665941)
                ·
                  refine ⟨330193050232859787734341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7044118404967675471665941 330193050232859787734341)
                  ·
                    rfl

theorem cell22_2893719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 6].length) (baseStart_2893719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893719 prefixEnd_2893719 := by exact prefixLift 2893719
  have htrace : WordTrace (prefixWord ++ tailWord_2893719) baseStart_2893719 baseEnd_2893719 := by
    simpa [prefixWord, tailWord_2893719, baseEnd_2893719] using wordTrace_append hprefix tailTrace_2893719
  have hstable : (prefixWord ++ tailWord_2893719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893719).length < 2 ^ (prefixWord ++ tailWord_2893719).sum := by decide
  have hdescent : baseEnd_2893719 < baseStart_2893719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893749 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2893749 : Nat := 118140960795 + 2893749 * 2 ^ 59
def prefixEnd_2893749 : Nat := 4983230072969 + 3 ^ 40 * 2893749 * 2
def baseEnd_2893749 : Nat := 990589420311669284952931

theorem tailTrace_2893749 : CollatzResearch.WordTrace tailWord_2893749 prefixEnd_2893749 990589420311669284952931 := by
  unfold tailWord_2893749
  simp only [CollatzResearch.WordTrace]
  refine ⟨105543696793449060828004301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70362464528966040552002867 105543696793449060828004301)
  ·
    refine ⟨39578886297543397810501613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105543696793449060828004301 39578886297543397810501613)
    ·
      refine ⟨14842082361578774178938105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39578886297543397810501613 14842082361578774178938105)
      ·
        refine ⟨11131561771184080634203579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14842082361578774178938105 11131561771184080634203579)
        ·
          refine ⟨16697342656776120951305369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11131561771184080634203579 16697342656776120951305369)
          ·
            refine ⟨12523006992582090713479027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16697342656776120951305369 12523006992582090713479027)
            ·
              refine ⟨18784510488873136070218541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12523006992582090713479027 18784510488873136070218541)
              ·
                refine ⟨7044191433327426026331953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18784510488873136070218541 7044191433327426026331953)
                ·
                  refine ⟨5283143574995569519748965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7044191433327426026331953 5283143574995569519748965)
                  ·
                    refine ⟨990589420311669284952931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283143574995569519748965 990589420311669284952931)
                    ·
                      rfl

theorem cell22_2893749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2893749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893749 prefixEnd_2893749 := by exact prefixLift 2893749
  have htrace : WordTrace (prefixWord ++ tailWord_2893749) baseStart_2893749 baseEnd_2893749 := by
    simpa [prefixWord, tailWord_2893749, baseEnd_2893749] using wordTrace_append hprefix tailTrace_2893749
  have hstable : (prefixWord ++ tailWord_2893749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893749).length < 2 ^ (prefixWord ++ tailWord_2893749).sum := by decide
  have hdescent : baseEnd_2893749 < baseStart_2893749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893807 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_2893807 : Nat := 118140960795 + 2893807 * 2 ^ 59
def prefixEnd_2893807 : Nat := 4983230072969 + 3 ^ 40 * 2893807 * 2
def baseEnd_2893807 : Nat := 990609274896976467002753

theorem tailTrace_2893807 : CollatzResearch.WordTrace tailWord_2893807 prefixEnd_2893807 990609274896976467002753 := by
  unfold tailWord_2893807
  simp only [CollatzResearch.WordTrace]
  refine ⟨105545812227238936733615675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70363874818159291155743783 105545812227238936733615675)
  ·
    refine ⟨158318718340858405100423513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105545812227238936733615675 158318718340858405100423513)
    ·
      refine ⟨118739038755643803825317635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158318718340858405100423513 118739038755643803825317635)
      ·
        refine ⟨178108558133465705737976453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118739038755643803825317635 178108558133465705737976453)
        ·
          refine ⟨33395354650024819825870585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178108558133465705737976453 33395354650024819825870585)
          ·
            refine ⟨25046515987518614869402939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33395354650024819825870585 25046515987518614869402939)
            ·
              refine ⟨37569773981277922304104409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25046515987518614869402939 37569773981277922304104409)
              ·
                refine ⟨28177330485958441728078307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37569773981277922304104409 28177330485958441728078307)
                ·
                  refine ⟨42265995728937662592117461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28177330485958441728078307 42265995728937662592117461)
                  ·
                    refine ⟨990609274896976467002753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42265995728937662592117461 990609274896976467002753)
                    ·
                      rfl

theorem cell22_2893807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_2893807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893807 prefixEnd_2893807 := by exact prefixLift 2893807
  have htrace : WordTrace (prefixWord ++ tailWord_2893807) baseStart_2893807 baseEnd_2893807 := by
    simpa [prefixWord, tailWord_2893807, baseEnd_2893807] using wordTrace_append hprefix tailTrace_2893807
  have hstable : (prefixWord ++ tailWord_2893807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893807).length < 2 ^ (prefixWord ++ tailWord_2893807).sum := by decide
  have hdescent : baseEnd_2893807 < baseStart_2893807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893864 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2893864 : Nat := 118140960795 + 2893864 * 2 ^ 59
def prefixEnd_2893864 : Nat := 4983230072969 + 3 ^ 40 * 2893864 * 2
def baseEnd_2893864 : Nat := 990628787161847318327579

theorem tailTrace_2893864 : CollatzResearch.WordTrace tailWord_2893864 prefixEnd_2893864 990628787161847318327579 := by
  unfold tailWord_2893864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52773945594016217734220323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70365260792021623645627097 52773945594016217734220323)
  ·
    refine ⟨79160918391024326601330485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52773945594016217734220323 79160918391024326601330485)
    ·
      refine ⟨7421336099158530618874733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79160918391024326601330485 7421336099158530618874733)
      ·
        refine ⟨2783001037184448982078025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7421336099158530618874733 2783001037184448982078025)
        ·
          refine ⟨2087250777888336736558519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783001037184448982078025 2087250777888336736558519)
          ·
            refine ⟨3130876166832505104837779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087250777888336736558519 3130876166832505104837779)
            ·
              refine ⟨4696314250248757657256669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130876166832505104837779 4696314250248757657256669)
              ·
                refine ⟨1761117843843284121471251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4696314250248757657256669 1761117843843284121471251)
                ·
                  refine ⟨2641676765764926182206877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761117843843284121471251 2641676765764926182206877)
                  ·
                    refine ⟨990628787161847318327579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641676765764926182206877 990628787161847318327579)
                    ·
                      rfl

theorem cell22_2893864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2893864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893864 prefixEnd_2893864 := by exact prefixLift 2893864
  have htrace : WordTrace (prefixWord ++ tailWord_2893864) baseStart_2893864 baseEnd_2893864 := by
    simpa [prefixWord, tailWord_2893864, baseEnd_2893864] using wordTrace_append hprefix tailTrace_2893864
  have hstable : (prefixWord ++ tailWord_2893864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893864).length < 2 ^ (prefixWord ++ tailWord_2893864).sum := by decide
  have hdescent : baseEnd_2893864 < baseStart_2893864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893888 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_2893888 : Nat := 118140960795 + 2893888 * 2 ^ 59
def prefixEnd_2893888 : Nat := 4983230072969 + 3 ^ 40 * 2893888 * 2
def baseEnd_2893888 : Nat := 330212334284106418575835

theorem tailTrace_2893888 : CollatzResearch.WordTrace tailWord_2893888 prefixEnd_2893888 330212334284106418575835 := by
  unfold tailWord_2893888
  simp only [CollatzResearch.WordTrace]
  refine ⟨52774383269972743783657159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70365844359963658378209545 52774383269972743783657159)
  ·
    refine ⟨79161574904959115675485739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52774383269972743783657159 79161574904959115675485739)
    ·
      refine ⟨118742362357438673513228609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79161574904959115675485739 118742362357438673513228609)
      ·
        refine ⟨89056771768079005134921457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118742362357438673513228609 89056771768079005134921457)
        ·
          refine ⟨66792578826059253851191093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89056771768079005134921457 66792578826059253851191093)
          ·
            refine ⟨6261804264943055048549165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66792578826059253851191093 6261804264943055048549165)
            ·
              refine ⟨2348176599353645643205937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6261804264943055048549165 2348176599353645643205937)
              ·
                refine ⟨1761132449515234232404453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348176599353645643205937 1761132449515234232404453)
                ·
                  refine ⟨330212334284106418575835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761132449515234232404453 330212334284106418575835)
                  ·
                    rfl

theorem cell22_2893888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_2893888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893888 prefixEnd_2893888 := by exact prefixLift 2893888
  have htrace : WordTrace (prefixWord ++ tailWord_2893888) baseStart_2893888 baseEnd_2893888 := by
    simpa [prefixWord, tailWord_2893888, baseEnd_2893888] using wordTrace_append hprefix tailTrace_2893888
  have hstable : (prefixWord ++ tailWord_2893888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893888).length < 2 ^ (prefixWord ++ tailWord_2893888).sum := by decide
  have hdescent : baseEnd_2893888 < baseStart_2893888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893901 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2893901 : Nat := 118140960795 + 2893901 * 2 ^ 59
def prefixEnd_2893901 : Nat := 4983230072969 + 3 ^ 40 * 2893901 * 2
def baseEnd_2893901 : Nat := 990641453017991555152465

theorem tailTrace_2893901 : CollatzResearch.WordTrace tailWord_2893901 prefixEnd_2893901 990641453017991555152465 := by
  unfold tailWord_2893901
  simp only [CollatzResearch.WordTrace]
  refine ⟨105549240688898390787537557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70366160459265593858358371 105549240688898390787537557)
  ·
    refine ⟨4947620657292112068165823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105549240688898390787537557 4947620657292112068165823)
    ·
      refine ⟨7421430985938168102248735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947620657292112068165823 7421430985938168102248735)
      ·
        refine ⟨11132146478907252153373103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421430985938168102248735 11132146478907252153373103)
        ·
          refine ⟨16698219718360878230059655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132146478907252153373103 16698219718360878230059655)
          ·
            refine ⟨25047329577541317345089483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16698219718360878230059655 25047329577541317345089483)
            ·
              refine ⟨37570994366311976017634225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25047329577541317345089483 37570994366311976017634225)
              ·
                refine ⟨28178245774733982013225669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37570994366311976017634225 28178245774733982013225669)
                ·
                  refine ⟨5283421082762621627479813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28178245774733982013225669 5283421082762621627479813)
                  ·
                    refine ⟨990641453017991555152465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283421082762621627479813 990641453017991555152465)
                    ·
                      rfl

theorem cell22_2893901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2893901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893901 prefixEnd_2893901 := by exact prefixLift 2893901
  have htrace : WordTrace (prefixWord ++ tailWord_2893901) baseStart_2893901 baseEnd_2893901 := by
    simpa [prefixWord, tailWord_2893901, baseEnd_2893901] using wordTrace_append hprefix tailTrace_2893901
  have hstable : (prefixWord ++ tailWord_2893901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893901).length < 2 ^ (prefixWord ++ tailWord_2893901).sum := by decide
  have hdescent : baseEnd_2893901 < baseStart_2893901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893959 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2893959 : Nat := 118140960795 + 2893959 * 2 ^ 59
def prefixEnd_2893959 : Nat := 4983230072969 + 3 ^ 40 * 2893959 * 2
def baseEnd_2893959 : Nat := 990661307603298737202287

theorem tailTrace_2893959 : CollatzResearch.WordTrace tailWord_2893959 prefixEnd_2893959 990661307603298737202287 := by
  unfold tailWord_2893959
  simp only [CollatzResearch.WordTrace]
  refine ⟨105551356122688266693148931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70367570748458844462099287 105551356122688266693148931)
  ·
    refine ⟨158327034184032400039723397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105551356122688266693148931 158327034184032400039723397)
    ·
      refine ⟨29686318909506075007448137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158327034184032400039723397 29686318909506075007448137)
      ·
        refine ⟨22264739182129556255586103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29686318909506075007448137 22264739182129556255586103)
        ·
          refine ⟨33397108773194334383379155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22264739182129556255586103 33397108773194334383379155)
          ·
            refine ⟨50095663159791501575068733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33397108773194334383379155 50095663159791501575068733)
            ·
              refine ⟨18785873684921813090650775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50095663159791501575068733 18785873684921813090650775)
              ·
                refine ⟨28178810527382719635976163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18785873684921813090650775 28178810527382719635976163)
                ·
                  refine ⟨42268215791074079453964245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28178810527382719635976163 42268215791074079453964245)
                  ·
                    refine ⟨990661307603298737202287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42268215791074079453964245 990661307603298737202287)
                    ·
                      rfl

theorem cell22_2893959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2893959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893959 prefixEnd_2893959 := by exact prefixLift 2893959
  have htrace : WordTrace (prefixWord ++ tailWord_2893959) baseStart_2893959 baseEnd_2893959 := by
    simpa [prefixWord, tailWord_2893959, baseEnd_2893959] using wordTrace_append hprefix tailTrace_2893959
  have hstable : (prefixWord ++ tailWord_2893959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893959).length < 2 ^ (prefixWord ++ tailWord_2893959).sum := by decide
  have hdescent : baseEnd_2893959 < baseStart_2893959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893989 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 8]
def baseStart_2893989 : Nat := 118140960795 + 2893989 * 2 ^ 59
def prefixEnd_2893989 : Nat := 4983230072969 + 3 ^ 40 * 2893989 * 2
def baseEnd_2893989 : Nat := 330223859072129552984065

theorem tailTrace_2893989 : CollatzResearch.WordTrace tailWord_2893989 prefixEnd_2893989 330223859072129552984065 := by
  unfold tailWord_2893989
  simp only [CollatzResearch.WordTrace]
  refine ⟨105552450312579581816741021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70368300208386387877827347 105552450312579581816741021)
  ·
    refine ⟨39582168867217343181277883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105552450312579581816741021 39582168867217343181277883)
    ·
      refine ⟨59373253300826014771916825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39582168867217343181277883 59373253300826014771916825)
      ·
        refine ⟨44529939975619511078937619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59373253300826014771916825 44529939975619511078937619)
        ·
          refine ⟨66794909963429266618406429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44529939975619511078937619 66794909963429266618406429)
          ·
            refine ⟨25048091236285974981902411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66794909963429266618406429 25048091236285974981902411)
            ·
              refine ⟨37572136854428962472853617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25048091236285974981902411 37572136854428962472853617)
              ·
                refine ⟨28179102640821721854640213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37572136854428962472853617 28179102640821721854640213)
                ·
                  refine ⟨330223859072129552984065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28179102640821721854640213 330223859072129552984065)
                  ·
                    rfl

theorem cell22_2893989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_2893989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2893989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2893989 prefixEnd_2893989 := by exact prefixLift 2893989
  have htrace : WordTrace (prefixWord ++ tailWord_2893989) baseStart_2893989 baseEnd_2893989 := by
    simpa [prefixWord, tailWord_2893989, baseEnd_2893989] using wordTrace_append hprefix tailTrace_2893989
  have hstable : (prefixWord ++ tailWord_2893989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893989).length < 2 ^ (prefixWord ++ tailWord_2893989).sum := by decide
  have hdescent : baseEnd_2893989 < baseStart_2893989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894021 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2894021 : Nat := 118140960795 + 2894021 * 2 ^ 59
def prefixEnd_2894021 : Nat := 4983230072969 + 3 ^ 40 * 2894021 * 2
def baseEnd_2894021 : Nat := 990682531470351242152097

theorem tailTrace_2894021 : CollatzResearch.WordTrace tailWord_2894021 prefixEnd_2894021 990682531470351242152097 := by
  unfold tailWord_2894021
  simp only [CollatzResearch.WordTrace]
  refine ⟨105553617448463651281905917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70369078298975767521270611 105553617448463651281905917)
  ·
    refine ⟨39582606543173869230714719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105553617448463651281905917 39582606543173869230714719)
    ·
      refine ⟨59373909814760803846072079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39582606543173869230714719 59373909814760803846072079)
      ·
        refine ⟨89060864722141205769108119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59373909814760803846072079 89060864722141205769108119)
        ·
          refine ⟨133591297083211808653662179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89060864722141205769108119 133591297083211808653662179)
          ·
            refine ⟨200386945624817712980493269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133591297083211808653662179 200386945624817712980493269)
            ·
              refine ⟨4696569038081665147980311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200386945624817712980493269 4696569038081665147980311)
              ·
                refine ⟨7044853557122497721970467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696569038081665147980311 7044853557122497721970467)
                ·
                  refine ⟨10567280335683746582955701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044853557122497721970467 10567280335683746582955701)
                  ·
                    refine ⟨990682531470351242152097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10567280335683746582955701 990682531470351242152097)
                    ·
                      rfl

theorem cell22_2894021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2894021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894021 prefixEnd_2894021 := by exact prefixLift 2894021
  have htrace : WordTrace (prefixWord ++ tailWord_2894021) baseStart_2894021 baseEnd_2894021 := by
    simpa [prefixWord, tailWord_2894021, baseEnd_2894021] using wordTrace_append hprefix tailTrace_2894021
  have hstable : (prefixWord ++ tailWord_2894021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894021).length < 2 ^ (prefixWord ++ tailWord_2894021).sum := by decide
  have hdescent : baseEnd_2894021 < baseStart_2894021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894040 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_2894040 : Nat := 118140960795 + 2894040 * 2 ^ 59
def prefixEnd_2894040 : Nat := 4983230072969 + 3 ^ 40 * 2894040 * 2
def baseEnd_2894040 : Nat := 330229678519547175309013

theorem tailTrace_2894040 : CollatzResearch.WordTrace tailWord_2894040 prefixEnd_2894040 330229678519547175309013 := by
  unfold tailWord_2894040
  simp only [CollatzResearch.WordTrace]
  refine ⟨52777155217697408763423787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70369540290263211684565049 52777155217697408763423787)
  ·
    refine ⟨79165732826546113145135681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52777155217697408763423787 79165732826546113145135681)
    ·
      refine ⟨59374299619909584858851761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79165732826546113145135681 59374299619909584858851761)
      ·
        refine ⟨44530724714932188644138821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59374299619909584858851761 44530724714932188644138821)
        ·
          refine ⟨8349510884049785370776029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44530724714932188644138821 8349510884049785370776029)
          ·
            refine ⟨3131066581518669514041011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8349510884049785370776029 3131066581518669514041011)
            ·
              refine ⟨4696599872278004271061517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131066581518669514041011 4696599872278004271061517)
              ·
                refine ⟨1761224952104251601648069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4696599872278004271061517 1761224952104251601648069)
                ·
                  refine ⟨330229678519547175309013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761224952104251601648069 330229678519547175309013)
                  ·
                    rfl

theorem cell22_2894040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_2894040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894040 prefixEnd_2894040 := by exact prefixLift 2894040
  have htrace : WordTrace (prefixWord ++ tailWord_2894040) baseStart_2894040 baseEnd_2894040 := by
    simpa [prefixWord, tailWord_2894040, baseEnd_2894040] using wordTrace_append hprefix tailTrace_2894040
  have hstable : (prefixWord ++ tailWord_2894040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894040).length < 2 ^ (prefixWord ++ tailWord_2894040).sum := by decide
  have hdescent : baseEnd_2894040 < baseStart_2894040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894053 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2894053 : Nat := 118140960795 + 2894053 * 2 ^ 59
def prefixEnd_2894053 : Nat := 4983230072969 + 3 ^ 40 * 2894053 * 2
def baseEnd_2894053 : Nat := 990693485724313825351999

theorem tailTrace_2894053 : CollatzResearch.WordTrace tailWord_2894053 prefixEnd_2894053 990693485724313825351999 := by
  unfold tailWord_2894053
  simp only [CollatzResearch.WordTrace]
  refine ⟨105554784584347720747070813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70369856389565147164713875 105554784584347720747070813)
  ·
    refine ⟨39583044219130395280151555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105554784584347720747070813 39583044219130395280151555)
    ·
      refine ⟨59374566328695592920227333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39583044219130395280151555 59374566328695592920227333)
      ·
        refine ⟨11132731186630423672542625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59374566328695592920227333 11132731186630423672542625)
        ·
          refine ⟨8349548389972817754406969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11132731186630423672542625 8349548389972817754406969)
          ·
            refine ⟨6262161292479613315805227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8349548389972817754406969 6262161292479613315805227)
            ·
              refine ⟨9393241938719419973707841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262161292479613315805227 9393241938719419973707841)
              ·
                refine ⟨7044931454039564980280881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9393241938719419973707841 7044931454039564980280881)
                ·
                  refine ⟨5283698590529673735210661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7044931454039564980280881 5283698590529673735210661)
                  ·
                    refine ⟨990693485724313825351999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283698590529673735210661 990693485724313825351999)
                    ·
                      rfl

theorem cell22_2894053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2894053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894053 prefixEnd_2894053 := by exact prefixLift 2894053
  have htrace : WordTrace (prefixWord ++ tailWord_2894053) baseStart_2894053 baseEnd_2894053 := by
    simpa [prefixWord, tailWord_2894053, baseEnd_2894053] using wordTrace_append hprefix tailTrace_2894053
  have hstable : (prefixWord ++ tailWord_2894053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894053).length < 2 ^ (prefixWord ++ tailWord_2894053).sum := by decide
  have hdescent : baseEnd_2894053 < baseStart_2894053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894117 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_2894117 : Nat := 118140960795 + 2894117 * 2 ^ 59
def prefixEnd_2894117 : Nat := 4983230072969 + 3 ^ 40 * 2894117 * 2
def baseEnd_2894117 : Nat := 990715394232238991751803

theorem tailTrace_2894117 : CollatzResearch.WordTrace tailWord_2894117 prefixEnd_2894117 990715394232238991751803 := by
  unfold tailWord_2894117
  simp only [CollatzResearch.WordTrace]
  refine ⟨105557118856115859677400605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70371412570743906451600403 105557118856115859677400605)
  ·
    refine ⟨39583919571043447379025227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105557118856115859677400605 39583919571043447379025227)
    ·
      refine ⟨59375879356565171068537841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39583919571043447379025227 59375879356565171068537841)
      ·
        refine ⟨44531909517423878301403381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59375879356565171068537841 44531909517423878301403381)
        ·
          refine ⟨4174866517258488590756567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44531909517423878301403381 4174866517258488590756567)
          ·
            refine ⟨6262299775887732886134851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174866517258488590756567 6262299775887732886134851)
            ·
              refine ⟨9393449663831599329202277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262299775887732886134851 9393449663831599329202277)
              ·
                refine ⟨1761271811968424874225427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9393449663831599329202277 1761271811968424874225427)
                ·
                  refine ⟨2641907717952637311338141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761271811968424874225427 2641907717952637311338141)
                  ·
                    refine ⟨990715394232238991751803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641907717952637311338141 990715394232238991751803)
                    ·
                      rfl

theorem cell22_2894117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_2894117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894117 prefixEnd_2894117 := by exact prefixLift 2894117
  have htrace : WordTrace (prefixWord ++ tailWord_2894117) baseStart_2894117 baseEnd_2894117 := by
    simpa [prefixWord, tailWord_2894117, baseEnd_2894117] using wordTrace_append hprefix tailTrace_2894117
  have hstable : (prefixWord ++ tailWord_2894117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894117).length < 2 ^ (prefixWord ++ tailWord_2894117).sum := by decide
  have hdescent : baseEnd_2894117 < baseStart_2894117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894119 : List Nat := [1, 1, 8, 1, 2, 1, 1, 7]
def baseStart_2894119 : Nat := 118140960795 + 2894119 * 2 ^ 59
def prefixEnd_2894119 : Nat := 4983230072969 + 3 ^ 40 * 2894119 * 2
def baseEnd_2894119 : Nat := 110079564319234628133533

theorem tailTrace_2894119 : CollatzResearch.WordTrace tailWord_2894119 prefixEnd_2894119 110079564319234628133533 := by
  unfold tailWord_2894119
  simp only [CollatzResearch.WordTrace]
  refine ⟨105557191802108614018973411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70371461201405742679315607 105557191802108614018973411)
  ·
    refine ⟨158335787703162921028460117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105557191802108614018973411 158335787703162921028460117)
    ·
      refine ⟨1855497512146440480802267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 158335787703162921028460117 1855497512146440480802267)
      ·
        refine ⟨2783246268219660721203401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855497512146440480802267 2783246268219660721203401)
        ·
          refine ⟨2087434701164745540902551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783246268219660721203401 2087434701164745540902551)
          ·
            refine ⟨3131152051747118311353827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087434701164745540902551 3131152051747118311353827)
            ·
              refine ⟨4696728077620677467030741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131152051747118311353827 4696728077620677467030741)
              ·
                refine ⟨110079564319234628133533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4696728077620677467030741 110079564319234628133533)
                ·
                  rfl

theorem cell22_2894119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 7].length) (baseStart_2894119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894119 prefixEnd_2894119 := by exact prefixLift 2894119
  have htrace : WordTrace (prefixWord ++ tailWord_2894119) baseStart_2894119 baseEnd_2894119 := by
    simpa [prefixWord, tailWord_2894119, baseEnd_2894119] using wordTrace_append hprefix tailTrace_2894119
  have hstable : (prefixWord ++ tailWord_2894119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894119).length < 2 ^ (prefixWord ++ tailWord_2894119).sum := by decide
  have hdescent : baseEnd_2894119 < baseStart_2894119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894143 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 1, 4]
def baseStart_2894143 : Nat := 118140960795 + 2894143 * 2 ^ 59
def prefixEnd_2894143 : Nat := 4983230072969 + 3 ^ 40 * 2894143 * 2
def baseEnd_2894143 : Nat := 990724294563583590601723

theorem tailTrace_2894143 : CollatzResearch.WordTrace tailWord_2894143 prefixEnd_2894143 990724294563583590601723 := by
  unfold tailWord_2894143
  simp only [CollatzResearch.WordTrace]
  refine ⟨105558067154021666117847083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70372044769347777411898055 105558067154021666117847083)
  ·
    refine ⟨158337100731032499176770625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105558067154021666117847083 158337100731032499176770625)
    ·
      refine ⟨118752825548274374382577969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158337100731032499176770625 118752825548274374382577969)
      ·
        refine ⟨89064619161205780786933477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118752825548274374382577969 89064619161205780786933477)
        ·
          refine ⟨16699616092726083897550027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89064619161205780786933477 16699616092726083897550027)
          ·
            refine ⟨25049424139089125846325041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699616092726083897550027 25049424139089125846325041)
            ·
              refine ⟨18787068104316844384743781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25049424139089125846325041 18787068104316844384743781)
              ·
                refine ⟨3522575269559408322139459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18787068104316844384743781 3522575269559408322139459)
                ·
                  refine ⟨5283862904339112483209189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522575269559408322139459 5283862904339112483209189)
                  ·
                    refine ⟨990724294563583590601723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283862904339112483209189 990724294563583590601723)
                    ·
                      rfl

theorem cell22_2894143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_2894143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894143 prefixEnd_2894143 := by exact prefixLift 2894143
  have htrace : WordTrace (prefixWord ++ tailWord_2894143) baseStart_2894143 baseEnd_2894143 := by
    simpa [prefixWord, tailWord_2894143, baseEnd_2894143] using wordTrace_append hprefix tailTrace_2894143
  have hstable : (prefixWord ++ tailWord_2894143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894143).length < 2 ^ (prefixWord ++ tailWord_2894143).sum := by decide
  have hdescent : baseEnd_2894143 < baseStart_2894143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894160 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_2894160 : Nat := 118140960795 + 2894160 * 2 ^ 59
def prefixEnd_2894160 : Nat := 4983230072969 + 3 ^ 40 * 2894160 * 2
def baseEnd_2894160 : Nat := 990730114011001212926671

theorem tailTrace_2894160 : CollatzResearch.WordTrace tailWord_2894160 prefixEnd_2894160 990730114011001212926671 := by
  unfold tailWord_2894160
  simp only [CollatzResearch.WordTrace]
  refine ⟨52779343597480039010607967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70372458129973385347477289 52779343597480039010607967)
  ·
    refine ⟨79169015396220058515911951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52779343597480039010607967 79169015396220058515911951)
    ·
      refine ⟨118753523094330087773867927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79169015396220058515911951 118753523094330087773867927)
      ·
        refine ⟨178130284641495131660801891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118753523094330087773867927 178130284641495131660801891)
        ·
          refine ⟨267195426962242697491202837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178130284641495131660801891 267195426962242697491202837)
          ·
            refine ⟨12524785638855126444900133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 267195426962242697491202837 12524785638855126444900133)
            ·
              refine ⟨2348397307285336208418775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12524785638855126444900133 2348397307285336208418775)
              ·
                refine ⟨3522595960928004312628163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348397307285336208418775 3522595960928004312628163)
                ·
                  refine ⟨5283893941392006468942245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522595960928004312628163 5283893941392006468942245)
                  ·
                    refine ⟨990730114011001212926671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283893941392006468942245 990730114011001212926671)
                    ·
                      rfl

theorem cell22_2894160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_2894160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894160 prefixEnd_2894160 := by exact prefixLift 2894160
  have htrace : WordTrace (prefixWord ++ tailWord_2894160) baseStart_2894160 baseEnd_2894160 := by
    simpa [prefixWord, tailWord_2894160, baseEnd_2894160] using wordTrace_append hprefix tailTrace_2894160
  have hstable : (prefixWord ++ tailWord_2894160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894160).length < 2 ^ (prefixWord ++ tailWord_2894160).sum := by decide
  have hdescent : baseEnd_2894160 < baseStart_2894160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894201 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_2894201 : Nat := 118140960795 + 2894201 * 2 ^ 59
def prefixEnd_2894201 : Nat := 4983230072969 + 3 ^ 40 * 2894201 * 2
def baseEnd_2894201 : Nat := 990744149148890772651545

theorem tailTrace_2894201 : CollatzResearch.WordTrace tailWord_2894201 prefixEnd_2894201 990744149148890772651545 := by
  unfold tailWord_2894201
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560182587811542023458457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70373455058541028015638971 105560182587811542023458457)
  ·
    refine ⟨79170136940858656517593843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105560182587811542023458457 79170136940858656517593843)
    ·
      refine ⟨118755205411287984776390765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79170136940858656517593843 118755205411287984776390765)
      ·
        refine ⟨44533202029232994291146537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118755205411287984776390765 44533202029232994291146537)
        ·
          refine ⟨33399901521924745718359903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44533202029232994291146537 33399901521924745718359903)
          ·
            refine ⟨50099852282887118577539855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33399901521924745718359903 50099852282887118577539855)
            ·
              refine ⟨75149778424330677866309783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50099852282887118577539855 75149778424330677866309783)
              ·
                refine ⟨112724667636496016799464675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75149778424330677866309783 112724667636496016799464675)
                ·
                  refine ⟨169087001454744025199197013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112724667636496016799464675 169087001454744025199197013)
                  ·
                    refine ⟨990744149148890772651545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169087001454744025199197013 990744149148890772651545)
                    ·
                      rfl

theorem cell22_2894201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_2894201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894201 prefixEnd_2894201 := by exact prefixLift 2894201
  have htrace : WordTrace (prefixWord ++ tailWord_2894201) baseStart_2894201 baseEnd_2894201 := by
    simpa [prefixWord, tailWord_2894201, baseEnd_2894201] using wordTrace_append hprefix tailTrace_2894201
  have hstable : (prefixWord ++ tailWord_2894201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894201).length < 2 ^ (prefixWord ++ tailWord_2894201).sum := by decide
  have hdescent : baseEnd_2894201 < baseStart_2894201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894203 : List Nat := [1, 1, 1, 1, 1, 7, 4, 6]
def baseStart_2894203 : Nat := 118140960795 + 2894203 * 2 ^ 59
def prefixEnd_2894203 : Nat := 4983230072969 + 3 ^ 40 * 2894203 * 2
def baseEnd_2894203 : Nat := 110082759309973714900171

theorem tailTrace_2894203 : CollatzResearch.WordTrace tailWord_2894203 prefixEnd_2894203 110082759309973714900171 := by
  unfold tailWord_2894203
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560255533804296365031263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70373503689202864243354175 105560255533804296365031263)
  ·
    refine ⟨158340383300706444547546895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105560255533804296365031263 158340383300706444547546895)
    ·
      refine ⟨237510574951059666821320343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158340383300706444547546895 237510574951059666821320343)
      ·
        refine ⟨356265862426589500231980515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237510574951059666821320343 356265862426589500231980515)
        ·
          refine ⟨534398793639884250347970773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356265862426589500231980515 534398793639884250347970773)
          ·
            refine ⟨12524971725934787117530565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 534398793639884250347970773 12524971725934787117530565)
            ·
              refine ⟨2348432198612772584536981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12524971725934787117530565 2348432198612772584536981)
              ·
                refine ⟨110082759309973714900171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2348432198612772584536981 110082759309973714900171)
                ·
                  rfl

theorem cell22_2894203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 6].length) (baseStart_2894203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894203 prefixEnd_2894203 := by exact prefixLift 2894203
  have htrace : WordTrace (prefixWord ++ tailWord_2894203) baseStart_2894203 baseEnd_2894203 := by
    simpa [prefixWord, tailWord_2894203, baseEnd_2894203] using wordTrace_append hprefix tailTrace_2894203
  have hstable : (prefixWord ++ tailWord_2894203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894203).length < 2 ^ (prefixWord ++ tailWord_2894203).sum := by decide
  have hdescent : baseEnd_2894203 < baseStart_2894203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894241 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2894241 : Nat := 118140960795 + 2894241 * 2 ^ 59
def prefixEnd_2894241 : Nat := 4983230072969 + 3 ^ 40 * 2894241 * 2
def baseEnd_2894241 : Nat := 990757841966344001651423

theorem tailTrace_2894241 : CollatzResearch.WordTrace tailWord_2894241 prefixEnd_2894241 990757841966344001651423 := by
  unfold tailWord_2894241
  simp only [CollatzResearch.WordTrace]
  refine ⟨105561641507666628854914577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70374427671777752569943051 105561641507666628854914577)
  ·
    refine ⟨79171231130749971641185933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105561641507666628854914577 79171231130749971641185933)
    ·
      refine ⟨29689211674031239365444725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79171231130749971641185933 29689211674031239365444725)
      ·
        refine ⟨2783363594440428690510443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29689211674031239365444725 2783363594440428690510443)
        ·
          refine ⟨4175045391660643035765665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783363594440428690510443 4175045391660643035765665)
          ·
            refine ⟨3131284043745482276824249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175045391660643035765665 3131284043745482276824249)
            ·
              refine ⟨2348463032809111707618187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131284043745482276824249 2348463032809111707618187)
              ·
                refine ⟨3522694549213667561427281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348463032809111707618187 3522694549213667561427281)
                ·
                  refine ⟨2642020911910250671070461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3522694549213667561427281 2642020911910250671070461)
                  ·
                    refine ⟨990757841966344001651423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642020911910250671070461 990757841966344001651423)
                    ·
                      rfl

theorem cell22_2894241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2894241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894241 prefixEnd_2894241 := by exact prefixLift 2894241
  have htrace : WordTrace (prefixWord ++ tailWord_2894241) baseStart_2894241 baseEnd_2894241 := by
    simpa [prefixWord, tailWord_2894241, baseEnd_2894241] using wordTrace_append hprefix tailTrace_2894241
  have hstable : (prefixWord ++ tailWord_2894241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894241).length < 2 ^ (prefixWord ++ tailWord_2894241).sum := by decide
  have hdescent : baseEnd_2894241 < baseStart_2894241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894323 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_2894323 : Nat := 118140960795 + 2894323 * 2 ^ 59
def prefixEnd_2894323 : Nat := 4983230072969 + 3 ^ 40 * 2894323 * 2
def baseEnd_2894323 : Nat := 990785912242123121101171

theorem tailTrace_2894323 : CollatzResearch.WordTrace tailWord_2894323 prefixEnd_2894323 990785912242123121101171 := by
  unfold tailWord_2894323
  simp only [CollatzResearch.WordTrace]
  refine ⟨105564632293369556859399623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70376421528913037906266415 105564632293369556859399623)
  ·
    refine ⟨158346948440054335289099435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105564632293369556859399623 158346948440054335289099435)
    ·
      refine ⟨237520422660081502933649153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158346948440054335289099435 237520422660081502933649153)
      ·
        refine ⟨178140316995061127200236865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237520422660081502933649153 178140316995061127200236865)
        ·
          refine ⟨133605237746295845400177649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178140316995061127200236865 133605237746295845400177649)
          ·
            refine ⟨100203928309721884050133237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133605237746295845400177649 100203928309721884050133237)
            ·
              refine ⟨9394118279036426629699991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100203928309721884050133237 9394118279036426629699991)
              ·
                refine ⟨14091177418554639944549987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394118279036426629699991 14091177418554639944549987)
                ·
                  refine ⟨21136766127831959916824981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14091177418554639944549987 21136766127831959916824981)
                  ·
                    refine ⟨990785912242123121101171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21136766127831959916824981 990785912242123121101171)
                    ·
                      rfl

theorem cell22_2894323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_2894323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894323 prefixEnd_2894323 := by exact prefixLift 2894323
  have htrace : WordTrace (prefixWord ++ tailWord_2894323) baseStart_2894323 baseEnd_2894323 := by
    simpa [prefixWord, tailWord_2894323, baseEnd_2894323] using wordTrace_append hprefix tailTrace_2894323
  have hstable : (prefixWord ++ tailWord_2894323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894323).length < 2 ^ (prefixWord ++ tailWord_2894323).sum := by decide
  have hdescent : baseEnd_2894323 < baseStart_2894323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894359 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 1, 5]
def baseStart_2894359 : Nat := 118140960795 + 2894359 * 2 ^ 59
def prefixEnd_2894359 : Nat := 4983230072969 + 3 ^ 40 * 2894359 * 2
def baseEnd_2894359 : Nat := 990798235777831027201061

theorem tailTrace_2894359 : CollatzResearch.WordTrace tailWord_2894359 prefixEnd_2894359 990798235777831027201061 := by
  unfold tailWord_2894359
  simp only [CollatzResearch.WordTrace]
  refine ⟨105565945321239135007710131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70377296880826090005140087 105565945321239135007710131)
  ·
    refine ⟨158348917981858702511565197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105565945321239135007710131 158348917981858702511565197)
    ·
      refine ⟨59380844243197013441836949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158348917981858702511565197 59380844243197013441836949)
      ·
        refine ⟨2783477073899860005086107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59380844243197013441836949 2783477073899860005086107)
        ·
          refine ⟨4175215610849790007629161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783477073899860005086107 4175215610849790007629161)
          ·
            refine ⟨3131411708137342505721871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175215610849790007629161 3131411708137342505721871)
            ·
              refine ⟨4697117562206013758582807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131411708137342505721871 4697117562206013758582807)
              ·
                refine ⟨7045676343309020637874211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697117562206013758582807 7045676343309020637874211)
                ·
                  refine ⟨10568514514963530956811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7045676343309020637874211 10568514514963530956811317)
                  ·
                    refine ⟨990798235777831027201061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10568514514963530956811317 990798235777831027201061)
                    ·
                      rfl

theorem cell22_2894359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_2894359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894359 prefixEnd_2894359 := by exact prefixLift 2894359
  have htrace : WordTrace (prefixWord ++ tailWord_2894359) baseStart_2894359 baseEnd_2894359 := by
    simpa [prefixWord, tailWord_2894359, baseEnd_2894359] using wordTrace_append hprefix tailTrace_2894359
  have hstable : (prefixWord ++ tailWord_2894359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894359).length < 2 ^ (prefixWord ++ tailWord_2894359).sum := by decide
  have hdescent : baseEnd_2894359 < baseStart_2894359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894372 : List Nat := [2, 3, 1, 5, 1, 1, 1, 8]
def baseStart_2894372 : Nat := 118140960795 + 2894372 * 2 ^ 59
def prefixEnd_2894372 : Nat := 4983230072969 + 3 ^ 40 * 2894372 * 2
def baseEnd_2894372 : Nat := 110089187327055925180669

theorem tailTrace_2894372 : CollatzResearch.WordTrace tailWord_2894372 prefixEnd_2894372 110089187327055925180669 := by
  unfold tailWord_2894372
  simp only [CollatzResearch.WordTrace]
  refine ⟨52783209735096019113966685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70377612980128025485288913 52783209735096019113966685)
  ·
    refine ⟨19793703650661007167737507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52783209735096019113966685 19793703650661007167737507)
    ·
      refine ⟨29690555475991510751606261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19793703650661007167737507 29690555475991510751606261)
      ·
        refine ⟨2783489575874204132963087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29690555475991510751606261 2783489575874204132963087)
        ·
          refine ⟨4175234363811306199444631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783489575874204132963087 4175234363811306199444631)
          ·
            refine ⟨6262851545716959299166947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175234363811306199444631 6262851545716959299166947)
            ·
              refine ⟨9394277318575438948750421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262851545716959299166947 9394277318575438948750421)
              ·
                refine ⟨110089187327055925180669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9394277318575438948750421 110089187327055925180669)
                ·
                  rfl

theorem cell22_2894372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_2894372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894372 prefixEnd_2894372 := by exact prefixLift 2894372
  have htrace : WordTrace (prefixWord ++ tailWord_2894372) baseStart_2894372 baseEnd_2894372 := by
    simpa [prefixWord, tailWord_2894372, baseEnd_2894372] using wordTrace_append hprefix tailTrace_2894372
  have hstable : (prefixWord ++ tailWord_2894372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894372).length < 2 ^ (prefixWord ++ tailWord_2894372).sum := by decide
  have hdescent : baseEnd_2894372 < baseStart_2894372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894417 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 5]
def baseStart_2894417 : Nat := 118140960795 + 2894417 * 2 ^ 59
def prefixEnd_2894417 : Nat := 4983230072969 + 3 ^ 40 * 2894417 * 2
def baseEnd_2894417 : Nat := 330272696787712736416961

theorem tailTrace_2894417 : CollatzResearch.WordTrace tailWord_2894417 prefixEnd_2894417 330272696787712736416961 := by
  unfold tailWord_2894417
  simp only [CollatzResearch.WordTrace]
  refine ⟨105568060755029010913321505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70378707170019340608881003 105568060755029010913321505)
  ·
    refine ⟨79176045566271758184991129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105568060755029010913321505 79176045566271758184991129)
    ·
      refine ⟨59382034174703818638743347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79176045566271758184991129 59382034174703818638743347)
      ·
        refine ⟨89073051262055727958115021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59382034174703818638743347 89073051262055727958115021)
        ·
          refine ⟨33402394223270897984293133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89073051262055727958115021 33402394223270897984293133)
          ·
            refine ⟨12525897833726586744109925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33402394223270897984293133 12525897833726586744109925)
            ·
              refine ⟨2348605843823735014520611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12525897833726586744109925 2348605843823735014520611)
              ·
                refine ⟨3522908765735602521780917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348605843823735014520611 3522908765735602521780917)
                ·
                  refine ⟨330272696787712736416961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3522908765735602521780917 330272696787712736416961)
                  ·
                    rfl

theorem cell22_2894417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_2894417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894417 prefixEnd_2894417 := by exact prefixLift 2894417
  have htrace : WordTrace (prefixWord ++ tailWord_2894417) baseStart_2894417 baseEnd_2894417 := by
    simpa [prefixWord, tailWord_2894417, baseEnd_2894417] using wordTrace_append hprefix tailTrace_2894417
  have hstable : (prefixWord ++ tailWord_2894417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894417).length < 2 ^ (prefixWord ++ tailWord_2894417).sum := by decide
  have hdescent : baseEnd_2894417 < baseStart_2894417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894492 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2894492 : Nat := 118140960795 + 2894492 * 2 ^ 59
def prefixEnd_2894492 : Nat := 4983230072969 + 3 ^ 40 * 2894492 * 2
def baseEnd_2894492 : Nat := 990843764395863013625653

theorem tailTrace_2894492 : CollatzResearch.WordTrace tailWord_2894492 prefixEnd_2894492 990843764395863013625653 := by
  unfold tailWord_2894492
  simp only [CollatzResearch.WordTrace]
  refine ⟨52785398114878649361150865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70380530819838199148201153 52785398114878649361150865)
  ·
    refine ⟨39589048586158987020863149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52785398114878649361150865 39589048586158987020863149)
    ·
      refine ⟨14845893219809620132823681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39589048586158987020863149 14845893219809620132823681)
      ·
        refine ⟨11134419914857215099617761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14845893219809620132823681 11134419914857215099617761)
        ·
          refine ⟨8350814936142911324713321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11134419914857215099617761 8350814936142911324713321)
          ·
            refine ⟨6263111202107183493534991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350814936142911324713321 6263111202107183493534991)
            ·
              refine ⟨9394666803160775240302487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263111202107183493534991 9394666803160775240302487)
              ·
                refine ⟨14092000204741162860453731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394666803160775240302487 14092000204741162860453731)
                ·
                  refine ⟨21138000307111744290680597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14092000204741162860453731 21138000307111744290680597)
                  ·
                    refine ⟨990843764395863013625653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21138000307111744290680597 990843764395863013625653)
                    ·
                      rfl

theorem cell22_2894492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2894492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894492 prefixEnd_2894492 := by exact prefixLift 2894492
  have htrace : WordTrace (prefixWord ++ tailWord_2894492) baseStart_2894492 baseEnd_2894492 := by
    simpa [prefixWord, tailWord_2894492, baseEnd_2894492] using wordTrace_append hprefix tailTrace_2894492
  have hstable : (prefixWord ++ tailWord_2894492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894492).length < 2 ^ (prefixWord ++ tailWord_2894492).sum := by decide
  have hdescent : baseEnd_2894492 < baseStart_2894492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894494 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2894494 : Nat := 118140960795 + 2894494 * 2 ^ 59
def prefixEnd_2894494 : Nat := 4983230072969 + 3 ^ 40 * 2894494 * 2
def baseEnd_2894494 : Nat := 990844449036735675075647

theorem tailTrace_2894494 : CollatzResearch.WordTrace tailWord_2894494 prefixEnd_2894494 990844449036735675075647 := by
  unfold tailWord_2894494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196358646968756632984317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70380579450500035375916357 13196358646968756632984317)
  ·
    refine ⟨4948634492613283737369119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13196358646968756632984317 4948634492613283737369119)
    ·
      refine ⟨7422951738919925606053679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4948634492613283737369119 7422951738919925606053679)
      ·
        refine ⟨11134427608379888409080519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422951738919925606053679 11134427608379888409080519)
        ·
          refine ⟨16701641412569832613620779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11134427608379888409080519 16701641412569832613620779)
          ·
            refine ⟨25052462118854748920431169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16701641412569832613620779 25052462118854748920431169)
            ·
              refine ⟨18789346589141061690323377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25052462118854748920431169 18789346589141061690323377)
              ·
                refine ⟨14092009941855796267742533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18789346589141061690323377 14092009941855796267742533)
                ·
                  refine ⟨2642251864097961800201725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14092009941855796267742533 2642251864097961800201725)
                  ·
                    refine ⟨990844449036735675075647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642251864097961800201725 990844449036735675075647)
                    ·
                      rfl

theorem cell22_2894494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2894494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894494 prefixEnd_2894494 := by exact prefixLift 2894494
  have htrace : WordTrace (prefixWord ++ tailWord_2894494) baseStart_2894494 baseEnd_2894494 := by
    simpa [prefixWord, tailWord_2894494, baseEnd_2894494] using wordTrace_append hprefix tailTrace_2894494
  have hstable : (prefixWord ++ tailWord_2894494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894494).length < 2 ^ (prefixWord ++ tailWord_2894494).sum := by decide
  have hdescent : baseEnd_2894494 < baseStart_2894494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894573 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_2894573 : Nat := 118140960795 + 2894573 * 2 ^ 59
def prefixEnd_2894573 : Nat := 4983230072969 + 3 ^ 40 * 2894573 * 2
def baseEnd_2894573 : Nat := 990871492351205802350405

theorem tailTrace_2894573 : CollatzResearch.WordTrace tailWord_2894573 prefixEnd_2894573 990871492351205802350405 := by
  unfold tailWord_2894573
  simp only [CollatzResearch.WordTrace]
  refine ⟨105573750542463849556000373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70382500361642566370666915 105573750542463849556000373)
  ·
    refine ⟨9897539113355985895875035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105573750542463849556000373 9897539113355985895875035)
    ·
      refine ⟨14846308670033978843812553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897539113355985895875035 14846308670033978843812553)
      ·
        refine ⟨11134731502525484132859415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14846308670033978843812553 11134731502525484132859415)
        ·
          refine ⟨16702097253788226199289123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11134731502525484132859415 16702097253788226199289123)
          ·
            refine ⟨25053145880682339298933685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16702097253788226199289123 25053145880682339298933685)
            ·
              refine ⟨2348732426313969309275033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25053145880682339298933685 2348732426313969309275033)
              ·
                refine ⟨1761549319735476981956275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348732426313969309275033 1761549319735476981956275)
                ·
                  refine ⟨2642323979603215472934413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761549319735476981956275 2642323979603215472934413)
                  ·
                    refine ⟨990871492351205802350405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642323979603215472934413 990871492351205802350405)
                    ·
                      rfl

theorem cell22_2894573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_2894573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894573 prefixEnd_2894573 := by exact prefixLift 2894573
  have htrace : WordTrace (prefixWord ++ tailWord_2894573) baseStart_2894573 baseEnd_2894573 := by
    simpa [prefixWord, tailWord_2894573, baseEnd_2894573] using wordTrace_append hprefix tailTrace_2894573
  have hstable : (prefixWord ++ tailWord_2894573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894573).length < 2 ^ (prefixWord ++ tailWord_2894573).sum := by decide
  have hdescent : baseEnd_2894573 < baseStart_2894573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894599 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2894599 : Nat := 118140960795 + 2894599 * 2 ^ 59
def prefixEnd_2894599 : Nat := 4983230072969 + 3 ^ 40 * 2894599 * 2
def baseEnd_2894599 : Nat := 990880392682550401200325

theorem tailTrace_2894599 : CollatzResearch.WordTrace tailWord_2894599 prefixEnd_2894599 990880392682550401200325 := by
  unfold tailWord_2894599
  simp only [CollatzResearch.WordTrace]
  refine ⟨105574698840369655996446851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70383132560246437330964567 105574698840369655996446851)
  ·
    refine ⟨158362048260554483994670277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105574698840369655996446851 158362048260554483994670277)
    ·
      refine ⟨29692884048853965749000677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158362048260554483994670277 29692884048853965749000677)
      ·
        refine ⟨5567415759160118577937627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29692884048853965749000677 5567415759160118577937627)
        ·
          refine ⟨8351123638740177866906441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567415759160118577937627 8351123638740177866906441)
          ·
            refine ⟨6263342729055133400179831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351123638740177866906441 6263342729055133400179831)
            ·
              refine ⟨9395014093582700100269747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263342729055133400179831 9395014093582700100269747)
              ·
                refine ⟨14092521140374050150404621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395014093582700100269747 14092521140374050150404621)
                ·
                  refine ⟨5284695427640268806401733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14092521140374050150404621 5284695427640268806401733)
                  ·
                    refine ⟨990880392682550401200325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5284695427640268806401733 990880392682550401200325)
                    ·
                      rfl

theorem cell22_2894599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2894599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894599 prefixEnd_2894599 := by exact prefixLift 2894599
  have htrace : WordTrace (prefixWord ++ tailWord_2894599) baseStart_2894599 baseEnd_2894599 := by
    simpa [prefixWord, tailWord_2894599, baseEnd_2894599] using wordTrace_append hprefix tailTrace_2894599
  have hstable : (prefixWord ++ tailWord_2894599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894599).length < 2 ^ (prefixWord ++ tailWord_2894599).sum := by decide
  have hdescent : baseEnd_2894599 < baseStart_2894599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894674 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2894674 : Nat := 118140960795 + 2894674 * 2 ^ 59
def prefixEnd_2894674 : Nat := 4983230072969 + 3 ^ 40 * 2894674 * 2
def baseEnd_2894674 : Nat := 990906066715275205575095

theorem tailTrace_2894674 : CollatzResearch.WordTrace tailWord_2894674 prefixEnd_2894674 990906066715275205575095 := by
  unfold tailWord_2894674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394358578774485951356769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70384956210065295870284717 26394358578774485951356769)
  ·
    refine ⟨19795768934080864463517577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26394358578774485951356769 19795768934080864463517577)
    ·
      refine ⟨14846826700560648347638183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19795768934080864463517577 14846826700560648347638183)
      ·
        refine ⟨22270240050840972521457275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14846826700560648347638183 22270240050840972521457275)
        ·
          refine ⟨33405360076261458782185913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22270240050840972521457275 33405360076261458782185913)
          ·
            refine ⟨25054020057196094086639435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33405360076261458782185913 25054020057196094086639435)
            ·
              refine ⟨37581030085794141129959153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25054020057196094086639435 37581030085794141129959153)
              ·
                refine ⟨28185772564345605847469365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37581030085794141129959153 28185772564345605847469365)
                ·
                  refine ⟨2642416177907400548200253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28185772564345605847469365 2642416177907400548200253)
                  ·
                    refine ⟨990906066715275205575095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642416177907400548200253 990906066715275205575095)
                    ·
                      rfl

theorem cell22_2894674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2894674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894674 prefixEnd_2894674 := by exact prefixLift 2894674
  have htrace : WordTrace (prefixWord ++ tailWord_2894674) baseStart_2894674 baseEnd_2894674 := by
    simpa [prefixWord, tailWord_2894674, baseEnd_2894674] using wordTrace_append hprefix tailTrace_2894674
  have hstable : (prefixWord ++ tailWord_2894674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894674).length < 2 ^ (prefixWord ++ tailWord_2894674).sum := by decide
  have hdescent : baseEnd_2894674 < baseStart_2894674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894687 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 7]
def baseStart_2894687 : Nat := 118140960795 + 2894687 * 2 ^ 59
def prefixEnd_2894687 : Nat := 4983230072969 + 3 ^ 40 * 2894687 * 2
def baseEnd_2894687 : Nat := 330303505626982501666685

theorem tailTrace_2894687 : CollatzResearch.WordTrace tailWord_2894687 prefixEnd_2894687 330303505626982501666685 := by
  unfold tailWord_2894687
  simp only [CollatzResearch.WordTrace]
  refine ⟨105577908464050847025650315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70385272309367231350433543 105577908464050847025650315)
  ·
    refine ⟨158366862696076270538475473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105577908464050847025650315 158366862696076270538475473)
    ·
      refine ⟨118775147022057202903856605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158366862696076270538475473 118775147022057202903856605)
      ·
        refine ⟨44540680133271451088946227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118775147022057202903856605 44540680133271451088946227)
        ·
          refine ⟨66811020199907176633419341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44540680133271451088946227 66811020199907176633419341)
          ·
            refine ⟨25054132574965191237532253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66811020199907176633419341 25054132574965191237532253)
            ·
              refine ⟨9395299715611946714074595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25054132574965191237532253 9395299715611946714074595)
              ·
                refine ⟨14092949573417920071111893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395299715611946714074595 14092949573417920071111893)
                ·
                  refine ⟨330303505626982501666685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14092949573417920071111893 330303505626982501666685)
                  ·
                    rfl

theorem cell22_2894687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_2894687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894687 prefixEnd_2894687 := by exact prefixLift 2894687
  have htrace : WordTrace (prefixWord ++ tailWord_2894687) baseStart_2894687 baseEnd_2894687 := by
    simpa [prefixWord, tailWord_2894687, baseEnd_2894687] using wordTrace_append hprefix tailTrace_2894687
  have hstable : (prefixWord ++ tailWord_2894687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894687).length < 2 ^ (prefixWord ++ tailWord_2894687).sum := by decide
  have hdescent : baseEnd_2894687 < baseStart_2894687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894691 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 3, 3]
def baseStart_2894691 : Nat := 118140960795 + 2894691 * 2 ^ 59
def prefixEnd_2894691 : Nat := 4983230072969 + 3 ^ 40 * 2894691 * 2
def baseEnd_2894691 : Nat := 990911886162692827900043

theorem tailTrace_2894691 : CollatzResearch.WordTrace tailWord_2894691 prefixEnd_2894691 990911886162692827900043 := by
  unfold tailWord_2894691
  simp only [CollatzResearch.WordTrace]
  refine ⟨105578054356036355708795927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70385369570690903805863951 105578054356036355708795927)
  ·
    refine ⟨158367081534054533563193891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105578054356036355708795927 158367081534054533563193891)
    ·
      refine ⟨237550622301081800344790837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158367081534054533563193891 237550622301081800344790837)
      ·
        refine ⟨22270370840726418782324141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237550622301081800344790837 22270370840726418782324141)
        ·
          refine ⟨8351389065272407043371553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22270370840726418782324141 8351389065272407043371553)
          ·
            refine ⟨6263541798954305282528665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351389065272407043371553 6263541798954305282528665)
            ·
              refine ⟨4697656349215728961896499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263541798954305282528665 4697656349215728961896499)
              ·
                refine ⟨7046484523823593442844749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697656349215728961896499 7046484523823593442844749)
                ·
                  refine ⟨2642431696433847541066781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7046484523823593442844749 2642431696433847541066781)
                  ·
                    refine ⟨990911886162692827900043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642431696433847541066781 990911886162692827900043)
                    ·
                      rfl

theorem cell22_2894691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3].length) (baseStart_2894691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894691 prefixEnd_2894691 := by exact prefixLift 2894691
  have htrace : WordTrace (prefixWord ++ tailWord_2894691) baseStart_2894691 baseEnd_2894691 := by
    simpa [prefixWord, tailWord_2894691, baseEnd_2894691] using wordTrace_append hprefix tailTrace_2894691
  have hstable : (prefixWord ++ tailWord_2894691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894691).length < 2 ^ (prefixWord ++ tailWord_2894691).sum := by decide
  have hdescent : baseEnd_2894691 < baseStart_2894691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894732 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_2894732 : Nat := 118140960795 + 2894732 * 2 ^ 59
def prefixEnd_2894732 : Nat := 4983230072969 + 3 ^ 40 * 2894732 * 2
def baseEnd_2894732 : Nat := 330308640433527462541639

theorem tailTrace_2894732 : CollatzResearch.WordTrace tailWord_2894732 prefixEnd_2894732 330308640433527462541639 := by
  unfold tailWord_2894732
  simp only [CollatzResearch.WordTrace]
  refine ⟨52789774874443909855519225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70386366499258546474025633 52789774874443909855519225)
  ·
    refine ⟨39592331155832932391639419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52789774874443909855519225 39592331155832932391639419)
    ·
      refine ⟨59388496733749398587459129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39592331155832932391639419 59388496733749398587459129)
      ·
        refine ⟨44541372550312048940594347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59388496733749398587459129 44541372550312048940594347)
        ·
          refine ⟨66812058825468073410891521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44541372550312048940594347 66812058825468073410891521)
          ·
            refine ⟨50109044119101055058168641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66812058825468073410891521 50109044119101055058168641)
            ·
              refine ⟨37581783089325791293626481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50109044119101055058168641 37581783089325791293626481)
              ·
                refine ⟨28186337316994343470219861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37581783089325791293626481 28186337316994343470219861)
                ·
                  refine ⟨330308640433527462541639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28186337316994343470219861 330308640433527462541639)
                  ·
                    rfl

theorem cell22_2894732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_2894732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894732 prefixEnd_2894732 := by exact prefixLift 2894732
  have htrace : WordTrace (prefixWord ++ tailWord_2894732) baseStart_2894732 baseEnd_2894732 := by
    simpa [prefixWord, tailWord_2894732, baseEnd_2894732] using wordTrace_append hprefix tailTrace_2894732
  have hstable : (prefixWord ++ tailWord_2894732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894732).length < 2 ^ (prefixWord ++ tailWord_2894732).sum := by decide
  have hdescent : baseEnd_2894732 < baseStart_2894732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894742 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2894742 : Nat := 118140960795 + 2894742 * 2 ^ 59
def prefixEnd_2894742 : Nat := 4983230072969 + 3 ^ 40 * 2894742 * 2
def baseEnd_2894742 : Nat := 990929344504945694874887

theorem tailTrace_2894742 : CollatzResearch.WordTrace tailWord_2894742 prefixEnd_2894742 990929344504945694874887 := by
  unfold tailWord_2894742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598744654928224463681405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70386609652567727612601653 6598744654928224463681405)
  ·
    refine ⟨2474529245598084173880527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6598744654928224463681405 2474529245598084173880527)
    ·
      refine ⟨3711793868397126260820791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474529245598084173880527 3711793868397126260820791)
      ·
        refine ⟨5567690802595689391231187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711793868397126260820791 5567690802595689391231187)
        ·
          refine ⟨8351536203893534086846781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567690802595689391231187 8351536203893534086846781)
          ·
            refine ⟨3131826076460075282567543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8351536203893534086846781 3131826076460075282567543)
            ·
              refine ⟨4697739114690112923851315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131826076460075282567543 4697739114690112923851315)
              ·
                refine ⟨7046608672035169385776973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697739114690112923851315 7046608672035169385776973)
                ·
                  refine ⟨2642478252013188519666365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7046608672035169385776973 2642478252013188519666365)
                  ·
                    refine ⟨990929344504945694874887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642478252013188519666365 990929344504945694874887)
                    ·
                      rfl

theorem cell22_2894742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2894742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894742 prefixEnd_2894742 := by exact prefixLift 2894742
  have htrace : WordTrace (prefixWord ++ tailWord_2894742) baseStart_2894742 baseEnd_2894742 := by
    simpa [prefixWord, tailWord_2894742, baseEnd_2894742] using wordTrace_append hprefix tailTrace_2894742
  have hstable : (prefixWord ++ tailWord_2894742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894742).length < 2 ^ (prefixWord ++ tailWord_2894742).sum := by decide
  have hdescent : baseEnd_2894742 < baseStart_2894742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894781 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2894781 : Nat := 118140960795 + 2894781 * 2 ^ 59
def prefixEnd_2894781 : Nat := 4983230072969 + 3 ^ 40 * 2894781 * 2
def baseEnd_2894781 : Nat := 990942695001962593149767

theorem tailTrace_2894781 : CollatzResearch.WordTrace tailWord_2894781 prefixEnd_2894781 990942695001962593149767 := by
  unfold tailWord_2894781
  simp only [CollatzResearch.WordTrace]
  refine ⟨105581336925710301079572197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70387557950473534053048131 105581336925710301079572197)
  ·
    refine ⟨19796500673570681452419787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105581336925710301079572197 19796500673570681452419787)
    ·
      refine ⟨29694751010356022178629681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19796500673570681452419787 29694751010356022178629681)
      ·
        refine ⟨22271063257767016633972261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29694751010356022178629681 22271063257767016633972261)
        ·
          refine ⟨4175824360831315618869799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22271063257767016633972261 4175824360831315618869799)
          ·
            refine ⟨6263736541246973428304699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175824360831315618869799 6263736541246973428304699)
            ·
              refine ⟨9395604811870460142457049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263736541246973428304699 9395604811870460142457049)
              ·
                refine ⟨7046703608902845106842787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9395604811870460142457049 7046703608902845106842787)
                ·
                  refine ⟨10570055413354267660264181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7046703608902845106842787 10570055413354267660264181)
                  ·
                    refine ⟨990942695001962593149767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10570055413354267660264181 990942695001962593149767)
                    ·
                      rfl

theorem cell22_2894781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2894781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894781 prefixEnd_2894781 := by exact prefixLift 2894781
  have htrace : WordTrace (prefixWord ++ tailWord_2894781) baseStart_2894781 baseEnd_2894781 := by
    simpa [prefixWord, tailWord_2894781, baseEnd_2894781] using wordTrace_append hprefix tailTrace_2894781
  have hstable : (prefixWord ++ tailWord_2894781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894781).length < 2 ^ (prefixWord ++ tailWord_2894781).sum := by decide
  have hdescent : baseEnd_2894781 < baseStart_2894781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894798 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_2894798 : Nat := 118140960795 + 2894798 * 2 ^ 59
def prefixEnd_2894798 : Nat := 4983230072969 + 3 ^ 40 * 2894798 * 2
def baseEnd_2894798 : Nat := 990948514449380215474715

theorem tailTrace_2894798 : CollatzResearch.WordTrace tailWord_2894798 prefixEnd_2894798 990948514449380215474715 := by
  unfold tailWord_2894798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197744620831089122867631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70387971311099141988627365 13197744620831089122867631)
  ·
    refine ⟨19796616931246633684301447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13197744620831089122867631 19796616931246633684301447)
    ·
      refine ⟨29694925396869950526452171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19796616931246633684301447 29694925396869950526452171)
      ·
        refine ⟨44542388095304925789678257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29694925396869950526452171 44542388095304925789678257)
        ·
          refine ⟨33406791071478694342258693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44542388095304925789678257 33406791071478694342258693)
          ·
            refine ⟨6263773325902255189173505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33406791071478694342258693 6263773325902255189173505)
            ·
              refine ⟨4697829994426691391880129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263773325902255189173505 4697829994426691391880129)
              ·
                refine ⟨3523372495820018543910097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697829994426691391880129 3523372495820018543910097)
                ·
                  refine ⟨2642529371865013907932573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3523372495820018543910097 2642529371865013907932573)
                  ·
                    refine ⟨990948514449380215474715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642529371865013907932573 990948514449380215474715)
                    ·
                      rfl

theorem cell22_2894798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_2894798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894798 prefixEnd_2894798 := by exact prefixLift 2894798
  have htrace : WordTrace (prefixWord ++ tailWord_2894798) baseStart_2894798 baseEnd_2894798 := by
    simpa [prefixWord, tailWord_2894798, baseEnd_2894798] using wordTrace_append hprefix tailTrace_2894798
  have hstable : (prefixWord ++ tailWord_2894798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894798).length < 2 ^ (prefixWord ++ tailWord_2894798).sum := by decide
  have hdescent : baseEnd_2894798 < baseStart_2894798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894826 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2894826 : Nat := 118140960795 + 2894826 * 2 ^ 59
def prefixEnd_2894826 : Nat := 4983230072969 + 3 ^ 40 * 2894826 * 2
def baseEnd_2894826 : Nat := 990958099421597475774629

theorem tailTrace_2894826 : CollatzResearch.WordTrace tailWord_2894826 prefixEnd_2894826 990958099421597475774629 := by
  unfold tailWord_2894826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26395744552636818441240083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70388652140364849176640221 26395744552636818441240083)
  ·
    refine ⟨39593616828955227661860125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26395744552636818441240083 39593616828955227661860125)
    ·
      refine ⟨14847606310858210373197547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39593616828955227661860125 14847606310858210373197547)
      ·
        refine ⟨22271409466287315559796321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14847606310858210373197547 22271409466287315559796321)
        ·
          refine ⟨16703557099715486669847241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22271409466287315559796321 16703557099715486669847241)
          ·
            refine ⟨12527667824786615002385431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16703557099715486669847241 12527667824786615002385431)
            ·
              refine ⟨18791501737179922503578147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527667824786615002385431 18791501737179922503578147)
              ·
                refine ⟨28187252605769883755367221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18791501737179922503578147 28187252605769883755367221)
                ·
                  refine ⟨2642554931790926602065677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28187252605769883755367221 2642554931790926602065677)
                  ·
                    refine ⟨990958099421597475774629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642554931790926602065677 990958099421597475774629)
                    ·
                      rfl

theorem cell22_2894826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2894826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894826 prefixEnd_2894826 := by exact prefixLift 2894826
  have htrace : WordTrace (prefixWord ++ tailWord_2894826) baseStart_2894826 baseEnd_2894826 := by
    simpa [prefixWord, tailWord_2894826, baseEnd_2894826] using wordTrace_append hprefix tailTrace_2894826
  have hstable : (prefixWord ++ tailWord_2894826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894826).length < 2 ^ (prefixWord ++ tailWord_2894826).sum := by decide
  have hdescent : baseEnd_2894826 < baseStart_2894826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894830 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2894830 : Nat := 118140960795 + 2894830 * 2 ^ 59
def prefixEnd_2894830 : Nat := 4983230072969 + 3 ^ 40 * 2894830 * 2
def baseEnd_2894830 : Nat := 990959468703342798674617

theorem tailTrace_2894830 : CollatzResearch.WordTrace tailWord_2894830 prefixEnd_2894830 990959468703342798674617 := by
  unfold tailWord_2894830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197890512816597806013243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70388749401688521632070629 13197890512816597806013243)
  ·
    refine ⟨19796835769224896709019865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13197890512816597806013243 19796835769224896709019865)
    ·
      refine ⟨14847626826918672531764899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19796835769224896709019865 14847626826918672531764899)
      ·
        refine ⟨22271440240378008797647349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14847626826918672531764899 22271440240378008797647349)
        ·
          refine ⟨2087947522535438324779439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22271440240378008797647349 2087947522535438324779439)
          ·
            refine ⟨3131921283803157487169159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087947522535438324779439 3131921283803157487169159)
            ·
              refine ⟨4697881925704736230753739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131921283803157487169159 4697881925704736230753739)
              ·
                refine ⟨7046822888557104346130609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697881925704736230753739 7046822888557104346130609)
                ·
                  refine ⟨5285117166417828259597957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7046822888557104346130609 5285117166417828259597957)
                  ·
                    refine ⟨990959468703342798674617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285117166417828259597957 990959468703342798674617)
                    ·
                      rfl

theorem cell22_2894830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2894830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894830 prefixEnd_2894830 := by exact prefixLift 2894830
  have htrace : WordTrace (prefixWord ++ tailWord_2894830) baseStart_2894830 baseEnd_2894830 := by
    simpa [prefixWord, tailWord_2894830, baseEnd_2894830] using wordTrace_append hprefix tailTrace_2894830
  have hstable : (prefixWord ++ tailWord_2894830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894830).length < 2 ^ (prefixWord ++ tailWord_2894830).sum := by decide
  have hdescent : baseEnd_2894830 < baseStart_2894830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894836 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2894836 : Nat := 118140960795 + 2894836 * 2 ^ 59
def prefixEnd_2894836 : Nat := 4983230072969 + 3 ^ 40 * 2894836 * 2
def baseEnd_2894836 : Nat := 990961522625960783024599

theorem tailTrace_2894836 : CollatzResearch.WordTrace tailWord_2894836 prefixEnd_2894836 990961522625960783024599 := by
  unfold tailWord_2894836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52791671470255522736412181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70388895293674030315216241 52791671470255522736412181)
  ·
    refine ⟨2474609600168227628269321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52791671470255522736412181 2474609600168227628269321)
    ·
      refine ⟨1855957200126170721201991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2474609600168227628269321 1855957200126170721201991)
      ·
        refine ⟨2783935800189256081802987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855957200126170721201991 2783935800189256081802987)
        ·
          refine ⟨4175903700283884122704481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783935800189256081802987 4175903700283884122704481)
          ·
            refine ⟨3131927775212913092028361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175903700283884122704481 3131927775212913092028361)
            ·
              refine ⟨2348945831409684819021271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131927775212913092028361 2348945831409684819021271)
              ·
                refine ⟨3523418747114527228531907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348945831409684819021271 3523418747114527228531907)
                ·
                  refine ⟨5285128120671790842797861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523418747114527228531907 5285128120671790842797861)
                  ·
                    refine ⟨990961522625960783024599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285128120671790842797861 990961522625960783024599)
                    ·
                      rfl

theorem cell22_2894836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2894836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894836 prefixEnd_2894836 := by exact prefixLift 2894836
  have htrace : WordTrace (prefixWord ++ tailWord_2894836) baseStart_2894836 baseEnd_2894836 := by
    simpa [prefixWord, tailWord_2894836, baseEnd_2894836] using wordTrace_append hprefix tailTrace_2894836
  have hstable : (prefixWord ++ tailWord_2894836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894836).length < 2 ^ (prefixWord ++ tailWord_2894836).sum := by decide
  have hdescent : baseEnd_2894836 < baseStart_2894836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894856 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_2894856 : Nat := 118140960795 + 2894856 * 2 ^ 59
def prefixEnd_2894856 : Nat := 4983230072969 + 3 ^ 40 * 2894856 * 2
def baseEnd_2894856 : Nat := 330322789678229132508179

theorem tailTrace_2894856 : CollatzResearch.WordTrace tailWord_2894856 prefixEnd_2894856 330322789678229132508179 := by
  unfold tailWord_2894856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52792036200219294444276211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70389381600292392592368281 52792036200219294444276211)
  ·
    refine ⟨79188054300328941666414317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52792036200219294444276211 79188054300328941666414317)
    ·
      refine ⟨29695520362623353124905369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79188054300328941666414317 29695520362623353124905369)
      ·
        refine ⟨22271640271967514843679027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29695520362623353124905369 22271640271967514843679027)
        ·
          refine ⟨33407460407951272265518541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22271640271967514843679027 33407460407951272265518541)
          ·
            refine ⟨12527797652981727099569453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33407460407951272265518541 12527797652981727099569453)
            ·
              refine ⟨4697924119868147662338545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12527797652981727099569453 4697924119868147662338545)
              ·
                refine ⟨3523443089901110746753909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697924119868147662338545 3523443089901110746753909)
                ·
                  refine ⟨330322789678229132508179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523443089901110746753909 330322789678229132508179)
                  ·
                    rfl

theorem cell22_2894856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_2894856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894856 prefixEnd_2894856 := by exact prefixLift 2894856
  have htrace : WordTrace (prefixWord ++ tailWord_2894856) baseStart_2894856 baseEnd_2894856 := by
    simpa [prefixWord, tailWord_2894856, baseEnd_2894856] using wordTrace_append hprefix tailTrace_2894856
  have hstable : (prefixWord ++ tailWord_2894856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894856).length < 2 ^ (prefixWord ++ tailWord_2894856).sum := by decide
  have hdescent : baseEnd_2894856 < baseStart_2894856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894871 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_2894871 : Nat := 118140960795 + 2894871 * 2 ^ 59
def prefixEnd_2894871 : Nat := 4983230072969 + 3 ^ 40 * 2894871 * 2
def baseEnd_2894871 : Nat := 990973503841232358399491

theorem tailTrace_2894871 : CollatzResearch.WordTrace tailWord_2894871 prefixEnd_2894871 990973503841232358399491 := by
  unfold tailWord_2894871
  simp only [CollatzResearch.WordTrace]
  refine ⟨105584619495384246450348467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70389746330256164300232311 105584619495384246450348467)
  ·
    refine ⟨158376929243076369675522701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105584619495384246450348467 158376929243076369675522701)
    ·
      refine ⟨59391348466153638628321013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158376929243076369675522701 59391348466153638628321013)
      ·
        refine ⟨5567938918701903621405095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59391348466153638628321013 5567938918701903621405095)
        ·
          refine ⟨8351908378052855432107643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567938918701903621405095 8351908378052855432107643)
          ·
            refine ⟨12527862567079283148161465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351908378052855432107643 12527862567079283148161465)
            ·
              refine ⟨9395896925309462361121099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12527862567079283148161465 9395896925309462361121099)
              ·
                refine ⟨14093845387964193541681649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395896925309462361121099 14093845387964193541681649)
                ·
                  refine ⟨10570384040973145156261237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14093845387964193541681649 10570384040973145156261237)
                  ·
                    refine ⟨990973503841232358399491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10570384040973145156261237 990973503841232358399491)
                    ·
                      rfl

theorem cell22_2894871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_2894871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894871 prefixEnd_2894871 := by exact prefixLift 2894871
  have htrace : WordTrace (prefixWord ++ tailWord_2894871) baseStart_2894871 baseEnd_2894871 := by
    simpa [prefixWord, tailWord_2894871, baseEnd_2894871] using wordTrace_append hprefix tailTrace_2894871
  have hstable : (prefixWord ++ tailWord_2894871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894871).length < 2 ^ (prefixWord ++ tailWord_2894871).sum := by decide
  have hdescent : baseEnd_2894871 < baseStart_2894871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894899 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_2894899 : Nat := 118140960795 + 2894899 * 2 ^ 59
def prefixEnd_2894899 : Nat := 4983230072969 + 3 ^ 40 * 2894899 * 2
def baseEnd_2894899 : Nat := 990983088813449618699405

theorem tailTrace_2894899 : CollatzResearch.WordTrace tailWord_2894899 prefixEnd_2894899 990983088813449618699405 := by
  unfold tailWord_2894899
  simp only [CollatzResearch.WordTrace]
  refine ⟨105585640739282807232367751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70390427159521871488245167 105585640739282807232367751)
  ·
    refine ⟨158378461108924210848551627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105585640739282807232367751 158378461108924210848551627)
    ·
      refine ⟨237567691663386316272827441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158378461108924210848551627 237567691663386316272827441)
      ·
        refine ⟨178175768747539737204620581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237567691663386316272827441 178175768747539737204620581)
        ·
          refine ⟨33407956640163700725866359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178175768747539737204620581 33407956640163700725866359)
          ·
            refine ⟨50111934960245551088799539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33407956640163700725866359 50111934960245551088799539)
            ·
              refine ⟨75167902440368326633199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50111934960245551088799539 75167902440368326633199309)
              ·
                refine ⟨28187963415138122487449741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75167902440368326633199309 28187963415138122487449741)
                ·
                  refine ⟨10570486280676795932793653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28187963415138122487449741 10570486280676795932793653)
                  ·
                    refine ⟨990983088813449618699405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10570486280676795932793653 990983088813449618699405)
                    ·
                      rfl

theorem cell22_2894899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_2894899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894899 prefixEnd_2894899 := by exact prefixLift 2894899
  have htrace : WordTrace (prefixWord ++ tailWord_2894899) baseStart_2894899 baseEnd_2894899 := by
    simpa [prefixWord, tailWord_2894899, baseEnd_2894899] using wordTrace_append hprefix tailTrace_2894899
  have hstable : (prefixWord ++ tailWord_2894899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894899).length < 2 ^ (prefixWord ++ tailWord_2894899).sum := by decide
  have hdescent : baseEnd_2894899 < baseStart_2894899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894929 : List Nat := [1, 2, 2, 1, 3, 1, 3, 9]
def baseStart_2894929 : Nat := 118140960795 + 2894929 * 2 ^ 59
def prefixEnd_2894929 : Nat := 4983230072969 + 3 ^ 40 * 2894929 * 2
def baseEnd_2894929 : Nat := 110110373158504393383257

theorem tailTrace_2894929 : CollatzResearch.WordTrace tailWord_2894929 prefixEnd_2894929 110110373158504393383257 := by
  unfold tailWord_2894929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105586734929174122355959841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70391156619449414903973227 105586734929174122355959841)
  ·
    refine ⟨79190051196880591766969881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105586734929174122355959841 79190051196880591766969881)
    ·
      refine ⟨59392538397660443825227411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79190051196880591766969881 59392538397660443825227411)
      ·
        refine ⟨89088807596490665737841117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59392538397660443825227411 89088807596490665737841117)
        ·
          refine ⟨33408302848683999651690419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89088807596490665737841117 33408302848683999651690419)
          ·
            refine ⟨50112454273025999477535629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33408302848683999651690419 50112454273025999477535629)
            ·
              refine ⟨18792170352384749804075861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50112454273025999477535629 18792170352384749804075861)
              ·
                refine ⟨110110373158504393383257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18792170352384749804075861 110110373158504393383257)
                ·
                  rfl

theorem cell22_2894929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 9].length) (baseStart_2894929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894929 prefixEnd_2894929 := by exact prefixLift 2894929
  have htrace : WordTrace (prefixWord ++ tailWord_2894929) baseStart_2894929 baseEnd_2894929 := by
    simpa [prefixWord, tailWord_2894929, baseEnd_2894929] using wordTrace_append hprefix tailTrace_2894929
  have hstable : (prefixWord ++ tailWord_2894929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894929).length < 2 ^ (prefixWord ++ tailWord_2894929).sum := by decide
  have hdescent : baseEnd_2894929 < baseStart_2894929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894933 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2894933 : Nat := 118140960795 + 2894933 * 2 ^ 59
def prefixEnd_2894933 : Nat := 4983230072969 + 3 ^ 40 * 2894933 * 2
def baseEnd_2894933 : Nat := 990994727708284863349301

theorem tailTrace_2894933 : CollatzResearch.WordTrace tailWord_2894933 prefixEnd_2894933 990994727708284863349301 := by
  unfold tailWord_2894933
  simp only [CollatzResearch.WordTrace]
  refine ⟨105586880821159631039105453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70391253880773087359403635 105586880821159631039105453)
  ·
    refine ⟨39595080307934861639664545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105586880821159631039105453 39595080307934861639664545)
    ·
      refine ⟨29696310230951146229748409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39595080307934861639664545 29696310230951146229748409)
      ·
        refine ⟨22272232673213359672311307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29696310230951146229748409 22272232673213359672311307)
        ·
          refine ⟨33408349009820039508466961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22272232673213359672311307 33408349009820039508466961)
          ·
            refine ⟨25056261757365029631350221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33408349009820039508466961 25056261757365029631350221)
            ·
              refine ⟨9396098159011886111756333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25056261757365029631350221 9396098159011886111756333)
              ·
                refine ⟨3523536809629457291908625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9396098159011886111756333 3523536809629457291908625)
                ·
                  refine ⟨2642652607222092968931469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3523536809629457291908625 2642652607222092968931469)
                  ·
                    refine ⟨990994727708284863349301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642652607222092968931469 990994727708284863349301)
                    ·
                      rfl

theorem cell22_2894933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2894933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894933 prefixEnd_2894933 := by exact prefixLift 2894933
  have htrace : WordTrace (prefixWord ++ tailWord_2894933) baseStart_2894933 baseEnd_2894933 := by
    simpa [prefixWord, tailWord_2894933, baseEnd_2894933] using wordTrace_append hprefix tailTrace_2894933
  have hstable : (prefixWord ++ tailWord_2894933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894933).length < 2 ^ (prefixWord ++ tailWord_2894933).sum := by decide
  have hdescent : baseEnd_2894933 < baseStart_2894933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894961 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_2894961 : Nat := 118140960795 + 2894961 * 2 ^ 59
def prefixEnd_2894961 : Nat := 4983230072969 + 3 ^ 40 * 2894961 * 2
def baseEnd_2894961 : Nat := 991004312680502123649215

theorem tailTrace_2894961 : CollatzResearch.WordTrace tailWord_2894961 prefixEnd_2894961 991004312680502123649215 := by
  unfold tailWord_2894961
  simp only [CollatzResearch.WordTrace]
  refine ⟨105587902065058191821124737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70391934710038794547416491 105587902065058191821124737)
  ·
    refine ⟨79190926548793643865843553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105587902065058191821124737 79190926548793643865843553)
    ·
      refine ⟨59393194911595232899382665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79190926548793643865843553 59393194911595232899382665)
      ·
        refine ⟨44544896183696424674536999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59393194911595232899382665 44544896183696424674536999)
        ·
          refine ⟨66817344275544637011805499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44544896183696424674536999 66817344275544637011805499)
          ·
            refine ⟨100226016413316955517708249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66817344275544637011805499 100226016413316955517708249)
            ·
              refine ⟨75169512309987716638281187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100226016413316955517708249 75169512309987716638281187)
              ·
                refine ⟨112754268464981574957421781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75169512309987716638281187 112754268464981574957421781)
                ·
                  refine ⟨2642678167148005663064573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112754268464981574957421781 2642678167148005663064573)
                  ·
                    refine ⟨991004312680502123649215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642678167148005663064573 991004312680502123649215)
                    ·
                      rfl

theorem cell22_2894961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_2894961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2894961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2894961 prefixEnd_2894961 := by exact prefixLift 2894961
  have htrace : WordTrace (prefixWord ++ tailWord_2894961) baseStart_2894961 baseEnd_2894961 := by
    simpa [prefixWord, tailWord_2894961, baseEnd_2894961] using wordTrace_append hprefix tailTrace_2894961
  have hstable : (prefixWord ++ tailWord_2894961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894961).length < 2 ^ (prefixWord ++ tailWord_2894961).sum := by decide
  have hdescent : baseEnd_2894961 < baseStart_2894961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895012 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2895012 : Nat := 118140960795 + 2895012 * 2 ^ 59
def prefixEnd_2895012 : Nat := 4983230072969 + 3 ^ 40 * 2895012 * 2
def baseEnd_2895012 : Nat := 991021771022754990624059

theorem tailTrace_2895012 : CollatzResearch.WordTrace tailWord_2895012 prefixEnd_2895012 991021771022754990624059 := by
  unfold tailWord_2895012
  simp only [CollatzResearch.WordTrace]
  refine ⟨52794881093936713765615645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70393174791915618354154193 52794881093936713765615645)
  ·
    refine ⟨19798080410226267662105867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52794881093936713765615645 19798080410226267662105867)
    ·
      refine ⟨29697120615339401493158801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19798080410226267662105867 29697120615339401493158801)
      ·
        refine ⟨22272840461504551119869101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29697120615339401493158801 22272840461504551119869101)
        ·
          refine ⟨8352315173064206669950913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22272840461504551119869101 8352315173064206669950913)
          ·
            refine ⟨6264236379798155002463185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8352315173064206669950913 6264236379798155002463185)
            ·
              refine ⟨4698177284848616251847389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6264236379798155002463185 4698177284848616251847389)
              ·
                refine ⟨1761816481818231094442771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4698177284848616251847389 1761816481818231094442771)
                ·
                  refine ⟨2642724722727346641664157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761816481818231094442771 2642724722727346641664157)
                  ·
                    refine ⟨991021771022754990624059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642724722727346641664157 991021771022754990624059)
                    ·
                      rfl

theorem cell22_2895012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2895012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895012 prefixEnd_2895012 := by exact prefixLift 2895012
  have htrace : WordTrace (prefixWord ++ tailWord_2895012) baseStart_2895012 baseEnd_2895012 := by
    simpa [prefixWord, tailWord_2895012, baseEnd_2895012] using wordTrace_append hprefix tailTrace_2895012
  have hstable : (prefixWord ++ tailWord_2895012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895012).length < 2 ^ (prefixWord ++ tailWord_2895012).sum := by decide
  have hdescent : baseEnd_2895012 < baseStart_2895012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895025 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 5]
def baseStart_2895025 : Nat := 118140960795 + 2895025 * 2 ^ 59
def prefixEnd_2895025 : Nat := 4983230072969 + 3 ^ 40 * 2895025 * 2
def baseEnd_2895025 : Nat := 330342073729475763349673

theorem tailTrace_2895025 : CollatzResearch.WordTrace tailWord_2895025 prefixEnd_2895025 330342073729475763349673 := by
  unfold tailWord_2895025
  simp only [CollatzResearch.WordTrace]
  refine ⟨105590236336826330751454529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70393490891217553834303019 105590236336826330751454529)
  ·
    refine ⟨79192677252619748063590897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105590236336826330751454529 79192677252619748063590897)
    ·
      refine ⟨59394507939464811047693173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79192677252619748063590897 59394507939464811047693173)
      ·
        refine ⟨5568235119324826035721235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59394507939464811047693173 5568235119324826035721235)
        ·
          refine ⟨8352352678987239053581853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568235119324826035721235 8352352678987239053581853)
          ·
            refine ⟨3132132254620214645093195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8352352678987239053581853 3132132254620214645093195)
            ·
              refine ⟨4698198381930321967639793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132132254620214645093195 4698198381930321967639793)
              ·
                refine ⟨3523648786447741475729845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698198381930321967639793 3523648786447741475729845)
                ·
                  refine ⟨330342073729475763349673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523648786447741475729845 330342073729475763349673)
                  ·
                    rfl

theorem cell22_2895025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_2895025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895025 prefixEnd_2895025 := by exact prefixLift 2895025
  have htrace : WordTrace (prefixWord ++ tailWord_2895025) baseStart_2895025 baseEnd_2895025 := by
    simpa [prefixWord, tailWord_2895025, baseEnd_2895025] using wordTrace_append hprefix tailTrace_2895025
  have hstable : (prefixWord ++ tailWord_2895025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895025).length < 2 ^ (prefixWord ++ tailWord_2895025).sum := by decide
  have hdescent : baseEnd_2895025 < baseStart_2895025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895051 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_2895051 : Nat := 118140960795 + 2895051 * 2 ^ 59
def prefixEnd_2895051 : Nat := 4983230072969 + 3 ^ 40 * 2895051 * 2
def baseEnd_2895051 : Nat := 991035121519771888898939

theorem tailTrace_2895051 : CollatzResearch.WordTrace tailWord_2895051 prefixEnd_2895051 991035121519771888898939 := by
  unfold tailWord_2895051
  simp only [CollatzResearch.WordTrace]
  refine ⟨105591184634732137191901007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70394123089821424794600671 105591184634732137191901007)
  ·
    refine ⟨158386776952098205787851511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105591184634732137191901007 158386776952098205787851511)
    ·
      refine ⟨237580165428147308681777267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158386776952098205787851511 237580165428147308681777267)
      ·
        refine ⟨356370248142220963022665901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237580165428147308681777267 356370248142220963022665901)
        ·
          refine ⟨133638843053332861133499713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356370248142220963022665901 133638843053332861133499713)
          ·
            refine ⟨100229132289999645850124785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133638843053332861133499713 100229132289999645850124785)
            ·
              refine ⟨75171849217499734387593589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100229132289999645850124785 75171849217499734387593589)
              ·
                refine ⟨7047360864140600098836899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75171849217499734387593589 7047360864140600098836899)
                ·
                  refine ⟨10571041296210900148255349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047360864140600098836899 10571041296210900148255349)
                  ·
                    refine ⟨991035121519771888898939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10571041296210900148255349 991035121519771888898939)
                    ·
                      rfl

theorem cell22_2895051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_2895051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895051 prefixEnd_2895051 := by exact prefixLift 2895051
  have htrace : WordTrace (prefixWord ++ tailWord_2895051) baseStart_2895051 baseEnd_2895051 := by
    simpa [prefixWord, tailWord_2895051, baseEnd_2895051] using wordTrace_append hprefix tailTrace_2895051
  have hstable : (prefixWord ++ tailWord_2895051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895051).length < 2 ^ (prefixWord ++ tailWord_2895051).sum := by decide
  have hdescent : baseEnd_2895051 < baseStart_2895051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895083 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_2895083 : Nat := 118140960795 + 2895083 * 2 ^ 59
def prefixEnd_2895083 : Nat := 4983230072969 + 3 ^ 40 * 2895083 * 2
def baseEnd_2895083 : Nat := 991046075773734472098841

theorem tailTrace_2895083 : CollatzResearch.WordTrace tailWord_2895083 prefixEnd_2895083 991046075773734472098841 := by
  unfold tailWord_2895083
  simp only [CollatzResearch.WordTrace]
  refine ⟨105592351770616206657065903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70394901180410804438043935 105592351770616206657065903)
  ·
    refine ⟨158388527655924309985598855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105592351770616206657065903 158388527655924309985598855)
    ·
      refine ⟨237582791483886464978398283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158388527655924309985598855 237582791483886464978398283)
      ·
        refine ⟨356374187225829697467597425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237582791483886464978398283 356374187225829697467597425)
        ·
          refine ⟨267280640419372273100698069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356374187225829697467597425 267280640419372273100698069)
          ·
            refine ⟨6264390009829037650797611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 267280640419372273100698069 6264390009829037650797611)
            ·
              refine ⟨9396585014743556476196417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264390009829037650797611 9396585014743556476196417)
              ·
                refine ⟨7047438761057667357147313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9396585014743556476196417 7047438761057667357147313)
                ·
                  refine ⟨5285579070793250517860485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047438761057667357147313 5285579070793250517860485)
                  ·
                    refine ⟨991046075773734472098841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285579070793250517860485 991046075773734472098841)
                    ·
                      rfl

theorem cell22_2895083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_2895083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895083 prefixEnd_2895083 := by exact prefixLift 2895083
  have htrace : WordTrace (prefixWord ++ tailWord_2895083) baseStart_2895083 baseEnd_2895083 := by
    simpa [prefixWord, tailWord_2895083, baseEnd_2895083] using wordTrace_append hprefix tailTrace_2895083
  have hstable : (prefixWord ++ tailWord_2895083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895083).length < 2 ^ (prefixWord ++ tailWord_2895083).sum := by decide
  have hdescent : baseEnd_2895083 < baseStart_2895083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895085 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2895085 : Nat := 118140960795 + 2895085 * 2 ^ 59
def prefixEnd_2895085 : Nat := 4983230072969 + 3 ^ 40 * 2895085 * 2
def baseEnd_2895085 : Nat := 991046760414607133548835

theorem tailTrace_2895085 : CollatzResearch.WordTrace tailWord_2895085 prefixEnd_2895085 991046760414607133548835 := by
  unfold tailWord_2895085
  simp only [CollatzResearch.WordTrace]
  refine ⟨105592424716608960998638709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70394949811072640665759139 105592424716608960998638709)
  ·
    refine ⟨9899289817182090093622379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105592424716608960998638709 9899289817182090093622379)
    ·
      refine ⟨14848934725773135140433569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9899289817182090093622379 14848934725773135140433569)
      ·
        refine ⟨11136701044329851355325177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14848934725773135140433569 11136701044329851355325177)
        ·
          refine ⟨8352525783247388516493883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11136701044329851355325177 8352525783247388516493883)
          ·
            refine ⟨12528788674871082774740825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8352525783247388516493883 12528788674871082774740825)
            ·
              refine ⟨9396591506153312081055619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12528788674871082774740825 9396591506153312081055619)
              ·
                refine ⟨14094887259229968121583429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396591506153312081055619 14094887259229968121583429)
                ·
                  refine ⟨2642791361105619022796893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14094887259229968121583429 2642791361105619022796893)
                  ·
                    refine ⟨991046760414607133548835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642791361105619022796893 991046760414607133548835)
                    ·
                      rfl

theorem cell22_2895085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2895085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895085 prefixEnd_2895085 := by exact prefixLift 2895085
  have htrace : WordTrace (prefixWord ++ tailWord_2895085) baseStart_2895085 baseEnd_2895085 := by
    simpa [prefixWord, tailWord_2895085, baseEnd_2895085] using wordTrace_append hprefix tailTrace_2895085
  have hstable : (prefixWord ++ tailWord_2895085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895085).length < 2 ^ (prefixWord ++ tailWord_2895085).sum := by decide
  have hdescent : baseEnd_2895085 < baseStart_2895085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895087 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 4]
def baseStart_2895087 : Nat := 118140960795 + 2895087 * 2 ^ 59
def prefixEnd_2895087 : Nat := 4983230072969 + 3 ^ 40 * 2895087 * 2
def baseEnd_2895087 : Nat := 330349148351826598332943

theorem tailTrace_2895087 : CollatzResearch.WordTrace tailWord_2895087 prefixEnd_2895087 330349148351826598332943 := by
  unfold tailWord_2895087
  simp only [CollatzResearch.WordTrace]
  refine ⟨105592497662601715340211515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70394998441734476893474343 105592497662601715340211515)
  ·
    refine ⟨158388746493902573010317273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105592497662601715340211515 158388746493902573010317273)
    ·
      refine ⟨118791559870426929757737955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158388746493902573010317273 118791559870426929757737955)
      ·
        refine ⟨178187339805640394636606933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118791559870426929757737955 178187339805640394636606933)
        ·
          refine ⟨4176265776694696749295475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 178187339805640394636606933 4176265776694696749295475)
          ·
            refine ⟨6264398665042045123943213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176265776694696749295475 6264398665042045123943213)
            ·
              refine ⟨2349149499390766921478705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6264398665042045123943213 2349149499390766921478705)
              ·
                refine ⟨1761862124543075191109029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2349149499390766921478705 1761862124543075191109029)
                ·
                  refine ⟨330349148351826598332943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761862124543075191109029 330349148351826598332943)
                  ·
                    rfl

theorem cell22_2895087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 4].length) (baseStart_2895087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895087 prefixEnd_2895087 := by exact prefixLift 2895087
  have htrace : WordTrace (prefixWord ++ tailWord_2895087) baseStart_2895087 baseEnd_2895087 := by
    simpa [prefixWord, tailWord_2895087, baseEnd_2895087] using wordTrace_append hprefix tailTrace_2895087
  have hstable : (prefixWord ++ tailWord_2895087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895087).length < 2 ^ (prefixWord ++ tailWord_2895087).sum := by decide
  have hdescent : baseEnd_2895087 < baseStart_2895087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895102 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2895102 : Nat := 118140960795 + 2895102 * 2 ^ 59
def prefixEnd_2895102 : Nat := 4983230072969 + 3 ^ 40 * 2895102 * 2
def baseEnd_2895102 : Nat := 991052579862024755873783

theorem tailTrace_2895102 : CollatzResearch.WordTrace tailWord_2895102 prefixEnd_2895102 991052579862024755873783 := by
  unfold tailWord_2895102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199130594693421612750945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70395363171698248601338373 13199130594693421612750945)
  ·
    refine ⟨9899347946020066209563209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13199130594693421612750945 9899347946020066209563209)
    ·
      refine ⟨7424510959515049657172407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9899347946020066209563209 7424510959515049657172407)
      ·
        refine ⟨11136766439272574485758611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7424510959515049657172407 11136766439272574485758611)
        ·
          refine ⟨16705149658908861728637917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11136766439272574485758611 16705149658908861728637917)
          ·
            refine ⟨6264431122090823148239219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16705149658908861728637917 6264431122090823148239219)
            ·
              refine ⟨9396646683136234722358829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264431122090823148239219 9396646683136234722358829)
              ·
                refine ⟨3523742506176088020884561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9396646683136234722358829 3523742506176088020884561)
                ·
                  refine ⟨2642806879632066015663421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3523742506176088020884561 2642806879632066015663421)
                  ·
                    refine ⟨991052579862024755873783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642806879632066015663421 991052579862024755873783)
                    ·
                      rfl

theorem cell22_2895102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2895102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895102 prefixEnd_2895102 := by exact prefixLift 2895102
  have htrace : WordTrace (prefixWord ++ tailWord_2895102) baseStart_2895102 baseEnd_2895102 := by
    simpa [prefixWord, tailWord_2895102, baseEnd_2895102] using wordTrace_append hprefix tailTrace_2895102
  have hstable : (prefixWord ++ tailWord_2895102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895102).length < 2 ^ (prefixWord ++ tailWord_2895102).sum := by decide
  have hdescent : baseEnd_2895102 < baseStart_2895102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895113 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_2895113 : Nat := 118140960795 + 2895113 * 2 ^ 59
def prefixEnd_2895113 : Nat := 4983230072969 + 3 ^ 40 * 2895113 * 2
def baseEnd_2895113 : Nat := 991056345386824393848749

theorem tailTrace_2895113 : CollatzResearch.WordTrace tailWord_2895113 prefixEnd_2895113 991056345386824393848749 := by
  unfold tailWord_2895113
  simp only [CollatzResearch.WordTrace]
  refine ⟨105593445960507521780657993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70395630640338347853771995 105593445960507521780657993)
  ·
    refine ⟨79195084470380641335493495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105593445960507521780657993 79195084470380641335493495)
    ·
      refine ⟨118792626705570962003240243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79195084470380641335493495 118792626705570962003240243)
      ·
        refine ⟨178188940058356443004860365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118792626705570962003240243 178188940058356443004860365)
        ·
          refine ⟨66820852521883666126822637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178188940058356443004860365 66820852521883666126822637)
          ·
            refine ⟨25057819695706374797558489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66820852521883666126822637 25057819695706374797558489)
            ·
              refine ⟨18793364771779781098168867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25057819695706374797558489 18793364771779781098168867)
              ·
                refine ⟨28190047157669671647253301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18793364771779781098168867 28190047157669671647253301)
                ·
                  refine ⟨2642816921031531716929997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28190047157669671647253301 2642816921031531716929997)
                  ·
                    refine ⟨991056345386824393848749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642816921031531716929997 991056345386824393848749)
                    ·
                      rfl

theorem cell22_2895113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_2895113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895113 prefixEnd_2895113 := by exact prefixLift 2895113
  have htrace : WordTrace (prefixWord ++ tailWord_2895113) baseStart_2895113 baseEnd_2895113 := by
    simpa [prefixWord, tailWord_2895113, baseEnd_2895113] using wordTrace_append hprefix tailTrace_2895113
  have hstable : (prefixWord ++ tailWord_2895113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895113).length < 2 ^ (prefixWord ++ tailWord_2895113).sum := by decide
  have hdescent : baseEnd_2895113 < baseStart_2895113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895188 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2895188 : Nat := 118140960795 + 2895188 * 2 ^ 59
def prefixEnd_2895188 : Nat := 4983230072969 + 3 ^ 40 * 2895188 * 2
def baseEnd_2895188 : Nat := 330360673139849732741173

theorem tailTrace_2895188 : CollatzResearch.WordTrace tailWord_2895188 prefixEnd_2895188 330360673139849732741173 := by
  unfold tailWord_2895188
  simp only [CollatzResearch.WordTrace]
  refine ⟨52798090717617904794819109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70397454290157206393092145 52798090717617904794819109)
  ·
    refine ⟨9899642009553357149028583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52798090717617904794819109 9899642009553357149028583)
    ·
      refine ⟨14849463014330035723542875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9899642009553357149028583 14849463014330035723542875)
      ·
        refine ⟨22274194521495053585314313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14849463014330035723542875 22274194521495053585314313)
        ·
          refine ⟨16705645891121290188985735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22274194521495053585314313 16705645891121290188985735)
          ·
            refine ⟨25058468836681935283478603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16705645891121290188985735 25058468836681935283478603)
            ·
              refine ⟨37587703255022902925217905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25058468836681935283478603 37587703255022902925217905)
              ·
                refine ⟨28190777441267177193913429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37587703255022902925217905 28190777441267177193913429)
                ·
                  refine ⟨330360673139849732741173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28190777441267177193913429 330360673139849732741173)
                  ·
                    rfl

theorem cell22_2895188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2895188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895188 prefixEnd_2895188 := by exact prefixLift 2895188
  have htrace : WordTrace (prefixWord ++ tailWord_2895188) baseStart_2895188 baseEnd_2895188 := by
    simpa [prefixWord, tailWord_2895188, baseEnd_2895188] using wordTrace_append hprefix tailTrace_2895188
  have hstable : (prefixWord ++ tailWord_2895188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895188).length < 2 ^ (prefixWord ++ tailWord_2895188).sum := by decide
  have hdescent : baseEnd_2895188 < baseStart_2895188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895205 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 4]
def baseStart_2895205 : Nat := 118140960795 + 2895205 * 2 ^ 59
def prefixEnd_2895205 : Nat := 4983230072969 + 3 ^ 40 * 2895205 * 2
def baseEnd_2895205 : Nat := 330362612955655606849489

theorem tailTrace_2895205 : CollatzResearch.WordTrace tailWord_2895205 prefixEnd_2895205 330362612955655606849489 := by
  unfold tailWord_2895205
  simp only [CollatzResearch.WordTrace]
  refine ⟨105596801476174221493007069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70397867650782814328671379 105596801476174221493007069)
  ·
    refine ⟨39598800553565333059877651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105596801476174221493007069 39598800553565333059877651)
    ·
      refine ⟨59398200830347999589816477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39598800553565333059877651 59398200830347999589816477)
      ·
        refine ⟨22274325311380499846181179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59398200830347999589816477 22274325311380499846181179)
        ·
          refine ⟨33411487967070749769271769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22274325311380499846181179 33411487967070749769271769)
          ·
            refine ⟨25058615975303062326953827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33411487967070749769271769 25058615975303062326953827)
            ·
              refine ⟨37587923962954593490430741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25058615975303062326953827 37587923962954593490430741)
              ·
                refine ⟨1761933935763496569863941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37587923962954593490430741 1761933935763496569863941)
                ·
                  refine ⟨330362612955655606849489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761933935763496569863941 330362612955655606849489)
                  ·
                    rfl

theorem cell22_2895205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_2895205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895205 prefixEnd_2895205 := by exact prefixLift 2895205
  have htrace : WordTrace (prefixWord ++ tailWord_2895205) baseStart_2895205 baseEnd_2895205 := by
    simpa [prefixWord, tailWord_2895205, baseEnd_2895205] using wordTrace_append hprefix tailTrace_2895205
  have hstable : (prefixWord ++ tailWord_2895205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895205).length < 2 ^ (prefixWord ++ tailWord_2895205).sum := by decide
  have hdescent : baseEnd_2895205 < baseStart_2895205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895218 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2895218 : Nat := 118140960795 + 2895218 * 2 ^ 59
def prefixEnd_2895218 : Nat := 4983230072969 + 3 ^ 40 * 2895218 * 2
def baseEnd_2895218 : Nat := 991092289032639119973427

theorem tailTrace_2895218 : CollatzResearch.WordTrace tailWord_2895218 prefixEnd_2895218 991092289032639119973427 := by
  unfold tailWord_2895218
  simp only [CollatzResearch.WordTrace]
  refine ⟨26399318906281781178307577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70398183750084749808820205 26399318906281781178307577)
  ·
    refine ⟨19799489179711335883730683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26399318906281781178307577 19799489179711335883730683)
    ·
      refine ⟨29699233769567003825596025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19799489179711335883730683 29699233769567003825596025)
      ·
        refine ⟨22274425327175252869197019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29699233769567003825596025 22274425327175252869197019)
        ·
          refine ⟨33411637990762879303795529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22274425327175252869197019 33411637990762879303795529)
          ·
            refine ⟨25058728493072159477846647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33411637990762879303795529 25058728493072159477846647)
            ·
              refine ⟨37588092739608239216769971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25058728493072159477846647 37588092739608239216769971)
              ·
                refine ⟨56382139109412358825154957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37588092739608239216769971 56382139109412358825154957)
                ·
                  refine ⟨21143302166029634559433109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56382139109412358825154957 21143302166029634559433109)
                  ·
                    refine ⟨991092289032639119973427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21143302166029634559433109 991092289032639119973427)
                    ·
                      rfl

theorem cell22_2895218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2895218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895218 prefixEnd_2895218 := by exact prefixLift 2895218
  have htrace : WordTrace (prefixWord ++ tailWord_2895218) baseStart_2895218 baseEnd_2895218 := by
    simpa [prefixWord, tailWord_2895218, baseEnd_2895218] using wordTrace_append hprefix tailTrace_2895218
  have hstable : (prefixWord ++ tailWord_2895218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895218).length < 2 ^ (prefixWord ++ tailWord_2895218).sum := by decide
  have hdescent : baseEnd_2895218 < baseStart_2895218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895252 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2895252 : Nat := 118140960795 + 2895252 * 2 ^ 59
def prefixEnd_2895252 : Nat := 4983230072969 + 3 ^ 40 * 2895252 * 2
def baseEnd_2895252 : Nat := 991103927927474364623323

theorem tailTrace_2895252 : CollatzResearch.WordTrace tailWord_2895252 prefixEnd_2895252 991103927927474364623323 := by
  unfold tailWord_2895252
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799257853501974259984005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70399010471335965679978673 52799257853501974259984005)
  ·
    refine ⟨9899860847531620173747001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52799257853501974259984005 9899860847531620173747001)
    ·
      refine ⟨7424895635648715130310251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9899860847531620173747001 7424895635648715130310251)
      ·
        refine ⟨11137343453473072695465377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7424895635648715130310251 11137343453473072695465377)
        ·
          refine ⟨8353007590104804521599033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11137343453473072695465377 8353007590104804521599033)
          ·
            refine ⟨6264755692578603391199275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8353007590104804521599033 6264755692578603391199275)
            ·
              refine ⟨9397133538867905086798913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264755692578603391199275 9397133538867905086798913)
              ·
                refine ⟨7047850154150928815099185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9397133538867905086798913 7047850154150928815099185)
                ·
                  refine ⟨5285887615613196611324389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047850154150928815099185 5285887615613196611324389)
                  ·
                    refine ⟨991103927927474364623323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285887615613196611324389 991103927927474364623323)
                    ·
                      rfl

theorem cell22_2895252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2895252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895252 prefixEnd_2895252 := by exact prefixLift 2895252
  have htrace : WordTrace (prefixWord ++ tailWord_2895252) baseStart_2895252 baseEnd_2895252 := by
    simpa [prefixWord, tailWord_2895252, baseEnd_2895252] using wordTrace_append hprefix tailTrace_2895252
  have hstable : (prefixWord ++ tailWord_2895252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895252).length < 2 ^ (prefixWord ++ tailWord_2895252).sum := by decide
  have hdescent : baseEnd_2895252 < baseStart_2895252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895316 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_2895316 : Nat := 118140960795 + 2895316 * 2 ^ 59
def prefixEnd_2895316 : Nat := 4983230072969 + 3 ^ 40 * 2895316 * 2
def baseEnd_2895316 : Nat := 991125836435399531023127

theorem tailTrace_2895316 : CollatzResearch.WordTrace tailWord_2895316 prefixEnd_2895316 991125836435399531023127 := by
  unfold tailWord_2895316
  simp only [CollatzResearch.WordTrace]
  refine ⟨52800424989386043725148901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70400566652514724966865201 52800424989386043725148901)
  ·
    refine ⟨9900079685509883198465419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52800424989386043725148901 9900079685509883198465419)
    ·
      refine ⟨14850119528264824797698129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900079685509883198465419 14850119528264824797698129)
      ·
        refine ⟨11137589646198618598273597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14850119528264824797698129 11137589646198618598273597)
        ·
          refine ⟨4176596117324481974352599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11137589646198618598273597 4176596117324481974352599)
          ·
            refine ⟨6264894175986722961528899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176596117324481974352599 6264894175986722961528899)
            ·
              refine ⟨9397341263980084442293349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264894175986722961528899 9397341263980084442293349)
              ·
                refine ⟨1762001486996265832930003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9397341263980084442293349 1762001486996265832930003)
                ·
                  refine ⟨2643002230494398749395005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762001486996265832930003 2643002230494398749395005)
                  ·
                    refine ⟨991125836435399531023127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643002230494398749395005 991125836435399531023127)
                    ·
                      rfl

theorem cell22_2895316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_2895316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895316 prefixEnd_2895316 := by exact prefixLift 2895316
  have htrace : WordTrace (prefixWord ++ tailWord_2895316) baseStart_2895316 baseEnd_2895316 := by
    simpa [prefixWord, tailWord_2895316, baseEnd_2895316] using wordTrace_append hprefix tailTrace_2895316
  have hstable : (prefixWord ++ tailWord_2895316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895316).length < 2 ^ (prefixWord ++ tailWord_2895316).sum := by decide
  have hdescent : baseEnd_2895316 < baseStart_2895316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895342 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2895342 : Nat := 118140960795 + 2895342 * 2 ^ 59
def prefixEnd_2895342 : Nat := 4983230072969 + 3 ^ 40 * 2895342 * 2
def baseEnd_2895342 : Nat := 991134736766744129873047

theorem tailTrace_2895342 : CollatzResearch.WordTrace tailWord_2895342 prefixEnd_2895342 991134736766744129873047 := by
  unfold tailWord_2895342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200224784584736736343035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70401198851118595927162853 13200224784584736736343035)
  ·
    refine ⟨19800337176877105104514553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13200224784584736736343035 19800337176877105104514553)
    ·
      refine ⟨14850252882657828828385915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19800337176877105104514553 14850252882657828828385915)
      ·
        refine ⟨22275379323986743242578873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14850252882657828828385915 22275379323986743242578873)
        ·
          refine ⟨16706534492990057431934155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22275379323986743242578873 16706534492990057431934155)
          ·
            refine ⟨25059801739485086147901233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16706534492990057431934155 25059801739485086147901233)
            ·
              refine ⟨18794851304613814610925925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25059801739485086147901233 18794851304613814610925925)
              ·
                refine ⟨3524034619615090239548611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18794851304613814610925925 3524034619615090239548611)
                ·
                  refine ⟨5286051929422635359322917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524034619615090239548611 5286051929422635359322917)
                  ·
                    refine ⟨991134736766744129873047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286051929422635359322917 991134736766744129873047)
                    ·
                      rfl

theorem cell22_2895342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2895342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895342 prefixEnd_2895342 := by exact prefixLift 2895342
  have htrace : WordTrace (prefixWord ++ tailWord_2895342) baseStart_2895342 baseEnd_2895342 := by
    simpa [prefixWord, tailWord_2895342, baseEnd_2895342] using wordTrace_append hprefix tailTrace_2895342
  have hstable : (prefixWord ++ tailWord_2895342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895342).length < 2 ^ (prefixWord ++ tailWord_2895342).sum := by decide
  have hdescent : baseEnd_2895342 < baseStart_2895342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895355 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 6, 3]
def baseStart_2895355 : Nat := 118140960795 + 2895355 * 2 ^ 59
def prefixEnd_2895355 : Nat := 4983230072969 + 3 ^ 40 * 2895355 * 2
def baseEnd_2895355 : Nat := 991139186932416429298007

theorem tailTrace_2895355 : CollatzResearch.WordTrace tailWord_2895355 prefixEnd_2895355 991139186932416429298007 := by
  unfold tailWord_2895355
  simp only [CollatzResearch.WordTrace]
  refine ⟨105602272425630797110967519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70401514950420531407311679 105602272425630797110967519)
  ·
    refine ⟨158403408638446195666451279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105602272425630797110967519 158403408638446195666451279)
    ·
      refine ⟨237605112957669293499676919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158403408638446195666451279 237605112957669293499676919)
      ·
        refine ⟨356407669436503940249515379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237605112957669293499676919 356407669436503940249515379)
        ·
          refine ⟨534611504154755910374273069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356407669436503940249515379 534611504154755910374273069)
          ·
            refine ⟨200479314058033466390352401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534611504154755910374273069 200479314058033466390352401)
            ·
              refine ⟨150359485543525099792764301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200479314058033466390352401 150359485543525099792764301)
              ·
                refine ⟨56384807078821912422286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150359485543525099792764301 56384807078821912422286613)
                ·
                  refine ⟨2643037831819777144794685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56384807078821912422286613 2643037831819777144794685)
                  ·
                    refine ⟨991139186932416429298007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643037831819777144794685 991139186932416429298007)
                    ·
                      rfl

theorem cell22_2895355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3].length) (baseStart_2895355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895355 prefixEnd_2895355 := by exact prefixLift 2895355
  have htrace : WordTrace (prefixWord ++ tailWord_2895355) baseStart_2895355 baseEnd_2895355 := by
    simpa [prefixWord, tailWord_2895355, baseEnd_2895355] using wordTrace_append hprefix tailTrace_2895355
  have hstable : (prefixWord ++ tailWord_2895355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895355).length < 2 ^ (prefixWord ++ tailWord_2895355).sum := by decide
  have hdescent : baseEnd_2895355 < baseStart_2895355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895357 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 4]
def baseStart_2895357 : Nat := 118140960795 + 2895357 * 2 ^ 59
def prefixEnd_2895357 : Nat := 4983230072969 + 3 ^ 40 * 2895357 * 2
def baseEnd_2895357 : Nat := 330379957191096363582667

theorem tailTrace_2895357 : CollatzResearch.WordTrace tailWord_2895357 prefixEnd_2895357 330379957191096363582667 := by
  unfold tailWord_2895357
  simp only [CollatzResearch.WordTrace]
  refine ⟨105602345371623551452540325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70401563581082367635026883 105602345371623551452540325)
  ·
    refine ⟨19800439757179415897351311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105602345371623551452540325 19800439757179415897351311)
    ·
      refine ⟨29700659635769123846026967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19800439757179415897351311 29700659635769123846026967)
      ·
        refine ⟨44550989453653685769040451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29700659635769123846026967 44550989453653685769040451)
        ·
          refine ⟨66826484180480528653560677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44550989453653685769040451 66826484180480528653560677)
          ·
            refine ⟨12529965783840099122542627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66826484180480528653560677 12529965783840099122542627)
            ·
              refine ⟨18794948675760148683813941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529965783840099122542627 18794948675760148683813941)
              ·
                refine ⟨1762026438352513939107557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18794948675760148683813941 1762026438352513939107557)
                ·
                  refine ⟨330379957191096363582667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1762026438352513939107557 330379957191096363582667)
                  ·
                    rfl

theorem cell22_2895357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_2895357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895357 prefixEnd_2895357 := by exact prefixLift 2895357
  have htrace : WordTrace (prefixWord ++ tailWord_2895357) baseStart_2895357 baseEnd_2895357 := by
    simpa [prefixWord, tailWord_2895357, baseEnd_2895357] using wordTrace_append hprefix tailTrace_2895357
  have hstable : (prefixWord ++ tailWord_2895357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895357).length < 2 ^ (prefixWord ++ tailWord_2895357).sum := by decide
  have hdescent : baseEnd_2895357 < baseStart_2895357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895445 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2895445 : Nat := 118140960795 + 2895445 * 2 ^ 59
def prefixEnd_2895445 : Nat := 4983230072969 + 3 ^ 40 * 2895445 * 2
def baseEnd_2895445 : Nat := 991169995771686194547731

theorem tailTrace_2895445 : CollatzResearch.WordTrace tailWord_2895445 prefixEnd_2895445 991169995771686194547731 := by
  unfold tailWord_2895445
  simp only [CollatzResearch.WordTrace]
  refine ⟨105605554995304742481743789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70403703330203161654495859 105605554995304742481743789)
  ·
    refine ⟨39602083123239278430653921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105605554995304742481743789 39602083123239278430653921)
    ·
      refine ⟨29701562342429458822990441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39602083123239278430653921 29701562342429458822990441)
      ·
        refine ⟨22276171756822094117242831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29701562342429458822990441 22276171756822094117242831)
        ·
          refine ⟨33414257635233141175864247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22276171756822094117242831 33414257635233141175864247)
          ·
            refine ⟨50121386452849711763796371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33414257635233141175864247 50121386452849711763796371)
            ·
              refine ⟨75182079679274567645694557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50121386452849711763796371 75182079679274567645694557)
              ·
                refine ⟨28193279879727962867135459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75182079679274567645694557 28193279879727962867135459)
                ·
                  refine ⟨42289919819591944300703189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28193279879727962867135459 42289919819591944300703189)
                  ·
                    refine ⟨991169995771686194547731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42289919819591944300703189 991169995771686194547731)
                    ·
                      rfl

theorem cell22_2895445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2895445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895445 prefixEnd_2895445 := by exact prefixLift 2895445
  have htrace : WordTrace (prefixWord ++ tailWord_2895445) baseStart_2895445 baseEnd_2895445 := by
    simpa [prefixWord, tailWord_2895445, baseEnd_2895445] using wordTrace_append hprefix tailTrace_2895445
  have hstable : (prefixWord ++ tailWord_2895445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895445).length < 2 ^ (prefixWord ++ tailWord_2895445).sum := by decide
  have hdescent : baseEnd_2895445 < baseStart_2895445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895447 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 5]
def baseStart_2895447 : Nat := 118140960795 + 2895447 * 2 ^ 59
def prefixEnd_2895447 : Nat := 4983230072969 + 3 ^ 40 * 2895447 * 2
def baseEnd_2895447 : Nat := 330390226804186285332575

theorem tailTrace_2895447 : CollatzResearch.WordTrace tailWord_2895447 prefixEnd_2895447 330390226804186285332575 := by
  unfold tailWord_2895447
  simp only [CollatzResearch.WordTrace]
  refine ⟨105605627941297496823316595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70403751960864997882211063 105605627941297496823316595)
  ·
    refine ⟨158408441911946245234974893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105605627941297496823316595 158408441911946245234974893)
    ·
      refine ⟨59403165716979841963115585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158408441911946245234974893 59403165716979841963115585)
      ·
        refine ⟨44552374287734881472336689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59403165716979841963115585 44552374287734881472336689)
        ·
          refine ⟨33414280715801161104252517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44552374287734881472336689 33414280715801161104252517)
          ·
            refine ⟨6265177634212717707047347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33414280715801161104252517 6265177634212717707047347)
            ·
              refine ⟨9397766451319076560571021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265177634212717707047347 9397766451319076560571021)
              ·
                refine ⟨3524162419244653710214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9397766451319076560571021 3524162419244653710214133)
                ·
                  refine ⟨330390226804186285332575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524162419244653710214133 330390226804186285332575)
                  ·
                    rfl

theorem cell22_2895447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 5].length) (baseStart_2895447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895447 prefixEnd_2895447 := by exact prefixLift 2895447
  have htrace : WordTrace (prefixWord ++ tailWord_2895447) baseStart_2895447 baseEnd_2895447 := by
    simpa [prefixWord, tailWord_2895447, baseEnd_2895447] using wordTrace_append hprefix tailTrace_2895447
  have hstable : (prefixWord ++ tailWord_2895447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895447).length < 2 ^ (prefixWord ++ tailWord_2895447).sum := by decide
  have hdescent : baseEnd_2895447 < baseStart_2895447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895541 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2895541 : Nat := 118140960795 + 2895541 * 2 ^ 59
def prefixEnd_2895541 : Nat := 4983230072969 + 3 ^ 40 * 2895541 * 2
def baseEnd_2895541 : Nat := 991202858533573944147437

theorem tailTrace_2895541 : CollatzResearch.WordTrace tailWord_2895541 prefixEnd_2895541 991202858533573944147437 := by
  unfold tailWord_2895541
  simp only [CollatzResearch.WordTrace]
  refine ⟨105609056402956950877238477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70406037601971300584825651 105609056402956950877238477)
  ·
    refine ⟨39603396151108856578964429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105609056402956950877238477 39603396151108856578964429)
    ·
      refine ⟨14851273556665821217111661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39603396151108856578964429 14851273556665821217111661)
      ·
        refine ⟨5569227583749682956416873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14851273556665821217111661 5569227583749682956416873)
        ·
          refine ⟨4176920687812262217312655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5569227583749682956416873 4176920687812262217312655)
          ·
            refine ⟨6265381031718393325968983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176920687812262217312655 6265381031718393325968983)
            ·
              refine ⟨9398071547577589988953475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265381031718393325968983 9398071547577589988953475)
              ·
                refine ⟨14097107321366384983430213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9398071547577589988953475 14097107321366384983430213)
                ·
                  refine ⟨2643207622756197184393165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14097107321366384983430213 2643207622756197184393165)
                  ·
                    refine ⟨991202858533573944147437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643207622756197184393165 991202858533573944147437)
                    ·
                      rfl

theorem cell22_2895541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2895541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895541 prefixEnd_2895541 := by exact prefixLift 2895541
  have htrace : WordTrace (prefixWord ++ tailWord_2895541) baseStart_2895541 baseEnd_2895541 := by
    simpa [prefixWord, tailWord_2895541, baseEnd_2895541] using wordTrace_append hprefix tailTrace_2895541
  have hstable : (prefixWord ++ tailWord_2895541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895541).length < 2 ^ (prefixWord ++ tailWord_2895541).sum := by decide
  have hdescent : baseEnd_2895541 < baseStart_2895541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895558 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2895558 : Nat := 118140960795 + 2895558 * 2 ^ 59
def prefixEnd_2895558 : Nat := 4983230072969 + 3 ^ 40 * 2895558 * 2
def baseEnd_2895558 : Nat := 991208677980991566472385

theorem tailTrace_2895558 : CollatzResearch.WordTrace tailWord_2895558 prefixEnd_2895558 991208677980991566472385 := by
  unfold tailWord_2895558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300302388871730086893979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70406450962596908520404885 3300302388871730086893979)
  ·
    refine ⟨4950453583307595130340969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300302388871730086893979 4950453583307595130340969)
    ·
      refine ⟨3712840187480696347755727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4950453583307595130340969 3712840187480696347755727)
      ·
        refine ⟨5569260281221044521633591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712840187480696347755727 5569260281221044521633591)
        ·
          refine ⟨8353890421831566782450387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569260281221044521633591 8353890421831566782450387)
          ·
            refine ⟨12530835632747350173675581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353890421831566782450387 12530835632747350173675581)
            ·
              refine ⟨4699063362280256315128343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12530835632747350173675581 4699063362280256315128343)
              ·
                refine ⟨7048595043420384472692515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699063362280256315128343 7048595043420384472692515)
                ·
                  refine ⟨10572892565130576709038773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7048595043420384472692515 10572892565130576709038773)
                  ·
                    refine ⟨991208677980991566472385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10572892565130576709038773 991208677980991566472385)
                    ·
                      rfl

theorem cell22_2895558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2895558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895558 prefixEnd_2895558 := by exact prefixLift 2895558
  have htrace : WordTrace (prefixWord ++ tailWord_2895558) baseStart_2895558 baseEnd_2895558 := by
    simpa [prefixWord, tailWord_2895558, baseEnd_2895558] using wordTrace_append hprefix tailTrace_2895558
  have hstable : (prefixWord ++ tailWord_2895558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895558).length < 2 ^ (prefixWord ++ tailWord_2895558).sum := by decide
  have hdescent : baseEnd_2895558 < baseStart_2895558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895569 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_2895569 : Nat := 118140960795 + 2895569 * 2 ^ 59
def prefixEnd_2895569 : Nat := 4983230072969 + 3 ^ 40 * 2895569 * 2
def baseEnd_2895569 : Nat := 991212443505791204447351

theorem tailTrace_2895569 : CollatzResearch.WordTrace tailWord_2895569 prefixEnd_2895569 991212443505791204447351 := by
  unfold tailWord_2895569
  simp only [CollatzResearch.WordTrace]
  refine ⟨105610077646855511659257761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70406718431237007772838507 105610077646855511659257761)
  ·
    refine ⟨79207558235141633744443321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105610077646855511659257761 79207558235141633744443321)
    ·
      refine ⟨59405668676356225308332491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79207558235141633744443321 59405668676356225308332491)
      ·
        refine ⟨89108503014534337962498737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59405668676356225308332491 89108503014534337962498737)
        ·
          refine ⟨66831377260900753471874053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89108503014534337962498737 66831377260900753471874053)
          ·
            refine ⟨12530883236418891275976385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66831377260900753471874053 12530883236418891275976385)
            ·
              refine ⟨9398162427314168456982289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12530883236418891275976385 9398162427314168456982289)
              ·
                refine ⟨7048621820485626342736717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9398162427314168456982289 7048621820485626342736717)
                ·
                  refine ⟨2643233182682109878526269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7048621820485626342736717 2643233182682109878526269)
                  ·
                    refine ⟨991212443505791204447351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643233182682109878526269 991212443505791204447351)
                    ·
                      rfl

theorem cell22_2895569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_2895569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895569 prefixEnd_2895569 := by exact prefixLift 2895569
  have htrace : WordTrace (prefixWord ++ tailWord_2895569) baseStart_2895569 baseEnd_2895569 := by
    simpa [prefixWord, tailWord_2895569, baseEnd_2895569] using wordTrace_append hprefix tailTrace_2895569
  have hstable : (prefixWord ++ tailWord_2895569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895569).length < 2 ^ (prefixWord ++ tailWord_2895569).sum := by decide
  have hdescent : baseEnd_2895569 < baseStart_2895569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895627 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 6]
def baseStart_2895627 : Nat := 118140960795 + 2895627 * 2 ^ 59
def prefixEnd_2895627 : Nat := 4983230072969 + 3 ^ 40 * 2895627 * 2
def baseEnd_2895627 : Nat := 330410766030366128832391

theorem tailTrace_2895627 : CollatzResearch.WordTrace tailWord_2895627 prefixEnd_2895627 330410766030366128832391 := by
  unfold tailWord_2895627
  simp only [CollatzResearch.WordTrace]
  refine ⟨105612193080645387564869135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70408128720430258376579423 105612193080645387564869135)
  ·
    refine ⟨158418289620968081347303703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105612193080645387564869135 158418289620968081347303703)
    ·
      refine ⟨237627434431452122020955555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158418289620968081347303703 237627434431452122020955555)
      ·
        refine ⟨356441151647178183031433333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237627434431452122020955555 356441151647178183031433333)
        ·
          refine ⟨33416357966922954659196875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 356441151647178183031433333 33416357966922954659196875)
          ·
            refine ⟨50124536950384431988795313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33416357966922954659196875 50124536950384431988795313)
            ·
              refine ⟨37593402712788323991596485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50124536950384431988795313 37593402712788323991596485)
              ·
                refine ⟨7048763008647810748424341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37593402712788323991596485 7048763008647810748424341)
                ·
                  refine ⟨330410766030366128832391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7048763008647810748424341 330410766030366128832391)
                  ·
                    rfl

theorem cell22_2895627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_2895627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895627 prefixEnd_2895627 := by exact prefixLift 2895627
  have htrace : WordTrace (prefixWord ++ tailWord_2895627) baseStart_2895627 baseEnd_2895627 := by
    simpa [prefixWord, tailWord_2895627, baseEnd_2895627] using wordTrace_append hprefix tailTrace_2895627
  have hstable : (prefixWord ++ tailWord_2895627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895627).length < 2 ^ (prefixWord ++ tailWord_2895627).sum := by decide
  have hdescent : baseEnd_2895627 < baseStart_2895627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895676 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_2895676 : Nat := 118140960795 + 2895676 * 2 ^ 59
def prefixEnd_2895676 : Nat := 4983230072969 + 3 ^ 40 * 2895676 * 2
def baseEnd_2895676 : Nat := 991249071792478592022023

theorem tailTrace_2895676 : CollatzResearch.WordTrace tailWord_2895676 prefixEnd_2895676 991249071792478592022023 := by
  unfold tailWord_2895676
  simp only [CollatzResearch.WordTrace]
  refine ⟨52806990128733934466701441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70409320171645245955601921 52806990128733934466701441)
  ·
    refine ⟨39605242596550450850026081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52806990128733934466701441 39605242596550450850026081)
    ·
      refine ⟨29703931947412838137519561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39605242596550450850026081 29703931947412838137519561)
      ·
        refine ⟨22277948960559628603139671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29703931947412838137519561 22277948960559628603139671)
        ·
          refine ⟨33416923440839442904709507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22277948960559628603139671 33416923440839442904709507)
          ·
            refine ⟨50125385161259164357064261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33416923440839442904709507 50125385161259164357064261)
            ·
              refine ⟨9398509717736093316949549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50125385161259164357064261 9398509717736093316949549)
              ·
                refine ⟨3524441144151034993856081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9398509717736093316949549 3524441144151034993856081)
                ·
                  refine ⟨2643330858113276245392061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3524441144151034993856081 2643330858113276245392061)
                  ·
                    refine ⟨991249071792478592022023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643330858113276245392061 991249071792478592022023)
                    ·
                      rfl

theorem cell22_2895676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_2895676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895676 prefixEnd_2895676 := by exact prefixLift 2895676
  have htrace : WordTrace (prefixWord ++ tailWord_2895676) baseStart_2895676 baseEnd_2895676 := by
    simpa [prefixWord, tailWord_2895676, baseEnd_2895676] using wordTrace_append hprefix tailTrace_2895676
  have hstable : (prefixWord ++ tailWord_2895676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895676).length < 2 ^ (prefixWord ++ tailWord_2895676).sum := by decide
  have hdescent : baseEnd_2895676 < baseStart_2895676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895689 : List Nat := [1, 2, 1, 1, 2, 4, 5, 6]
def baseStart_2895689 : Nat := 118140960795 + 2895689 * 2 ^ 59
def prefixEnd_2895689 : Nat := 4983230072969 + 3 ^ 40 * 2895689 * 2
def baseEnd_2895689 : Nat := 110139280217572321271887

theorem tailTrace_2895689 : CollatzResearch.WordTrace tailWord_2895689 prefixEnd_2895689 110139280217572321271887 := by
  unfold tailWord_2895689
  simp only [CollatzResearch.WordTrace]
  refine ⟨105614454406420772153626121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70409636270947181435750747 105614454406420772153626121)
  ·
    refine ⟨79210840804815579115219591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105614454406420772153626121 79210840804815579115219591)
    ·
      refine ⟨118816261207223368672829387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79210840804815579115219591 118816261207223368672829387)
      ·
        refine ⟨178224391810835053009244081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118816261207223368672829387 178224391810835053009244081)
        ·
          refine ⟨133668293858126289756933061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178224391810835053009244081 133668293858126289756933061)
          ·
            refine ⟨25062805098398679329424949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133668293858126289756933061 25062805098398679329424949)
            ·
              refine ⟨2349637977974876187133589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25062805098398679329424949 2349637977974876187133589)
              ·
                refine ⟨110139280217572321271887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2349637977974876187133589 110139280217572321271887)
                ·
                  rfl

theorem cell22_2895689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 6].length) (baseStart_2895689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895689 prefixEnd_2895689 := by exact prefixLift 2895689
  have htrace : WordTrace (prefixWord ++ tailWord_2895689) baseStart_2895689 baseEnd_2895689 := by
    simpa [prefixWord, tailWord_2895689, baseEnd_2895689] using wordTrace_append hprefix tailTrace_2895689
  have hstable : (prefixWord ++ tailWord_2895689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895689).length < 2 ^ (prefixWord ++ tailWord_2895689).sum := by decide
  have hdescent : baseEnd_2895689 < baseStart_2895689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895772 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_2895772 : Nat := 118140960795 + 2895772 * 2 ^ 59
def prefixEnd_2895772 : Nat := 4983230072969 + 3 ^ 40 * 2895772 * 2
def baseEnd_2895772 : Nat := 991281934554366341621729

theorem tailTrace_2895772 : CollatzResearch.WordTrace tailWord_2895772 prefixEnd_2895772 991281934554366341621729 := by
  unfold tailWord_2895772
  simp only [CollatzResearch.WordTrace]
  refine ⟨52808740832560038664448785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70411654443413384885931713 52808740832560038664448785)
  ·
    refine ⟨39606555624420028998336589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52808740832560038664448785 39606555624420028998336589)
    ·
      refine ⟨14852458359157510874376221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39606555624420028998336589 14852458359157510874376221)
      ·
        refine ⟨5569671884684066577891083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14852458359157510874376221 5569671884684066577891083)
        ·
          refine ⟨8354507827026099866836625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569671884684066577891083 8354507827026099866836625)
          ·
            refine ⟨6265880870269574900127469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8354507827026099866836625 6265880870269574900127469)
            ·
              refine ⟨2349705326351090587547801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6265880870269574900127469 2349705326351090587547801)
              ·
                refine ⟨1762278994763317940660851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2349705326351090587547801 1762278994763317940660851)
                ·
                  refine ⟨2643418492144976910991277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762278994763317940660851 2643418492144976910991277)
                  ·
                    refine ⟨991281934554366341621729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643418492144976910991277 991281934554366341621729)
                    ·
                      rfl

theorem cell22_2895772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_2895772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895772 prefixEnd_2895772 := by exact prefixLift 2895772
  have htrace : WordTrace (prefixWord ++ tailWord_2895772) baseStart_2895772 baseEnd_2895772 := by
    simpa [prefixWord, tailWord_2895772, baseEnd_2895772] using wordTrace_append hprefix tailTrace_2895772
  have hstable : (prefixWord ++ tailWord_2895772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895772).length < 2 ^ (prefixWord ++ tailWord_2895772).sum := by decide
  have hdescent : baseEnd_2895772 < baseStart_2895772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895794 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2895794 : Nat := 118140960795 + 2895794 * 2 ^ 59
def prefixEnd_2895794 : Nat := 4983230072969 + 3 ^ 40 * 2895794 * 2
def baseEnd_2895794 : Nat := 991289465603965617571661

theorem tailTrace_2895794 : CollatzResearch.WordTrace tailWord_2895794 prefixEnd_2895794 991289465603965617571661 := by
  unfold tailWord_2895794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404571017760093771549609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70412189380693583390798957 26404571017760093771549609)
  ·
    refine ⟨19803428263320070328662207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26404571017760093771549609 19803428263320070328662207)
    ·
      refine ⟨29705142394980105492993311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19803428263320070328662207 29705142394980105492993311)
      ·
        refine ⟨44557713592470158239489967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29705142394980105492993311 44557713592470158239489967)
        ·
          refine ⟨66836570388705237359234951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44557713592470158239489967 66836570388705237359234951)
          ·
            refine ⟨100254855583057856038852427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66836570388705237359234951 100254855583057856038852427)
            ·
              refine ⟨150382283374586784058278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100254855583057856038852427 150382283374586784058278641)
              ·
                refine ⟨112786712530940088043708981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150382283374586784058278641 112786712530940088043708981)
                ·
                  refine ⟨10573754299775633254097717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112786712530940088043708981 10573754299775633254097717)
                  ·
                    refine ⟨991289465603965617571661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10573754299775633254097717 991289465603965617571661)
                    ·
                      rfl

theorem cell22_2895794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2895794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895794 prefixEnd_2895794 := by exact prefixLift 2895794
  have htrace : WordTrace (prefixWord ++ tailWord_2895794) baseStart_2895794 baseEnd_2895794 := by
    simpa [prefixWord, tailWord_2895794, baseEnd_2895794] using wordTrace_append hprefix tailTrace_2895794
  have hstable : (prefixWord ++ tailWord_2895794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895794).length < 2 ^ (prefixWord ++ tailWord_2895794).sum := by decide
  have hdescent : baseEnd_2895794 < baseStart_2895794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895856 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_2895856 : Nat := 118140960795 + 2895856 * 2 ^ 59
def prefixEnd_2895856 : Nat := 4983230072969 + 3 ^ 40 * 2895856 * 2
def baseEnd_2895856 : Nat := 991310689471018122521471

theorem tailTrace_2895856 : CollatzResearch.WordTrace tailWord_2895856 prefixEnd_2895856 991310689471018122521471 := by
  unfold tailWord_2895856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52810272698407879837477711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70413696931210506449970281 52810272698407879837477711)
  ·
    refine ⟨79215409047611819756216567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52810272698407879837477711 79215409047611819756216567)
    ·
      refine ⟨118823113571417729634324851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79215409047611819756216567 118823113571417729634324851)
      ·
        refine ⟨178234670357126594451487277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118823113571417729634324851 178234670357126594451487277)
        ·
          refine ⟨66838001383922472919307729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178234670357126594451487277 66838001383922472919307729)
          ·
            refine ⟨50128501037941854689480797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66838001383922472919307729 50128501037941854689480797)
            ·
              refine ⟨18798187889228195508555299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50128501037941854689480797 18798187889228195508555299)
              ·
                refine ⟨28197281833842293262832949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18798187889228195508555299 28197281833842293262832949)
                ·
                  refine ⟨2643495171922714993390589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28197281833842293262832949 2643495171922714993390589)
                  ·
                    refine ⟨991310689471018122521471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643495171922714993390589 991310689471018122521471)
                    ·
                      rfl

theorem cell22_2895856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_2895856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895856 prefixEnd_2895856 := by exact prefixLift 2895856
  have htrace : WordTrace (prefixWord ++ tailWord_2895856) baseStart_2895856 baseEnd_2895856 := by
    simpa [prefixWord, tailWord_2895856, baseEnd_2895856] using wordTrace_append hprefix tailTrace_2895856
  have hstable : (prefixWord ++ tailWord_2895856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895856).length < 2 ^ (prefixWord ++ tailWord_2895856).sum := by decide
  have hdescent : baseEnd_2895856 < baseStart_2895856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895886 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_2895886 : Nat := 118140960795 + 2895886 * 2 ^ 59
def prefixEnd_2895886 : Nat := 4983230072969 + 3 ^ 40 * 2895886 * 2
def baseEnd_2895886 : Nat := 330440319694702681423793

theorem tailTrace_2895886 : CollatzResearch.WordTrace tailWord_2895886 prefixEnd_2895886 330440319694702681423793 := by
  unfold tailWord_2895886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202704948338384349818439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70414426391138049865698341 13202704948338384349818439)
  ·
    refine ⟨19804057422507576524727659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13202704948338384349818439 19804057422507576524727659)
    ·
      refine ⟨29706086133761364787091489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19804057422507576524727659 29706086133761364787091489)
      ·
        refine ⟨22279564600321023590318617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29706086133761364787091489 22279564600321023590318617)
        ·
          refine ⟨16709673450240767692738963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22279564600321023590318617 16709673450240767692738963)
          ·
            refine ⟨25064510175361151539108445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16709673450240767692738963 25064510175361151539108445)
            ·
              refine ⟨9399191315760431827165667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25064510175361151539108445 9399191315760431827165667)
              ·
                refine ⟨14098786973640647740748501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399191315760431827165667 14098786973640647740748501)
                ·
                  refine ⟨330440319694702681423793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14098786973640647740748501 330440319694702681423793)
                  ·
                    rfl

theorem cell22_2895886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_2895886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895886 prefixEnd_2895886 := by exact prefixLift 2895886
  have htrace : WordTrace (prefixWord ++ tailWord_2895886) baseStart_2895886 baseEnd_2895886 := by
    simpa [prefixWord, tailWord_2895886, baseEnd_2895886] using wordTrace_append hprefix tailTrace_2895886
  have hstable : (prefixWord ++ tailWord_2895886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895886).length < 2 ^ (prefixWord ++ tailWord_2895886).sum := by decide
  have hdescent : baseEnd_2895886 < baseStart_2895886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895899 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_2895899 : Nat := 118140960795 + 2895899 * 2 ^ 59
def prefixEnd_2895899 : Nat := 4983230072969 + 3 ^ 40 * 2895899 * 2
def baseEnd_2895899 : Nat := 991325409249780343696339

theorem tailTrace_2895899 : CollatzResearch.WordTrace tailWord_2895899 prefixEnd_2895899 991325409249780343696339 := by
  unfold tailWord_2895899
  simp only [CollatzResearch.WordTrace]
  refine ⟨105622113735659978018770751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70414742490439985345847167 105622113735659978018770751)
  ·
    refine ⟨158433170603489967028156127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105622113735659978018770751 158433170603489967028156127)
    ·
      refine ⟨237649755905234950542234191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158433170603489967028156127 237649755905234950542234191)
      ·
        refine ⟨356474633857852425813351287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237649755905234950542234191 356474633857852425813351287)
        ·
          refine ⟨534711950786778638720026931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356474633857852425813351287 534711950786778638720026931)
          ·
            refine ⟨802067926180167958080040397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534711950786778638720026931 802067926180167958080040397)
            ·
              refine ⟨300775472317562984280015149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802067926180167958080040397 300775472317562984280015149)
              ·
                refine ⟨112790802119086119105005681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300775472317562984280015149 112790802119086119105005681)
                ·
                  refine ⟨84593101589314589328754261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112790802119086119105005681 84593101589314589328754261)
                  ·
                    refine ⟨991325409249780343696339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84593101589314589328754261 991325409249780343696339)
                    ·
                      rfl

theorem cell22_2895899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_2895899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895899 prefixEnd_2895899 := by exact prefixLift 2895899
  have htrace : WordTrace (prefixWord ++ tailWord_2895899) baseStart_2895899 baseEnd_2895899 := by
    simpa [prefixWord, tailWord_2895899, baseEnd_2895899] using wordTrace_append hprefix tailTrace_2895899
  have hstable : (prefixWord ++ tailWord_2895899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895899).length < 2 ^ (prefixWord ++ tailWord_2895899).sum := by decide
  have hdescent : baseEnd_2895899 < baseStart_2895899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895903 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 5]
def baseStart_2895903 : Nat := 118140960795 + 2895903 * 2 ^ 59
def prefixEnd_2895903 : Nat := 4983230072969 + 3 ^ 40 * 2895903 * 2
def baseEnd_2895903 : Nat := 330442259510508555532109

theorem tailTrace_2895903 : CollatzResearch.WordTrace tailWord_2895903 prefixEnd_2895903 330442259510508555532109 := by
  unfold tailWord_2895903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105622259627645486701916363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70414839751763657801277575 105622259627645486701916363)
  ·
    refine ⟨158433389441468230052874545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105622259627645486701916363 158433389441468230052874545)
    ·
      refine ⟨118825042081101172539655909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158433389441468230052874545 118825042081101172539655909)
      ·
        refine ⟨22279695390206469851185483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118825042081101172539655909 22279695390206469851185483)
        ·
          refine ⟨33419543085309704776778225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22279695390206469851185483 33419543085309704776778225)
          ·
            refine ⟨25064657313982278582583669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33419543085309704776778225 25064657313982278582583669)
            ·
              refine ⟨2349811623185838617117219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25064657313982278582583669 2349811623185838617117219)
              ·
                refine ⟨3524717434778757925675829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349811623185838617117219 3524717434778757925675829)
                ·
                  refine ⟨330442259510508555532109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524717434778757925675829 330442259510508555532109)
                  ·
                    rfl

theorem cell22_2895903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 5].length) (baseStart_2895903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895903 prefixEnd_2895903 := by exact prefixLift 2895903
  have htrace : WordTrace (prefixWord ++ tailWord_2895903) baseStart_2895903 baseEnd_2895903 := by
    simpa [prefixWord, tailWord_2895903, baseEnd_2895903] using wordTrace_append hprefix tailTrace_2895903
  have hstable : (prefixWord ++ tailWord_2895903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895903).length < 2 ^ (prefixWord ++ tailWord_2895903).sum := by decide
  have hdescent : baseEnd_2895903 < baseStart_2895903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895933 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2895933 : Nat := 118140960795 + 2895933 * 2 ^ 59
def prefixEnd_2895933 : Nat := 4983230072969 + 3 ^ 40 * 2895933 * 2
def baseEnd_2895933 : Nat := 991337048144615588346235

theorem tailTrace_2895933 : CollatzResearch.WordTrace tailWord_2895933 prefixEnd_2895933 991337048144615588346235 := by
  unfold tailWord_2895933
  simp only [CollatzResearch.WordTrace]
  refine ⟨105623353817536801825508453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70415569211691201217005635 105623353817536801825508453)
  ·
    refine ⟨19804378840788150342282835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105623353817536801825508453 19804378840788150342282835)
    ·
      refine ⟨29706568261182225513424253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19804378840788150342282835 29706568261182225513424253)
      ·
        refine ⟨11139963097943334567534095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29706568261182225513424253 11139963097943334567534095)
        ·
          refine ⟨16709944646915001851301143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11139963097943334567534095 16709944646915001851301143)
          ·
            refine ⟨25064916970372502776951715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16709944646915001851301143 25064916970372502776951715)
            ·
              refine ⟨37597375455558754165427573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25064916970372502776951715 37597375455558754165427573)
              ·
                refine ⟨3524753948958633203008835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37597375455558754165427573 3524753948958633203008835)
                ·
                  refine ⟨5287130923437949804513253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524753948958633203008835 5287130923437949804513253)
                  ·
                    refine ⟨991337048144615588346235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287130923437949804513253 991337048144615588346235)
                    ·
                      rfl

theorem cell22_2895933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2895933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895933 prefixEnd_2895933 := by exact prefixLift 2895933
  have htrace : WordTrace (prefixWord ++ tailWord_2895933) baseStart_2895933 baseEnd_2895933 := by
    simpa [prefixWord, tailWord_2895933, baseEnd_2895933] using wordTrace_append hprefix tailTrace_2895933
  have hstable : (prefixWord ++ tailWord_2895933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895933).length < 2 ^ (prefixWord ++ tailWord_2895933).sum := by decide
  have hdescent : baseEnd_2895933 < baseStart_2895933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895948 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_2895948 : Nat := 118140960795 + 2895948 * 2 ^ 59
def prefixEnd_2895948 : Nat := 4983230072969 + 3 ^ 40 * 2895948 * 2
def baseEnd_2895948 : Nat := 330447394317053516407063

theorem tailTrace_2895948 : CollatzResearch.WordTrace tailWord_2895948 prefixEnd_2895948 330447394317053516407063 := by
  unfold tailWord_2895948
  simp only [CollatzResearch.WordTrace]
  refine ⟨52811950456241229693652249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70415933941654972924869665 52811950456241229693652249)
  ·
    refine ⟨39608962842180922270239187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52811950456241229693652249 39608962842180922270239187)
    ·
      refine ⟨59413444263271383405358781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39608962842180922270239187 59413444263271383405358781)
      ·
        refine ⟨22280041598726768777009543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59413444263271383405358781 22280041598726768777009543)
        ·
          refine ⟨33420062398090153165514315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22280041598726768777009543 33420062398090153165514315)
          ·
            refine ⟨50130093597135229748271473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33420062398090153165514315 50130093597135229748271473)
            ·
              refine ⟨37597570197851422311203605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50130093597135229748271473 37597570197851422311203605)
              ·
                refine ⟨1762386103024285420837669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37597570197851422311203605 1762386103024285420837669)
                ·
                  refine ⟨330447394317053516407063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1762386103024285420837669 330447394317053516407063)
                  ·
                    rfl

theorem cell22_2895948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_2895948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895948 prefixEnd_2895948 := by exact prefixLift 2895948
  have htrace : WordTrace (prefixWord ++ tailWord_2895948) baseStart_2895948 baseEnd_2895948 := by
    simpa [prefixWord, tailWord_2895948, baseEnd_2895948] using wordTrace_append hprefix tailTrace_2895948
  have hstable : (prefixWord ++ tailWord_2895948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895948).length < 2 ^ (prefixWord ++ tailWord_2895948).sum := by decide
  have hdescent : baseEnd_2895948 < baseStart_2895948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895961 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_2895961 : Nat := 118140960795 + 2895961 * 2 ^ 59
def prefixEnd_2895961 : Nat := 4983230072969 + 3 ^ 40 * 2895961 * 2
def baseEnd_2895961 : Nat := 991346633116832848646149

theorem tailTrace_2895961 : CollatzResearch.WordTrace tailWord_2895961 prefixEnd_2895961 991346633116832848646149 := by
  unfold tailWord_2895961
  simp only [CollatzResearch.WordTrace]
  refine ⟨105624375061435362607527737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70416250040956908405018491 105624375061435362607527737)
  ·
    refine ⟨79218281296076521955645803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105624375061435362607527737 79218281296076521955645803)
    ·
      refine ⟨118827421944114782933468705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79218281296076521955645803 118827421944114782933468705)
      ·
        refine ⟨89120566458086087200101529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118827421944114782933468705 89120566458086087200101529)
        ·
          refine ⟨66840424843564565400076147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89120566458086087200101529 66840424843564565400076147)
          ·
            refine ⟨100260637265346848100114221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66840424843564565400076147 100260637265346848100114221)
            ·
              refine ⟨37597738974505068037542833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100260637265346848100114221 37597738974505068037542833)
              ·
                refine ⟨28198304230878801028157125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37597738974505068037542833 28198304230878801028157125)
                ·
                  refine ⟨5287182043289775192779461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28198304230878801028157125 5287182043289775192779461)
                  ·
                    refine ⟨991346633116832848646149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287182043289775192779461 991346633116832848646149)
                    ·
                      rfl

theorem cell22_2895961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_2895961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2895961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2895961 prefixEnd_2895961 := by exact prefixLift 2895961
  have htrace : WordTrace (prefixWord ++ tailWord_2895961) baseStart_2895961 baseEnd_2895961 := by
    simpa [prefixWord, tailWord_2895961, baseEnd_2895961] using wordTrace_append hprefix tailTrace_2895961
  have hstable : (prefixWord ++ tailWord_2895961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895961).length < 2 ^ (prefixWord ++ tailWord_2895961).sum := by decide
  have hdescent : baseEnd_2895961 < baseStart_2895961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896055 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 5]
def baseStart_2896055 : Nat := 118140960795 + 2896055 * 2 ^ 59
def prefixEnd_2896055 : Nat := 4983230072969 + 3 ^ 40 * 2896055 * 2
def baseEnd_2896055 : Nat := 330459603745949312265287

theorem tailTrace_2896055 : CollatzResearch.WordTrace tailWord_2896055 prefixEnd_2896055 330459603745949312265287 := by
  unfold tailWord_2896055
  simp only [CollatzResearch.WordTrace]
  refine ⟨105627803523094816661449619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70418535682063211107633079 105627803523094816661449619)
  ·
    refine ⟨158441705284642224992174429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105627803523094816661449619 158441705284642224992174429)
    ·
      refine ⟨59415639481740834372065411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158441705284642224992174429 59415639481740834372065411)
      ·
        refine ⟨89123459222611251558098117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59415639481740834372065411 89123459222611251558098117)
        ·
          refine ⟨16710648604239609667143397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89123459222611251558098117 16710648604239609667143397)
          ·
            refine ⟨3133246613294926812589387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16710648604239609667143397 3133246613294926812589387)
            ·
              refine ⟨4699869919942390218884081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133246613294926812589387 4699869919942390218884081)
              ·
                refine ⟨3524902439956792664163061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699869919942390218884081 3524902439956792664163061)
                ·
                  refine ⟨330459603745949312265287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524902439956792664163061 330459603745949312265287)
                  ·
                    rfl

theorem cell22_2896055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 5].length) (baseStart_2896055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896055 prefixEnd_2896055 := by exact prefixLift 2896055
  have htrace : WordTrace (prefixWord ++ tailWord_2896055) baseStart_2896055 baseEnd_2896055 := by
    simpa [prefixWord, tailWord_2896055, baseEnd_2896055] using wordTrace_append hprefix tailTrace_2896055
  have hstable : (prefixWord ++ tailWord_2896055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896055).length < 2 ^ (prefixWord ++ tailWord_2896055).sum := by decide
  have hdescent : baseEnd_2896055 < baseStart_2896055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896113 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2896113 : Nat := 118140960795 + 2896113 * 2 ^ 59
def prefixEnd_2896113 : Nat := 4983230072969 + 3 ^ 40 * 2896113 * 2
def baseEnd_2896113 : Nat := 991398665823155118845683

theorem tailTrace_2896113 : CollatzResearch.WordTrace tailWord_2896113 prefixEnd_2896113 991398665823155118845683 := by
  unfold tailWord_2896113
  simp only [CollatzResearch.WordTrace]
  refine ⟨105629918956884692567060993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70419945971256461711373995 105629918956884692567060993)
  ·
    refine ⟨79222439217663519425295745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105629918956884692567060993 79222439217663519425295745)
    ·
      refine ⟨59416829413247639568971809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79222439217663519425295745 59416829413247639568971809)
      ·
        refine ⟨44562622059935729676728857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59416829413247639568971809 44562622059935729676728857)
        ·
          refine ⟨33421966544951797257546643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44562622059935729676728857 33421966544951797257546643)
          ·
            refine ⟨50132949817427695886319965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33421966544951797257546643 50132949817427695886319965)
            ·
              refine ⟨18799856181535385957369987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50132949817427695886319965 18799856181535385957369987)
              ·
                refine ⟨28199784272303078936054981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18799856181535385957369987 28199784272303078936054981)
                ·
                  refine ⟨5287459551056827300510309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28199784272303078936054981 5287459551056827300510309)
                  ·
                    refine ⟨991398665823155118845683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287459551056827300510309 991398665823155118845683)
                    ·
                      rfl

theorem cell22_2896113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2896113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896113 prefixEnd_2896113 := by exact prefixLift 2896113
  have htrace : WordTrace (prefixWord ++ tailWord_2896113) baseStart_2896113 baseEnd_2896113 := by
    simpa [prefixWord, tailWord_2896113, baseEnd_2896113] using wordTrace_append hprefix tailTrace_2896113
  have hstable : (prefixWord ++ tailWord_2896113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896113).length < 2 ^ (prefixWord ++ tailWord_2896113).sum := by decide
  have hdescent : baseEnd_2896113 < baseStart_2896113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896115 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 2, 3]
def baseStart_2896115 : Nat := 118140960795 + 2896115 * 2 ^ 59
def prefixEnd_2896115 : Nat := 4983230072969 + 3 ^ 40 * 2896115 * 2
def baseEnd_2896115 : Nat := 991399350464027780295677

theorem tailTrace_2896115 : CollatzResearch.WordTrace tailWord_2896115 prefixEnd_2896115 991399350464027780295677 := by
  unfold tailWord_2896115
  simp only [CollatzResearch.WordTrace]
  refine ⟨105629991902877446908633799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70419994601918297939089199 105629991902877446908633799)
  ·
    refine ⟨158444987854316170362950699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105629991902877446908633799 158444987854316170362950699)
    ·
      refine ⟨237667481781474255544426049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158444987854316170362950699 237667481781474255544426049)
      ·
        refine ⟨178250611336105691658319537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237667481781474255544426049 178250611336105691658319537)
        ·
          refine ⟨133687958502079268743739653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178250611336105691658319537 133687958502079268743739653)
          ·
            refine ⟨25066492219139862889451185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133687958502079268743739653 25066492219139862889451185)
            ·
              refine ⟨18799869164354897167088389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25066492219139862889451185 18799869164354897167088389)
              ·
                refine ⟨3524975468316543218829073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18799869164354897167088389 3524975468316543218829073)
                ·
                  refine ⟨2643731601237407414121805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3524975468316543218829073 2643731601237407414121805)
                  ·
                    refine ⟨991399350464027780295677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643731601237407414121805 991399350464027780295677)
                    ·
                      rfl

theorem cell22_2896115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3].length) (baseStart_2896115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896115 prefixEnd_2896115 := by exact prefixLift 2896115
  have htrace : WordTrace (prefixWord ++ tailWord_2896115) baseStart_2896115 baseEnd_2896115 := by
    simpa [prefixWord, tailWord_2896115, baseEnd_2896115] using wordTrace_append hprefix tailTrace_2896115
  have hstable : (prefixWord ++ tailWord_2896115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896115).length < 2 ^ (prefixWord ++ tailWord_2896115).sum := by decide
  have hdescent : baseEnd_2896115 < baseStart_2896115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896218 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_2896218 : Nat := 118140960795 + 2896218 * 2 ^ 59
def prefixEnd_2896218 : Nat := 4983230072969 + 3 ^ 40 * 2896218 * 2
def baseEnd_2896218 : Nat := 330478203156323281656787

theorem tailTrace_2896218 : CollatzResearch.WordTrace tailWord_2896218 prefixEnd_2896218 330478203156323281656787 := by
  unfold tailWord_2896218
  simp only [CollatzResearch.WordTrace]
  refine ⟨26408437155376073874908327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70422499081002863666422205 26408437155376073874908327)
  ·
    refine ⟨39612655733064110812362491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26408437155376073874908327 39612655733064110812362491)
    ·
      refine ⟨59418983599596166218543737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39612655733064110812362491 59418983599596166218543737)
      ·
        refine ⟨44564237699697124663907803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59418983599596166218543737 44564237699697124663907803)
        ·
          refine ⟨66846356549545686995861705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44564237699697124663907803 66846356549545686995861705)
          ·
            refine ⟨50134767412159265246896279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66846356549545686995861705 50134767412159265246896279)
            ·
              refine ⟨75202151118238897870344419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50134767412159265246896279 75202151118238897870344419)
              ·
                refine ⟨112803226677358346805516629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75202151118238897870344419 112803226677358346805516629)
                ·
                  refine ⟨330478203156323281656787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112803226677358346805516629 330478203156323281656787)
                  ·
                    rfl

theorem cell22_2896218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_2896218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896218 prefixEnd_2896218 := by exact prefixLift 2896218
  have htrace : WordTrace (prefixWord ++ tailWord_2896218) baseStart_2896218 baseEnd_2896218 := by
    simpa [prefixWord, tailWord_2896218, baseEnd_2896218] using wordTrace_append hprefix tailTrace_2896218
  have hstable : (prefixWord ++ tailWord_2896218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896218).length < 2 ^ (prefixWord ++ tailWord_2896218).sum := by decide
  have hdescent : baseEnd_2896218 < baseStart_2896218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896224 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_2896224 : Nat := 118140960795 + 2896224 * 2 ^ 59
def prefixEnd_2896224 : Nat := 4983230072969 + 3 ^ 40 * 2896224 * 2
def baseEnd_2896224 : Nat := 330478887797195943106781

theorem tailTrace_2896224 : CollatzResearch.WordTrace tailWord_2896224 prefixEnd_2896224 330478887797195943106781 := by
  unfold tailWord_2896224
  simp only [CollatzResearch.WordTrace]
  refine ⟨52816983729741279262175863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70422644972988372349567817 52816983729741279262175863)
  ·
    refine ⟨79225475594611918893263795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52816983729741279262175863 79225475594611918893263795)
    ·
      refine ⟨118838213391917878339895693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79225475594611918893263795 118838213391917878339895693)
      ·
        refine ⟨44564330021969204377460885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118838213391917878339895693 44564330021969204377460885)
        ·
          refine ⟨2088952969779806455193479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44564330021969204377460885 2088952969779806455193479)
          ·
            refine ⟨3133429454669709682790219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088952969779806455193479 3133429454669709682790219)
            ·
              refine ⟨4700144182004564524185329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133429454669709682790219 4700144182004564524185329)
              ·
                refine ⟨3525108136503423393138997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700144182004564524185329 3525108136503423393138997)
                ·
                  refine ⟨330478887797195943106781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3525108136503423393138997 330478887797195943106781)
                  ·
                    rfl

theorem cell22_2896224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_2896224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896224 prefixEnd_2896224 := by exact prefixLift 2896224
  have htrace : WordTrace (prefixWord ++ tailWord_2896224) baseStart_2896224 baseEnd_2896224 := by
    simpa [prefixWord, tailWord_2896224, baseEnd_2896224] using wordTrace_append hprefix tailTrace_2896224
  have hstable : (prefixWord ++ tailWord_2896224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896224).length < 2 ^ (prefixWord ++ tailWord_2896224).sum := by decide
  have hdescent : baseEnd_2896224 < baseStart_2896224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896250 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_2896250 : Nat := 118140960795 + 2896250 * 2 ^ 59
def prefixEnd_2896250 : Nat := 4983230072969 + 3 ^ 40 * 2896250 * 2
def baseEnd_2896250 : Nat := 991445563722932428170263

theorem tailTrace_2896250 : CollatzResearch.WordTrace tailWord_2896250 prefixEnd_2896250 991445563722932428170263 := by
  unfold tailWord_2896250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26408728939347091241199551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70423277171592243309865469 26408728939347091241199551)
  ·
    refine ⟨39613093409020636861799327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26408728939347091241199551 39613093409020636861799327)
    ·
      refine ⟨59419640113530955292698991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39613093409020636861799327 59419640113530955292698991)
      ·
        refine ⟨89129460170296432939048487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59419640113530955292698991 89129460170296432939048487)
        ·
          refine ⟨133694190255444649408572731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89129460170296432939048487 133694190255444649408572731)
          ·
            refine ⟨200541285383166974112859097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133694190255444649408572731 200541285383166974112859097)
            ·
              refine ⟨150405964037375230584644323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200541285383166974112859097 150405964037375230584644323)
              ·
                refine ⟨225608946056062845876966485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150405964037375230584644323 225608946056062845876966485)
                ·
                  refine ⟨2643854836594486475120701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 225608946056062845876966485 2643854836594486475120701)
                  ·
                    refine ⟨991445563722932428170263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643854836594486475120701 991445563722932428170263)
                    ·
                      rfl

theorem cell22_2896250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_2896250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896250 prefixEnd_2896250 := by exact prefixLift 2896250
  have htrace : WordTrace (prefixWord ++ tailWord_2896250) baseStart_2896250 baseEnd_2896250 := by
    simpa [prefixWord, tailWord_2896250, baseEnd_2896250] using wordTrace_append hprefix tailTrace_2896250
  have hstable : (prefixWord ++ tailWord_2896250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896250).length < 2 ^ (prefixWord ++ tailWord_2896250).sum := by decide
  have hdescent : baseEnd_2896250 < baseStart_2896250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896265 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_2896265 : Nat := 118140960795 + 2896265 * 2 ^ 59
def prefixEnd_2896265 : Nat := 4983230072969 + 3 ^ 40 * 2896265 * 2
def baseEnd_2896265 : Nat := 991450698529477389045217

theorem tailTrace_2896265 : CollatzResearch.WordTrace tailWord_2896265 prefixEnd_2896265 991450698529477389045217 := by
  unfold tailWord_2896265
  simp only [CollatzResearch.WordTrace]
  refine ⟨105635462852334022526594249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70423641901556015017729499 105635462852334022526594249)
  ·
    refine ⟨79226597139250516894945687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105635462852334022526594249 79226597139250516894945687)
    ·
      refine ⟨118839895708875775342418531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79226597139250516894945687 118839895708875775342418531)
      ·
        refine ⟨178259843563313663013627797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118839895708875775342418531 178259843563313663013627797)
        ·
          refine ⟨8355930167030327953763803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178259843563313663013627797 8355930167030327953763803)
          ·
            refine ⟨12533895250545491930645705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355930167030327953763803 12533895250545491930645705)
            ·
              refine ⟨9400421437909118947984279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12533895250545491930645705 9400421437909118947984279)
              ·
                refine ⟨14100632156863678421976419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9400421437909118947984279 14100632156863678421976419)
                ·
                  refine ⟨21150948235295517632964629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14100632156863678421976419 21150948235295517632964629)
                  ·
                    refine ⟨991450698529477389045217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21150948235295517632964629 991450698529477389045217)
                    ·
                      rfl

theorem cell22_2896265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_2896265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896265 prefixEnd_2896265 := by exact prefixLift 2896265
  have htrace : WordTrace (prefixWord ++ tailWord_2896265) baseStart_2896265 baseEnd_2896265 := by
    simpa [prefixWord, tailWord_2896265, baseEnd_2896265] using wordTrace_append hprefix tailTrace_2896265
  have hstable : (prefixWord ++ tailWord_2896265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896265).length < 2 ^ (prefixWord ++ tailWord_2896265).sum := by decide
  have hdescent : baseEnd_2896265 < baseStart_2896265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896280 : List Nat := [2, 1, 2, 5, 1, 1, 10]
def baseStart_2896280 : Nat := 118140960795 + 2896280 * 2 ^ 59
def prefixEnd_2896280 : Nat := 4983230072969 + 3 ^ 40 * 2896280 * 2
def baseEnd_2896280 : Nat := 36720586419852679626673

theorem tailTrace_2896280 : CollatzResearch.WordTrace tailWord_2896280 prefixEnd_2896280 36720586419852679626673 := by
  unfold tailWord_2896280
  simp only [CollatzResearch.WordTrace]
  refine ⟨52818004973639840044195147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70424006631519786725593529 52818004973639840044195147)
  ·
    refine ⟨79227007460459760066292721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52818004973639840044195147 79227007460459760066292721)
    ·
      refine ⟨59420255595344820049719541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79227007460459760066292721 59420255595344820049719541)
      ·
        refine ⟨5570648962063576879661207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59420255595344820049719541 5570648962063576879661207)
        ·
          refine ⟨8355973443095365319491811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570648962063576879661207 8355973443095365319491811)
          ·
            refine ⟨12533960164643047979237717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355973443095365319491811 12533960164643047979237717)
            ·
              refine ⟨36720586419852679626673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12533960164643047979237717 36720586419852679626673)
              ·
                rfl

theorem cell22_2896280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 10].length) (baseStart_2896280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896280 prefixEnd_2896280 := by exact prefixLift 2896280
  have htrace : WordTrace (prefixWord ++ tailWord_2896280) baseStart_2896280 baseEnd_2896280 := by
    simpa [prefixWord, tailWord_2896280, baseEnd_2896280] using wordTrace_append hprefix tailTrace_2896280
  have hstable : (prefixWord ++ tailWord_2896280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896280).length < 2 ^ (prefixWord ++ tailWord_2896280).sum := by decide
  have hdescent : baseEnd_2896280 < baseStart_2896280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896282 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_2896282 : Nat := 118140960795 + 2896282 * 2 ^ 59
def prefixEnd_2896282 : Nat := 4983230072969 + 3 ^ 40 * 2896282 * 2
def baseEnd_2896282 : Nat := 991456517976895011370165

theorem tailTrace_2896282 : CollatzResearch.WordTrace tailWord_2896282 prefixEnd_2896282 991456517976895011370165 := by
  unfold tailWord_2896282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26409020723318108607490775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70424055262181622953308733 26409020723318108607490775)
  ·
    refine ⟨39613531084977162911236163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26409020723318108607490775 39613531084977162911236163)
    ·
      refine ⟨59420296627465744366854245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39613531084977162911236163 59420296627465744366854245)
      ·
        refine ⟨11141305617649827068785171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59420296627465744366854245 11141305617649827068785171)
        ·
          refine ⟨16711958426474740603177757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11141305617649827068785171 16711958426474740603177757)
          ·
            refine ⟨6266984409928027726191659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16711958426474740603177757 6266984409928027726191659)
            ·
              refine ⟨9400476614892041589287489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266984409928027726191659 9400476614892041589287489)
              ·
                refine ⟨7050357461169031191965617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9400476614892041589287489 7050357461169031191965617)
                ·
                  refine ⟨5287768095876773393974213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7050357461169031191965617 5287768095876773393974213)
                  ·
                    refine ⟨991456517976895011370165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287768095876773393974213 991456517976895011370165)
                    ·
                      rfl

theorem cell22_2896282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_2896282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896282 prefixEnd_2896282 := by exact prefixLift 2896282
  have htrace : WordTrace (prefixWord ++ tailWord_2896282) baseStart_2896282 baseEnd_2896282 := by
    simpa [prefixWord, tailWord_2896282, baseEnd_2896282] using wordTrace_append hprefix tailTrace_2896282
  have hstable : (prefixWord ++ tailWord_2896282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896282).length < 2 ^ (prefixWord ++ tailWord_2896282).sum := by decide
  have hdescent : baseEnd_2896282 < baseStart_2896282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896301 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2896301 : Nat := 118140960795 + 2896301 * 2 ^ 59
def prefixEnd_2896301 : Nat := 4983230072969 + 3 ^ 40 * 2896301 * 2
def baseEnd_2896301 : Nat := 991463022065185295145107

theorem tailTrace_2896301 : CollatzResearch.WordTrace tailWord_2896301 prefixEnd_2896301 991463022065185295145107 := by
  unfold tailWord_2896301
  simp only [CollatzResearch.WordTrace]
  refine ⟨105636775880203600674904757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70424517253469067116603171 105636775880203600674904757)
  ·
    refine ⟨9903447738769087563272321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105636775880203600674904757 9903447738769087563272321)
    ·
      refine ⟨7427585804076815672454241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9903447738769087563272321 7427585804076815672454241)
      ·
        refine ⟨5570689353057611754340681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7427585804076815672454241 5570689353057611754340681)
        ·
          refine ⟨4178017014793208815755511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5570689353057611754340681 4178017014793208815755511)
          ·
            refine ⟨6267025522189813223633267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178017014793208815755511 6267025522189813223633267)
            ·
              refine ⟨9400538283284719835449901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267025522189813223633267 9400538283284719835449901)
              ·
                refine ⟨3525201856231769938293713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9400538283284719835449901 3525201856231769938293713)
                ·
                  refine ⟨2643901392173827453720285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3525201856231769938293713 2643901392173827453720285)
                  ·
                    refine ⟨991463022065185295145107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643901392173827453720285 991463022065185295145107)
                    ·
                      rfl

theorem cell22_2896301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2896301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896301 prefixEnd_2896301 := by exact prefixLift 2896301
  have htrace : WordTrace (prefixWord ++ tailWord_2896301) baseStart_2896301 baseEnd_2896301 := by
    simpa [prefixWord, tailWord_2896301, baseEnd_2896301] using wordTrace_append hprefix tailTrace_2896301
  have hstable : (prefixWord ++ tailWord_2896301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896301).length < 2 ^ (prefixWord ++ tailWord_2896301).sum := by decide
  have hdescent : baseEnd_2896301 < baseStart_2896301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896389 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_2896389 : Nat := 118140960795 + 2896389 * 2 ^ 59
def prefixEnd_2896389 : Nat := 4983230072969 + 3 ^ 40 * 2896389 * 2
def baseEnd_2896389 : Nat := 991493146263582398944837

theorem tailTrace_2896389 : CollatzResearch.WordTrace tailWord_2896389 prefixEnd_2896389 991493146263582398944837 := by
  unfold tailWord_2896389
  simp only [CollatzResearch.WordTrace]
  refine ⟨105639985503884791704108221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70426657002589861136072147 105639985503884791704108221)
  ·
    refine ⟨39614994563956796889040583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105639985503884791704108221 39614994563956796889040583)
    ·
      refine ⟨59422491845935195333560875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39614994563956796889040583 59422491845935195333560875)
      ·
        refine ⟨89133737768902793000341313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59422491845935195333560875 89133737768902793000341313)
        ·
          refine ⟨66850303326677094750255985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89133737768902793000341313 66850303326677094750255985)
          ·
            refine ⟨50137727495007821062691989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66850303326677094750255985 50137727495007821062691989)
            ·
              refine ⟨2350205976328491612313687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50137727495007821062691989 2350205976328491612313687)
              ·
                refine ⟨3525308964492737418470531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350205976328491612313687 3525308964492737418470531)
                ·
                  refine ⟨5287963446739106127705797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525308964492737418470531 5287963446739106127705797)
                  ·
                    refine ⟨991493146263582398944837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287963446739106127705797 991493146263582398944837)
                    ·
                      rfl

theorem cell22_2896389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_2896389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896389 prefixEnd_2896389 := by exact prefixLift 2896389
  have htrace : WordTrace (prefixWord ++ tailWord_2896389) baseStart_2896389 baseEnd_2896389 := by
    simpa [prefixWord, tailWord_2896389, baseEnd_2896389] using wordTrace_append hprefix tailTrace_2896389
  have hstable : (prefixWord ++ tailWord_2896389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896389).length < 2 ^ (prefixWord ++ tailWord_2896389).sum := by decide
  have hdescent : baseEnd_2896389 < baseStart_2896389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896404 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_2896404 : Nat := 118140960795 + 2896404 * 2 ^ 59
def prefixEnd_2896404 : Nat := 4983230072969 + 3 ^ 40 * 2896404 * 2
def baseEnd_2896404 : Nat := 330499427023375786606597

theorem tailTrace_2896404 : CollatzResearch.WordTrace tailWord_2896404 prefixEnd_2896404 330499427023375786606597 := by
  unfold tailWord_2896404
  simp only [CollatzResearch.WordTrace]
  refine ⟨52820266299415224632952133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70427021732553632843936177 52820266299415224632952133)
  ·
    refine ⟨9903799931140354618678525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52820266299415224632952133 9903799931140354618678525)
    ·
      refine ⟨3713924974177632982004447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9903799931140354618678525 3713924974177632982004447)
      ·
        refine ⟨5570887461266449473006671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713924974177632982004447 5570887461266449473006671)
        ·
          refine ⟨8356331191899674209510007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570887461266449473006671 8356331191899674209510007)
          ·
            refine ⟨12534496787849511314265011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356331191899674209510007 12534496787849511314265011)
            ·
              refine ⟨18801745181774266971397517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12534496787849511314265011 18801745181774266971397517)
              ·
                refine ⟨7050654443165350114274069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18801745181774266971397517 7050654443165350114274069)
                ·
                  refine ⟨330499427023375786606597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7050654443165350114274069 330499427023375786606597)
                  ·
                    rfl

theorem cell22_2896404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_2896404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896404 prefixEnd_2896404 := by exact prefixLift 2896404
  have htrace : WordTrace (prefixWord ++ tailWord_2896404) baseStart_2896404 baseEnd_2896404 := by
    simpa [prefixWord, tailWord_2896404, baseEnd_2896404] using wordTrace_append hprefix tailTrace_2896404
  have hstable : (prefixWord ++ tailWord_2896404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896404).length < 2 ^ (prefixWord ++ tailWord_2896404).sum := by decide
  have hdescent : baseEnd_2896404 < baseStart_2896404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896415 : List Nat := [1, 1, 2, 4, 1, 1, 1, 11]
def baseStart_2896415 : Nat := 118140960795 + 2896415 * 2 ^ 59
def prefixEnd_2896415 : Nat := 4983230072969 + 3 ^ 40 * 2896415 * 2
def baseEnd_2896415 : Nat := 110166894066102999754973

theorem tailTrace_2896415 : CollatzResearch.WordTrace tailWord_2896415 prefixEnd_2896415 110166894066102999754973 := by
  unfold tailWord_2896415
  simp only [CollatzResearch.WordTrace]
  refine ⟨105640933801790598144554699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70427289201193732096369799 105640933801790598144554699)
  ·
    refine ⟨158461400702685897216832049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105640933801790598144554699 158461400702685897216832049)
    ·
      refine ⟨118846050527014422912624037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158461400702685897216832049 118846050527014422912624037)
      ·
        refine ⟨22283634473815204296117007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118846050527014422912624037 22283634473815204296117007)
        ·
          refine ⟨33425451710722806444175511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22283634473815204296117007 33425451710722806444175511)
          ·
            refine ⟨50138177566084209666263267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33425451710722806444175511 50138177566084209666263267)
            ·
              refine ⟨75207266349126314499394901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50138177566084209666263267 75207266349126314499394901)
              ·
                refine ⟨110166894066102999754973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75207266349126314499394901 110166894066102999754973)
                ·
                  rfl

theorem cell22_2896415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 11].length) (baseStart_2896415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896415 prefixEnd_2896415 := by exact prefixLift 2896415
  have htrace : WordTrace (prefixWord ++ tailWord_2896415) baseStart_2896415 baseEnd_2896415 := by
    simpa [prefixWord, tailWord_2896415, baseEnd_2896415] using wordTrace_append hprefix tailTrace_2896415
  have hstable : (prefixWord ++ tailWord_2896415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896415).length < 2 ^ (prefixWord ++ tailWord_2896415).sum := by decide
  have hdescent : baseEnd_2896415 < baseStart_2896415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896419 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 1, 5]
def baseStart_2896419 : Nat := 118140960795 + 2896419 * 2 ^ 59
def prefixEnd_2896419 : Nat := 4983230072969 + 3 ^ 40 * 2896419 * 2
def baseEnd_2896419 : Nat := 991503415876672320694745

theorem tailTrace_2896419 : CollatzResearch.WordTrace tailWord_2896419 prefixEnd_2896419 991503415876672320694745 := by
  unfold tailWord_2896419
  simp only [CollatzResearch.WordTrace]
  refine ⟨105641079693776106827700311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70427386462517404551800207 105641079693776106827700311)
  ·
    refine ⟨158461619540664160241550467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105641079693776106827700311 158461619540664160241550467)
    ·
      refine ⟨237692429310996240362325701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158461619540664160241550467 237692429310996240362325701)
      ·
        refine ⟨44567330495811795067936069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237692429310996240362325701 44567330495811795067936069)
        ·
          refine ⟨8356374467964711575238013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44567330495811795067936069 8356374467964711575238013)
          ·
            refine ⟨3133640425486766840714255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8356374467964711575238013 3133640425486766840714255)
            ·
              refine ⟨4700460638230150261071383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133640425486766840714255 4700460638230150261071383)
              ·
                refine ⟨7050690957345225391607075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700460638230150261071383 7050690957345225391607075)
                ·
                  refine ⟨10576036436017838087410613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050690957345225391607075 10576036436017838087410613)
                  ·
                    refine ⟨991503415876672320694745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10576036436017838087410613 991503415876672320694745)
                    ·
                      rfl

theorem cell22_2896419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5].length) (baseStart_2896419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896419 prefixEnd_2896419 := by exact prefixLift 2896419
  have htrace : WordTrace (prefixWord ++ tailWord_2896419) baseStart_2896419 baseEnd_2896419 := by
    simpa [prefixWord, tailWord_2896419, baseEnd_2896419] using wordTrace_append hprefix tailTrace_2896419
  have hstable : (prefixWord ++ tailWord_2896419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896419).length < 2 ^ (prefixWord ++ tailWord_2896419).sum := by decide
  have hdescent : baseEnd_2896419 < baseStart_2896419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896423 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2896423 : Nat := 118140960795 + 2896423 * 2 ^ 59
def prefixEnd_2896423 : Nat := 4983230072969 + 3 ^ 40 * 2896423 * 2
def baseEnd_2896423 : Nat := 991504785158417643594733

theorem tailTrace_2896423 : CollatzResearch.WordTrace tailWord_2896423 prefixEnd_2896423 991504785158417643594733 := by
  unfold tailWord_2896423
  simp only [CollatzResearch.WordTrace]
  refine ⟨105641225585761615510845923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70427483723841077007230615 105641225585761615510845923)
  ·
    refine ⟨158461838378642423266268885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105641225585761615510845923 158461838378642423266268885)
    ·
      refine ⟨3713949336999431795303177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158461838378642423266268885 3713949336999431795303177)
      ·
        refine ⟨2785462002749573846477383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713949336999431795303177 2785462002749573846477383)
        ·
          refine ⟨4178193004124360769716075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785462002749573846477383 4178193004124360769716075)
          ·
            refine ⟨6267289506186541154574113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178193004124360769716075 6267289506186541154574113)
            ·
              refine ⟨4700467129639905865930585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267289506186541154574113 4700467129639905865930585)
              ·
                refine ⟨3525350347229929399447939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700467129639905865930585 3525350347229929399447939)
                ·
                  refine ⟨5288025520844894099171909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525350347229929399447939 5288025520844894099171909)
                  ·
                    refine ⟨991504785158417643594733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288025520844894099171909 991504785158417643594733)
                    ·
                      rfl

theorem cell22_2896423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2896423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896423 prefixEnd_2896423 := by exact prefixLift 2896423
  have htrace : WordTrace (prefixWord ++ tailWord_2896423) baseStart_2896423 baseEnd_2896423 := by
    simpa [prefixWord, tailWord_2896423, baseEnd_2896423] using wordTrace_append hprefix tailTrace_2896423
  have hstable : (prefixWord ++ tailWord_2896423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896423).length < 2 ^ (prefixWord ++ tailWord_2896423).sum := by decide
  have hdescent : baseEnd_2896423 < baseStart_2896423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896432 : List Nat := [2, 1, 1, 1, 2, 3, 6, 6]
def baseStart_2896432 : Nat := 118140960795 + 2896432 * 2 ^ 59
def prefixEnd_2896432 : Nat := 4983230072969 + 3 ^ 40 * 2896432 * 2
def baseEnd_2896432 : Nat := 110167540671371624457745

theorem tailTrace_2896432 : CollatzResearch.WordTrace tailWord_2896432 prefixEnd_2896432 110167540671371624457745 := by
  unfold tailWord_2896432
  simp only [CollatzResearch.WordTrace]
  refine ⟨52820776921364505023961775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70427702561819340031949033 52820776921364505023961775)
  ·
    refine ⟨79231165382046757535942663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52820776921364505023961775 79231165382046757535942663)
    ·
      refine ⟨118846748073070136303913995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79231165382046757535942663 118846748073070136303913995)
      ·
        refine ⟨178270122109605204455870993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118846748073070136303913995 178270122109605204455870993)
        ·
          refine ⟨133702591582203903341903245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178270122109605204455870993 133702591582203903341903245)
          ·
            refine ⟨50138471843326463753213717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133702591582203903341903245 50138471843326463753213717)
            ·
              refine ⟨2350240867655927988431893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50138471843326463753213717 2350240867655927988431893)
              ·
                refine ⟨110167540671371624457745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2350240867655927988431893 110167540671371624457745)
                ·
                  rfl

theorem cell22_2896432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_2896432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896432 prefixEnd_2896432 := by exact prefixLift 2896432
  have htrace : WordTrace (prefixWord ++ tailWord_2896432) baseStart_2896432 baseEnd_2896432 := by
    simpa [prefixWord, tailWord_2896432, baseEnd_2896432] using wordTrace_append hprefix tailTrace_2896432
  have hstable : (prefixWord ++ tailWord_2896432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896432).length < 2 ^ (prefixWord ++ tailWord_2896432).sum := by decide
  have hdescent : baseEnd_2896432 < baseStart_2896432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896438 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2896438 : Nat := 118140960795 + 2896438 * 2 ^ 59
def prefixEnd_2896438 : Nat := 4983230072969 + 3 ^ 40 * 2896438 * 2
def baseEnd_2896438 : Nat := 330503306654987534823229

theorem tailTrace_2896438 : CollatzResearch.WordTrace tailWord_2896438 prefixEnd_2896438 330503306654987534823229 := by
  unfold tailWord_2896438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6602610792544204567040123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70427848453804848715094645 6602610792544204567040123)
  ·
    refine ⟨9903916188816306850560185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6602610792544204567040123 9903916188816306850560185)
    ·
      refine ⟨7427937141612230137920139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9903916188816306850560185 7427937141612230137920139)
      ·
        refine ⟨11141905712418345206880209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7427937141612230137920139 11141905712418345206880209)
        ·
          refine ⟨8356429284313758905160157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11141905712418345206880209 8356429284313758905160157)
          ·
            refine ⟨3133660981617659589435059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8356429284313758905160157 3133660981617659589435059)
            ·
              refine ⟨4700491472426489384152589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133660981617659589435059 4700491472426489384152589)
              ·
                refine ⟨1762684302159933519057221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4700491472426489384152589 1762684302159933519057221)
                ·
                  refine ⟨330503306654987534823229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1762684302159933519057221 330503306654987534823229)
                  ·
                    rfl

theorem cell22_2896438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2896438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896438 prefixEnd_2896438 := by exact prefixLift 2896438
  have htrace : WordTrace (prefixWord ++ tailWord_2896438) baseStart_2896438 baseEnd_2896438 := by
    simpa [prefixWord, tailWord_2896438, baseEnd_2896438] using wordTrace_append hprefix tailTrace_2896438
  have hstable : (prefixWord ++ tailWord_2896438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896438).length < 2 ^ (prefixWord ++ tailWord_2896438).sum := by decide
  have hdescent : baseEnd_2896438 < baseStart_2896438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896558 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2896558 : Nat := 118140960795 + 2896558 * 2 ^ 59
def prefixEnd_2896558 : Nat := 4983230072969 + 3 ^ 40 * 2896558 * 2
def baseEnd_2896558 : Nat := 991550998417322291469319

theorem tailTrace_2896558 : CollatzResearch.WordTrace tailWord_2896558 prefixEnd_2896558 991550998417322291469319 := by
  unfold tailWord_2896558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13205768680034066695876291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70430766293515022378006885 13205768680034066695876291)
  ·
    refine ⟨19808653020051100043814437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13205768680034066695876291 19808653020051100043814437)
    ·
      refine ⟨3714122441259581258215207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19808653020051100043814437 3714122441259581258215207)
      ·
        refine ⟨5571183661889371887322811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3714122441259581258215207 5571183661889371887322811)
        ·
          refine ⟨8356775492834057830984217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571183661889371887322811 8356775492834057830984217)
          ·
            refine ⟨6267581619625543373238163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8356775492834057830984217 6267581619625543373238163)
            ·
              refine ⟨9401372429438315059857245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267581619625543373238163 9401372429438315059857245)
              ·
                refine ⟨3525514661039368147446467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9401372429438315059857245 3525514661039368147446467)
                ·
                  refine ⟨5288271991559052221169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525514661039368147446467 5288271991559052221169701)
                  ·
                    refine ⟨991550998417322291469319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288271991559052221169701 991550998417322291469319)
                    ·
                      rfl

theorem cell22_2896558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2896558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896558 prefixEnd_2896558 := by exact prefixLift 2896558
  have htrace : WordTrace (prefixWord ++ tailWord_2896558) baseStart_2896558 baseEnd_2896558 := by
    simpa [prefixWord, tailWord_2896558, baseEnd_2896558] using wordTrace_append hprefix tailTrace_2896558
  have hstable : (prefixWord ++ tailWord_2896558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896558).length < 2 ^ (prefixWord ++ tailWord_2896558).sum := by decide
  have hdescent : baseEnd_2896558 < baseStart_2896558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896644 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2896644 : Nat := 118140960795 + 2896644 * 2 ^ 59
def prefixEnd_2896644 : Nat := 4983230072969 + 3 ^ 40 * 2896644 * 2
def baseEnd_2896644 : Nat := 991580437974846733819055

theorem tailTrace_2896644 : CollatzResearch.WordTrace tailWord_2896644 prefixEnd_2896644 991580437974846733819055 := by
  unfold tailWord_2896644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52824643058980485127320493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70432857411973980169760657 52824643058980485127320493)
  ·
    refine ⟨19809241147117681922745185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52824643058980485127320493 19809241147117681922745185)
    ·
      refine ⟨14856930860338261442058889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19809241147117681922745185 14856930860338261442058889)
      ·
        refine ⟨11142698145253696081544167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14856930860338261442058889 11142698145253696081544167)
        ·
          refine ⟨16714047217880544122316251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11142698145253696081544167 16714047217880544122316251)
          ·
            refine ⟨25071070826820816183474377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16714047217880544122316251 25071070826820816183474377)
            ·
              refine ⟨18803303120115612137605783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25071070826820816183474377 18803303120115612137605783)
              ·
                refine ⟨28204954680173418206408675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18803303120115612137605783 28204954680173418206408675)
                ·
                  refine ⟨42307432020260127309613013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28204954680173418206408675 42307432020260127309613013)
                  ·
                    refine ⟨991580437974846733819055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42307432020260127309613013 991580437974846733819055)
                    ·
                      rfl

theorem cell22_2896644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2896644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896644 prefixEnd_2896644 := by exact prefixLift 2896644
  have htrace : WordTrace (prefixWord ++ tailWord_2896644) baseStart_2896644 baseEnd_2896644 := by
    simpa [prefixWord, tailWord_2896644, baseEnd_2896644] using wordTrace_append hprefix tailTrace_2896644
  have hstable : (prefixWord ++ tailWord_2896644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896644).length < 2 ^ (prefixWord ++ tailWord_2896644).sum := by decide
  have hdescent : baseEnd_2896644 < baseStart_2896644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896659 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_2896659 : Nat := 118140960795 + 2896659 * 2 ^ 59
def prefixEnd_2896659 : Nat := 4983230072969 + 3 ^ 40 * 2896659 * 2
def baseEnd_2896659 : Nat := 991585572781391694694009

theorem tailTrace_2896659 : CollatzResearch.WordTrace tailWord_2896659 prefixEnd_2896659 991585572781391694694009 := by
  unfold tailWord_2896659
  simp only [CollatzResearch.WordTrace]
  refine ⟨105649833212906627816437031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70433222141937751877624687 105649833212906627816437031)
  ·
    refine ⟨158474749819359941724655547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105649833212906627816437031 158474749819359941724655547)
    ·
      refine ⟨237712124729039912586983321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158474749819359941724655547 237712124729039912586983321)
      ·
        refine ⟨178284093546779934440237491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237712124729039912586983321 178284093546779934440237491)
        ·
          refine ⟨267426140320169901660356237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178284093546779934440237491 267426140320169901660356237)
          ·
            refine ⟨100284802620063713122633589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267426140320169901660356237 100284802620063713122633589)
            ·
              refine ⟨9401700245630973105246899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100284802620063713122633589 9401700245630973105246899)
              ·
                refine ⟨14102550368446459657870349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9401700245630973105246899 14102550368446459657870349)
                ·
                  refine ⟨5288456388167422371701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14102550368446459657870349 5288456388167422371701381)
                  ·
                    refine ⟨991585572781391694694009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288456388167422371701381 991585572781391694694009)
                    ·
                      rfl

theorem cell22_2896659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_2896659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896659 prefixEnd_2896659 := by exact prefixLift 2896659
  have htrace : WordTrace (prefixWord ++ tailWord_2896659) baseStart_2896659 baseEnd_2896659 := by
    simpa [prefixWord, tailWord_2896659, baseEnd_2896659] using wordTrace_append hprefix tailTrace_2896659
  have hstable : (prefixWord ++ tailWord_2896659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896659).length < 2 ^ (prefixWord ++ tailWord_2896659).sum := by decide
  have hdescent : baseEnd_2896659 < baseStart_2896659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896689 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2896689 : Nat := 118140960795 + 2896689 * 2 ^ 59
def prefixEnd_2896689 : Nat := 4983230072969 + 3 ^ 40 * 2896689 * 2
def baseEnd_2896689 : Nat := 991595842394481616443917

theorem tailTrace_2896689 : CollatzResearch.WordTrace tailWord_2896689 prefixEnd_2896689 991595842394481616443917 := by
  unfold tailWord_2896689
  simp only [CollatzResearch.WordTrace]
  refine ⟨105650927402797942940029121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70433951601865295293352747 105650927402797942940029121)
  ·
    refine ⟨79238195552098457205021841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105650927402797942940029121 79238195552098457205021841)
    ·
      refine ⟨59428646664073842903766381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79238195552098457205021841 59428646664073842903766381)
      ·
        refine ⟨22285742499027691088912393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59428646664073842903766381 22285742499027691088912393)
        ·
          refine ⟨16714306874270768316684295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22285742499027691088912393 16714306874270768316684295)
          ·
            refine ⟨25071460311406152475026443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16714306874270768316684295 25071460311406152475026443)
            ·
              refine ⟨37607190467109228712539665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25071460311406152475026443 37607190467109228712539665)
              ·
                refine ⟨28205392850331921534404749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37607190467109228712539665 28205392850331921534404749)
                ·
                  refine ⟨10577022318874470575401781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28205392850331921534404749 10577022318874470575401781)
                  ·
                    refine ⟨991595842394481616443917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10577022318874470575401781 991595842394481616443917)
                    ·
                      rfl

theorem cell22_2896689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2896689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896689 prefixEnd_2896689 := by exact prefixLift 2896689
  have htrace : WordTrace (prefixWord ++ tailWord_2896689) baseStart_2896689 baseEnd_2896689 := by
    simpa [prefixWord, tailWord_2896689, baseEnd_2896689] using wordTrace_append hprefix tailTrace_2896689
  have hstable : (prefixWord ++ tailWord_2896689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896689).length < 2 ^ (prefixWord ++ tailWord_2896689).sum := by decide
  have hdescent : baseEnd_2896689 < baseStart_2896689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896704 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_2896704 : Nat := 118140960795 + 2896704 * 2 ^ 59
def prefixEnd_2896704 : Nat := 4983230072969 + 3 ^ 40 * 2896704 * 2
def baseEnd_2896704 : Nat := 991600977201026577318871

theorem tailTrace_2896704 : CollatzResearch.WordTrace tailWord_2896704 prefixEnd_2896704 991600977201026577318871 := by
  unfold tailWord_2896704
  simp only [CollatzResearch.WordTrace]
  refine ⟨52825737248871800250912583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70434316331829067001216777 52825737248871800250912583)
  ·
    refine ⟨79238605873307700376368875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52825737248871800250912583 79238605873307700376368875)
    ·
      refine ⟨118857908809961550564553313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79238605873307700376368875 118857908809961550564553313)
      ·
        refine ⟨89143431607471162923414985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118857908809961550564553313 89143431607471162923414985)
        ·
          refine ⟨66857573705603372192561239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89143431607471162923414985 66857573705603372192561239)
          ·
            refine ⟨100286360558405058288841859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66857573705603372192561239 100286360558405058288841859)
            ·
              refine ⟨150429540837607587433262789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100286360558405058288841859 150429540837607587433262789)
              ·
                refine ⟨28205538907051422643736773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150429540837607587433262789 28205538907051422643736773)
                ·
                  refine ⟨5288538545072141745700645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28205538907051422643736773 5288538545072141745700645)
                  ·
                    refine ⟨991600977201026577318871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288538545072141745700645 991600977201026577318871)
                    ·
                      rfl

theorem cell22_2896704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_2896704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896704 prefixEnd_2896704 := by exact prefixLift 2896704
  have htrace : WordTrace (prefixWord ++ tailWord_2896704) baseStart_2896704 baseEnd_2896704 := by
    simpa [prefixWord, tailWord_2896704, baseEnd_2896704] using wordTrace_append hprefix tailTrace_2896704
  have hstable : (prefixWord ++ tailWord_2896704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896704).length < 2 ^ (prefixWord ++ tailWord_2896704).sum := by decide
  have hdescent : baseEnd_2896704 < baseStart_2896704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896721 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_2896721 : Nat := 118140960795 + 2896721 * 2 ^ 59
def prefixEnd_2896721 : Nat := 4983230072969 + 3 ^ 40 * 2896721 * 2
def baseEnd_2896721 : Nat := 991606796648444199643819

theorem tailTrace_2896721 : CollatzResearch.WordTrace tailWord_2896721 prefixEnd_2896721 991606796648444199643819 := by
  unfold tailWord_2896721
  simp only [CollatzResearch.WordTrace]
  refine ⟨105652094538682012405194017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70434729692454674936796011 105652094538682012405194017)
  ·
    refine ⟨79239070904011509303895513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105652094538682012405194017 79239070904011509303895513)
    ·
      refine ⟨59429303178008631977921635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79239070904011509303895513 59429303178008631977921635)
      ·
        refine ⟨89143954767012947966882453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59429303178008631977921635 89143954767012947966882453)
        ·
          refine ⟨4178622879703731935947615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89143954767012947966882453 4178622879703731935947615)
          ·
            refine ⟨6267934319555597903921423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178622879703731935947615 6267934319555597903921423)
            ·
              refine ⟨9401901479333396855882135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267934319555597903921423 9401901479333396855882135)
              ·
                refine ⟨14102852219000095283823203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9401901479333396855882135 14102852219000095283823203)
                ·
                  refine ⟨21154278328500142925734805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14102852219000095283823203 21154278328500142925734805)
                  ·
                    refine ⟨991606796648444199643819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21154278328500142925734805 991606796648444199643819)
                    ·
                      rfl

theorem cell22_2896721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_2896721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896721 prefixEnd_2896721 := by exact prefixLift 2896721
  have htrace : WordTrace (prefixWord ++ tailWord_2896721) baseStart_2896721 baseEnd_2896721 := by
    simpa [prefixWord, tailWord_2896721, baseEnd_2896721] using wordTrace_append hprefix tailTrace_2896721
  have hstable : (prefixWord ++ tailWord_2896721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896721).length < 2 ^ (prefixWord ++ tailWord_2896721).sum := by decide
  have hdescent : baseEnd_2896721 < baseStart_2896721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896740 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2896740 : Nat := 118140960795 + 2896740 * 2 ^ 59
def prefixEnd_2896740 : Nat := 4983230072969 + 3 ^ 40 * 2896740 * 2
def baseEnd_2896740 : Nat := 991613300736734483418761

theorem tailTrace_2896740 : CollatzResearch.WordTrace tailWord_2896740 prefixEnd_2896740 991613300736734483418761 := by
  unfold tailWord_2896740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52826393762806589325067837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70435191683742119100090449 52826393762806589325067837)
  ·
    refine ⟨19809897661052470996900439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52826393762806589325067837 19809897661052470996900439)
    ·
      refine ⟨29714846491578706495350659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19809897661052470996900439 29714846491578706495350659)
      ·
        refine ⟨44572269737368059743025989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29714846491578706495350659 44572269737368059743025989)
        ·
          refine ⟨8357300575756511201817373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44572269737368059743025989 8357300575756511201817373)
          ·
            refine ⟨3133987715908691700681515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8357300575756511201817373 3133987715908691700681515)
            ·
              refine ⟨4700981573863037551022273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133987715908691700681515 4700981573863037551022273)
              ·
                refine ⟨3525736180397278163266705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700981573863037551022273 3525736180397278163266705)
                ·
                  refine ⟨2644302135297958622450029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3525736180397278163266705 2644302135297958622450029)
                  ·
                    refine ⟨991613300736734483418761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644302135297958622450029 991613300736734483418761)
                    ·
                      rfl

theorem cell22_2896740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2896740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896740 prefixEnd_2896740 := by exact prefixLift 2896740
  have htrace : WordTrace (prefixWord ++ tailWord_2896740) baseStart_2896740 baseEnd_2896740 := by
    simpa [prefixWord, tailWord_2896740, baseEnd_2896740] using wordTrace_append hprefix tailTrace_2896740
  have hstable : (prefixWord ++ tailWord_2896740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896740).length < 2 ^ (prefixWord ++ tailWord_2896740).sum := by decide
  have hdescent : baseEnd_2896740 < baseStart_2896740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896770 : List Nat := [3, 4, 2, 2, 1, 1, 1, 8]
def baseStart_2896770 : Nat := 118140960795 + 2896770 * 2 ^ 59
def prefixEnd_2896770 : Nat := 4983230072969 + 3 ^ 40 * 2896770 * 2
def baseEnd_2896770 : Nat := 110180396705536045018741

theorem tailTrace_2896770 : CollatzResearch.WordTrace tailWord_2896770 prefixEnd_2896770 110180396705536045018741 := by
  unfold tailWord_2896770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413470428876123443431941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70435921143669662515818509 26413470428876123443431941)
  ·
    refine ⟨4952525705414273145643489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26413470428876123443431941 4952525705414273145643489)
    ·
      refine ⟨3714394279060704859232617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4952525705414273145643489 3714394279060704859232617)
      ·
        refine ⟨2785795709295528644424463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714394279060704859232617 2785795709295528644424463)
        ·
          refine ⟨4178693563943292966636695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785795709295528644424463 4178693563943292966636695)
          ·
            refine ⟨6268040345914939449955043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178693563943292966636695 6268040345914939449955043)
            ·
              refine ⟨9402060518872409174932565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268040345914939449955043 9402060518872409174932565)
              ·
                refine ⟨110180396705536045018741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9402060518872409174932565 110180396705536045018741)
                ·
                  rfl

theorem cell22_2896770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_2896770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896770 prefixEnd_2896770 := by exact prefixLift 2896770
  have htrace : WordTrace (prefixWord ++ tailWord_2896770) baseStart_2896770 baseEnd_2896770 := by
    simpa [prefixWord, tailWord_2896770, baseEnd_2896770] using wordTrace_append hprefix tailTrace_2896770
  have hstable : (prefixWord ++ tailWord_2896770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896770).length < 2 ^ (prefixWord ++ tailWord_2896770).sum := by decide
  have hdescent : baseEnd_2896770 < baseStart_2896770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896779 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_2896779 : Nat := 118140960795 + 2896779 * 2 ^ 59
def prefixEnd_2896779 : Nat := 4983230072969 + 3 ^ 40 * 2896779 * 2
def baseEnd_2896779 : Nat := 991626651233751381693641

theorem tailTrace_2896779 : CollatzResearch.WordTrace tailWord_2896779 prefixEnd_2896779 991626651233751381693641 := by
  unfold tailWord_2896779
  simp only [CollatzResearch.WordTrace]
  refine ⟨105654209972471888310805391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70436139981647925540536927 105654209972471888310805391)
  ·
    refine ⟨158481314958707832466208087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105654209972471888310805391 158481314958707832466208087)
    ·
      refine ⟨237721972438061748699312131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158481314958707832466208087 237721972438061748699312131)
      ·
        refine ⟨356582958657092623048968197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237721972438061748699312131 356582958657092623048968197)
        ·
          refine ⟨66859304748204866821681537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356582958657092623048968197 66859304748204866821681537)
          ·
            refine ⟨50144478561153650116261153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66859304748204866821681537 50144478561153650116261153)
            ·
              refine ⟨37608358920865237587195865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50144478561153650116261153 37608358920865237587195865)
              ·
                refine ⟨28206269190648928190396899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37608358920865237587195865 28206269190648928190396899)
                ·
                  refine ⟨42309403785973392285595349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28206269190648928190396899 42309403785973392285595349)
                  ·
                    refine ⟨991626651233751381693641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42309403785973392285595349 991626651233751381693641)
                    ·
                      rfl

theorem cell22_2896779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_2896779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896779 prefixEnd_2896779 := by exact prefixLift 2896779
  have htrace : WordTrace (prefixWord ++ tailWord_2896779) baseStart_2896779 baseEnd_2896779 := by
    simpa [prefixWord, tailWord_2896779, baseEnd_2896779] using wordTrace_append hprefix tailTrace_2896779
  have hstable : (prefixWord ++ tailWord_2896779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896779).length < 2 ^ (prefixWord ++ tailWord_2896779).sum := by decide
  have hdescent : baseEnd_2896779 < baseStart_2896779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896903 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2896903 : Nat := 118140960795 + 2896903 * 2 ^ 59
def prefixEnd_2896903 : Nat := 4983230072969 + 3 ^ 40 * 2896903 * 2
def baseEnd_2896903 : Nat := 991669098967856391593261

theorem tailTrace_2896903 : CollatzResearch.WordTrace tailWord_2896903 prefixEnd_2896903 991669098967856391593261 := by
  unfold tailWord_2896903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105658732624022657488319363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70439155082681771658879575 105658732624022657488319363)
  ·
    refine ⟨158488098936033986232479045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105658732624022657488319363 158488098936033986232479045)
    ·
      refine ⟨29716518550506372418589821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158488098936033986232479045 29716518550506372418589821)
      ·
        refine ⟨11143694456439889656971183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29716518550506372418589821 11143694456439889656971183)
        ·
          refine ⟨16715541684659834485456775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143694456439889656971183 16715541684659834485456775)
          ·
            refine ⟨25073312526989751728185163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16715541684659834485456775 25073312526989751728185163)
            ·
              refine ⟨37609968790484627592277745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25073312526989751728185163 37609968790484627592277745)
              ·
                refine ⟨28207476592863470694208309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37609968790484627592277745 28207476592863470694208309)
                ·
                  refine ⟨2644450930580950377582029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28207476592863470694208309 2644450930580950377582029)
                  ·
                    refine ⟨991669098967856391593261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644450930580950377582029 991669098967856391593261)
                    ·
                      rfl

theorem cell22_2896903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2896903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896903 prefixEnd_2896903 := by exact prefixLift 2896903
  have htrace : WordTrace (prefixWord ++ tailWord_2896903) baseStart_2896903 baseEnd_2896903 := by
    simpa [prefixWord, tailWord_2896903, baseEnd_2896903] using wordTrace_append hprefix tailTrace_2896903
  have hstable : (prefixWord ++ tailWord_2896903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896903).length < 2 ^ (prefixWord ++ tailWord_2896903).sum := by decide
  have hdescent : baseEnd_2896903 < baseStart_2896903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896920 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_2896920 : Nat := 118140960795 + 2896920 * 2 ^ 59
def prefixEnd_2896920 : Nat := 4983230072969 + 3 ^ 40 * 2896920 * 2
def baseEnd_2896920 : Nat := 991674918415274013918209

theorem tailTrace_2896920 : CollatzResearch.WordTrace tailWord_2896920 prefixEnd_2896920 991674918415274013918209 := by
  unfold tailWord_2896920
  simp only [CollatzResearch.WordTrace]
  refine ⟨52829676332480534695844107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70439568443307379594458809 52829676332480534695844107)
  ·
    refine ⟨79244514498720802043766161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52829676332480534695844107 79244514498720802043766161)
    ·
      refine ⟨59433385874040601532824621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79244514498720802043766161 59433385874040601532824621)
      ·
        refine ⟨22287519702765225574809233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59433385874040601532824621 22287519702765225574809233)
        ·
          refine ⟨16715639777073919181106925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22287519702765225574809233 16715639777073919181106925)
          ·
            refine ⟨6268364916402719692915097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16715639777073919181106925 6268364916402719692915097)
            ·
              refine ⟨4701273687302039769686323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6268364916402719692915097 4701273687302039769686323)
              ·
                refine ⟨7051910530953059654529485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701273687302039769686323 7051910530953059654529485)
                ·
                  refine ⟨2644466449107397370448557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7051910530953059654529485 2644466449107397370448557)
                  ·
                    refine ⟨991674918415274013918209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644466449107397370448557 991674918415274013918209)
                    ·
                      rfl

theorem cell22_2896920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_2896920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896920 prefixEnd_2896920 := by exact prefixLift 2896920
  have htrace : WordTrace (prefixWord ++ tailWord_2896920) baseStart_2896920 baseEnd_2896920 := by
    simpa [prefixWord, tailWord_2896920, baseEnd_2896920] using wordTrace_append hprefix tailTrace_2896920
  have hstable : (prefixWord ++ tailWord_2896920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896920).length < 2 ^ (prefixWord ++ tailWord_2896920).sum := by decide
  have hdescent : baseEnd_2896920 < baseStart_2896920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896963 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 1, 4]
def baseStart_2896963 : Nat := 118140960795 + 2896963 * 2 ^ 59
def prefixEnd_2896963 : Nat := 4983230072969 + 3 ^ 40 * 2896963 * 2
def baseEnd_2896963 : Nat := 991689638194036235093077

theorem tailTrace_2896963 : CollatzResearch.WordTrace tailWord_2896963 prefixEnd_2896963 991689638194036235093077 := by
  unfold tailWord_2896963
  simp only [CollatzResearch.WordTrace]
  refine ⟨105660921003805287735503543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70440614002536858490335695 105660921003805287735503543)
  ·
    refine ⟨158491381505707931603255315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105660921003805287735503543 158491381505707931603255315)
    ·
      refine ⟨237737072258561897404882973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158491381505707931603255315 237737072258561897404882973)
      ·
        refine ⟨89151402096960711526831115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237737072258561897404882973 89151402096960711526831115)
        ·
          refine ⟨133727103145441067290246673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89151402096960711526831115 133727103145441067290246673)
          ·
            refine ⟨100295327359080800467685005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133727103145441067290246673 100295327359080800467685005)
            ·
              refine ⟨37610747759655300175381877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100295327359080800467685005 37610747759655300175381877)
              ·
                refine ⟨3526007602467684391442051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37610747759655300175381877 3526007602467684391442051)
                ·
                  refine ⟨5289011403701526587163077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526007602467684391442051 5289011403701526587163077)
                  ·
                    refine ⟨991689638194036235093077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289011403701526587163077 991689638194036235093077)
                    ·
                      rfl

theorem cell22_2896963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4].length) (baseStart_2896963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2896963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2896963 prefixEnd_2896963 := by exact prefixLift 2896963
  have htrace : WordTrace (prefixWord ++ tailWord_2896963) baseStart_2896963 baseEnd_2896963 := by
    simpa [prefixWord, tailWord_2896963, baseEnd_2896963] using wordTrace_append hprefix tailTrace_2896963
  have hstable : (prefixWord ++ tailWord_2896963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896963).length < 2 ^ (prefixWord ++ tailWord_2896963).sum := by decide
  have hdescent : baseEnd_2896963 < baseStart_2896963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897022 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2897022 : Nat := 118140960795 + 2897022 * 2 ^ 59
def prefixEnd_2897022 : Nat := 4983230072969 + 3 ^ 40 * 2897022 * 2
def baseEnd_2897022 : Nat := 991709835099779747867897

theorem tailTrace_2897022 : CollatzResearch.WordTrace tailWord_2897022 prefixEnd_2897022 991709835099779747867897 := by
  unfold tailWord_2897022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13207884113823942601487665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70442048607061027207934213 13207884113823942601487665)
  ·
    refine ⟨9905913085367956951115749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13207884113823942601487665 9905913085367956951115749)
    ·
      refine ⟨1857358703506491928334203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9905913085367956951115749 1857358703506491928334203)
      ·
        refine ⟨2786038055259737892501305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857358703506491928334203 2786038055259737892501305)
        ·
          refine ⟨2089528541444803419375979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2786038055259737892501305 2089528541444803419375979)
          ·
            refine ⟨3134292812167205129063969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089528541444803419375979 3134292812167205129063969)
            ·
              refine ⟨2350719609125403846797977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134292812167205129063969 2350719609125403846797977)
              ·
                refine ⟨1763039706844052885098483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350719609125403846797977 1763039706844052885098483)
                ·
                  refine ⟨2644559560266079327647725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763039706844052885098483 2644559560266079327647725)
                  ·
                    refine ⟨991709835099779747867897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644559560266079327647725 991709835099779747867897)
                    ·
                      rfl

theorem cell22_2897022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2897022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897022 prefixEnd_2897022 := by exact prefixLift 2897022
  have htrace : WordTrace (prefixWord ++ tailWord_2897022) baseStart_2897022 baseEnd_2897022 := by
    simpa [prefixWord, tailWord_2897022, baseEnd_2897022] using wordTrace_append hprefix tailTrace_2897022
  have hstable : (prefixWord ++ tailWord_2897022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897022).length < 2 ^ (prefixWord ++ tailWord_2897022).sum := by decide
  have hdescent : baseEnd_2897022 < baseStart_2897022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897025 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2897025 : Nat := 118140960795 + 2897025 * 2 ^ 59
def prefixEnd_2897025 : Nat := 4983230072969 + 3 ^ 40 * 2897025 * 2
def baseEnd_2897025 : Nat := 991710862061088740042887

theorem tailTrace_2897025 : CollatzResearch.WordTrace tailWord_2897025 prefixEnd_2897025 991710862061088740042887 := by
  unfold tailWord_2897025
  simp only [CollatzResearch.WordTrace]
  refine ⟨105663182329580672324260529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70442121553053781549507019 105663182329580672324260529)
  ·
    refine ⟨79247386747185504243195397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105663182329580672324260529 79247386747185504243195397)
    ·
      refine ⟨14858885015097282045599137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79247386747185504243195397 14858885015097282045599137)
      ·
        refine ⟨11144163761322961534199353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14858885015097282045599137 11144163761322961534199353)
        ·
          refine ⟨8358122820992221150649515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11144163761322961534199353 8358122820992221150649515)
          ·
            refine ⟨12537184231488331725974273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8358122820992221150649515 12537184231488331725974273)
            ·
              refine ⟨9402888173616248794480705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12537184231488331725974273 9402888173616248794480705)
              ·
                refine ⟨7052166130212186595860529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9402888173616248794480705 7052166130212186595860529)
                ·
                  refine ⟨5289124597659139946895397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052166130212186595860529 5289124597659139946895397)
                  ·
                    refine ⟨991710862061088740042887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289124597659139946895397 991710862061088740042887)
                    ·
                      rfl

theorem cell22_2897025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2897025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897025 prefixEnd_2897025 := by exact prefixLift 2897025
  have htrace : WordTrace (prefixWord ++ tailWord_2897025) baseStart_2897025 baseEnd_2897025 := by
    simpa [prefixWord, tailWord_2897025, baseEnd_2897025] using wordTrace_append hprefix tailTrace_2897025
  have hstable : (prefixWord ++ tailWord_2897025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897025).length < 2 ^ (prefixWord ++ tailWord_2897025).sum := by decide
  have hdescent : baseEnd_2897025 < baseStart_2897025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897029 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 4]
def baseStart_2897029 : Nat := 118140960795 + 2897029 * 2 ^ 59
def prefixEnd_2897029 : Nat := 4983230072969 + 3 ^ 40 * 2897029 * 2
def baseEnd_2897029 : Nat := 330570743780944687647625

theorem tailTrace_2897029 : CollatzResearch.WordTrace tailWord_2897029 prefixEnd_2897029 330570743780944687647625 := by
  unfold tailWord_2897029
  simp only [CollatzResearch.WordTrace]
  refine ⟨105663328221566181007406141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70442218814377454004937427 105663328221566181007406141)
  ·
    refine ⟨39623748083087317877777303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105663328221566181007406141 39623748083087317877777303)
    ·
      refine ⟨59435622124630976816665955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39623748083087317877777303 59435622124630976816665955)
      ·
        refine ⟨89153433186946465224998933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59435622124630976816665955 89153433186946465224998933)
        ·
          refine ⟨4179067180638115557421825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89153433186946465224998933 4179067180638115557421825)
          ·
            refine ⟨3134300385478586668066369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179067180638115557421825 3134300385478586668066369)
            ·
              refine ⟨2350725289108940001049777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134300385478586668066369 2350725289108940001049777)
              ·
                refine ⟨1763043966831705000787333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350725289108940001049777 1763043966831705000787333)
                ·
                  refine ⟨330570743780944687647625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763043966831705000787333 330570743780944687647625)
                  ·
                    rfl

theorem cell22_2897029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_2897029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897029 prefixEnd_2897029 := by exact prefixLift 2897029
  have htrace : WordTrace (prefixWord ++ tailWord_2897029) baseStart_2897029 baseEnd_2897029 := by
    simpa [prefixWord, tailWord_2897029, baseEnd_2897029] using wordTrace_append hprefix tailTrace_2897029
  have hstable : (prefixWord ++ tailWord_2897029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897029).length < 2 ^ (prefixWord ++ tailWord_2897029).sum := by decide
  have hdescent : baseEnd_2897029 < baseStart_2897029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897053 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2897053 : Nat := 118140960795 + 2897053 * 2 ^ 59
def prefixEnd_2897053 : Nat := 4983230072969 + 3 ^ 40 * 2897053 * 2
def baseEnd_2897053 : Nat := 991720447033306000342801

theorem tailTrace_2897053 : CollatzResearch.WordTrace tailWord_2897053 prefixEnd_2897053 991720447033306000342801 := by
  unfold tailWord_2897053
  simp only [CollatzResearch.WordTrace]
  refine ⟨105664203573479233106279813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70442802382319488737519875 105664203573479233106279813)
  ·
    refine ⟨19812038170027356207427465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105664203573479233106279813 19812038170027356207427465)
    ·
      refine ⟨14859028627520517155570599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19812038170027356207427465 14859028627520517155570599)
      ·
        refine ⟨22288542941280775733355899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14859028627520517155570599 22288542941280775733355899)
        ·
          refine ⟨33432814411921163600033849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22288542941280775733355899 33432814411921163600033849)
          ·
            refine ⟨25074610808940872700025387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33432814411921163600033849 25074610808940872700025387)
            ·
              refine ⟨37611916213411309050038081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25074610808940872700025387 37611916213411309050038081)
              ·
                refine ⟨28208937160058481787528561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37611916213411309050038081 28208937160058481787528561)
                ·
                  refine ⟨21156702870043861340646421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28208937160058481787528561 21156702870043861340646421)
                  ·
                    refine ⟨991720447033306000342801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21156702870043861340646421 991720447033306000342801)
                    ·
                      rfl

theorem cell22_2897053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2897053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897053 prefixEnd_2897053 := by exact prefixLift 2897053
  have htrace : WordTrace (prefixWord ++ tailWord_2897053) baseStart_2897053 baseEnd_2897053 := by
    simpa [prefixWord, tailWord_2897053, baseEnd_2897053] using wordTrace_append hprefix tailTrace_2897053
  have hstable : (prefixWord ++ tailWord_2897053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897053).length < 2 ^ (prefixWord ++ tailWord_2897053).sum := by decide
  have hdescent : baseEnd_2897053 < baseStart_2897053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897078 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2897078 : Nat := 118140960795 + 2897078 * 2 ^ 59
def prefixEnd_2897078 : Nat := 4983230072969 + 3 ^ 40 * 2897078 * 2
def baseEnd_2897078 : Nat := 991729005044214268467725

theorem tailTrace_2897078 : CollatzResearch.WordTrace tailWord_2897078 prefixEnd_2897078 991729005044214268467725 := by
  unfold tailWord_2897078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604069712399291398496243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70443410265592441583959925 6604069712399291398496243)
  ·
    refine ⟨9906104568598937097744365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6604069712399291398496243 9906104568598937097744365)
    ·
      refine ⟨3714789213224601411654137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9906104568598937097744365 3714789213224601411654137)
      ·
        refine ⟨2786091909918451058740603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714789213224601411654137 2786091909918451058740603)
        ·
          refine ⟨4179137864877676588110905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786091909918451058740603 4179137864877676588110905)
          ·
            refine ⟨3134353398658257441083179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179137864877676588110905 3134353398658257441083179)
            ·
              refine ⟨4701530097987386161624769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134353398658257441083179 4701530097987386161624769)
              ·
                refine ⟨3526147573490539621218577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4701530097987386161624769 3526147573490539621218577)
                ·
                  refine ⟨2644610680117904715913933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3526147573490539621218577 2644610680117904715913933)
                  ·
                    refine ⟨991729005044214268467725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644610680117904715913933 991729005044214268467725)
                    ·
                      rfl

theorem cell22_2897078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2897078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897078 prefixEnd_2897078 := by exact prefixLift 2897078
  have htrace : WordTrace (prefixWord ++ tailWord_2897078) baseStart_2897078 baseEnd_2897078 := by
    simpa [prefixWord, tailWord_2897078, baseEnd_2897078] using wordTrace_append hprefix tailTrace_2897078
  have hstable : (prefixWord ++ tailWord_2897078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897078).length < 2 ^ (prefixWord ++ tailWord_2897078).sum := by decide
  have hdescent : baseEnd_2897078 < baseStart_2897078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897085 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2897085 : Nat := 118140960795 + 2897085 * 2 ^ 59
def prefixEnd_2897085 : Nat := 4983230072969 + 3 ^ 40 * 2897085 * 2
def baseEnd_2897085 : Nat := 330577133762422861180901

theorem tailTrace_2897085 : CollatzResearch.WordTrace tailWord_2897085 prefixEnd_2897085 330577133762422861180901 := by
  unfold tailWord_2897085
  simp only [CollatzResearch.WordTrace]
  refine ⟨105665370709363302571444709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70443580472908868380963139 105665370709363302571444709)
  ·
    refine ⟨19812257008005619232145883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105665370709363302571444709 19812257008005619232145883)
    ·
      refine ⟨29718385512008428848218825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19812257008005619232145883 29718385512008428848218825)
      ·
        refine ⟨22288789134006321636164119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29718385512008428848218825 22288789134006321636164119)
        ·
          refine ⟨33433183701009482454246179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22288789134006321636164119 33433183701009482454246179)
          ·
            refine ⟨50149775551514223681369269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33433183701009482454246179 50149775551514223681369269)
            ·
              refine ⟨4701541457954458470128369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50149775551514223681369269 4701541457954458470128369)
              ·
                refine ⟨3526156093465843852596277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4701541457954458470128369 3526156093465843852596277)
                ·
                  refine ⟨330577133762422861180901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3526156093465843852596277 330577133762422861180901)
                  ·
                    rfl

theorem cell22_2897085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2897085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897085 prefixEnd_2897085 := by exact prefixLift 2897085
  have htrace : WordTrace (prefixWord ++ tailWord_2897085) baseStart_2897085 baseEnd_2897085 := by
    simpa [prefixWord, tailWord_2897085, baseEnd_2897085] using wordTrace_append hprefix tailTrace_2897085
  have hstable : (prefixWord ++ tailWord_2897085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897085).length < 2 ^ (prefixWord ++ tailWord_2897085).sum := by decide
  have hdescent : baseEnd_2897085 < baseStart_2897085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897089 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2897089 : Nat := 118140960795 + 2897089 * 2 ^ 59
def prefixEnd_2897089 : Nat := 4983230072969 + 3 ^ 40 * 2897089 * 2
def baseEnd_2897089 : Nat := 991732770569013906442691

theorem tailTrace_2897089 : CollatzResearch.WordTrace tailWord_2897089 prefixEnd_2897089 991732770569013906442691 := by
  unfold tailWord_2897089
  simp only [CollatzResearch.WordTrace]
  refine ⟨105665516601348811254590321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70443677734232540836393547 105665516601348811254590321)
  ·
    refine ⟨79249137451011608440942741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105665516601348811254590321 79249137451011608440942741)
    ·
      refine ⟨3714803318016169145669191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79249137451011608440942741 3714803318016169145669191)
      ·
        refine ⟨5572204977024253718503787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3714803318016169145669191 5572204977024253718503787)
        ·
          refine ⟨8358307465536380577755681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572204977024253718503787 8358307465536380577755681)
          ·
            refine ⟨6268730599152285433316761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8358307465536380577755681 6268730599152285433316761)
            ·
              refine ⟨4701547949364214074987571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6268730599152285433316761 4701547949364214074987571)
              ·
                refine ⟨7052321924046321112481357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701547949364214074987571 7052321924046321112481357)
                ·
                  refine ⟨2644620721517370417180509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7052321924046321112481357 2644620721517370417180509)
                  ·
                    refine ⟨991732770569013906442691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644620721517370417180509 991732770569013906442691)
                    ·
                      rfl

theorem cell22_2897089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2897089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897089 prefixEnd_2897089 := by exact prefixLift 2897089
  have htrace : WordTrace (prefixWord ++ tailWord_2897089) baseStart_2897089 baseEnd_2897089 := by
    simpa [prefixWord, tailWord_2897089, baseEnd_2897089] using wordTrace_append hprefix tailTrace_2897089
  have hstable : (prefixWord ++ tailWord_2897089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897089).length < 2 ^ (prefixWord ++ tailWord_2897089).sum := by decide
  have hdescent : baseEnd_2897089 < baseStart_2897089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897140 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2897140 : Nat := 118140960795 + 2897140 * 2 ^ 59
def prefixEnd_2897140 : Nat := 4983230072969 + 3 ^ 40 * 2897140 * 2
def baseEnd_2897140 : Nat := 991750228911266773417535

theorem tailTrace_2897140 : CollatzResearch.WordTrace tailWord_2897140 prefixEnd_2897140 991750228911266773417535 := by
  unfold tailWord_2897140
  simp only [CollatzResearch.WordTrace]
  refine ⟨52833688362082023482348437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70444917816109364643131249 52833688362082023482348437)
  ·
    refine ⟨2476579141972594850735083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52833688362082023482348437 2476579141972594850735083)
    ·
      refine ⟨3714868712958892276102625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476579141972594850735083 3714868712958892276102625)
      ·
        refine ⟨2786151534719169207076969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714868712958892276102625 2786151534719169207076969)
        ·
          refine ⟨2089613651039376905307727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2786151534719169207076969 2089613651039376905307727)
          ·
            refine ⟨3134420476559065357961591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089613651039376905307727 3134420476559065357961591)
            ·
              refine ⟨4701630714838598036942387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134420476559065357961591 4701630714838598036942387)
              ·
                refine ⟨7052446072257897055413581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701630714838598036942387 7052446072257897055413581)
                ·
                  refine ⟨2644667277096711395780093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7052446072257897055413581 2644667277096711395780093)
                  ·
                    refine ⟨991750228911266773417535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644667277096711395780093 991750228911266773417535)
                    ·
                      rfl

theorem cell22_2897140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2897140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897140 prefixEnd_2897140 := by exact prefixLift 2897140
  have htrace : WordTrace (prefixWord ++ tailWord_2897140) baseStart_2897140 baseEnd_2897140 := by
    simpa [prefixWord, tailWord_2897140, baseEnd_2897140] using wordTrace_append hprefix tailTrace_2897140
  have hstable : (prefixWord ++ tailWord_2897140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897140).length < 2 ^ (prefixWord ++ tailWord_2897140).sum := by decide
  have hdescent : baseEnd_2897140 < baseStart_2897140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897145 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_2897145 : Nat := 118140960795 + 2897145 * 2 ^ 59
def prefixEnd_2897145 : Nat := 4983230072969 + 3 ^ 40 * 2897145 * 2
def baseEnd_2897145 : Nat := 991751940513448427042519

theorem tailTrace_2897145 : CollatzResearch.WordTrace tailWord_2897145 prefixEnd_2897145 991751940513448427042519 := by
  unfold tailWord_2897145
  simp only [CollatzResearch.WordTrace]
  refine ⟨105667559089145932818628889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70445039392763955212419259 105667559089145932818628889)
  ·
    refine ⟨79250669316859449613971667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105667559089145932818628889 79250669316859449613971667)
    ·
      refine ⟨118876003975289174420957501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79250669316859449613971667 118876003975289174420957501)
      ·
        refine ⟨44578501490733440407859063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118876003975289174420957501 44578501490733440407859063)
        ·
          refine ⟨66867752236100160611788595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44578501490733440407859063 66867752236100160611788595)
          ·
            refine ⟨100301628354150240917682893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66867752236100160611788595 100301628354150240917682893)
            ·
              refine ⟨37613110632806340344131085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100301628354150240917682893 37613110632806340344131085)
              ·
                refine ⟨14104916487302377629049157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37613110632806340344131085 14104916487302377629049157)
                ·
                  refine ⟨2644671841369195805446717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14104916487302377629049157 2644671841369195805446717)
                  ·
                    refine ⟨991751940513448427042519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644671841369195805446717 991751940513448427042519)
                    ·
                      rfl

theorem cell22_2897145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_2897145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897145 prefixEnd_2897145 := by exact prefixLift 2897145
  have htrace : WordTrace (prefixWord ++ tailWord_2897145) baseStart_2897145 baseEnd_2897145 := by
    simpa [prefixWord, tailWord_2897145, baseEnd_2897145] using wordTrace_append hprefix tailTrace_2897145
  have hstable : (prefixWord ++ tailWord_2897145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897145).length < 2 ^ (prefixWord ++ tailWord_2897145).sum := by decide
  have hdescent : baseEnd_2897145 < baseStart_2897145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897205 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2897205 : Nat := 118140960795 + 2897205 * 2 ^ 59
def prefixEnd_2897205 : Nat := 4983230072969 + 3 ^ 40 * 2897205 * 2
def baseEnd_2897205 : Nat := 991772479739628270542335

theorem tailTrace_2897205 : CollatzResearch.WordTrace tailWord_2897205 prefixEnd_2897205 991772479739628270542335 := by
  unfold tailWord_2897205
  simp only [CollatzResearch.WordTrace]
  refine ⟨105669747468928563065813069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70446498312619042043875379 105669747468928563065813069)
  ·
    refine ⟨39626155300848211149679901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105669747468928563065813069 39626155300848211149679901)
    ·
      refine ⟨14859808237818079181129963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39626155300848211149679901 14859808237818079181129963)
      ·
        refine ⟨22289712356727118771694945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14859808237818079181129963 22289712356727118771694945)
        ·
          refine ⟨16717284267545339078771209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22289712356727118771694945 16717284267545339078771209)
          ·
            refine ⟨12537963200659004309078407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16717284267545339078771209 12537963200659004309078407)
            ·
              refine ⟨18806944800988506463617611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12537963200659004309078407 18806944800988506463617611)
              ·
                refine ⟨28210417201482759695426417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18806944800988506463617611 28210417201482759695426417)
                ·
                  refine ⟨21157812901112069771569813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28210417201482759695426417 21157812901112069771569813)
                  ·
                    refine ⟨991772479739628270542335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21157812901112069771569813 991772479739628270542335)
                    ·
                      rfl

theorem cell22_2897205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2897205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897205 prefixEnd_2897205 := by exact prefixLift 2897205
  have htrace : WordTrace (prefixWord ++ tailWord_2897205) baseStart_2897205 baseEnd_2897205 := by
    simpa [prefixWord, tailWord_2897205, baseEnd_2897205] using wordTrace_append hprefix tailTrace_2897205
  have hstable : (prefixWord ++ tailWord_2897205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897205).length < 2 ^ (prefixWord ++ tailWord_2897205).sum := by decide
  have hdescent : baseEnd_2897205 < baseStart_2897205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897209 : List Nat := [1, 2, 1, 6, 3, 1, 1, 7]
def baseStart_2897209 : Nat := 118140960795 + 2897209 * 2 ^ 59
def prefixEnd_2897209 : Nat := 4983230072969 + 3 ^ 40 * 2897209 * 2
def baseEnd_2897209 : Nat := 110197094335708177049147

theorem tailTrace_2897209 : CollatzResearch.WordTrace tailWord_2897209 prefixEnd_2897209 110197094335708177049147 := by
  unfold tailWord_2897209
  simp only [CollatzResearch.WordTrace]
  refine ⟨105669893360914071748958681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70446595573942714499305787 105669893360914071748958681)
  ·
    refine ⟨79252420020685553811719011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105669893360914071748958681 79252420020685553811719011)
    ·
      refine ⟨118878630031028330717578517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79252420020685553811719011 118878630031028330717578517)
      ·
        refine ⟨5572435782704453002386493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118878630031028330717578517 5572435782704453002386493)
        ·
          refine ⟨2089663418514169875894935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5572435782704453002386493 2089663418514169875894935)
          ·
            refine ⟨3134495127771254813842403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089663418514169875894935 3134495127771254813842403)
            ·
              refine ⟨4701742691656882220763605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134495127771254813842403 4701742691656882220763605)
              ·
                refine ⟨110197094335708177049147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4701742691656882220763605 110197094335708177049147)
                ·
                  rfl

theorem cell22_2897209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 7].length) (baseStart_2897209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897209 prefixEnd_2897209 := by exact prefixLift 2897209
  have htrace : WordTrace (prefixWord ++ tailWord_2897209) baseStart_2897209 baseEnd_2897209 := by
    simpa [prefixWord, tailWord_2897209, baseEnd_2897209] using wordTrace_append hprefix tailTrace_2897209
  have hstable : (prefixWord ++ tailWord_2897209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897209).length < 2 ^ (prefixWord ++ tailWord_2897209).sum := by decide
  have hdescent : baseEnd_2897209 < baseStart_2897209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897265 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 6]
def baseStart_2897265 : Nat := 118140960795 + 2897265 * 2 ^ 59
def prefixEnd_2897265 : Nat := 4983230072969 + 3 ^ 40 * 2897265 * 2
def baseEnd_2897265 : Nat := 330597672988602704680717

theorem tailTrace_2897265 : CollatzResearch.WordTrace tailWord_2897265 prefixEnd_2897265 330597672988602704680717 := by
  unfold tailWord_2897265
  simp only [CollatzResearch.WordTrace]
  refine ⟨105671935848711193312997249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70447957232474128875331499 105671935848711193312997249)
  ·
    refine ⟨79253951886533394984747937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105671935848711193312997249 79253951886533394984747937)
    ·
      refine ⟨59440463914900046238560953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79253951886533394984747937 59440463914900046238560953)
      ·
        refine ⟨44580347936175034678920715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59440463914900046238560953 44580347936175034678920715)
        ·
          refine ⟨66870521904262552018381073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44580347936175034678920715 66870521904262552018381073)
          ·
            refine ⟨50152891428196914013785805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66870521904262552018381073 50152891428196914013785805)
            ·
              refine ⟨18807334285573842755169677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50152891428196914013785805 18807334285573842755169677)
              ·
                refine ⟨7052750357090191033188629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18807334285573842755169677 7052750357090191033188629)
                ·
                  refine ⟨330597672988602704680717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7052750357090191033188629 330597672988602704680717)
                  ·
                    rfl

theorem cell22_2897265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_2897265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897265 prefixEnd_2897265 := by exact prefixLift 2897265
  have htrace : WordTrace (prefixWord ++ tailWord_2897265) baseStart_2897265 baseEnd_2897265 := by
    simpa [prefixWord, tailWord_2897265, baseEnd_2897265] using wordTrace_append hprefix tailTrace_2897265
  have hstable : (prefixWord ++ tailWord_2897265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897265).length < 2 ^ (prefixWord ++ tailWord_2897265).sum := by decide
  have hdescent : baseEnd_2897265 < baseStart_2897265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897284 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2897284 : Nat := 118140960795 + 2897284 * 2 ^ 59
def prefixEnd_2897284 : Nat := 4983230072969 + 3 ^ 40 * 2897284 * 2
def baseEnd_2897284 : Nat := 991799523054098397817093

theorem tailTrace_2897284 : CollatzResearch.WordTrace tailWord_2897284 prefixEnd_2897284 991799523054098397817093 := by
  unfold tailWord_2897284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52836314417821179778969453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70448419223761573038625937 52836314417821179778969453)
  ·
    refine ⟨19813617906682942417113545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52836314417821179778969453 19813617906682942417113545)
    ·
      refine ⟨14860213430012206812835159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19813617906682942417113545 14860213430012206812835159)
      ·
        refine ⟨22290320145018310219252739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14860213430012206812835159 22290320145018310219252739)
        ·
          refine ⟨33435480217527465328879109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22290320145018310219252739 33435480217527465328879109)
          ·
            refine ⟨6269152540786399749164833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33435480217527465328879109 6269152540786399749164833)
            ·
              refine ⟨4701864405589799811873625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6269152540786399749164833 4701864405589799811873625)
              ·
                refine ⟨3526398304192349858905219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4701864405589799811873625 3526398304192349858905219)
                ·
                  refine ⟨5289597456288524788357829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526398304192349858905219 5289597456288524788357829)
                  ·
                    refine ⟨991799523054098397817093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289597456288524788357829 991799523054098397817093)
                    ·
                      rfl

theorem cell22_2897284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2897284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897284 prefixEnd_2897284 := by exact prefixLift 2897284
  have htrace : WordTrace (prefixWord ++ tailWord_2897284) baseStart_2897284 baseEnd_2897284 := by
    simpa [prefixWord, tailWord_2897284, baseEnd_2897284] using wordTrace_append hprefix tailTrace_2897284
  have hstable : (prefixWord ++ tailWord_2897284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897284).length < 2 ^ (prefixWord ++ tailWord_2897284).sum := by decide
  have hdescent : baseEnd_2897284 < baseStart_2897284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897312 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_2897312 : Nat := 118140960795 + 2897312 * 2 ^ 59
def prefixEnd_2897312 : Nat := 4983230072969 + 3 ^ 40 * 2897312 * 2
def baseEnd_2897312 : Nat := 991809108026315658117007

theorem tailTrace_2897312 : CollatzResearch.WordTrace tailWord_2897312 prefixEnd_2897312 991809108026315658117007 := by
  unfold tailWord_2897312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52836825039770460169979095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70449100053027280226638793 52836825039770460169979095)
  ·
    refine ⟨79255237559655690254968643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52836825039770460169979095 79255237559655690254968643)
    ·
      refine ⟨118882856339483535382452965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79255237559655690254968643 118882856339483535382452965)
      ·
        refine ⟨22290535563653162884209931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118882856339483535382452965 22290535563653162884209931)
        ·
          refine ⟨33435803345479744326314897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22290535563653162884209931 33435803345479744326314897)
          ·
            refine ⟨25076852509109808244736173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33435803345479744326314897 25076852509109808244736173)
            ·
              refine ⟨9403819690916178091776065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25076852509109808244736173 9403819690916178091776065)
              ·
                refine ⟨7052864768187133568832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9403819690916178091776065 7052864768187133568832049)
                ·
                  refine ⟨5289648576140350176624037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052864768187133568832049 5289648576140350176624037)
                  ·
                    refine ⟨991809108026315658117007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289648576140350176624037 991809108026315658117007)
                    ·
                      rfl

theorem cell22_2897312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_2897312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897312 prefixEnd_2897312 := by exact prefixLift 2897312
  have htrace : WordTrace (prefixWord ++ tailWord_2897312) baseStart_2897312 baseEnd_2897312 := by
    simpa [prefixWord, tailWord_2897312, baseEnd_2897312] using wordTrace_append hprefix tailTrace_2897312
  have hstable : (prefixWord ++ tailWord_2897312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897312).length < 2 ^ (prefixWord ++ tailWord_2897312).sum := by decide
  have hdescent : baseEnd_2897312 < baseStart_2897312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897314 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2897314 : Nat := 118140960795 + 2897314 * 2 ^ 59
def prefixEnd_2897314 : Nat := 4983230072969 + 3 ^ 40 * 2897314 * 2
def baseEnd_2897314 : Nat := 991809792667188319567001

theorem tailTrace_2897314 : CollatzResearch.WordTrace tailWord_2897314 prefixEnd_2897314 991809792667188319567001 := by
  unfold tailWord_2897314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418430756383418670382749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70449148683689116454353997 26418430756383418670382749)
  ·
    refine ⟨9906911533643782001393531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26418430756383418670382749 9906911533643782001393531)
    ·
      refine ⟨14860367300465673002090297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9906911533643782001393531 14860367300465673002090297)
      ·
        refine ⟨11145275475349254751567723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14860367300465673002090297 11145275475349254751567723)
        ·
          refine ⟨16717913213023882127351585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11145275475349254751567723 16717913213023882127351585)
          ·
            refine ⟨12538434909767911595513689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16717913213023882127351585 12538434909767911595513689)
            ·
              refine ⟨9403826182325933696635267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12538434909767911595513689 9403826182325933696635267)
              ·
                refine ⟨14105739273488900544952901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9403826182325933696635267 14105739273488900544952901)
                ·
                  refine ⟨2644826113779168852178669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14105739273488900544952901 2644826113779168852178669)
                  ·
                    refine ⟨991809792667188319567001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644826113779168852178669 991809792667188319567001)
                    ·
                      rfl

theorem cell22_2897314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2897314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897314 prefixEnd_2897314 := by exact prefixLift 2897314
  have htrace : WordTrace (prefixWord ++ tailWord_2897314) baseStart_2897314 baseEnd_2897314 := by
    simpa [prefixWord, tailWord_2897314, baseEnd_2897314] using wordTrace_append hprefix tailTrace_2897314
  have hstable : (prefixWord ++ tailWord_2897314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897314).length < 2 ^ (prefixWord ++ tailWord_2897314).sum := by decide
  have hdescent : baseEnd_2897314 < baseStart_2897314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897355 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 9]
def baseStart_2897355 : Nat := 118140960795 + 2897355 * 2 ^ 59
def prefixEnd_2897355 : Nat := 4983230072969 + 3 ^ 40 * 2897355 * 2
def baseEnd_2897355 : Nat := 330607942601692626430625

theorem tailTrace_2897355 : CollatzResearch.WordTrace tailWord_2897355 prefixEnd_2897355 330607942601692626430625 := by
  unfold tailWord_2897355
  simp only [CollatzResearch.WordTrace]
  refine ⟨105675218418385138683773519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70450145612256759122515679 105675218418385138683773519)
  ·
    refine ⟨158512827627577708025660279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105675218418385138683773519 158512827627577708025660279)
    ·
      refine ⟨237769241441366562038490419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158512827627577708025660279 237769241441366562038490419)
      ·
        refine ⟨356653862162049843057735629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237769241441366562038490419 356653862162049843057735629)
        ·
          refine ⟨133745198310768691146650861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356653862162049843057735629 133745198310768691146650861)
          ·
            refine ⟨50154449366538259179994073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133745198310768691146650861 50154449366538259179994073)
            ·
              refine ⟨37615837024903694384995555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50154449366538259179994073 37615837024903694384995555)
              ·
                refine ⟨56423755537355541577493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37615837024903694384995555 56423755537355541577493333)
                ·
                  refine ⟨330607942601692626430625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56423755537355541577493333 330607942601692626430625)
                  ·
                    rfl

theorem cell22_2897355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_2897355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897355 prefixEnd_2897355 := by exact prefixLift 2897355
  have htrace : WordTrace (prefixWord ++ tailWord_2897355) baseStart_2897355 baseEnd_2897355 := by
    simpa [prefixWord, tailWord_2897355, baseEnd_2897355] using wordTrace_append hprefix tailTrace_2897355
  have hstable : (prefixWord ++ tailWord_2897355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897355).length < 2 ^ (prefixWord ++ tailWord_2897355).sum := by decide
  have hdescent : baseEnd_2897355 < baseStart_2897355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897402 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_2897402 : Nat := 118140960795 + 2897402 * 2 ^ 59
def prefixEnd_2897402 : Nat := 4983230072969 + 3 ^ 40 * 2897402 * 2
def baseEnd_2897402 : Nat := 991839916865585423366731

theorem tailTrace_2897402 : CollatzResearch.WordTrace tailWord_2897402 prefixEnd_2897402 991839916865585423366731 := by
  unfold tailWord_2897402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419233162303716427683615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70451288432809910473822973 26419233162303716427683615)
  ·
    refine ⟨39628849743455574641525423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26419233162303716427683615 39628849743455574641525423)
    ·
      refine ⟨59443274615183361962288135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39628849743455574641525423 59443274615183361962288135)
      ·
        refine ⟨89164911922775042943432203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59443274615183361962288135 89164911922775042943432203)
        ·
          refine ⟨133747367884162564415148305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89164911922775042943432203 133747367884162564415148305)
          ·
            refine ⟨100310525913121923311361229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133747367884162564415148305 100310525913121923311361229)
            ·
              refine ⟨37616447217420721241760461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100310525913121923311361229 37616447217420721241760461)
              ·
                refine ⟨14106167706532770465660173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37616447217420721241760461 14106167706532770465660173)
                ·
                  refine ⟨5289812889949788924622565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14106167706532770465660173 5289812889949788924622565)
                  ·
                    refine ⟨991839916865585423366731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289812889949788924622565 991839916865585423366731)
                    ·
                      rfl

theorem cell22_2897402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_2897402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897402 prefixEnd_2897402 := by exact prefixLift 2897402
  have htrace : WordTrace (prefixWord ++ tailWord_2897402) baseStart_2897402 baseEnd_2897402 := by
    simpa [prefixWord, tailWord_2897402, baseEnd_2897402] using wordTrace_append hprefix tailTrace_2897402
  have hstable : (prefixWord ++ tailWord_2897402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897402).length < 2 ^ (prefixWord ++ tailWord_2897402).sum := by decide
  have hdescent : baseEnd_2897402 < baseStart_2897402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897410 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2897410 : Nat := 118140960795 + 2897410 * 2 ^ 59
def prefixEnd_2897410 : Nat := 4983230072969 + 3 ^ 40 * 2897410 * 2
def baseEnd_2897410 : Nat := 991842655429076069166707

theorem tailTrace_2897410 : CollatzResearch.WordTrace tailWord_2897410 prefixEnd_2897410 991842655429076069166707 := by
  unfold tailWord_2897410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419306108296470769256421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70451482955457255384683789 26419306108296470769256421)
  ·
    refine ⟨4953619895305588269235579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26419306108296470769256421 4953619895305588269235579)
    ·
      refine ⟨7430429842958382403853369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953619895305588269235579 7430429842958382403853369)
      ·
        refine ⟨5572822382218786802890027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7430429842958382403853369 5572822382218786802890027)
        ·
          refine ⟨8359233573328180204335041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572822382218786802890027 8359233573328180204335041)
          ·
            refine ⟨6269425179996135153251281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8359233573328180204335041 6269425179996135153251281)
            ·
              refine ⟨4702068884997101364938461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6269425179996135153251281 4702068884997101364938461)
              ·
                refine ⟨1763275831873913011851923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4702068884997101364938461 1763275831873913011851923)
                ·
                  refine ⟨2644913747810869517777885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763275831873913011851923 2644913747810869517777885)
                  ·
                    refine ⟨991842655429076069166707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644913747810869517777885 991842655429076069166707)
                    ·
                      rfl

theorem cell22_2897410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2897410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897410 prefixEnd_2897410 := by exact prefixLift 2897410
  have htrace : WordTrace (prefixWord ++ tailWord_2897410) baseStart_2897410 baseEnd_2897410 := by
    simpa [prefixWord, tailWord_2897410, baseEnd_2897410] using wordTrace_append hprefix tailTrace_2897410
  have hstable : (prefixWord ++ tailWord_2897410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897410).length < 2 ^ (prefixWord ++ tailWord_2897410).sum := by decide
  have hdescent : baseEnd_2897410 < baseStart_2897410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897468 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_2897468 : Nat := 118140960795 + 2897468 * 2 ^ 59
def prefixEnd_2897468 : Nat := 4983230072969 + 3 ^ 40 * 2897468 * 2
def baseEnd_2897468 : Nat := 330620836671461083738843

theorem tailTrace_2897468 : CollatzResearch.WordTrace tailWord_2897468 prefixEnd_2897468 330620836671461083738843 := by
  unfold tailWord_2897468
  simp only [CollatzResearch.WordTrace]
  refine ⟨52839669933487879491318529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70452893244650505988424705 52839669933487879491318529)
  ·
    refine ⟨39629752450115909618488897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52839669933487879491318529 39629752450115909618488897)
    ·
      refine ⟨29722314337586932213866673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39629752450115909618488897 29722314337586932213866673)
      ·
        refine ⟨22291735753190199160400005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29722314337586932213866673 22291735753190199160400005)
        ·
          refine ⟨4179700453723162342575001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22291735753190199160400005 4179700453723162342575001)
          ·
            refine ⟨3134775340292371756931251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179700453723162342575001 3134775340292371756931251)
            ·
              refine ⟨4702163010438557635396877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134775340292371756931251 4702163010438557635396877)
              ·
                refine ⟨1763311128914459113273829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4702163010438557635396877 1763311128914459113273829)
                ·
                  refine ⟨330620836671461083738843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763311128914459113273829 330620836671461083738843)
                  ·
                    rfl

theorem cell22_2897468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_2897468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897468 prefixEnd_2897468 := by exact prefixLift 2897468
  have htrace : WordTrace (prefixWord ++ tailWord_2897468) baseStart_2897468 baseEnd_2897468 := by
    simpa [prefixWord, tailWord_2897468, baseEnd_2897468] using wordTrace_append hprefix tailTrace_2897468
  have hstable : (prefixWord ++ tailWord_2897468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897468).length < 2 ^ (prefixWord ++ tailWord_2897468).sum := by decide
  have hdescent : baseEnd_2897468 < baseStart_2897468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897479 : List Nat := [1, 1, 4, 1, 5, 2, 8]
def baseStart_2897479 : Nat := 118140960795 + 2897479 * 2 ^ 59
def prefixEnd_2897479 : Nat := 4983230072969 + 3 ^ 40 * 2897479 * 2
def baseEnd_2897479 : Nat := 36735787982932699599685

theorem tailTrace_2897479 : CollatzResearch.WordTrace tailWord_2897479 prefixEnd_2897479 36735787982932699599685 := by
  unfold tailWord_2897479
  simp only [CollatzResearch.WordTrace]
  refine ⟨105679741069935907861287491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70453160713290605240858327 105679741069935907861287491)
  ·
    refine ⟨158519611604903861791931237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105679741069935907861287491 158519611604903861791931237)
    ·
      refine ⟨29722427175919474085987107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158519611604903861791931237 29722427175919474085987107)
      ·
        refine ⟨44583640763879211128980661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29722427175919474085987107 44583640763879211128980661)
        ·
          refine ⟨4179716321613676043341937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44583640763879211128980661 4179716321613676043341937)
          ·
            refine ⟨3134787241210257032506453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179716321613676043341937 3134787241210257032506453)
            ·
              refine ⟨36735787982932699599685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3134787241210257032506453 36735787982932699599685)
              ·
                rfl

theorem cell22_2897479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 8].length) (baseStart_2897479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897479 prefixEnd_2897479 := by exact prefixLift 2897479
  have htrace : WordTrace (prefixWord ++ tailWord_2897479) baseStart_2897479 baseEnd_2897479 := by
    simpa [prefixWord, tailWord_2897479, baseEnd_2897479] using wordTrace_append hprefix tailTrace_2897479
  have hstable : (prefixWord ++ tailWord_2897479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897479).length < 2 ^ (prefixWord ++ tailWord_2897479).sum := by decide
  have hdescent : baseEnd_2897479 < baseStart_2897479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897485 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2897485 : Nat := 118140960795 + 2897485 * 2 ^ 59
def prefixEnd_2897485 : Nat := 4983230072969 + 3 ^ 40 * 2897485 * 2
def baseEnd_2897485 : Nat := 330622776487266957847159

theorem tailTrace_2897485 : CollatzResearch.WordTrace tailWord_2897485 prefixEnd_2897485 330622776487266957847159 := by
  unfold tailWord_2897485
  simp only [CollatzResearch.WordTrace]
  refine ⟨105679959907914170886005909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70453306605276113924003939 105679959907914170886005909)
  ·
    refine ⟨4953748120683476760281527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105679959907914170886005909 4953748120683476760281527)
    ·
      refine ⟨7430622181025215140422291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953748120683476760281527 7430622181025215140422291)
      ·
        refine ⟨11145933271537822710633437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430622181025215140422291 11145933271537822710633437)
        ·
          refine ⟨4179724976826683516487539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11145933271537822710633437 4179724976826683516487539)
          ·
            refine ⟨6269587465240025274731309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179724976826683516487539 6269587465240025274731309)
            ·
              refine ⟨2351095299465009478024241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6269587465240025274731309 2351095299465009478024241)
              ·
                refine ⟨1763321474598757108518181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351095299465009478024241 1763321474598757108518181)
                ·
                  refine ⟨330622776487266957847159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763321474598757108518181 330622776487266957847159)
                  ·
                    rfl

theorem cell22_2897485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2897485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897485 prefixEnd_2897485 := by exact prefixLift 2897485
  have htrace : WordTrace (prefixWord ++ tailWord_2897485) baseStart_2897485 baseEnd_2897485 := by
    simpa [prefixWord, tailWord_2897485, baseEnd_2897485] using wordTrace_append hprefix tailTrace_2897485
  have hstable : (prefixWord ++ tailWord_2897485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897485).length < 2 ^ (prefixWord ++ tailWord_2897485).sum := by decide
  have hdescent : baseEnd_2897485 < baseStart_2897485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897500 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2897500 : Nat := 118140960795 + 2897500 * 2 ^ 59
def prefixEnd_2897500 : Nat := 4983230072969 + 3 ^ 40 * 2897500 * 2
def baseEnd_2897500 : Nat := 991873464268345834416431

theorem tailTrace_2897500 : CollatzResearch.WordTrace tailWord_2897500 prefixEnd_2897500 991873464268345834416431 := by
  unfold tailWord_2897500
  simp only [CollatzResearch.WordTrace]
  refine ⟨52840253501429914223900977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70453671335239885631867969 52840253501429914223900977)
  ·
    refine ⟨39630190126072435667925733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52840253501429914223900977 39630190126072435667925733)
    ·
      refine ⟨7430660648638581687736075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39630190126072435667925733 7430660648638581687736075)
      ·
        refine ⟨11145990972957872531604113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430660648638581687736075 11145990972957872531604113)
        ·
          refine ⟨8359493229718404398703085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11145990972957872531604113 8359493229718404398703085)
          ·
            refine ⟨3134809961144401649513657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8359493229718404398703085 3134809961144401649513657)
            ·
              refine ⟨2351107470858301237135243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134809961144401649513657 2351107470858301237135243)
              ·
                refine ⟨3526661206287451855702865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351107470858301237135243 3526661206287451855702865)
                ·
                  refine ⟨2644995904715588891777149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3526661206287451855702865 2644995904715588891777149)
                  ·
                    refine ⟨991873464268345834416431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644995904715588891777149 991873464268345834416431)
                    ·
                      rfl

theorem cell22_2897500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2897500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897500 prefixEnd_2897500 := by exact prefixLift 2897500
  have htrace : WordTrace (prefixWord ++ tailWord_2897500) baseStart_2897500 baseEnd_2897500 := by
    simpa [prefixWord, tailWord_2897500, baseEnd_2897500] using wordTrace_append hprefix tailTrace_2897500
  have hstable : (prefixWord ++ tailWord_2897500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897500).length < 2 ^ (prefixWord ++ tailWord_2897500).sum := by decide
  have hdescent : baseEnd_2897500 < baseStart_2897500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897552 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_2897552 : Nat := 118140960795 + 2897552 * 2 ^ 59
def prefixEnd_2897552 : Nat := 4983230072969 + 3 ^ 40 * 2897552 * 2
def baseEnd_2897552 : Nat := 330630421643678344038757

theorem tailTrace_2897552 : CollatzResearch.WordTrace tailWord_2897552 prefixEnd_2897552 330630421643678344038757 := by
  unfold tailWord_2897552
  simp only [CollatzResearch.WordTrace]
  refine ⟨52841201799335720664347455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70454935732447627552463273 52841201799335720664347455)
  ·
    refine ⟨79261802699003580996521183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52841201799335720664347455 79261802699003580996521183)
    ·
      refine ⟨118892704048505371494781775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79261802699003580996521183 118892704048505371494781775)
      ·
        refine ⟨178339056072758057242172663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118892704048505371494781775 178339056072758057242172663)
        ·
          refine ⟨267508584109137085863258995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178339056072758057242172663 267508584109137085863258995)
          ·
            refine ⟨401262876163705628794888493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267508584109137085863258995 401262876163705628794888493)
            ·
              refine ⟨150473578561389610798083185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401262876163705628794888493 150473578561389610798083185)
              ·
                refine ⟨112855183921042208098562389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150473578561389610798083185 112855183921042208098562389)
                ·
                  refine ⟨330630421643678344038757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112855183921042208098562389 330630421643678344038757)
                  ·
                    rfl

theorem cell22_2897552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_2897552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897552 prefixEnd_2897552 := by exact prefixLift 2897552
  have htrace : WordTrace (prefixWord ++ tailWord_2897552) baseStart_2897552 baseEnd_2897552 := by
    simpa [prefixWord, tailWord_2897552, baseEnd_2897552] using wordTrace_append hprefix tailTrace_2897552
  have hstable : (prefixWord ++ tailWord_2897552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897552).length < 2 ^ (prefixWord ++ tailWord_2897552).sum := by decide
  have hdescent : baseEnd_2897552 < baseStart_2897552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897569 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 8]
def baseStart_2897569 : Nat := 118140960795 + 2897569 * 2 ^ 59
def prefixEnd_2897569 : Nat := 4983230072969 + 3 ^ 40 * 2897569 * 2
def baseEnd_2897569 : Nat := 330632361459484218147073

theorem tailTrace_2897569 : CollatzResearch.WordTrace tailWord_2897569 prefixEnd_2897569 330632361459484218147073 := by
  unfold tailWord_2897569
  simp only [CollatzResearch.WordTrace]
  refine ⟨105683023639609853232063761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70455349093073235488042507 105683023639609853232063761)
  ·
    refine ⟨79262267729707389924047821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105683023639609853232063761 79262267729707389924047821)
    ·
      refine ⟨29723350398640271221517933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79262267729707389924047821 29723350398640271221517933)
      ·
        refine ⟨11146256399490101708069225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29723350398640271221517933 11146256399490101708069225)
        ·
          refine ⟨8359692299617576281051919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11146256399490101708069225 8359692299617576281051919)
          ·
            refine ⟨12539538449426364421577879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359692299617576281051919 12539538449426364421577879)
            ·
              refine ⟨18809307674139546632366819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12539538449426364421577879 18809307674139546632366819)
              ·
                refine ⟨28213961511209319948550229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18809307674139546632366819 28213961511209319948550229)
                ·
                  refine ⟨330632361459484218147073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28213961511209319948550229 330632361459484218147073)
                  ·
                    rfl

theorem cell22_2897569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_2897569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897569 prefixEnd_2897569 := by exact prefixLift 2897569
  have htrace : WordTrace (prefixWord ++ tailWord_2897569) baseStart_2897569 baseEnd_2897569 := by
    simpa [prefixWord, tailWord_2897569, baseEnd_2897569] using wordTrace_append hprefix tailTrace_2897569
  have hstable : (prefixWord ++ tailWord_2897569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897569).length < 2 ^ (prefixWord ++ tailWord_2897569).sum := by decide
  have hdescent : baseEnd_2897569 < baseStart_2897569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897584 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_2897584 : Nat := 118140960795 + 2897584 * 2 ^ 59
def prefixEnd_2897584 : Nat := 4983230072969 + 3 ^ 40 * 2897584 * 2
def baseEnd_2897584 : Nat := 991902219184997615316173

theorem tailTrace_2897584 : CollatzResearch.WordTrace tailWord_2897584 prefixEnd_2897584 991902219184997615316173 := by
  unfold tailWord_2897584
  simp only [CollatzResearch.WordTrace]
  refine ⟨52841785367277755396929903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70455713823037007195906537 52841785367277755396929903)
  ·
    refine ⟨79262678050916633095394855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52841785367277755396929903 79262678050916633095394855)
    ·
      refine ⟨118894017076374949643092283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79262678050916633095394855 118894017076374949643092283)
      ·
        refine ⟨178341025614562424464638425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118894017076374949643092283 178341025614562424464638425)
        ·
          refine ⟨133755769210921818348478819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178341025614562424464638425 133755769210921818348478819)
          ·
            refine ⟨200633653816382727522718229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133755769210921818348478819 200633653816382727522718229)
            ·
              refine ⟨9404702522642940352627417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200633653816382727522718229 9404702522642940352627417)
              ·
                refine ⟨7053526891982205264470563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9404702522642940352627417 7053526891982205264470563)
                ·
                  refine ⟨10580290337973307896705845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7053526891982205264470563 10580290337973307896705845)
                  ·
                    refine ⟨991902219184997615316173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10580290337973307896705845 991902219184997615316173)
                    ·
                      rfl

theorem cell22_2897584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_2897584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897584 prefixEnd_2897584 := by exact prefixLift 2897584
  have htrace : WordTrace (prefixWord ++ tailWord_2897584) baseStart_2897584 baseEnd_2897584 := by
    simpa [prefixWord, tailWord_2897584, baseEnd_2897584] using wordTrace_append hprefix tailTrace_2897584
  have hstable : (prefixWord ++ tailWord_2897584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897584).length < 2 ^ (prefixWord ++ tailWord_2897584).sum := by decide
  have hdescent : baseEnd_2897584 < baseStart_2897584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897586 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_2897586 : Nat := 118140960795 + 2897586 * 2 ^ 59
def prefixEnd_2897586 : Nat := 4983230072969 + 3 ^ 40 * 2897586 * 2
def baseEnd_2897586 : Nat := 330634301275290092255389

theorem tailTrace_2897586 : CollatzResearch.WordTrace tailWord_2897586 prefixEnd_2897586 330634301275290092255389 := by
  unfold tailWord_2897586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26420910920137066283858153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70455762453698843423621741 26420910920137066283858153)
  ·
    refine ⟨19815683190102799712893615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26420910920137066283858153 19815683190102799712893615)
    ·
      refine ⟨29723524785154199569340423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19815683190102799712893615 29723524785154199569340423)
      ·
        refine ⟨44585287177731299354010635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29723524785154199569340423 44585287177731299354010635)
        ·
          refine ⟨66877930766596949031015953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44585287177731299354010635 66877930766596949031015953)
          ·
            refine ⟨50158448074947711773261965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66877930766596949031015953 50158448074947711773261965)
            ·
              refine ⟨18809418028105391914973237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50158448074947711773261965 18809418028105391914973237)
              ·
                refine ⟨1763382940134880492028741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18809418028105391914973237 1763382940134880492028741)
                ·
                  refine ⟨330634301275290092255389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763382940134880492028741 330634301275290092255389)
                  ·
                    rfl

theorem cell22_2897586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_2897586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897586 prefixEnd_2897586 := by exact prefixLift 2897586
  have htrace : WordTrace (prefixWord ++ tailWord_2897586) baseStart_2897586 baseEnd_2897586 := by
    simpa [prefixWord, tailWord_2897586, baseEnd_2897586] using wordTrace_append hprefix tailTrace_2897586
  have hstable : (prefixWord ++ tailWord_2897586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897586).length < 2 ^ (prefixWord ++ tailWord_2897586).sum := by decide
  have hdescent : baseEnd_2897586 < baseStart_2897586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897599 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_2897599 : Nat := 118140960795 + 2897599 * 2 ^ 59
def prefixEnd_2897599 : Nat := 4983230072969 + 3 ^ 40 * 2897599 * 2
def baseEnd_2897599 : Nat := 991907353991542576191127

theorem tailTrace_2897599 : CollatzResearch.WordTrace tailWord_2897599 prefixEnd_2897599 991907353991542576191127 := by
  unfold tailWord_2897599
  simp only [CollatzResearch.WordTrace]
  refine ⟨105684117829501168355655851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70456078553000778903770567 105684117829501168355655851)
  ·
    refine ⟨158526176744251752533483777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105684117829501168355655851 158526176744251752533483777)
    ·
      refine ⟨118894632558188814400112833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158526176744251752533483777 118894632558188814400112833)
      ·
        refine ⟨89170974418641610800084625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118894632558188814400112833 89170974418641610800084625)
        ·
          refine ⟨66878230813981208100063469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89170974418641610800084625 66878230813981208100063469)
          ·
            refine ⟨25079336555242953037523801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66878230813981208100063469 25079336555242953037523801)
            ·
              refine ⟨18809502416432214778142851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25079336555242953037523801 18809502416432214778142851)
              ·
                refine ⟨28214253624648322167214277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18809502416432214778142851 28214253624648322167214277)
                ·
                  refine ⟨5290172554621560406352677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28214253624648322167214277 5290172554621560406352677)
                  ·
                    refine ⟨991907353991542576191127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290172554621560406352677 991907353991542576191127)
                    ·
                      rfl

theorem cell22_2897599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_2897599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897599 prefixEnd_2897599 := by exact prefixLift 2897599
  have htrace : WordTrace (prefixWord ++ tailWord_2897599) baseStart_2897599 baseEnd_2897599 := by
    simpa [prefixWord, tailWord_2897599, baseEnd_2897599] using wordTrace_append hprefix tailTrace_2897599
  have hstable : (prefixWord ++ tailWord_2897599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897599).length < 2 ^ (prefixWord ++ tailWord_2897599).sum := by decide
  have hdescent : baseEnd_2897599 < baseStart_2897599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897614 : List Nat := [4, 1, 1, 1, 3, 1, 2, 9]
def baseStart_2897614 : Nat := 118140960795 + 2897614 * 2 ^ 59
def prefixEnd_2897614 : Nat := 4983230072969 + 3 ^ 40 * 2897614 * 2
def baseEnd_2897614 : Nat := 110212498755343059674009

theorem tailTrace_2897614 : CollatzResearch.WordTrace tailWord_2897614 prefixEnd_2897614 110212498755343059674009 := by
  unfold tailWord_2897614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210583115555853239681487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70456443282964550611634597 13210583115555853239681487)
  ·
    refine ⟨19815874673333779859522231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13210583115555853239681487 19815874673333779859522231)
    ·
      refine ⟨29723812010000669789283347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19815874673333779859522231 29723812010000669789283347)
      ·
        refine ⟨44585718015001004683925021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29723812010000669789283347 44585718015001004683925021)
        ·
          refine ⟨16719644255625376756471883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44585718015001004683925021 16719644255625376756471883)
          ·
            refine ⟨25079466383438065134707825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16719644255625376756471883 25079466383438065134707825)
            ·
              refine ⟨18809599787578548851030869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25079466383438065134707825 18809599787578548851030869)
              ·
                refine ⟨110212498755343059674009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18809599787578548851030869 110212498755343059674009)
                ·
                  rfl

theorem cell22_2897614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_2897614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897614 prefixEnd_2897614 := by exact prefixLift 2897614
  have htrace : WordTrace (prefixWord ++ tailWord_2897614) baseStart_2897614 baseEnd_2897614 := by
    simpa [prefixWord, tailWord_2897614, baseEnd_2897614] using wordTrace_append hprefix tailTrace_2897614
  have hstable : (prefixWord ++ tailWord_2897614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897614).length < 2 ^ (prefixWord ++ tailWord_2897614).sum := by decide
  have hdescent : baseEnd_2897614 < baseStart_2897614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897618 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2897618 : Nat := 118140960795 + 2897618 * 2 ^ 59
def prefixEnd_2897618 : Nat := 4983230072969 + 3 ^ 40 * 2897618 * 2
def baseEnd_2897618 : Nat := 991913858079832859966069

theorem tailTrace_2897618 : CollatzResearch.WordTrace tailWord_2897618 prefixEnd_2897618 991913858079832859966069 := by
  unfold tailWord_2897618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26421202704108083650149377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70456540544288223067065005 26421202704108083650149377)
  ·
    refine ⟨19815902028081062737612033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26421202704108083650149377 19815902028081062737612033)
    ·
      refine ⟨14861926521060797053209025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19815902028081062737612033 14861926521060797053209025)
      ·
        refine ⟨11146444890795597789906769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14861926521060797053209025 11146444890795597789906769)
        ·
          refine ⟨8359833668096698342430077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11146444890795597789906769 8359833668096698342430077)
          ·
            refine ⟨3134937625536261878411279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8359833668096698342430077 3134937625536261878411279)
            ·
              refine ⟨4702406438304392817616919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134937625536261878411279 4702406438304392817616919)
              ·
                refine ⟨7053609657456589226425379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702406438304392817616919 7053609657456589226425379)
                ·
                  refine ⟨10580414486184883839638069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7053609657456589226425379 10580414486184883839638069)
                  ·
                    refine ⟨991913858079832859966069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10580414486184883839638069 991913858079832859966069)
                    ·
                      rfl

theorem cell22_2897618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2897618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897618 prefixEnd_2897618 := by exact prefixLift 2897618
  have htrace : WordTrace (prefixWord ++ tailWord_2897618) baseStart_2897618 baseEnd_2897618 := by
    simpa [prefixWord, tailWord_2897618, baseEnd_2897618] using wordTrace_append hprefix tailTrace_2897618
  have hstable : (prefixWord ++ tailWord_2897618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897618).length < 2 ^ (prefixWord ++ tailWord_2897618).sum := by decide
  have hdescent : baseEnd_2897618 < baseStart_2897618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897622 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2897622 : Nat := 118140960795 + 2897622 * 2 ^ 59
def prefixEnd_2897622 : Nat := 4983230072969 + 3 ^ 40 * 2897622 * 2
def baseEnd_2897622 : Nat := 991915227361578182866057

theorem tailTrace_2897622 : CollatzResearch.WordTrace tailWord_2897622 prefixEnd_2897622 991915227361578182866057 := by
  unfold tailWord_2897622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6605309794276115205233945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70456637805611895522495413 6605309794276115205233945)
  ·
    refine ⟨4953982345707086403925459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6605309794276115205233945 4953982345707086403925459)
    ·
      refine ⟨7430973518560629605888189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953982345707086403925459 7430973518560629605888189)
      ·
        refine ⟨2786615069460236102208071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7430973518560629605888189 2786615069460236102208071)
        ·
          refine ⟨4179922604190354153312107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786615069460236102208071 4179922604190354153312107)
          ·
            refine ⟨6269883906285531229968161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179922604190354153312107 6269883906285531229968161)
            ·
              refine ⟨4702412929714148422476121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6269883906285531229968161 4702412929714148422476121)
              ·
                refine ⟨3526809697285611316857091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4702412929714148422476121 3526809697285611316857091)
                ·
                  refine ⟨5290214545928416975285637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526809697285611316857091 5290214545928416975285637)
                  ·
                    refine ⟨991915227361578182866057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290214545928416975285637 991915227361578182866057)
                    ·
                      rfl

theorem cell22_2897622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2897622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897622 prefixEnd_2897622 := by exact prefixLift 2897622
  have htrace : WordTrace (prefixWord ++ tailWord_2897622) baseStart_2897622 baseEnd_2897622 := by
    simpa [prefixWord, tailWord_2897622, baseEnd_2897622] using wordTrace_append hprefix tailTrace_2897622
  have hstable : (prefixWord ++ tailWord_2897622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897622).length < 2 ^ (prefixWord ++ tailWord_2897622).sum := by decide
  have hdescent : baseEnd_2897622 < baseStart_2897622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897663 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 1, 3]
def baseStart_2897663 : Nat := 118140960795 + 2897663 * 2 ^ 59
def prefixEnd_2897663 : Nat := 4983230072969 + 3 ^ 40 * 2897663 * 2
def baseEnd_2897663 : Nat := 991929262499467742590931

theorem tailTrace_2897663 : CollatzResearch.WordTrace tailWord_2897663 prefixEnd_2897663 991929262499467742590931 := by
  unfold tailWord_2897663
  simp only [CollatzResearch.WordTrace]
  refine ⟨105686452101269307285985643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70457634734179538190657095 105686452101269307285985643)
  ·
    refine ⟨158529678151903960928978465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105686452101269307285985643 158529678151903960928978465)
    ·
      refine ⟨118897258613927970696733849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158529678151903960928978465 118897258613927970696733849)
      ·
        refine ⟨89172943960445978022550387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118897258613927970696733849 89172943960445978022550387)
        ·
          refine ⟨133759415940668967033825581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89172943960445978022550387 133759415940668967033825581)
          ·
            refine ⟨50159780977750862637684593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133759415940668967033825581 50159780977750862637684593)
            ·
              refine ⟨37619835733313146978263445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50159780977750862637684593 37619835733313146978263445)
              ·
                refine ⟨1763429799999053764606099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37619835733313146978263445 1763429799999053764606099)
                ·
                  refine ⟨2645144699998580646909149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763429799999053764606099 2645144699998580646909149)
                  ·
                    refine ⟨991929262499467742590931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645144699998580646909149 991929262499467742590931)
                    ·
                      rfl

theorem cell22_2897663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_2897663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897663 prefixEnd_2897663 := by exact prefixLift 2897663
  have htrace : WordTrace (prefixWord ++ tailWord_2897663) baseStart_2897663 baseEnd_2897663 := by
    simpa [prefixWord, tailWord_2897663, baseEnd_2897663] using wordTrace_append hprefix tailTrace_2897663
  have hstable : (prefixWord ++ tailWord_2897663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897663).length < 2 ^ (prefixWord ++ tailWord_2897663).sum := by decide
  have hdescent : baseEnd_2897663 < baseStart_2897663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897710 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_2897710 : Nat := 118140960795 + 2897710 * 2 ^ 59
def prefixEnd_2897710 : Nat := 4983230072969 + 3 ^ 40 * 2897710 * 2
def baseEnd_2897710 : Nat := 330648450519991762221929

theorem tailTrace_2897710 : CollatzResearch.WordTrace tailWord_2897710 prefixEnd_2897710 330648450519991762221929 := by
  unfold tailWord_2897710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211020791512379289118323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70458777554732689541964389 13211020791512379289118323)
  ·
    refine ⟨19816531187268568933677485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211020791512379289118323 19816531187268568933677485)
    ·
      refine ⟨7431199195225713350129057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19816531187268568933677485 7431199195225713350129057)
      ·
        refine ⟨5573399396419285012596793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7431199195225713350129057 5573399396419285012596793)
        ·
          refine ⟨4180049547314463759447595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5573399396419285012596793 4180049547314463759447595)
          ·
            refine ⟨6270074320971695639171393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180049547314463759447595 6270074320971695639171393)
            ·
              refine ⟨4702555740728771729378545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270074320971695639171393 4702555740728771729378545)
              ·
                refine ⟨3526916805546578797033909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4702555740728771729378545 3526916805546578797033909)
                ·
                  refine ⟨330648450519991762221929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3526916805546578797033909 330648450519991762221929)
                  ·
                    rfl

theorem cell22_2897710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_2897710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897710 prefixEnd_2897710 := by exact prefixLift 2897710
  have htrace : WordTrace (prefixWord ++ tailWord_2897710) baseStart_2897710 baseEnd_2897710 := by
    simpa [prefixWord, tailWord_2897710, baseEnd_2897710] using wordTrace_append hprefix tailTrace_2897710
  have hstable : (prefixWord ++ tailWord_2897710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897710).length < 2 ^ (prefixWord ++ tailWord_2897710).sum := by decide
  have hdescent : baseEnd_2897710 < baseStart_2897710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897736 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2897736 : Nat := 118140960795 + 2897736 * 2 ^ 59
def prefixEnd_2897736 : Nat := 4983230072969 + 3 ^ 40 * 2897736 * 2
def baseEnd_2897736 : Nat := 991954251891319885515707

theorem tailTrace_2897736 : CollatzResearch.WordTrace tailWord_2897736 prefixEnd_2897736 991954251891319885515707 := by
  unfold tailWord_2897736
  simp only [CollatzResearch.WordTrace]
  refine ⟨52844557315002420376696531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70459409753336560502262041 52844557315002420376696531)
  ·
    refine ⟨79266835972503630565044797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52844557315002420376696531 79266835972503630565044797)
    ·
      refine ⟨29725063489688861461891799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79266835972503630565044797 29725063489688861461891799)
      ·
        refine ⟨44587595234533292192837699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29725063489688861461891799 44587595234533292192837699)
        ·
          refine ⟨66881392851799938289256549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44587595234533292192837699 66881392851799938289256549)
          ·
            refine ⟨12540261159712488429235603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66881392851799938289256549 12540261159712488429235603)
            ·
              refine ⟨18810391739568732643853405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12540261159712488429235603 18810391739568732643853405)
              ·
                refine ⟨7053896902338274741445027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18810391739568732643853405 7053896902338274741445027)
                ·
                  refine ⟨10580845353507412112167541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7053896902338274741445027 10580845353507412112167541)
                  ·
                    refine ⟨991954251891319885515707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10580845353507412112167541 991954251891319885515707)
                    ·
                      rfl

theorem cell22_2897736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2897736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897736 prefixEnd_2897736 := by exact prefixLift 2897736
  have htrace : WordTrace (prefixWord ++ tailWord_2897736) baseStart_2897736 baseEnd_2897736 := by
    simpa [prefixWord, tailWord_2897736, baseEnd_2897736] using wordTrace_append hprefix tailTrace_2897736
  have hstable : (prefixWord ++ tailWord_2897736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897736).length < 2 ^ (prefixWord ++ tailWord_2897736).sum := by decide
  have hdescent : baseEnd_2897736 < baseStart_2897736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897796 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2897796 : Nat := 118140960795 + 2897796 * 2 ^ 59
def prefixEnd_2897796 : Nat := 4983230072969 + 3 ^ 40 * 2897796 * 2
def baseEnd_2897796 : Nat := 991974791117499729015523

theorem tailTrace_2897796 : CollatzResearch.WordTrace tailWord_2897796 prefixEnd_2897796 991974791117499729015523 := by
  unfold tailWord_2897796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52845651504893735500288621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70460868673191647333718161 52845651504893735500288621)
  ·
    refine ⟨19817119314335150812608233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52845651504893735500288621 19817119314335150812608233)
    ·
      refine ⟨14862839485751363109456175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19817119314335150812608233 14862839485751363109456175)
      ·
        refine ⟨22294259228627044664184263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14862839485751363109456175 22294259228627044664184263)
        ·
          refine ⟨33441388842940566996276395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22294259228627044664184263 33441388842940566996276395)
          ·
            refine ⟨50162083264410850494414593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33441388842940566996276395 50162083264410850494414593)
            ·
              refine ⟨37621562448308137870810945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50162083264410850494414593 37621562448308137870810945)
              ·
                refine ⟨28216171836231103403108209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37621562448308137870810945 28216171836231103403108209)
                ·
                  refine ⟨21162128877173327552331157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28216171836231103403108209 21162128877173327552331157)
                  ·
                    refine ⟨991974791117499729015523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21162128877173327552331157 991974791117499729015523)
                    ·
                      rfl

theorem cell22_2897796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2897796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897796 prefixEnd_2897796 := by exact prefixLift 2897796
  have htrace : WordTrace (prefixWord ++ tailWord_2897796) baseStart_2897796 baseEnd_2897796 := by
    simpa [prefixWord, tailWord_2897796, baseEnd_2897796] using wordTrace_append hprefix tailTrace_2897796
  have hstable : (prefixWord ++ tailWord_2897796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897796).length < 2 ^ (prefixWord ++ tailWord_2897796).sum := by decide
  have hdescent : baseEnd_2897796 < baseStart_2897796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897800 : List Nat := [2, 1, 3, 3, 3, 2, 2, 6]
def baseStart_2897800 : Nat := 118140960795 + 2897800 * 2 ^ 59
def prefixEnd_2897800 : Nat := 4983230072969 + 3 ^ 40 * 2897800 * 2
def baseEnd_2897800 : Nat := 110219573377693894657279

theorem tailTrace_2897800 : CollatzResearch.WordTrace tailWord_2897800 prefixEnd_2897800 110219573377693894657279 := by
  unfold tailWord_2897800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52845724450886489841861427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70460965934515319789148569 52845724450886489841861427)
  ·
    refine ⟨79268586676329734762792141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52845724450886489841861427 79268586676329734762792141)
    ·
      refine ⟨29725720003623650536047053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79268586676329734762792141 29725720003623650536047053)
      ·
        refine ⟨11147145001358868951017645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29725720003623650536047053 11147145001358868951017645)
        ·
          refine ⟨4180179375509575856631617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11147145001358868951017645 4180179375509575856631617)
          ·
            refine ⟨3135134531632181892473713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180179375509575856631617 3135134531632181892473713)
            ·
              refine ⟨2351350898724136419355285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135134531632181892473713 2351350898724136419355285)
              ·
                refine ⟨110219573377693894657279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2351350898724136419355285 110219573377693894657279)
                ·
                  rfl

theorem cell22_2897800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_2897800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897800 prefixEnd_2897800 := by exact prefixLift 2897800
  have htrace : WordTrace (prefixWord ++ tailWord_2897800) baseStart_2897800 baseEnd_2897800 := by
    simpa [prefixWord, tailWord_2897800, baseEnd_2897800] using wordTrace_append hprefix tailTrace_2897800
  have hstable : (prefixWord ++ tailWord_2897800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897800).length < 2 ^ (prefixWord ++ tailWord_2897800).sum := by decide
  have hdescent : baseEnd_2897800 < baseStart_2897800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897838 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2897838 : Nat := 118140960795 + 2897838 * 2 ^ 59
def prefixEnd_2897838 : Nat := 4983230072969 + 3 ^ 40 * 2897838 * 2
def baseEnd_2897838 : Nat := 991989168575825619465395

theorem tailTrace_2897838 : CollatzResearch.WordTrace tailWord_2897838 prefixEnd_2897838 991989168575825619465395 := by
  unfold tailWord_2897838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211604359454414021700771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70461889917090208115737445 13211604359454414021700771)
  ·
    refine ⟨19817406539181621032551157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211604359454414021700771 19817406539181621032551157)
    ·
      refine ⟨1857881863048276971801671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19817406539181621032551157 1857881863048276971801671)
      ·
        refine ⟨2786822794572415457702507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857881863048276971801671 2786822794572415457702507)
        ·
          refine ⟨4180234191858623186553761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786822794572415457702507 4180234191858623186553761)
          ·
            refine ⟨3135175643893967389915321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180234191858623186553761 3135175643893967389915321)
            ·
              refine ⟨2351381732920475542436491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135175643893967389915321 2351381732920475542436491)
              ·
                refine ⟨3527072599380713313654737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351381732920475542436491 3527072599380713313654737)
                ·
                  refine ⟨2645304449535534985241053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527072599380713313654737 2645304449535534985241053)
                  ·
                    refine ⟨991989168575825619465395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645304449535534985241053 991989168575825619465395)
                    ·
                      rfl

theorem cell22_2897838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2897838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897838 prefixEnd_2897838 := by exact prefixLift 2897838
  have htrace : WordTrace (prefixWord ++ tailWord_2897838) baseStart_2897838 baseEnd_2897838 := by
    simpa [prefixWord, tailWord_2897838, baseEnd_2897838] using wordTrace_append hprefix tailTrace_2897838
  have hstable : (prefixWord ++ tailWord_2897838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897838).length < 2 ^ (prefixWord ++ tailWord_2897838).sum := by decide
  have hdescent : baseEnd_2897838 < baseStart_2897838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897845 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 5]
def baseStart_2897845 : Nat := 118140960795 + 2897845 * 2 ^ 59
def prefixEnd_2897845 : Nat := 4983230072969 + 3 ^ 40 * 2897845 * 2
def baseEnd_2897845 : Nat := 330663854939626644846791

theorem tailTrace_2897845 : CollatzResearch.WordTrace tailWord_2897845 prefixEnd_2897845 330663854939626644846791 := by
  unfold tailWord_2897845
  simp only [CollatzResearch.WordTrace]
  refine ⟨105693090186609952369110989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70462060124406634912740659 105693090186609952369110989)
  ·
    refine ⟨39634908819978732138416621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105693090186609952369110989 39634908819978732138416621)
    ·
      refine ⟨14863090807492024551906233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39634908819978732138416621 14863090807492024551906233)
      ·
        refine ⟨11147318105619018413929675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14863090807492024551906233 11147318105619018413929675)
        ·
          refine ⟨16720977158428527620894513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11147318105619018413929675 16720977158428527620894513)
          ·
            refine ⟨12540732868821395715670885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16720977158428527620894513 12540732868821395715670885)
            ·
              refine ⟨2351387412904011696688291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12540732868821395715670885 2351387412904011696688291)
              ·
                refine ⟨3527081119356017545032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351387412904011696688291 3527081119356017545032437)
                ·
                  refine ⟨330663854939626644846791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527081119356017545032437 330663854939626644846791)
                  ·
                    rfl

theorem cell22_2897845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_2897845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897845 prefixEnd_2897845 := by exact prefixLift 2897845
  have htrace : WordTrace (prefixWord ++ tailWord_2897845) baseStart_2897845 baseEnd_2897845 := by
    simpa [prefixWord, tailWord_2897845, baseEnd_2897845] using wordTrace_append hprefix tailTrace_2897845
  have hstable : (prefixWord ++ tailWord_2897845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897845).length < 2 ^ (prefixWord ++ tailWord_2897845).sum := by decide
  have hdescent : baseEnd_2897845 < baseStart_2897845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897856 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_2897856 : Nat := 118140960795 + 2897856 * 2 ^ 59
def prefixEnd_2897856 : Nat := 4983230072969 + 3 ^ 40 * 2897856 * 2
def baseEnd_2897856 : Nat := 330665110114559857505113

theorem tailTrace_2897856 : CollatzResearch.WordTrace tailWord_2897856 prefixEnd_2897856 330665110114559857505113 := by
  unfold tailWord_2897856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52846745694785050623880711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70462327593046734165174281 52846745694785050623880711)
  ·
    refine ⟨79270118542177575935821067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52846745694785050623880711 79270118542177575935821067)
    ·
      refine ⟨118905177813266363903731601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79270118542177575935821067 118905177813266363903731601)
      ·
        refine ⟨89178883359949772927798701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118905177813266363903731601 89178883359949772927798701)
        ·
          refine ⟨33442081259981164847924513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89178883359949772927798701 33442081259981164847924513)
          ·
            refine ⟨25081560944985873635943385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33442081259981164847924513 25081560944985873635943385)
            ·
              refine ⟨18811170708739405226957539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25081560944985873635943385 18811170708739405226957539)
              ·
                refine ⟨28216756063109107840436309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18811170708739405226957539 28216756063109107840436309)
                ·
                  refine ⟨330665110114559857505113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28216756063109107840436309 330665110114559857505113)
                  ·
                    rfl

theorem cell22_2897856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_2897856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897856 prefixEnd_2897856 := by exact prefixLift 2897856
  have htrace : WordTrace (prefixWord ++ tailWord_2897856) baseStart_2897856 baseEnd_2897856 := by
    simpa [prefixWord, tailWord_2897856, baseEnd_2897856] using wordTrace_append hprefix tailTrace_2897856
  have hstable : (prefixWord ++ tailWord_2897856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897856).length < 2 ^ (prefixWord ++ tailWord_2897856).sum := by decide
  have hdescent : baseEnd_2897856 < baseStart_2897856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897888 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_2897888 : Nat := 118140960795 + 2897888 * 2 ^ 59
def prefixEnd_2897888 : Nat := 4983230072969 + 3 ^ 40 * 2897888 * 2
def baseEnd_2897888 : Nat := 992006284597642155715241

theorem tailTrace_2897888 : CollatzResearch.WordTrace tailWord_2897888 prefixEnd_2897888 992006284597642155715241 := by
  unfold tailWord_2897888
  simp only [CollatzResearch.WordTrace]
  refine ⟨52847329262727085356463159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70463105683636113808617545 52847329262727085356463159)
  ·
    refine ⟨79270993894090628034694739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52847329262727085356463159 79270993894090628034694739)
    ·
      refine ⟨118906490841135942052042109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79270993894090628034694739 118906490841135942052042109)
      ·
        refine ⟨44589934065425978269515791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118906490841135942052042109 44589934065425978269515791)
        ·
          refine ⟨66884901098138967404273687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44589934065425978269515791 66884901098138967404273687)
          ·
            refine ⟨100327351647208451106410531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66884901098138967404273687 100327351647208451106410531)
            ·
              refine ⟨150491027470812676659615797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100327351647208451106410531 150491027470812676659615797)
              ·
                refine ⟨14108533825388688436838981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150491027470812676659615797 14108533825388688436838981)
                ·
                  refine ⟨2645350092260379081907309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14108533825388688436838981 2645350092260379081907309)
                  ·
                    refine ⟨992006284597642155715241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645350092260379081907309 992006284597642155715241)
                    ·
                      rfl

theorem cell22_2897888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_2897888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897888 prefixEnd_2897888 := by exact prefixLift 2897888
  have htrace : WordTrace (prefixWord ++ tailWord_2897888) baseStart_2897888 baseEnd_2897888 := by
    simpa [prefixWord, tailWord_2897888, baseEnd_2897888] using wordTrace_append hprefix tailTrace_2897888
  have hstable : (prefixWord ++ tailWord_2897888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897888).length < 2 ^ (prefixWord ++ tailWord_2897888).sum := by decide
  have hdescent : baseEnd_2897888 < baseStart_2897888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897905 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_2897905 : Nat := 118140960795 + 2897905 * 2 ^ 59
def prefixEnd_2897905 : Nat := 4983230072969 + 3 ^ 40 * 2897905 * 2
def baseEnd_2897905 : Nat := 992012104045059778040189

theorem tailTrace_2897905 : CollatzResearch.WordTrace tailWord_2897905 prefixEnd_2897905 992012104045059778040189 := by
  unfold tailWord_2897905
  simp only [CollatzResearch.WordTrace]
  refine ⟨105695278566392582616295169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70463519044261721744196779 105695278566392582616295169)
  ·
    refine ⟨79271458924794436962221377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105695278566392582616295169 79271458924794436962221377)
    ·
      refine ⟨59453594193595827721666033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79271458924794436962221377 59453594193595827721666033)
      ·
        refine ⟨44590195645196870791249525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59453594193595827721666033 44590195645196870791249525)
        ·
          refine ⟨4180330841737206636679643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44590195645196870791249525 4180330841737206636679643)
          ·
            refine ⟨6270496262605809955019465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180330841737206636679643 6270496262605809955019465)
            ·
              refine ⟨4702872196954357466264599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270496262605809955019465 4702872196954357466264599)
              ·
                refine ⟨7054308295431536199396899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702872196954357466264599 7054308295431536199396899)
                ·
                  refine ⟨10581462443147304299095349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7054308295431536199396899 10581462443147304299095349)
                  ·
                    refine ⟨992012104045059778040189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10581462443147304299095349 992012104045059778040189)
                    ·
                      rfl

theorem cell22_2897905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_2897905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897905 prefixEnd_2897905 := by exact prefixLift 2897905
  have htrace : WordTrace (prefixWord ++ tailWord_2897905) baseStart_2897905 baseEnd_2897905 := by
    simpa [prefixWord, tailWord_2897905, baseEnd_2897905] using wordTrace_append hprefix tailTrace_2897905
  have hstable : (prefixWord ++ tailWord_2897905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897905).length < 2 ^ (prefixWord ++ tailWord_2897905).sum := by decide
  have hdescent : baseEnd_2897905 < baseStart_2897905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897924 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_2897924 : Nat := 118140960795 + 2897924 * 2 ^ 59
def prefixEnd_2897924 : Nat := 4983230072969 + 3 ^ 40 * 2897924 * 2
def baseEnd_2897924 : Nat := 330672869377783353938377

theorem tailTrace_2897924 : CollatzResearch.WordTrace tailWord_2897924 prefixEnd_2897924 330672869377783353938377 := by
  unfold tailWord_2897924
  simp only [CollatzResearch.WordTrace]
  refine ⟨52847985776661874430618413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70463981035549165907491217 52847985776661874430618413)
  ·
    refine ⟨19817994666248202911481905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52847985776661874430618413 19817994666248202911481905)
    ·
      refine ⟨14863495999686152183611429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19817994666248202911481905 14863495999686152183611429)
      ·
        refine ⟨2786905499941153534427143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14863495999686152183611429 2786905499941153534427143)
        ·
          refine ⟨4180358249911730301640715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786905499941153534427143 4180358249911730301640715)
          ·
            refine ⟨6270537374867595452461073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180358249911730301640715 6270537374867595452461073)
            ·
              refine ⟨4702903031150696589345805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270537374867595452461073 4702903031150696589345805)
              ·
                refine ⟨1763588636681511221004677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4702903031150696589345805 1763588636681511221004677)
                ·
                  refine ⟨330672869377783353938377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763588636681511221004677 330672869377783353938377)
                  ·
                    rfl

theorem cell22_2897924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_2897924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897924 prefixEnd_2897924 := by exact prefixLift 2897924
  have htrace : WordTrace (prefixWord ++ tailWord_2897924) baseStart_2897924 baseEnd_2897924 := by
    simpa [prefixWord, tailWord_2897924, baseEnd_2897924] using wordTrace_append hprefix tailTrace_2897924
  have hstable : (prefixWord ++ tailWord_2897924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897924).length < 2 ^ (prefixWord ++ tailWord_2897924).sum := by decide
  have hdescent : baseEnd_2897924 < baseStart_2897924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897984 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 1, 3]
def baseStart_2897984 : Nat := 118140960795 + 2897984 * 2 ^ 59
def prefixEnd_2897984 : Nat := 4983230072969 + 3 ^ 40 * 2897984 * 2
def baseEnd_2897984 : Nat := 992039147359529905314947

theorem tailTrace_2897984 : CollatzResearch.WordTrace tailWord_2897984 prefixEnd_2897984 992039147359529905314947 := by
  unfold tailWord_2897984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52849079966553189554210503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70465439955404252738947337 52849079966553189554210503)
  ·
    refine ⟨79273619949829784331315755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52849079966553189554210503 79273619949829784331315755)
    ·
      refine ⟨118910429924744676496973633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79273619949829784331315755 118910429924744676496973633)
      ·
        refine ⟨89182822443558507372730225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118910429924744676496973633 89182822443558507372730225)
        ·
          refine ⟨66887116832668880529547669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89182822443558507372730225 66887116832668880529547669)
          ·
            refine ⟨3135333601531353774822547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66887116832668880529547669 3135333601531353774822547)
            ·
              refine ⟨4703000402297030662233821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135333601531353774822547 4703000402297030662233821)
              ·
                refine ⟨1763625150861386498337683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4703000402297030662233821 1763625150861386498337683)
                ·
                  refine ⟨2645437726292079747506525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763625150861386498337683 2645437726292079747506525)
                  ·
                    refine ⟨992039147359529905314947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645437726292079747506525 992039147359529905314947)
                    ·
                      rfl

theorem cell22_2897984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_2897984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2897984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2897984 prefixEnd_2897984 := by exact prefixLift 2897984
  have htrace : WordTrace (prefixWord ++ tailWord_2897984) baseStart_2897984 baseEnd_2897984 := by
    simpa [prefixWord, tailWord_2897984, baseEnd_2897984] using wordTrace_append hprefix tailTrace_2897984
  have hstable : (prefixWord ++ tailWord_2897984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897984).length < 2 ^ (prefixWord ++ tailWord_2897984).sum := by decide
  have hdescent : baseEnd_2897984 < baseStart_2897984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898053 : List Nat := [1, 3, 1, 1, 5, 11]
def baseStart_2898053 : Nat := 118140960795 + 2898053 * 2 ^ 59
def prefixEnd_2898053 : Nat := 4983230072969 + 3 ^ 40 * 2898053 * 2
def baseEnd_2898053 : Nat := 12247688487279465744935

theorem tailTrace_2898053 : CollatzResearch.WordTrace tailWord_2898053 prefixEnd_2898053 12247688487279465744935 := by
  unfold tailWord_2898053
  simp only [CollatzResearch.WordTrace]
  refine ⟨105700676569856403892682813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70467117713237602595121875 105700676569856403892682813)
  ·
    refine ⟨39637753713696151459756055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105700676569856403892682813 39637753713696151459756055)
    ·
      refine ⟨59456630570544227189634083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39637753713696151459756055 59456630570544227189634083)
      ·
        refine ⟨89184945855816340784451125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59456630570544227189634083 89184945855816340784451125)
        ·
          refine ⟨8361088673982781948542293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89184945855816340784451125 8361088673982781948542293)
          ·
            refine ⟨12247688487279465744935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8361088673982781948542293 12247688487279465744935)
            ·
              rfl

theorem cell22_2898053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 11].length) (baseStart_2898053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898053 prefixEnd_2898053 := by exact prefixLift 2898053
  have htrace : WordTrace (prefixWord ++ tailWord_2898053) baseStart_2898053 baseEnd_2898053 := by
    simpa [prefixWord, tailWord_2898053, baseEnd_2898053] using wordTrace_append hprefix tailTrace_2898053
  have hstable : (prefixWord ++ tailWord_2898053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898053).length < 2 ^ (prefixWord ++ tailWord_2898053).sum := by decide
  have hdescent : baseEnd_2898053 < baseStart_2898053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898055 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2898055 : Nat := 118140960795 + 2898055 * 2 ^ 59
def prefixEnd_2898055 : Nat := 4983230072969 + 3 ^ 40 * 2898055 * 2
def baseEnd_2898055 : Nat := 992063452110509386789729

theorem tailTrace_2898055 : CollatzResearch.WordTrace tailWord_2898055 prefixEnd_2898055 992063452110509386789729 := by
  unfold tailWord_2898055
  simp only [CollatzResearch.WordTrace]
  refine ⟨105700749515849158234255619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70467166343899438822837079 105700749515849158234255619)
  ·
    refine ⟨158551124273773737351383429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105700749515849158234255619 158551124273773737351383429)
    ·
      refine ⟨29728335801332575753384393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158551124273773737351383429 29728335801332575753384393)
      ·
        refine ⟨22296251850999431815038295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29728335801332575753384393 22296251850999431815038295)
        ·
          refine ⟨33444377776499147722557443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22296251850999431815038295 33444377776499147722557443)
          ·
            refine ⟨50166566664748721583836165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33444377776499147722557443 50166566664748721583836165)
            ·
              refine ⟨9406231249640385296969281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50166566664748721583836165 9406231249640385296969281)
              ·
                refine ⟨7054673437230288972726961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9406231249640385296969281 7054673437230288972726961)
                ·
                  refine ⟨5291005077922716729545221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054673437230288972726961 5291005077922716729545221)
                  ·
                    refine ⟨992063452110509386789729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291005077922716729545221 992063452110509386789729)
                    ·
                      rfl

theorem cell22_2898055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2898055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898055 prefixEnd_2898055 := by exact prefixLift 2898055
  have htrace : WordTrace (prefixWord ++ tailWord_2898055) baseStart_2898055 baseEnd_2898055 := by
    simpa [prefixWord, tailWord_2898055, baseEnd_2898055] using wordTrace_append hprefix tailTrace_2898055
  have hstable : (prefixWord ++ tailWord_2898055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898055).length < 2 ^ (prefixWord ++ tailWord_2898055).sum := by decide
  have hdescent : baseEnd_2898055 < baseStart_2898055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898057 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_2898057 : Nat := 118140960795 + 2898057 * 2 ^ 59
def prefixEnd_2898057 : Nat := 4983230072969 + 3 ^ 40 * 2898057 * 2
def baseEnd_2898057 : Nat := 992064136751382048239723

theorem tailTrace_2898057 : CollatzResearch.WordTrace tailWord_2898057 prefixEnd_2898057 992064136751382048239723 := by
  unfold tailWord_2898057
  simp only [CollatzResearch.WordTrace]
  refine ⟨105700822461841912575828425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70467214974561275050552283 105700822461841912575828425)
  ·
    refine ⟨79275616846381434431871319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105700822461841912575828425 79275616846381434431871319)
    ·
      refine ⟨118913425269572151647806979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79275616846381434431871319 118913425269572151647806979)
      ·
        refine ⟨178370137904358227471710469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118913425269572151647806979 178370137904358227471710469)
        ·
          refine ⟨33444400857067167650945713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178370137904358227471710469 33444400857067167650945713)
          ·
            refine ⟨25083300642800375738209285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33444400857067167650945713 25083300642800375738209285)
            ·
              refine ⟨4703118870525070450914241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25083300642800375738209285 4703118870525070450914241)
              ·
                refine ⟨3527339152893802838185681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703118870525070450914241 3527339152893802838185681)
                ·
                  refine ⟨2645504364670352128639261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527339152893802838185681 2645504364670352128639261)
                  ·
                    refine ⟨992064136751382048239723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645504364670352128639261 992064136751382048239723)
                    ·
                      rfl

theorem cell22_2898057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_2898057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898057 prefixEnd_2898057 := by exact prefixLift 2898057
  have htrace : WordTrace (prefixWord ++ tailWord_2898057) baseStart_2898057 baseEnd_2898057 := by
    simpa [prefixWord, tailWord_2898057, baseEnd_2898057] using wordTrace_append hprefix tailTrace_2898057
  have hstable : (prefixWord ++ tailWord_2898057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898057).length < 2 ^ (prefixWord ++ tailWord_2898057).sum := by decide
  have hdescent : baseEnd_2898057 < baseStart_2898057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898183 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 5]
def baseStart_2898183 : Nat := 118140960795 + 2898183 * 2 ^ 59
def prefixEnd_2898183 : Nat := 4983230072969 + 3 ^ 40 * 2898183 * 2
def baseEnd_2898183 : Nat := 330702423042119906529779

theorem tailTrace_2898183 : CollatzResearch.WordTrace tailWord_2898183 prefixEnd_2898183 330702423042119906529779 := by
  unfold tailWord_2898183
  simp only [CollatzResearch.WordTrace]
  refine ⟨105705418059385436094915203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70470278706256957396610135 105705418059385436094915203)
  ·
    refine ⟨158558127089078154142372805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105705418059385436094915203 158558127089078154142372805)
    ·
      refine ⟨29729648829202153901694901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158558127089078154142372805 29729648829202153901694901)
      ·
        refine ⟨2787154577737701928283897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29729648829202153901694901 2787154577737701928283897)
        ·
          refine ⟨2090365933303276446212923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2787154577737701928283897 2090365933303276446212923)
          ·
            refine ⟨3135548899954914669319385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090365933303276446212923 3135548899954914669319385)
            ·
              refine ⟨2351661674966186001989539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135548899954914669319385 2351661674966186001989539)
              ·
                refine ⟨3527492512449279002984309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351661674966186001989539 3527492512449279002984309)
                ·
                  refine ⟨330702423042119906529779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527492512449279002984309 330702423042119906529779)
                  ·
                    rfl

theorem cell22_2898183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 5].length) (baseStart_2898183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898183 prefixEnd_2898183 := by exact prefixLift 2898183
  have htrace : WordTrace (prefixWord ++ tailWord_2898183) baseStart_2898183 baseEnd_2898183 := by
    simpa [prefixWord, tailWord_2898183, baseEnd_2898183] using wordTrace_append hprefix tailTrace_2898183
  have hstable : (prefixWord ++ tailWord_2898183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898183).length < 2 ^ (prefixWord ++ tailWord_2898183).sum := by decide
  have hdescent : baseEnd_2898183 < baseStart_2898183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898207 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_2898207 : Nat := 118140960795 + 2898207 * 2 ^ 59
def prefixEnd_2898207 : Nat := 4983230072969 + 3 ^ 40 * 2898207 * 2
def baseEnd_2898207 : Nat := 992115484816831656989263

theorem tailTrace_2898207 : CollatzResearch.WordTrace tailWord_2898207 prefixEnd_2898207 992115484816831656989263 := by
  unfold tailWord_2898207
  simp only [CollatzResearch.WordTrace]
  refine ⟨105706293411298488193788875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70470862274198992129192583 105706293411298488193788875)
  ·
    refine ⟨158559440116947732290683313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105706293411298488193788875 158559440116947732290683313)
    ·
      refine ⟨118919580087710799218012485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158559440116947732290683313 118919580087710799218012485)
      ·
        refine ⟨22297421266445774853377341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118919580087710799218012485 22297421266445774853377341)
        ·
          refine ⟨8361532974917165570016503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22297421266445774853377341 8361532974917165570016503)
          ·
            refine ⟨12542299462375748355024755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361532974917165570016503 12542299462375748355024755)
            ·
              refine ⟨18813449193563622532537133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12542299462375748355024755 18813449193563622532537133)
              ·
                refine ⟨7055043447586358449701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18813449193563622532537133 7055043447586358449701425)
                ·
                  refine ⟨5291282585689768837276069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055043447586358449701425 5291282585689768837276069)
                  ·
                    refine ⟨992115484816831656989263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291282585689768837276069 992115484816831656989263)
                    ·
                      rfl

theorem cell22_2898207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_2898207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898207 prefixEnd_2898207 := by exact prefixLift 2898207
  have htrace : WordTrace (prefixWord ++ tailWord_2898207) baseStart_2898207 baseEnd_2898207 := by
    simpa [prefixWord, tailWord_2898207, baseEnd_2898207] using wordTrace_append hprefix tailTrace_2898207
  have hstable : (prefixWord ++ tailWord_2898207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898207).length < 2 ^ (prefixWord ++ tailWord_2898207).sum := by decide
  have hdescent : baseEnd_2898207 < baseStart_2898207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898222 : List Nat := [4, 1, 3, 3, 11]
def baseStart_2898222 : Nat := 118140960795 + 2898222 * 2 ^ 59
def prefixEnd_2898222 : Nat := 4983230072969 + 3 ^ 40 * 2898222 * 2
def baseEnd_2898222 : Nat := 4082800903799903777219

theorem tailTrace_2898222 : CollatzResearch.WordTrace tailWord_2898222 prefixEnd_2898222 4082800903799903777219 := by
  unfold tailWord_2898222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13213355063280518219448115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70471227004162763837056613 13213355063280518219448115)
  ·
    refine ⟨19820032594920777329172173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13213355063280518219448115 19820032594920777329172173)
    ·
      refine ⟨7432512223095291498439565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19820032594920777329172173 7432512223095291498439565)
      ·
        refine ⟨2787192083660734311914837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7432512223095291498439565 2787192083660734311914837)
        ·
          refine ⟨4082800903799903777219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2787192083660734311914837 4082800903799903777219)
          ·
            rfl

theorem cell22_2898222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 11].length) (baseStart_2898222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898222 prefixEnd_2898222 := by exact prefixLift 2898222
  have htrace : WordTrace (prefixWord ++ tailWord_2898222) baseStart_2898222 baseEnd_2898222 := by
    simpa [prefixWord, tailWord_2898222, baseEnd_2898222] using wordTrace_append hprefix tailTrace_2898222
  have hstable : (prefixWord ++ tailWord_2898222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898222).length < 2 ^ (prefixWord ++ tailWord_2898222).sum := by decide
  have hdescent : baseEnd_2898222 < baseStart_2898222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898226 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_2898226 : Nat := 118140960795 + 2898226 * 2 ^ 59
def prefixEnd_2898226 : Nat := 4983230072969 + 3 ^ 40 * 2898226 * 2
def baseEnd_2898226 : Nat := 992121988905121940764205

theorem tailTrace_2898226 : CollatzResearch.WordTrace tailWord_2898226 prefixEnd_2898226 992121988905121940764205 := by
  unfold tailWord_2898226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26426746599557413609682633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70471324265486436292487021 26426746599557413609682633)
  ·
    refine ⟨19820059949668060207261975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26426746599557413609682633 19820059949668060207261975)
    ·
      refine ⟨29730089924502090310892963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19820059949668060207261975 29730089924502090310892963)
      ·
        refine ⟨44595134886753135466339445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29730089924502090310892963 44595134886753135466339445)
        ·
          refine ⟨4180793895633106449969323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44595134886753135466339445 4180793895633106449969323)
          ·
            refine ⟨6271190843449659674953985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180793895633106449969323 6271190843449659674953985)
            ·
              refine ⟨4703393132587244756215489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6271190843449659674953985 4703393132587244756215489)
              ·
                refine ⟨3527544849440433567161617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703393132587244756215489 3527544849440433567161617)
                ·
                  refine ⟨2645658637080325175371213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527544849440433567161617 2645658637080325175371213)
                  ·
                    refine ⟨992121988905121940764205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645658637080325175371213 992121988905121940764205)
                    ·
                      rfl

theorem cell22_2898226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_2898226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898226 prefixEnd_2898226 := by exact prefixLift 2898226
  have htrace : WordTrace (prefixWord ++ tailWord_2898226) baseStart_2898226 baseEnd_2898226 := by
    simpa [prefixWord, tailWord_2898226, baseEnd_2898226] using wordTrace_append hprefix tailTrace_2898226
  have hstable : (prefixWord ++ tailWord_2898226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898226).length < 2 ^ (prefixWord ++ tailWord_2898226).sum := by decide
  have hdescent : baseEnd_2898226 < baseStart_2898226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898228 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2898228 : Nat := 118140960795 + 2898228 * 2 ^ 59
def prefixEnd_2898228 : Nat := 4983230072969 + 3 ^ 40 * 2898228 * 2
def baseEnd_2898228 : Nat := 330707557848664867404733

theorem tailTrace_2898228 : CollatzResearch.WordTrace tailWord_2898228 prefixEnd_2898228 330707557848664867404733 := by
  unfold tailWord_2898228
  simp only [CollatzResearch.WordTrace]
  refine ⟨52853529672111204390151669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70471372896148272520202225 52853529672111204390151669)
  ·
    refine ⟨4955018406760425411576719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52853529672111204390151669 4955018406760425411576719)
    ·
      refine ⟨7432527610140638117365079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955018406760425411576719 7432527610140638117365079)
      ·
        refine ⟨11148791415210957176047619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432527610140638117365079 11148791415210957176047619)
        ·
          refine ⟨16723187122816435764071429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148791415210957176047619 16723187122816435764071429)
          ·
            refine ⟨3135597585528081705763393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16723187122816435764071429 3135597585528081705763393)
            ·
              refine ⟨2351698189146061279322545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135597585528081705763393 2351698189146061279322545)
              ·
                refine ⟨1763773641859545959491909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351698189146061279322545 1763773641859545959491909)
                ·
                  refine ⟨330707557848664867404733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763773641859545959491909 330707557848664867404733)
                  ·
                    rfl

theorem cell22_2898228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2898228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898228 prefixEnd_2898228 := by exact prefixLift 2898228
  have htrace : WordTrace (prefixWord ++ tailWord_2898228) baseStart_2898228 baseEnd_2898228 := by
    simpa [prefixWord, tailWord_2898228, baseEnd_2898228] using wordTrace_append hprefix tailTrace_2898228
  have hstable : (prefixWord ++ tailWord_2898228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898228).length < 2 ^ (prefixWord ++ tailWord_2898228).sum := by decide
  have hdescent : baseEnd_2898228 < baseStart_2898228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898250 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_2898250 : Nat := 118140960795 + 2898250 * 2 ^ 59
def prefixEnd_2898250 : Nat := 4983230072969 + 3 ^ 40 * 2898250 * 2
def baseEnd_2898250 : Nat := 330710068198531292721377

theorem tailTrace_2898250 : CollatzResearch.WordTrace tailWord_2898250 prefixEnd_2898250 330710068198531292721377 := by
  unfold tailWord_2898250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26426965437535676634401051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70471907833428471025069469 26426965437535676634401051)
  ·
    refine ⟨39640448156303514951601577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26426965437535676634401051 39640448156303514951601577)
    ·
      refine ⟨29730336117227636213701183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39640448156303514951601577 29730336117227636213701183)
      ·
        refine ⟨44595504175841454320551775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29730336117227636213701183 44595504175841454320551775)
        ·
          refine ⟨66893256263762181480827663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44595504175841454320551775 66893256263762181480827663)
          ·
            refine ⟨100339884395643272221241495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66893256263762181480827663 100339884395643272221241495)
            ·
              refine ⟨150509826593464908331862243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100339884395643272221241495 150509826593464908331862243)
              ·
                refine ⟨225764739890197362497793365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150509826593464908331862243 225764739890197362497793365)
                ·
                  refine ⟨330710068198531292721377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 225764739890197362497793365 330710068198531292721377)
                  ·
                    rfl

theorem cell22_2898250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_2898250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898250 prefixEnd_2898250 := by exact prefixLift 2898250
  have htrace : WordTrace (prefixWord ++ tailWord_2898250) baseStart_2898250 baseEnd_2898250 := by
    simpa [prefixWord, tailWord_2898250, baseEnd_2898250] using wordTrace_append hprefix tailTrace_2898250
  have hstable : (prefixWord ++ tailWord_2898250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898250).length < 2 ^ (prefixWord ++ tailWord_2898250).sum := by decide
  have hdescent : baseEnd_2898250 < baseStart_2898250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898265 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_2898265 : Nat := 118140960795 + 2898265 * 2 ^ 59
def prefixEnd_2898265 : Nat := 4983230072969 + 3 ^ 40 * 2898265 * 2
def baseEnd_2898265 : Nat := 992135339402138839039085

theorem tailTrace_2898265 : CollatzResearch.WordTrace tailWord_2898265 prefixEnd_2898265 992135339402138839039085 := by
  unfold tailWord_2898265
  simp only [CollatzResearch.WordTrace]
  refine ⟨105708408845088364099400249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70472272563392242732933499 105708408845088364099400249)
  ·
    refine ⟨79281306633816273074550187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105708408845088364099400249 79281306633816273074550187)
    ·
      refine ⟨118921959950724409611825281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79281306633816273074550187 118921959950724409611825281)
      ·
        refine ⟨89191469963043307208868961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118921959950724409611825281 89191469963043307208868961)
        ·
          refine ⟨66893602472282480406651721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89191469963043307208868961 66893602472282480406651721)
          ·
            refine ⟨50170201854211860304988791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66893602472282480406651721 50170201854211860304988791)
            ·
              refine ⟨75255302781317790457483187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50170201854211860304988791 75255302781317790457483187)
              ·
                refine ⟨112882954171976685686224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75255302781317790457483187 112882954171976685686224781)
                ·
                  refine ⟨42331107814491257132334293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112882954171976685686224781 42331107814491257132334293)
                  ·
                    refine ⟨992135339402138839039085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42331107814491257132334293 992135339402138839039085)
                    ·
                      rfl

theorem cell22_2898265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_2898265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898265 prefixEnd_2898265 := by exact prefixLift 2898265
  have htrace : WordTrace (prefixWord ++ tailWord_2898265) baseStart_2898265 baseEnd_2898265 := by
    simpa [prefixWord, tailWord_2898265, baseEnd_2898265] using wordTrace_append hprefix tailTrace_2898265
  have hstable : (prefixWord ++ tailWord_2898265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898265).length < 2 ^ (prefixWord ++ tailWord_2898265).sum := by decide
  have hdescent : baseEnd_2898265 < baseStart_2898265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898312 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_2898312 : Nat := 118140960795 + 2898312 * 2 ^ 59
def prefixEnd_2898312 : Nat := 4983230072969 + 3 ^ 40 * 2898312 * 2
def baseEnd_2898312 : Nat := 330717142820882127704647

theorem tailTrace_2898312 : CollatzResearch.WordTrace tailWord_2898312 prefixEnd_2898312 330717142820882127704647 := by
  unfold tailWord_2898312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52855061537959045563180595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70473415383945394084240793 52855061537959045563180595)
  ·
    refine ⟨79282592306938568344770893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52855061537959045563180595 79282592306938568344770893)
    ·
      refine ⟨29730972115101963129289085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79282592306938568344770893 29730972115101963129289085)
      ·
        refine ⟨11149114543163236173483407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29730972115101963129289085 11149114543163236173483407)
        ·
          refine ⟨16723671814744854260225111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149114543163236173483407 16723671814744854260225111)
          ·
            refine ⟨25085507722117281390337667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16723671814744854260225111 25085507722117281390337667)
            ·
              refine ⟨37628261583175922085506501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25085507722117281390337667 37628261583175922085506501)
              ·
                refine ⟨7055299046845485391032469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37628261583175922085506501 7055299046845485391032469)
                ·
                  refine ⟨330717142820882127704647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7055299046845485391032469 330717142820882127704647)
                  ·
                    rfl

theorem cell22_2898312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_2898312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898312 prefixEnd_2898312 := by exact prefixLift 2898312
  have htrace : WordTrace (prefixWord ++ tailWord_2898312) baseStart_2898312 baseEnd_2898312 := by
    simpa [prefixWord, tailWord_2898312, baseEnd_2898312] using wordTrace_append hprefix tailTrace_2898312
  have hstable : (prefixWord ++ tailWord_2898312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898312).length < 2 ^ (prefixWord ++ tailWord_2898312).sum := by decide
  have hdescent : baseEnd_2898312 < baseStart_2898312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898327 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_2898327 : Nat := 118140960795 + 2898327 * 2 ^ 59
def prefixEnd_2898327 : Nat := 4983230072969 + 3 ^ 40 * 2898327 * 2
def baseEnd_2898327 : Nat := 992156563269191343988895

theorem tailTrace_2898327 : CollatzResearch.WordTrace tailWord_2898327 prefixEnd_2898327 992156563269191343988895 := by
  unfold tailWord_2898327
  simp only [CollatzResearch.WordTrace]
  refine ⟨105710670170863748688157235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70473780113909165792104823 105710670170863748688157235)
  ·
    refine ⟨158566005256295623032235853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105710670170863748688157235 158566005256295623032235853)
    ·
      refine ⟨59462251971110858637088445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158566005256295623032235853 59462251971110858637088445)
      ·
        refine ⟨22298344489166571988908167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59462251971110858637088445 22298344489166571988908167)
        ·
          refine ⟨33447516733749857983362251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22298344489166571988908167 33447516733749857983362251)
          ·
            refine ⟨50171275100624786975043377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33447516733749857983362251 50171275100624786975043377)
            ·
              refine ⟨37628456325468590231282533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50171275100624786975043377 37628456325468590231282533)
              ·
                refine ⟨7055335561025360668365475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37628456325468590231282533 7055335561025360668365475)
                ·
                  refine ⟨10583003341538041002548213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055335561025360668365475 10583003341538041002548213)
                  ·
                    refine ⟨992156563269191343988895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10583003341538041002548213 992156563269191343988895)
                    ·
                      rfl

theorem cell22_2898327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_2898327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898327 prefixEnd_2898327 := by exact prefixLift 2898327
  have htrace : WordTrace (prefixWord ++ tailWord_2898327) baseStart_2898327 baseEnd_2898327 := by
    simpa [prefixWord, tailWord_2898327, baseEnd_2898327] using wordTrace_append hprefix tailTrace_2898327
  have hstable : (prefixWord ++ tailWord_2898327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898327).length < 2 ^ (prefixWord ++ tailWord_2898327).sum := by decide
  have hdescent : baseEnd_2898327 < baseStart_2898327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898361 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_2898361 : Nat := 118140960795 + 2898361 * 2 ^ 59
def prefixEnd_2898361 : Nat := 4983230072969 + 3 ^ 40 * 2898361 * 2
def baseEnd_2898361 : Nat := 992168202164026588638791

theorem tailTrace_2898361 : CollatzResearch.WordTrace tailWord_2898361 prefixEnd_2898361 992168202164026588638791 := by
  unfold tailWord_2898361
  simp only [CollatzResearch.WordTrace]
  refine ⟨105711910252740572494894937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70474606835160381663263291 105711910252740572494894937)
  ·
    refine ⟨79283932689555429371171203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105711910252740572494894937 79283932689555429371171203)
    ·
      refine ⟨118925899034333144056756805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79283932689555429371171203 118925899034333144056756805)
      ·
        refine ⟨22298606068937464510641901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118925899034333144056756805 22298606068937464510641901)
        ·
          refine ⟨8361977275851549191490713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22298606068937464510641901 8361977275851549191490713)
          ·
            refine ⟨6271482956888661893618035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8361977275851549191490713 6271482956888661893618035)
            ·
              refine ⟨9407224435332992840427053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6271482956888661893618035 9407224435332992840427053)
              ·
                refine ⟨3527709163249872315160145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9407224435332992840427053 3527709163249872315160145)
                ·
                  refine ⟨2645781872437404236370109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527709163249872315160145 2645781872437404236370109)
                  ·
                    refine ⟨992168202164026588638791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645781872437404236370109 992168202164026588638791)
                    ·
                      rfl

theorem cell22_2898361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_2898361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898361 prefixEnd_2898361 := by exact prefixLift 2898361
  have htrace : WordTrace (prefixWord ++ tailWord_2898361) baseStart_2898361 baseEnd_2898361 := by
    simpa [prefixWord, tailWord_2898361, baseEnd_2898361] using wordTrace_append hprefix tailTrace_2898361
  have hstable : (prefixWord ++ tailWord_2898361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898361).length < 2 ^ (prefixWord ++ tailWord_2898361).sum := by decide
  have hdescent : baseEnd_2898361 < baseStart_2898361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898569 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_2898569 : Nat := 118140960795 + 2898569 * 2 ^ 59
def prefixEnd_2898569 : Nat := 4983230072969 + 3 ^ 40 * 2898569 * 2
def baseEnd_2898569 : Nat := 992239404814783379438153

theorem tailTrace_2898569 : CollatzResearch.WordTrace tailWord_2898569 prefixEnd_2898569 992239404814783379438153 := by
  unfold tailWord_2898569
  simp only [CollatzResearch.WordTrace]
  refine ⟨105719496635987024018466761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70479664423991349345644507 105719496635987024018466761)
  ·
    refine ⟨79289622476990268013850071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105719496635987024018466761 79289622476990268013850071)
    ·
      refine ⟨118934433715485402020775107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79289622476990268013850071 118934433715485402020775107)
      ·
        refine ⟨178401650573228103031162661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118934433715485402020775107 178401650573228103031162661)
        ·
          refine ⟨33450309482480269318342999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178401650573228103031162661 33450309482480269318342999)
          ·
            refine ⟨50175464223720403977514499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33450309482480269318342999 50175464223720403977514499)
            ·
              refine ⟨75263196335580605966271749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50175464223720403977514499 75263196335580605966271749)
              ·
                refine ⟨14111849312921363618675953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75263196335580605966271749 14111849312921363618675953)
                ·
                  refine ⟨10583886984691022714006965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14111849312921363618675953 10583886984691022714006965)
                  ·
                    refine ⟨992239404814783379438153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10583886984691022714006965 992239404814783379438153)
                    ·
                      rfl

theorem cell22_2898569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_2898569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898569 prefixEnd_2898569 := by exact prefixLift 2898569
  have htrace : WordTrace (prefixWord ++ tailWord_2898569) baseStart_2898569 baseEnd_2898569 := by
    simpa [prefixWord, tailWord_2898569, baseEnd_2898569] using wordTrace_append hprefix tailTrace_2898569
  have hstable : (prefixWord ++ tailWord_2898569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898569).length < 2 ^ (prefixWord ++ tailWord_2898569).sum := by decide
  have hdescent : baseEnd_2898569 < baseStart_2898569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898629 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2898629 : Nat := 118140960795 + 2898629 * 2 ^ 59
def prefixEnd_2898629 : Nat := 4983230072969 + 3 ^ 40 * 2898629 * 2
def baseEnd_2898629 : Nat := 992259944040963222937969

theorem tailTrace_2898629 : CollatzResearch.WordTrace tailWord_2898629 prefixEnd_2898629 992259944040963222937969 := by
  unfold tailWord_2898629
  simp only [CollatzResearch.WordTrace]
  refine ⟨105721685015769654265650941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70481123343846436177100627 105721685015769654265650941)
  ·
    refine ⟨39645631880913620349619103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105721685015769654265650941 39645631880913620349619103)
    ·
      refine ⟨59468447821370430524428655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39645631880913620349619103 59468447821370430524428655)
      ·
        refine ⟨89202671732055645786642983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59468447821370430524428655 89202671732055645786642983)
        ·
          refine ⟨133804007598083468679964475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89202671732055645786642983 133804007598083468679964475)
          ·
            refine ⟨200706011397125203019946713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133804007598083468679964475 200706011397125203019946713)
            ·
              refine ⟨150529508547843902264960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200706011397125203019946713 150529508547843902264960035)
              ·
                refine ⟨225794262821765853397440053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150529508547843902264960035 225794262821765853397440053)
                ·
                  refine ⟨21168212139540548756010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225794262821765853397440053 21168212139540548756010005)
                  ·
                    refine ⟨992259944040963222937969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21168212139540548756010005 992259944040963222937969)
                    ·
                      rfl

theorem cell22_2898629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2898629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898629 prefixEnd_2898629 := by exact prefixLift 2898629
  have htrace : WordTrace (prefixWord ++ tailWord_2898629) baseStart_2898629 baseEnd_2898629 := by
    simpa [prefixWord, tailWord_2898629, baseEnd_2898629] using wordTrace_append hprefix tailTrace_2898629
  have hstable : (prefixWord ++ tailWord_2898629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898629).length < 2 ^ (prefixWord ++ tailWord_2898629).sum := by decide
  have hdescent : baseEnd_2898629 < baseStart_2898629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898648 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_2898648 : Nat := 118140960795 + 2898648 * 2 ^ 59
def prefixEnd_2898648 : Nat := 4983230072969 + 3 ^ 40 * 2898648 * 2
def baseEnd_2898648 : Nat := 992266448129253506712911

theorem tailTrace_2898648 : CollatzResearch.WordTrace tailWord_2898648 prefixEnd_2898648 992266448129253506712911 := by
  unfold tailWord_2898648
  simp only [CollatzResearch.WordTrace]
  refine ⟨52861189001350410255296299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70481585335133880340395065 52861189001350410255296299)
  ·
    refine ⟨79291783502025615382944449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52861189001350410255296299 79291783502025615382944449)
    ·
      refine ⟨59468837626519211537208337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79291783502025615382944449 59468837626519211537208337)
      ·
        refine ⟨44601628219889408652906253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59468837626519211537208337 44601628219889408652906253)
        ·
          refine ⟨16725610582458528244839845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44601628219889408652906253 16725610582458528244839845)
          ·
            refine ⟨3136051984210974045907471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16725610582458528244839845 3136051984210974045907471)
            ·
              refine ⟨4704077976316461068861207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136051984210974045907471 4704077976316461068861207)
              ·
                refine ⟨7056116964474691603291811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704077976316461068861207 7056116964474691603291811)
                ·
                  refine ⟨10584175446712037404937717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056116964474691603291811 10584175446712037404937717)
                  ·
                    refine ⟨992266448129253506712911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10584175446712037404937717 992266448129253506712911)
                    ·
                      rfl

theorem cell22_2898648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_2898648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898648 prefixEnd_2898648 := by exact prefixLift 2898648
  have htrace : WordTrace (prefixWord ++ tailWord_2898648) baseStart_2898648 baseEnd_2898648 := by
    simpa [prefixWord, tailWord_2898648, baseEnd_2898648] using wordTrace_append hprefix tailTrace_2898648
  have hstable : (prefixWord ++ tailWord_2898648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898648).length < 2 ^ (prefixWord ++ tailWord_2898648).sum := by decide
  have hdescent : baseEnd_2898648 < baseStart_2898648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898661 : List Nat := [1, 3, 1, 4, 1, 3, 1, 8]
def baseStart_2898661 : Nat := 118140960795 + 2898661 * 2 ^ 59
def prefixEnd_2898661 : Nat := 4983230072969 + 3 ^ 40 * 2898661 * 2
def baseEnd_2898661 : Nat := 110252322032769534015319

theorem tailTrace_2898661 : CollatzResearch.WordTrace tailWord_2898661 prefixEnd_2898661 110252322032769534015319 := by
  unfold tailWord_2898661
  simp only [CollatzResearch.WordTrace]
  refine ⟨105722852151653723730815837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70481901434435815820543891 105722852151653723730815837)
  ·
    refine ⟨39646069556870146399055939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105722852151653723730815837 39646069556870146399055939)
    ·
      refine ⟨59469104335305219598583909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39646069556870146399055939 59469104335305219598583909)
      ·
        refine ⟨11150457062869728674734483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59469104335305219598583909 11150457062869728674734483)
        ·
          refine ⟨16725685594304593012101725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150457062869728674734483 16725685594304593012101725)
          ·
            refine ⟨6272132097864222379538147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16725685594304593012101725 6272132097864222379538147)
            ·
              refine ⟨9408198146796333569307221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272132097864222379538147 9408198146796333569307221)
              ·
                refine ⟨110252322032769534015319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9408198146796333569307221 110252322032769534015319)
                ·
                  rfl

theorem cell22_2898661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 8].length) (baseStart_2898661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898661 prefixEnd_2898661 := by exact prefixLift 2898661
  have htrace : WordTrace (prefixWord ++ tailWord_2898661) baseStart_2898661 baseEnd_2898661 := by
    simpa [prefixWord, tailWord_2898661, baseEnd_2898661] using wordTrace_append hprefix tailTrace_2898661
  have hstable : (prefixWord ++ tailWord_2898661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898661).length < 2 ^ (prefixWord ++ tailWord_2898661).sum := by decide
  have hdescent : baseEnd_2898661 < baseStart_2898661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898783 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 4, 3]
def baseStart_2898783 : Nat := 118140960795 + 2898783 * 2 ^ 59
def prefixEnd_2898783 : Nat := 4983230072969 + 3 ^ 40 * 2898783 * 2
def baseEnd_2898783 : Nat := 992312661388158154587497

theorem tailTrace_2898783 : CollatzResearch.WordTrace tailWord_2898783 prefixEnd_2898783 992312661388158154587497 := by
  unfold tailWord_2898783
  simp only [CollatzResearch.WordTrace]
  refine ⟨105727301857211738566757003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70484867904807825711171335 105727301857211738566757003)
  ·
    refine ⟨158590952785817607850135505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105727301857211738566757003 158590952785817607850135505)
    ·
      refine ⟨118943214589363205887601629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158590952785817607850135505 118943214589363205887601629)
      ·
        refine ⟨44603705471011202207850611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118943214589363205887601629 44603705471011202207850611)
        ·
          refine ⟨66905558206516803311775917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44603705471011202207850611 66905558206516803311775917)
          ·
            refine ⟨25089584327443801241915969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66905558206516803311775917 25089584327443801241915969)
            ·
              refine ⟨18817188245582850931436977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25089584327443801241915969 18817188245582850931436977)
              ·
                refine ⟨14112891184187138198577733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18817188245582850931436977 14112891184187138198577733)
                ·
                  refine ⟨2646167097035088412233325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14112891184187138198577733 2646167097035088412233325)
                  ·
                    refine ⟨992312661388158154587497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646167097035088412233325 992312661388158154587497)
                    ·
                      rfl

theorem cell22_2898783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_2898783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898783 prefixEnd_2898783 := by exact prefixLift 2898783
  have htrace : WordTrace (prefixWord ++ tailWord_2898783) baseStart_2898783 baseEnd_2898783 := by
    simpa [prefixWord, tailWord_2898783, baseEnd_2898783] using wordTrace_append hprefix tailTrace_2898783
  have hstable : (prefixWord ++ tailWord_2898783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898783).length < 2 ^ (prefixWord ++ tailWord_2898783).sum := by decide
  have hdescent : baseEnd_2898783 < baseStart_2898783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898787 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 1, 4]
def baseStart_2898787 : Nat := 118140960795 + 2898787 * 2 ^ 59
def prefixEnd_2898787 : Nat := 4983230072969 + 3 ^ 40 * 2898787 * 2
def baseEnd_2898787 : Nat := 992314030669903477487485

theorem tailTrace_2898787 : CollatzResearch.WordTrace tailWord_2898787 prefixEnd_2898787 992314030669903477487485 := by
  unfold tailWord_2898787
  simp only [CollatzResearch.WordTrace]
  refine ⟨105727447749197247249902615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70484965166131498166601743 105727447749197247249902615)
  ·
    refine ⟨158591171623795870874853923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105727447749197247249902615 158591171623795870874853923)
    ·
      refine ⟨237886757435693806312280885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158591171623795870874853923 237886757435693806312280885)
      ·
        refine ⟨22301883509596294341776333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237886757435693806312280885 22301883509596294341776333)
        ·
          refine ⟨8363206316098610378166125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22301883509596294341776333 8363206316098610378166125)
          ·
            refine ⟨3136202368536978891812297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8363206316098610378166125 3136202368536978891812297)
            ·
              refine ⟨2352151776402734168859223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136202368536978891812297 2352151776402734168859223)
              ·
                refine ⟨3528227664604101253288835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352151776402734168859223 3528227664604101253288835)
                ·
                  refine ⟨5292341496906151879933253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528227664604101253288835 5292341496906151879933253)
                  ·
                    refine ⟨992314030669903477487485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292341496906151879933253 992314030669903477487485)
                    ·
                      rfl

theorem cell22_2898787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 4].length) (baseStart_2898787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898787 prefixEnd_2898787 := by exact prefixLift 2898787
  have htrace : WordTrace (prefixWord ++ tailWord_2898787) baseStart_2898787 baseEnd_2898787 := by
    simpa [prefixWord, tailWord_2898787, baseEnd_2898787] using wordTrace_append hprefix tailTrace_2898787
  have hstable : (prefixWord ++ tailWord_2898787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898787).length < 2 ^ (prefixWord ++ tailWord_2898787).sum := by decide
  have hdescent : baseEnd_2898787 < baseStart_2898787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898796 : List Nat := [2, 2, 1, 1, 4, 1, 11]
def baseStart_2898796 : Nat := 118140960795 + 2898796 * 2 ^ 59
def prefixEnd_2898796 : Nat := 4983230072969 + 3 ^ 40 * 2898796 * 2
def baseEnd_2898796 : Nat := 36752485613104831630091

theorem tailTrace_2898796 : CollatzResearch.WordTrace tailWord_2898796 prefixEnd_2898796 36752485613104831630091 := by
  unfold tailWord_2898796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52863888003082320893490121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70485184004109761191320161 52863888003082320893490121)
  ·
    refine ⟨39647916002311740670117591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52863888003082320893490121 39647916002311740670117591)
    ·
      refine ⟨59471874003467611005176387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39647916002311740670117591 59471874003467611005176387)
      ·
        refine ⟨89207811005201416507764581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59471874003467611005176387 89207811005201416507764581)
        ·
          refine ⟨16726464563475265595205859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89207811005201416507764581 16726464563475265595205859)
          ·
            refine ⟨25089696845212898392808789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16726464563475265595205859 25089696845212898392808789)
            ·
              refine ⟨36752485613104831630091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25089696845212898392808789 36752485613104831630091)
              ·
                rfl

theorem cell22_2898796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 11].length) (baseStart_2898796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898796 prefixEnd_2898796 := by exact prefixLift 2898796
  have htrace : WordTrace (prefixWord ++ tailWord_2898796) baseStart_2898796 baseEnd_2898796 := by
    simpa [prefixWord, tailWord_2898796, baseEnd_2898796] using wordTrace_append hprefix tailTrace_2898796
  have hstable : (prefixWord ++ tailWord_2898796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898796).length < 2 ^ (prefixWord ++ tailWord_2898796).sum := by decide
  have hdescent : baseEnd_2898796 < baseStart_2898796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898800 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_2898800 : Nat := 118140960795 + 2898800 * 2 ^ 59
def prefixEnd_2898800 : Nat := 4983230072969 + 3 ^ 40 * 2898800 * 2
def baseEnd_2898800 : Nat := 992318480835575776912445

theorem tailTrace_2898800 : CollatzResearch.WordTrace tailWord_2898800 prefixEnd_2898800 992318480835575776912445 := by
  unfold tailWord_2898800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52863960949075075235062927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70485281265433433646750569 52863960949075075235062927)
  ·
    refine ⟨79295941423612612852594391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52863960949075075235062927 79295941423612612852594391)
    ·
      refine ⟨118943912135418919278891587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79295941423612612852594391 118943912135418919278891587)
      ·
        refine ⟨178415868203128378918337381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118943912135418919278891587 178415868203128378918337381)
        ·
          refine ⟨33452975288086571047188259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178415868203128378918337381 33452975288086571047188259)
          ·
            refine ⟨50179462932129856570782389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33452975288086571047188259 50179462932129856570782389)
            ·
              refine ⟨4704324649887174053510849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50179462932129856570782389 4704324649887174053510849)
              ·
                refine ⟨3528243487415380540133137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704324649887174053510849 3528243487415380540133137)
                ·
                  refine ⟨2646182615561535405099853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528243487415380540133137 2646182615561535405099853)
                  ·
                    refine ⟨992318480835575776912445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646182615561535405099853 992318480835575776912445)
                    ·
                      rfl

theorem cell22_2898800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_2898800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898800 prefixEnd_2898800 := by exact prefixLift 2898800
  have htrace : WordTrace (prefixWord ++ tailWord_2898800) baseStart_2898800 baseEnd_2898800 := by
    simpa [prefixWord, tailWord_2898800, baseEnd_2898800] using wordTrace_append hprefix tailTrace_2898800
  have hstable : (prefixWord ++ tailWord_2898800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898800).length < 2 ^ (prefixWord ++ tailWord_2898800).sum := by decide
  have hdescent : baseEnd_2898800 < baseStart_2898800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898986 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2898986 : Nat := 118140960795 + 2898986 * 2 ^ 59
def prefixEnd_2898986 : Nat := 4983230072969 + 3 ^ 40 * 2898986 * 2
def baseEnd_2898986 : Nat := 992382152436733291761875

theorem tailTrace_2898986 : CollatzResearch.WordTrace tailWord_2898986 prefixEnd_2898986 992382152436733291761875 := by
  unfold tailWord_2898986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26433676468869076059099203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70489803916984202824264541 26433676468869076059099203)
  ·
    refine ⟨39650514703303614088648805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26433676468869076059099203 39650514703303614088648805)
    ·
      refine ⟨7434471506869427641621651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39650514703303614088648805 7434471506869427641621651)
      ·
        refine ⟨11151707260304141462432477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434471506869427641621651 11151707260304141462432477)
        ·
          refine ⟨4181890222614053048412179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11151707260304141462432477 4181890222614053048412179)
          ·
            refine ⟨6272835333921079572618269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181890222614053048412179 6272835333921079572618269)
            ·
              refine ⟨2352313250220404839731851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6272835333921079572618269 2352313250220404839731851)
              ·
                refine ⟨3528469875330607259597777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352313250220404839731851 3528469875330607259597777)
                ·
                  refine ⟨2646352406497955444698333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528469875330607259597777 2646352406497955444698333)
                  ·
                    refine ⟨992382152436733291761875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646352406497955444698333 992382152436733291761875)
                    ·
                      rfl

theorem cell22_2898986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2898986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2898986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2898986 prefixEnd_2898986 := by exact prefixLift 2898986
  have htrace : WordTrace (prefixWord ++ tailWord_2898986) baseStart_2898986 baseEnd_2898986 := by
    simpa [prefixWord, tailWord_2898986, baseEnd_2898986] using wordTrace_append hprefix tailTrace_2898986
  have hstable : (prefixWord ++ tailWord_2898986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898986).length < 2 ^ (prefixWord ++ tailWord_2898986).sum := by decide
  have hdescent : baseEnd_2898986 < baseStart_2898986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899040 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_2899040 : Nat := 118140960795 + 2899040 * 2 ^ 59
def prefixEnd_2899040 : Nat := 4983230072969 + 3 ^ 40 * 2899040 * 2
def baseEnd_2899040 : Nat := 992400637740295150911709

theorem tailTrace_2899040 : CollatzResearch.WordTrace tailWord_2899040 prefixEnd_2899040 992400637740295150911709 := by
  unfold tailWord_2899040
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868337708640335729431287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70491116944853780972575049 52868337708640335729431287)
  ·
    refine ⟨79302506562960503594146931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52868337708640335729431287 79302506562960503594146931)
    ·
      refine ⟨118953759844440755391220397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79302506562960503594146931 118953759844440755391220397)
      ·
        refine ⟨44607659941665283271707649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118953759844440755391220397 44607659941665283271707649)
        ·
          refine ⟨33455744956248962453780737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44607659941665283271707649 33455744956248962453780737)
          ·
            refine ⟨25091808717186721840335553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33455744956248962453780737 25091808717186721840335553)
            ·
              refine ⟨18818856537890041380251665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25091808717186721840335553 18818856537890041380251665)
              ·
                refine ⟨14114142403417531035188749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18818856537890041380251665 14114142403417531035188749)
                ·
                  refine ⟨5292803401281574138195781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14114142403417531035188749 5292803401281574138195781)
                  ·
                    refine ⟨992400637740295150911709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292803401281574138195781 992400637740295150911709)
                    ·
                      rfl

theorem cell22_2899040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_2899040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899040 prefixEnd_2899040 := by exact prefixLift 2899040
  have htrace : WordTrace (prefixWord ++ tailWord_2899040) baseStart_2899040 baseEnd_2899040 := by
    simpa [prefixWord, tailWord_2899040, baseEnd_2899040] using wordTrace_append hprefix tailTrace_2899040
  have hstable : (prefixWord ++ tailWord_2899040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899040).length < 2 ^ (prefixWord ++ tailWord_2899040).sum := by decide
  have hdescent : baseEnd_2899040 < baseStart_2899040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899138 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2899138 : Nat := 118140960795 + 2899138 * 2 ^ 59
def prefixEnd_2899138 : Nat := 4983230072969 + 3 ^ 40 * 2899138 * 2
def baseEnd_2899138 : Nat := 992434185143055561961409

theorem tailTrace_2899138 : CollatzResearch.WordTrace tailWord_2899138 prefixEnd_2899138 992434185143055561961409 := by
  unfold tailWord_2899138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26435062442731408548982517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70493499847283756130620045 26435062442731408548982517)
  ·
    refine ⟨2478287104006069551467111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26435062442731408548982517 2478287104006069551467111)
    ·
      refine ⟨3717430656009104327200667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478287104006069551467111 3717430656009104327200667)
      ·
        refine ⟨5576145984013656490801001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717430656009104327200667 5576145984013656490801001)
        ·
          refine ⟨4182109488010242368100751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5576145984013656490801001 4182109488010242368100751)
          ·
            refine ⟨6273164232015363552151127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182109488010242368100751 6273164232015363552151127)
            ·
              refine ⟨9409746348023045328226691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273164232015363552151127 9409746348023045328226691)
              ·
                refine ⟨14114619522034567992340037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9409746348023045328226691 14114619522034567992340037)
                ·
                  refine ⟨2646491160381481498563757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14114619522034567992340037 2646491160381481498563757)
                  ·
                    refine ⟨992434185143055561961409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646491160381481498563757 992434185143055561961409)
                    ·
                      rfl

theorem cell22_2899138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2899138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899138 prefixEnd_2899138 := by exact prefixLift 2899138
  have htrace : WordTrace (prefixWord ++ tailWord_2899138) baseStart_2899138 baseEnd_2899138 := by
    simpa [prefixWord, tailWord_2899138, baseEnd_2899138] using wordTrace_append hprefix tailTrace_2899138
  have hstable : (prefixWord ++ tailWord_2899138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899138).length < 2 ^ (prefixWord ++ tailWord_2899138).sum := by decide
  have hdescent : baseEnd_2899138 < baseStart_2899138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899183 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 1, 3]
def baseStart_2899183 : Nat := 118140960795 + 2899183 * 2 ^ 59
def prefixEnd_2899183 : Nat := 4983230072969 + 3 ^ 40 * 2899183 * 2
def baseEnd_2899183 : Nat := 992449589562690444586271

theorem tailTrace_2899183 : CollatzResearch.WordTrace tailWord_2899183 prefixEnd_2899183 992449589562690444586271 := by
  unfold tailWord_2899183
  simp only [CollatzResearch.WordTrace]
  refine ⟨105741891055762606881318203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70494594037175071254212135 105741891055762606881318203)
  ·
    refine ⟨158612836583643910321977305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105741891055762606881318203 158612836583643910321977305)
    ·
      refine ⟨118959627437732932741482979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158612836583643910321977305 118959627437732932741482979)
      ·
        refine ⟨178439441156599399112224469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118959627437732932741482979 178439441156599399112224469)
        ·
          refine ⟨4182174402107798416692761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 178439441156599399112224469 4182174402107798416692761)
          ·
            refine ⟨3136630801580848812519571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182174402107798416692761 3136630801580848812519571)
            ·
              refine ⟨4704946202371273218779357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136630801580848812519571 4704946202371273218779357)
              ·
                refine ⟨1764354825889227457042259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4704946202371273218779357 1764354825889227457042259)
                ·
                  refine ⟨2646532238833841185563389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764354825889227457042259 2646532238833841185563389)
                  ·
                    refine ⟨992449589562690444586271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646532238833841185563389 992449589562690444586271)
                    ·
                      rfl

theorem cell22_2899183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_2899183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899183 prefixEnd_2899183 := by exact prefixLift 2899183
  have htrace : WordTrace (prefixWord ++ tailWord_2899183) baseStart_2899183 baseEnd_2899183 := by
    simpa [prefixWord, tailWord_2899183, baseEnd_2899183] using wordTrace_append hprefix tailTrace_2899183
  have hstable : (prefixWord ++ tailWord_2899183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899183).length < 2 ^ (prefixWord ++ tailWord_2899183).sum := by decide
  have hdescent : baseEnd_2899183 < baseStart_2899183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899226 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_2899226 : Nat := 118140960795 + 2899226 * 2 ^ 59
def prefixEnd_2899226 : Nat := 4983230072969 + 3 ^ 40 * 2899226 * 2
def baseEnd_2899226 : Nat := 992464309341452665761139

theorem tailTrace_2899226 : CollatzResearch.WordTrace tailWord_2899226 prefixEnd_2899226 992464309341452665761139 := by
  unfold tailWord_2899226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26435864848651706306283383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70495639596404550150089021 26435864848651706306283383)
  ·
    refine ⟨39653797272977559459425075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26435864848651706306283383 39653797272977559459425075)
    ·
      refine ⟨59480695909466339189137613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39653797272977559459425075 59480695909466339189137613)
      ·
        refine ⟨22305260966049877195926605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59480695909466339189137613 22305260966049877195926605)
        ·
          refine ⟨8364472862268703948472477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22305260966049877195926605 8364472862268703948472477)
          ·
            refine ⟨3136677323350763980677179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8364472862268703948472477 3136677323350763980677179)
            ·
              refine ⟨4705015985026145971015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136677323350763980677179 4705015985026145971015769)
              ·
                refine ⟨3528761988769609478261827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705015985026145971015769 3528761988769609478261827)
                ·
                  refine ⟨5293142983154414217392741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528761988769609478261827 5293142983154414217392741)
                  ·
                    refine ⟨992464309341452665761139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293142983154414217392741 992464309341452665761139)
                    ·
                      rfl

theorem cell22_2899226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_2899226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899226 prefixEnd_2899226 := by exact prefixLift 2899226
  have htrace : WordTrace (prefixWord ++ tailWord_2899226) baseStart_2899226 baseEnd_2899226 := by
    simpa [prefixWord, tailWord_2899226, baseEnd_2899226] using wordTrace_append hprefix tailTrace_2899226
  have hstable : (prefixWord ++ tailWord_2899226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899226).length < 2 ^ (prefixWord ++ tailWord_2899226).sum := by decide
  have hdescent : baseEnd_2899226 < baseStart_2899226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899282 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2899282 : Nat := 118140960795 + 2899282 * 2 ^ 59
def prefixEnd_2899282 : Nat := 4983230072969 + 3 ^ 40 * 2899282 * 2
def baseEnd_2899282 : Nat := 992483479285887186360967

theorem tailTrace_2899282 : CollatzResearch.WordTrace tailWord_2899282 prefixEnd_2899282 992483479285887186360967 := by
  unfold tailWord_2899282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26436375470600986697293025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70497001254935964526114733 26436375470600986697293025)
  ·
    refine ⟨19827281602950740022969769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26436375470600986697293025 19827281602950740022969769)
    ·
      refine ⟨14870461202213055017227327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19827281602950740022969769 14870461202213055017227327)
      ·
        refine ⟨22305691803319582525840991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14870461202213055017227327 22305691803319582525840991)
        ·
          refine ⟨33458537704979373788761487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22305691803319582525840991 33458537704979373788761487)
          ·
            refine ⟨50187806557469060683142231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33458537704979373788761487 50187806557469060683142231)
            ·
              refine ⟨75281709836203591024713347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50187806557469060683142231 75281709836203591024713347)
              ·
                refine ⟨112922564754305386537070021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75281709836203591024713347 112922564754305386537070021)
                ·
                  refine ⟨21172980891432259975700629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112922564754305386537070021 21172980891432259975700629)
                  ·
                    refine ⟨992483479285887186360967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21172980891432259975700629 992483479285887186360967)
                    ·
                      rfl

theorem cell22_2899282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2899282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899282 prefixEnd_2899282 := by exact prefixLift 2899282
  have htrace : WordTrace (prefixWord ++ tailWord_2899282) baseStart_2899282 baseEnd_2899282 := by
    simpa [prefixWord, tailWord_2899282, baseEnd_2899282] using wordTrace_append hprefix tailTrace_2899282
  have hstable : (prefixWord ++ tailWord_2899282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899282).length < 2 ^ (prefixWord ++ tailWord_2899282).sum := by decide
  have hdescent : baseEnd_2899282 < baseStart_2899282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899312 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_2899312 : Nat := 118140960795 + 2899312 * 2 ^ 59
def prefixEnd_2899312 : Nat := 4983230072969 + 3 ^ 40 * 2899312 * 2
def baseEnd_2899312 : Nat := 992493748898977108110875

theorem tailTrace_2899312 : CollatzResearch.WordTrace tailWord_2899312 prefixEnd_2899312 992493748898977108110875 := by
  unfold tailWord_2899312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52873298036147630956382095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70497730714863507941842793 52873298036147630956382095)
  ·
    refine ⟨79309947054221446434573143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52873298036147630956382095 79309947054221446434573143)
    ·
      refine ⟨118964920581332169651859715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79309947054221446434573143 118964920581332169651859715)
      ·
        refine ⟨178447380871998254477789573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118964920581332169651859715 178447380871998254477789573)
        ·
          refine ⟨33458883913499672714585545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178447380871998254477789573 33458883913499672714585545)
          ·
            refine ⟨25094162935124754535939159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33458883913499672714585545 25094162935124754535939159)
            ·
              refine ⟨37641244402687131803908739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25094162935124754535939159 37641244402687131803908739)
              ·
                refine ⟨56461866604030697705863109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37641244402687131803908739 56461866604030697705863109)
                ·
                  refine ⟨10586599988255755819849333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56461866604030697705863109 10586599988255755819849333)
                  ·
                    refine ⟨992493748898977108110875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10586599988255755819849333 992493748898977108110875)
                    ·
                      rfl

theorem cell22_2899312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_2899312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899312 prefixEnd_2899312 := by exact prefixLift 2899312
  have htrace : WordTrace (prefixWord ++ tailWord_2899312) baseStart_2899312 baseEnd_2899312 := by
    simpa [prefixWord, tailWord_2899312, baseEnd_2899312] using wordTrace_append hprefix tailTrace_2899312
  have hstable : (prefixWord ++ tailWord_2899312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899312).length < 2 ^ (prefixWord ++ tailWord_2899312).sum := by decide
  have hdescent : baseEnd_2899312 < baseStart_2899312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899331 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 5]
def baseStart_2899331 : Nat := 118140960795 + 2899331 * 2 ^ 59
def prefixEnd_2899331 : Nat := 4983230072969 + 3 ^ 40 * 2899331 * 2
def baseEnd_2899331 : Nat := 330833417662422463961939

theorem tailTrace_2899331 : CollatzResearch.WordTrace tailWord_2899331 prefixEnd_2899331 330833417662422463961939 := by
  unfold tailWord_2899331
  simp only [CollatzResearch.WordTrace]
  refine ⟨105747289059226428157705847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70498192706150952105137231 105747289059226428157705847)
  ·
    refine ⟨158620933588839642236558771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105747289059226428157705847 158620933588839642236558771)
    ·
      refine ⟨237931400383259463354838157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158620933588839642236558771 237931400383259463354838157)
      ·
        refine ⟨89224275143722298758064309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237931400383259463354838157 89224275143722298758064309)
        ·
          refine ⟨8364775794723965508568529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89224275143722298758064309 8364775794723965508568529)
          ·
            refine ⟨6273581846042974131426397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8364775794723965508568529 6273581846042974131426397)
            ·
              refine ⟨2352593192266115299284899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6273581846042974131426397 2352593192266115299284899)
              ·
                refine ⟨3528889788399172948927349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352593192266115299284899 3528889788399172948927349)
                ·
                  refine ⟨330833417662422463961939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528889788399172948927349 330833417662422463961939)
                  ·
                    rfl

theorem cell22_2899331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 5].length) (baseStart_2899331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899331 prefixEnd_2899331 := by exact prefixLift 2899331
  have htrace : WordTrace (prefixWord ++ tailWord_2899331) baseStart_2899331 baseEnd_2899331 := by
    simpa [prefixWord, tailWord_2899331, baseEnd_2899331] using wordTrace_append hprefix tailTrace_2899331
  have hstable : (prefixWord ++ tailWord_2899331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899331).length < 2 ^ (prefixWord ++ tailWord_2899331).sum := by decide
  have hdescent : baseEnd_2899331 < baseStart_2899331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899352 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 1, 3]
def baseStart_2899352 : Nat := 118140960795 + 2899352 * 2 ^ 59
def prefixEnd_2899352 : Nat := 4983230072969 + 3 ^ 40 * 2899352 * 2
def baseEnd_2899352 : Nat := 992507441716430337110753

theorem tailTrace_2899352 : CollatzResearch.WordTrace tailWord_2899352 prefixEnd_2899352 992507441716430337110753 := by
  unfold tailWord_2899352
  simp only [CollatzResearch.WordTrace]
  refine ⟨52874027496075174372110155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70498703328100232496146873 52874027496075174372110155)
  ·
    refine ⟨79311041244112761558165233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52874027496075174372110155 79311041244112761558165233)
    ·
      refine ⟨59483280933084571168623925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79311041244112761558165233 59483280933084571168623925)
      ·
        refine ⟨5576557587476678547058493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59483280933084571168623925 5576557587476678547058493)
        ·
          refine ⟨2091209095303754455146935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5576557587476678547058493 2091209095303754455146935)
          ·
            refine ⟨3136813642955631682720403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091209095303754455146935 3136813642955631682720403)
            ·
              refine ⟨4705220464433447524080605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136813642955631682720403 4705220464433447524080605)
              ·
                refine ⟨1764457674162542821530227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4705220464433447524080605 1764457674162542821530227)
                ·
                  refine ⟨2646686511243814232295341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764457674162542821530227 2646686511243814232295341)
                  ·
                    refine ⟨992507441716430337110753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646686511243814232295341 992507441716430337110753)
                    ·
                      rfl

theorem cell22_2899352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_2899352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899352 prefixEnd_2899352 := by exact prefixLift 2899352
  have htrace : WordTrace (prefixWord ++ tailWord_2899352) baseStart_2899352 baseEnd_2899352 := by
    simpa [prefixWord, tailWord_2899352, baseEnd_2899352] using wordTrace_append hprefix tailTrace_2899352
  have hstable : (prefixWord ++ tailWord_2899352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899352).length < 2 ^ (prefixWord ++ tailWord_2899352).sum := by decide
  have hdescent : baseEnd_2899352 < baseStart_2899352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899389 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2899389 : Nat := 118140960795 + 2899389 * 2 ^ 59
def prefixEnd_2899389 : Nat := 4983230072969 + 3 ^ 40 * 2899389 * 2
def baseEnd_2899389 : Nat := 992520107572574573935639

theorem tailTrace_2899389 : CollatzResearch.WordTrace tailWord_2899389 prefixEnd_2899389 992520107572574573935639 := by
  unfold tailWord_2899389
  simp only [CollatzResearch.WordTrace]
  refine ⟨105749404493016304063317221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70499602995344202708878147 105749404493016304063317221)
  ·
    refine ⟨19828013342440557011871979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105749404493016304063317221 19828013342440557011871979)
    ·
      refine ⟨29742020013660835517807969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19828013342440557011871979 29742020013660835517807969)
      ·
        refine ⟨22306515010245626638355977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29742020013660835517807969 22306515010245626638355977)
        ·
          refine ⟨16729886257684219978766983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22306515010245626638355977 16729886257684219978766983)
          ·
            refine ⟨25094829386526329968150475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16729886257684219978766983 25094829386526329968150475)
            ·
              refine ⟨37642244079789494952225713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25094829386526329968150475 37642244079789494952225713)
              ·
                refine ⟨28231683059842121214169285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37642244079789494952225713 28231683059842121214169285)
                ·
                  refine ⟨5293440573720397727656741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28231683059842121214169285 5293440573720397727656741)
                  ·
                    refine ⟨992520107572574573935639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293440573720397727656741 992520107572574573935639)
                    ·
                      rfl

theorem cell22_2899389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2899389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899389 prefixEnd_2899389 := by exact prefixLift 2899389
  have htrace : WordTrace (prefixWord ++ tailWord_2899389) baseStart_2899389 baseEnd_2899389 := by
    simpa [prefixWord, tailWord_2899389, baseEnd_2899389] using wordTrace_append hprefix tailTrace_2899389
  have hstable : (prefixWord ++ tailWord_2899389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899389).length < 2 ^ (prefixWord ++ tailWord_2899389).sum := by decide
  have hdescent : baseEnd_2899389 < baseStart_2899389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899404 : List Nat := [2, 2, 1, 4, 2, 1, 2, 8]
def baseStart_2899404 : Nat := 118140960795 + 2899404 * 2 ^ 59
def prefixEnd_2899404 : Nat := 4983230072969 + 3 ^ 40 * 2899404 * 2
def baseEnd_2899404 : Nat := 110280582486568837201177

theorem tailTrace_2899404 : CollatzResearch.WordTrace tailWord_2899404 prefixEnd_2899404 110280582486568837201177 := by
  unfold tailWord_2899404
  simp only [CollatzResearch.WordTrace]
  refine ⟨52874975793980980812556633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70499967725307974416742177 52874975793980980812556633)
  ·
    refine ⟨39656231845485735609417475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52874975793980980812556633 39656231845485735609417475)
    ·
      refine ⟨59484347768228603414126213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39656231845485735609417475 59484347768228603414126213)
      ·
        refine ⟨11153315206542863140148665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59484347768228603414126213 11153315206542863140148665)
        ·
          refine ⟨8364986404907147355111499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11153315206542863140148665 8364986404907147355111499)
          ·
            refine ⟨12547479607360721032667249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364986404907147355111499 12547479607360721032667249)
            ·
              refine ⟨9410609705520540774500437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12547479607360721032667249 9410609705520540774500437)
              ·
                refine ⟨110280582486568837201177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9410609705520540774500437 110280582486568837201177)
                ·
                  rfl

theorem cell22_2899404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_2899404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899404 prefixEnd_2899404 := by exact prefixLift 2899404
  have htrace : WordTrace (prefixWord ++ tailWord_2899404) baseStart_2899404 baseEnd_2899404 := by
    simpa [prefixWord, tailWord_2899404, baseEnd_2899404] using wordTrace_append hprefix tailTrace_2899404
  have hstable : (prefixWord ++ tailWord_2899404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899404).length < 2 ^ (prefixWord ++ tailWord_2899404).sum := by decide
  have hdescent : baseEnd_2899404 < baseStart_2899404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899513 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_2899513 : Nat := 118140960795 + 2899513 * 2 ^ 59
def prefixEnd_2899513 : Nat := 4983230072969 + 3 ^ 40 * 2899513 * 2
def baseEnd_2899513 : Nat := 992562555306679583835259

theorem tailTrace_2899513 : CollatzResearch.WordTrace tailWord_2899513 prefixEnd_2899513 992562555306679583835259 := by
  unfold tailWord_2899513
  simp only [CollatzResearch.WordTrace]
  refine ⟨105753927144567073240831193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70502618096378048827220795 105753927144567073240831193)
  ·
    refine ⟨79315445358425304930623395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105753927144567073240831193 79315445358425304930623395)
    ·
      refine ⟨118973168037637957395935093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79315445358425304930623395 118973168037637957395935093)
      ·
        refine ⟨11153734503528558505868915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118973168037637957395935093 11153734503528558505868915)
        ·
          refine ⟨16730601755292837758803373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11153734503528558505868915 16730601755292837758803373)
          ·
            refine ⟨6273975658234814159551265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16730601755292837758803373 6273975658234814159551265)
            ·
              refine ⟨4705481743676110619663449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273975658234814159551265 4705481743676110619663449)
              ·
                refine ⟨3529111307757082964747587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705481743676110619663449 3529111307757082964747587)
                ·
                  refine ⟨5293666961635624447121381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529111307757082964747587 5293666961635624447121381)
                  ·
                    refine ⟨992562555306679583835259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293666961635624447121381 992562555306679583835259)
                    ·
                      rfl

theorem cell22_2899513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_2899513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899513 prefixEnd_2899513 := by exact prefixLift 2899513
  have htrace : WordTrace (prefixWord ++ tailWord_2899513) baseStart_2899513 baseEnd_2899513 := by
    simpa [prefixWord, tailWord_2899513, baseEnd_2899513] using wordTrace_append hprefix tailTrace_2899513
  have hstable : (prefixWord ++ tailWord_2899513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899513).length < 2 ^ (prefixWord ++ tailWord_2899513).sum := by decide
  have hdescent : baseEnd_2899513 < baseStart_2899513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899556 : List Nat := [2, 3, 1, 1, 2, 4, 2, 7]
def baseStart_2899556 : Nat := 118140960795 + 2899556 * 2 ^ 59
def prefixEnd_2899556 : Nat := 4983230072969 + 3 ^ 40 * 2899556 * 2
def baseEnd_2899556 : Nat := 110286363898382422778903

theorem tailTrace_2899556 : CollatzResearch.WordTrace tailWord_2899556 prefixEnd_2899556 110286363898382422778903 := by
  unfold tailWord_2899556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52877747741705645792323261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70503663655607527723097681 52877747741705645792323261)
  ·
    refine ⟨19829155403139617172121223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52877747741705645792323261 19829155403139617172121223)
    ·
      refine ⟨29743733104709425758181835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19829155403139617172121223 29743733104709425758181835)
      ·
        refine ⟨44615599657064138637272753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29743733104709425758181835 44615599657064138637272753)
        ·
          refine ⟨33461699742798103977954565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44615599657064138637272753 33461699742798103977954565)
          ·
            refine ⟨6274068701774644495866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33461699742798103977954565 6274068701774644495866481)
            ·
              refine ⟨4705551526330983371899861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274068701774644495866481 4705551526330983371899861)
              ·
                refine ⟨110286363898382422778903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4705551526330983371899861 110286363898382422778903)
                ·
                  rfl

theorem cell22_2899556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_2899556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899556 prefixEnd_2899556 := by exact prefixLift 2899556
  have htrace : WordTrace (prefixWord ++ tailWord_2899556) baseStart_2899556 baseEnd_2899556 := by
    simpa [prefixWord, tailWord_2899556, baseEnd_2899556] using wordTrace_append hprefix tailTrace_2899556
  have hstable : (prefixWord ++ tailWord_2899556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899556).length < 2 ^ (prefixWord ++ tailWord_2899556).sum := by decide
  have hdescent : baseEnd_2899556 < baseStart_2899556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899560 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_2899560 : Nat := 118140960795 + 2899560 * 2 ^ 59
def prefixEnd_2899560 : Nat := 4983230072969 + 3 ^ 40 * 2899560 * 2
def baseEnd_2899560 : Nat := 992578644367187127910115

theorem tailTrace_2899560 : CollatzResearch.WordTrace tailWord_2899560 prefixEnd_2899560 992578644367187127910115 := by
  unfold tailWord_2899560
  simp only [CollatzResearch.WordTrace]
  refine ⟨52877820687698400133896067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70503760916931200178528089 52877820687698400133896067)
  ·
    refine ⟨79316731031547600200844101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52877820687698400133896067 79316731031547600200844101)
    ·
      refine ⟨14871887068415175037658269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79316731031547600200844101 14871887068415175037658269)
      ·
        refine ⟨5576957650655690639121851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14871887068415175037658269 5576957650655690639121851)
        ·
          refine ⟨8365436475983535958682777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576957650655690639121851 8365436475983535958682777)
          ·
            refine ⟨6274077356987651969012083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8365436475983535958682777 6274077356987651969012083)
            ·
              refine ⟨9411116035481477953518125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274077356987651969012083 9411116035481477953518125)
              ·
                refine ⟨3529168513305554232569297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9411116035481477953518125 3529168513305554232569297)
                ·
                  refine ⟨2646876384979165674426973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3529168513305554232569297 2646876384979165674426973)
                  ·
                    refine ⟨992578644367187127910115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646876384979165674426973 992578644367187127910115)
                    ·
                      rfl

theorem cell22_2899560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_2899560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899560 prefixEnd_2899560 := by exact prefixLift 2899560
  have htrace : WordTrace (prefixWord ++ tailWord_2899560) baseStart_2899560 baseEnd_2899560 := by
    simpa [prefixWord, tailWord_2899560, baseEnd_2899560] using wordTrace_append hprefix tailTrace_2899560
  have hstable : (prefixWord ++ tailWord_2899560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899560).length < 2 ^ (prefixWord ++ tailWord_2899560).sum := by decide
  have hdescent : baseEnd_2899560 < baseStart_2899560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899616 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_2899616 : Nat := 118140960795 + 2899616 * 2 ^ 59
def prefixEnd_2899616 : Nat := 4983230072969 + 3 ^ 40 * 2899616 * 2
def baseEnd_2899616 : Nat := 992597814311621648509943

theorem tailTrace_2899616 : CollatzResearch.WordTrace tailWord_2899616 prefixEnd_2899616 992597814311621648509943 := by
  unfold tailWord_2899616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52878841931596960915915351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70505122575462614554553801 52878841931596960915915351)
  ·
    refine ⟨79318262897395441373873027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52878841931596960915915351 79318262897395441373873027)
    ·
      refine ⟨118977394346093162060809541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79318262897395441373873027 118977394346093162060809541)
      ·
        refine ⟨22308261439892467886401789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118977394346093162060809541 22308261439892467886401789)
        ·
          refine ⟨8365598039959675457400671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22308261439892467886401789 8365598039959675457400671)
          ·
            refine ⟨12548397059939513186101007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8365598039959675457400671 12548397059939513186101007)
            ·
              refine ⟨18822595589909269779151511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12548397059939513186101007 18822595589909269779151511)
              ·
                refine ⟨28233893384863904668727267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18822595589909269779151511 28233893384863904668727267)
                ·
                  refine ⟨42350840077295857003090901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28233893384863904668727267 42350840077295857003090901)
                  ·
                    refine ⟨992597814311621648509943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42350840077295857003090901 992597814311621648509943)
                    ·
                      rfl

theorem cell22_2899616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_2899616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899616 prefixEnd_2899616 := by exact prefixLift 2899616
  have htrace : WordTrace (prefixWord ++ tailWord_2899616) baseStart_2899616 baseEnd_2899616 := by
    simpa [prefixWord, tailWord_2899616, baseEnd_2899616] using wordTrace_append hprefix tailTrace_2899616
  have hstable : (prefixWord ++ tailWord_2899616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899616).length < 2 ^ (prefixWord ++ tailWord_2899616).sum := by decide
  have hdescent : baseEnd_2899616 < baseStart_2899616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899631 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_2899631 : Nat := 118140960795 + 2899631 * 2 ^ 59
def prefixEnd_2899631 : Nat := 4983230072969 + 3 ^ 40 * 2899631 * 2
def baseEnd_2899631 : Nat := 992602949118166609384897

theorem tailTrace_2899631 : CollatzResearch.WordTrace tailWord_2899631 prefixEnd_2899631 992602949118166609384897 := by
  unfold tailWord_2899631
  simp only [CollatzResearch.WordTrace]
  refine ⟨105758230958139579393626747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70505487305426386262417831 105758230958139579393626747)
  ·
    refine ⟨158637346437209369090440121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105758230958139579393626747 158637346437209369090440121)
    ·
      refine ⟨118978009827907026817830091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158637346437209369090440121 118978009827907026817830091)
      ·
        refine ⟨178467014741860540226745137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118978009827907026817830091 178467014741860540226745137)
        ·
          refine ⟨133850261056395405170058853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178467014741860540226745137 133850261056395405170058853)
          ·
            refine ⟨25096923948074138469386035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133850261056395405170058853 25096923948074138469386035)
            ·
              refine ⟨37645385922111207704079053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25096923948074138469386035 37645385922111207704079053)
              ·
                refine ⟨14117019720791702889029645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37645385922111207704079053 14117019720791702889029645)
                ·
                  refine ⟨5293882395296888583386117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14117019720791702889029645 5293882395296888583386117)
                  ·
                    refine ⟨992602949118166609384897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293882395296888583386117 992602949118166609384897)
                    ·
                      rfl

theorem cell22_2899631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_2899631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899631 prefixEnd_2899631 := by exact prefixLift 2899631
  have htrace : WordTrace (prefixWord ++ tailWord_2899631) baseStart_2899631 baseEnd_2899631 := by
    simpa [prefixWord, tailWord_2899631, baseEnd_2899631] using wordTrace_append hprefix tailTrace_2899631
  have hstable : (prefixWord ++ tailWord_2899631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899631).length < 2 ^ (prefixWord ++ tailWord_2899631).sum := by decide
  have hdescent : baseEnd_2899631 < baseStart_2899631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899648 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_2899648 : Nat := 118140960795 + 2899648 * 2 ^ 59
def prefixEnd_2899648 : Nat := 4983230072969 + 3 ^ 40 * 2899648 * 2
def baseEnd_2899648 : Nat := 992608768565584231709845

theorem tailTrace_2899648 : CollatzResearch.WordTrace tailWord_2899648 prefixEnd_2899648 992608768565584231709845 := by
  unfold tailWord_2899648
  simp only [CollatzResearch.WordTrace]
  refine ⟨52879425499538995648497799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70505900666051994197997065 52879425499538995648497799)
  ·
    refine ⟨79319138249308493472746699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52879425499538995648497799 79319138249308493472746699)
    ·
      refine ⟨118978707373962740209120049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79319138249308493472746699 118978707373962740209120049)
      ·
        refine ⟨89234030530472055156840037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118978707373962740209120049 89234030530472055156840037)
        ·
          refine ⟨16731380724463510341907507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89234030530472055156840037 16731380724463510341907507)
          ·
            refine ⟨25097071086695265512861261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16731380724463510341907507 25097071086695265512861261)
            ·
              refine ⟨9411401657510724567322973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25097071086695265512861261 9411401657510724567322973)
              ·
                refine ⟨3529275621566521712746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9411401657510724567322973 3529275621566521712746115)
                ·
                  refine ⟨5293913432349782569119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529275621566521712746115 5293913432349782569119173)
                  ·
                    refine ⟨992608768565584231709845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293913432349782569119173 992608768565584231709845)
                    ·
                      rfl

theorem cell22_2899648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_2899648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899648 prefixEnd_2899648 := by exact prefixLift 2899648
  have htrace : WordTrace (prefixWord ++ tailWord_2899648) baseStart_2899648 baseEnd_2899648 := by
    simpa [prefixWord, tailWord_2899648, baseEnd_2899648] using wordTrace_append hprefix tailTrace_2899648
  have hstable : (prefixWord ++ tailWord_2899648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899648).length < 2 ^ (prefixWord ++ tailWord_2899648).sum := by decide
  have hdescent : baseEnd_2899648 < baseStart_2899648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899693 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2899693 : Nat := 118140960795 + 2899693 * 2 ^ 59
def prefixEnd_2899693 : Nat := 4983230072969 + 3 ^ 40 * 2899693 * 2
def baseEnd_2899693 : Nat := 992624172985219114334707

theorem tailTrace_2899693 : CollatzResearch.WordTrace tailWord_2899693 prefixEnd_2899693 992624172985219114334707 := by
  unfold tailWord_2899693
  simp only [CollatzResearch.WordTrace]
  refine ⟨105760492283914963982383733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70506994855943309321589155 105760492283914963982383733)
  ·
    refine ⟨9915046151617027873348475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105760492283914963982383733 9915046151617027873348475)
    ·
      refine ⟨14872569227425541810022713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9915046151617027873348475 14872569227425541810022713)
      ·
        refine ⟨11154426920569156357517035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14872569227425541810022713 11154426920569156357517035)
        ·
          refine ⟨16731640380853734536275553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154426920569156357517035 16731640380853734536275553)
          ·
            refine ⟨12548730285640300902206665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16731640380853734536275553 12548730285640300902206665)
            ·
              refine ⟨9411547714230225676654999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12548730285640300902206665 9411547714230225676654999)
              ·
                refine ⟨14117321571345338514982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9411547714230225676654999 14117321571345338514982499)
                ·
                  refine ⟨21175982357018007772473749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14117321571345338514982499 21175982357018007772473749)
                  ·
                    refine ⟨992624172985219114334707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21175982357018007772473749 992624172985219114334707)
                    ·
                      rfl

theorem cell22_2899693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2899693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899693 prefixEnd_2899693 := by exact prefixLift 2899693
  have htrace : WordTrace (prefixWord ++ tailWord_2899693) baseStart_2899693 baseEnd_2899693 := by
    simpa [prefixWord, tailWord_2899693, baseEnd_2899693] using wordTrace_append hprefix tailTrace_2899693
  have hstable : (prefixWord ++ tailWord_2899693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899693).length < 2 ^ (prefixWord ++ tailWord_2899693).sum := by decide
  have hdescent : baseEnd_2899693 < baseStart_2899693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899721 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_2899721 : Nat := 118140960795 + 2899721 * 2 ^ 59
def prefixEnd_2899721 : Nat := 4983230072969 + 3 ^ 40 * 2899721 * 2
def baseEnd_2899721 : Nat := 992633757957436374634621

theorem tailTrace_2899721 : CollatzResearch.WordTrace tailWord_2899721 prefixEnd_2899721 992633757957436374634621 := by
  unfold tailWord_2899721
  simp only [CollatzResearch.WordTrace]
  refine ⟨105761513527813524764403017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70507675685209016509602011 105761513527813524764403017)
  ·
    refine ⟨79321135145860143573302263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105761513527813524764403017 79321135145860143573302263)
    ·
      refine ⟨118981702718790215359953395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79321135145860143573302263 118981702718790215359953395)
      ·
        refine ⟨178472554078185323039930093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118981702718790215359953395 178472554078185323039930093)
        ·
          refine ⟨66927207779319496139973785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178472554078185323039930093 66927207779319496139973785)
          ·
            refine ⟨50195405834489622104980339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66927207779319496139973785 50195405834489622104980339)
            ·
              refine ⟨75293108751734433157470509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50195405834489622104980339 75293108751734433157470509)
              ·
                refine ⟨28234915781900412434051441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75293108751734433157470509 28234915781900412434051441)
                ·
                  refine ⟨21176186836425309325538581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28234915781900412434051441 21176186836425309325538581)
                  ·
                    refine ⟨992633757957436374634621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21176186836425309325538581 992633757957436374634621)
                    ·
                      rfl

theorem cell22_2899721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_2899721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899721 prefixEnd_2899721 := by exact prefixLift 2899721
  have htrace : WordTrace (prefixWord ++ tailWord_2899721) baseStart_2899721 baseEnd_2899721 := by
    simpa [prefixWord, tailWord_2899721, baseEnd_2899721] using wordTrace_append hprefix tailTrace_2899721
  have hstable : (prefixWord ++ tailWord_2899721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899721).length < 2 ^ (prefixWord ++ tailWord_2899721).sum := by decide
  have hdescent : baseEnd_2899721 < baseStart_2899721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899770 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_2899770 : Nat := 118140960795 + 2899770 * 2 ^ 59
def prefixEnd_2899770 : Nat := 4983230072969 + 3 ^ 40 * 2899770 * 2
def baseEnd_2899770 : Nat := 330883510552938860053157

theorem tailTrace_2899770 : CollatzResearch.WordTrace tailWord_2899770 prefixEnd_2899770 330883510552938860053157 := by
  unfold tailWord_2899770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26440825176159001533234191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70508867136424004088624509 26440825176159001533234191)
  ·
    refine ⟨39661237764238502299851287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26440825176159001533234191 39661237764238502299851287)
    ·
      refine ⟨59491856646357753449776931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39661237764238502299851287 59491856646357753449776931)
      ·
        refine ⟨89237784969536630174665397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59491856646357753449776931 89237784969536630174665397)
        ·
          refine ⟨8366042340894059078874881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89237784969536630174665397 8366042340894059078874881)
          ·
            refine ⟨6274531755670544309156161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366042340894059078874881 6274531755670544309156161)
            ·
              refine ⟨4705898816752908231867121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274531755670544309156161 4705898816752908231867121)
              ·
                refine ⟨3529424112564681173900341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705898816752908231867121 3529424112564681173900341)
                ·
                  refine ⟨330883510552938860053157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3529424112564681173900341 330883510552938860053157)
                  ·
                    rfl

theorem cell22_2899770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_2899770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899770 prefixEnd_2899770 := by exact prefixLift 2899770
  have htrace : WordTrace (prefixWord ++ tailWord_2899770) baseStart_2899770 baseEnd_2899770 := by
    simpa [prefixWord, tailWord_2899770, baseEnd_2899770] using wordTrace_append hprefix tailTrace_2899770
  have hstable : (prefixWord ++ tailWord_2899770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899770).length < 2 ^ (prefixWord ++ tailWord_2899770).sum := by decide
  have hdescent : baseEnd_2899770 < baseStart_2899770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899774 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2899774 : Nat := 118140960795 + 2899774 * 2 ^ 59
def prefixEnd_2899774 : Nat := 4983230072969 + 3 ^ 40 * 2899774 * 2
def baseEnd_2899774 : Nat := 992651900940561903059459

theorem tailTrace_2899774 : CollatzResearch.WordTrace tailWord_2899774 prefixEnd_2899774 992651900940561903059459 := by
  unfold tailWord_2899774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13220430824577689352010297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70508964397747676544054917 13220430824577689352010297)
  ·
    refine ⟨9915323118433267014007723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13220430824577689352010297 9915323118433267014007723)
    ·
      refine ⟨14872984677649900521011585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9915323118433267014007723 14872984677649900521011585)
      ·
        refine ⟨11154738508237425390758689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14872984677649900521011585 11154738508237425390758689)
        ·
          refine ⟨8366053881178069043069017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11154738508237425390758689 8366053881178069043069017)
          ·
            refine ⟨6274540410883551782301763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366053881178069043069017 6274540410883551782301763)
            ·
              refine ⟨9411810616325327673452645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274540410883551782301763 9411810616325327673452645)
              ·
                refine ⟨1764714490560998938772371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9411810616325327673452645 1764714490560998938772371)
                ·
                  refine ⟨2647071735841498408158557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764714490560998938772371 2647071735841498408158557)
                  ·
                    refine ⟨992651900940561903059459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2647071735841498408158557 992651900940561903059459)
                    ·
                      rfl

theorem cell22_2899774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2899774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899774 prefixEnd_2899774 := by exact prefixLift 2899774
  have htrace : WordTrace (prefixWord ++ tailWord_2899774) baseStart_2899774 baseEnd_2899774 := by
    simpa [prefixWord, tailWord_2899774, baseEnd_2899774] using wordTrace_append hprefix tailTrace_2899774
  have hstable : (prefixWord ++ tailWord_2899774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899774).length < 2 ^ (prefixWord ++ tailWord_2899774).sum := by decide
  have hdescent : baseEnd_2899774 < baseStart_2899774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899783 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2899783 : Nat := 118140960795 + 2899783 * 2 ^ 59
def prefixEnd_2899783 : Nat := 4983230072969 + 3 ^ 40 * 2899783 * 2
def baseEnd_2899783 : Nat := 992654981824488879584431

theorem tailTrace_2899783 : CollatzResearch.WordTrace tailWord_2899783 prefixEnd_2899783 992654981824488879584431 := by
  unfold tailWord_2899783
  simp only [CollatzResearch.WordTrace]
  refine ⟨105763774853588909353160003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70509183235725939568773335 105763774853588909353160003)
  ·
    refine ⟨158645662280383364029740005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105763774853588909353160003 158645662280383364029740005)
    ·
      refine ⟨29746061677571880755576251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158645662280383364029740005 29746061677571880755576251)
      ·
        refine ⟨44619092516357821133364377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29746061677571880755576251 44619092516357821133364377)
        ·
          refine ⟨33464319387268365850023283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44619092516357821133364377 33464319387268365850023283)
          ·
            refine ⟨50196479080902548775034925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33464319387268365850023283 50196479080902548775034925)
            ·
              refine ⟨18823679655338455790638097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50196479080902548775034925 18823679655338455790638097)
              ·
                refine ⟨14117759741503841842978573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18823679655338455790638097 14117759741503841842978573)
                ·
                  refine ⟨5294159903063940691116965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14117759741503841842978573 5294159903063940691116965)
                  ·
                    refine ⟨992654981824488879584431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294159903063940691116965 992654981824488879584431)
                    ·
                      rfl

theorem cell22_2899783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2899783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899783 prefixEnd_2899783 := by exact prefixLift 2899783
  have htrace : WordTrace (prefixWord ++ tailWord_2899783) baseStart_2899783 baseEnd_2899783 := by
    simpa [prefixWord, tailWord_2899783, baseEnd_2899783] using wordTrace_append hprefix tailTrace_2899783
  have hstable : (prefixWord ++ tailWord_2899783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899783).length < 2 ^ (prefixWord ++ tailWord_2899783).sum := by decide
  have hdescent : baseEnd_2899783 < baseStart_2899783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899847 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 1, 5]
def baseStart_2899847 : Nat := 118140960795 + 2899847 * 2 ^ 59
def prefixEnd_2899847 : Nat := 4983230072969 + 3 ^ 40 * 2899847 * 2
def baseEnd_2899847 : Nat := 992676890332414045984235

theorem tailTrace_2899847 : CollatzResearch.WordTrace tailWord_2899847 prefixEnd_2899847 992676890332414045984235 := by
  unfold tailWord_2899847
  simp only [CollatzResearch.WordTrace]
  refine ⟨105766109125357048283489795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70510739416904698855659863 105766109125357048283489795)
  ·
    refine ⟨158649163688035572425234693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105766109125357048283489795 158649163688035572425234693)
    ·
      refine ⟨29746718191506669829731505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158649163688035572425234693 29746718191506669829731505)
      ·
        refine ⟨22310038643630002372298629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29746718191506669829731505 22310038643630002372298629)
        ·
          refine ⟨4183132245680625444805993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22310038643630002372298629 4183132245680625444805993)
          ·
            refine ⟨3137349184260469083604495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183132245680625444805993 3137349184260469083604495)
            ·
              refine ⟨4706023776390703625406743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137349184260469083604495 4706023776390703625406743)
              ·
                refine ⟨7059035664586055438110115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706023776390703625406743 7059035664586055438110115)
                ·
                  refine ⟨10588553496879083157165173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059035664586055438110115 10588553496879083157165173)
                  ·
                    refine ⟨992676890332414045984235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10588553496879083157165173 992676890332414045984235)
                    ·
                      rfl

theorem cell22_2899847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_2899847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899847 prefixEnd_2899847 := by exact prefixLift 2899847
  have htrace : WordTrace (prefixWord ++ tailWord_2899847) baseStart_2899847 baseEnd_2899847 := by
    simpa [prefixWord, tailWord_2899847, baseEnd_2899847] using wordTrace_append hprefix tailTrace_2899847
  have hstable : (prefixWord ++ tailWord_2899847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899847).length < 2 ^ (prefixWord ++ tailWord_2899847).sum := by decide
  have hdescent : baseEnd_2899847 < baseStart_2899847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899860 : List Nat := [2, 4, 2, 1, 1, 3, 1, 8]
def baseStart_2899860 : Nat := 118140960795 + 2899860 * 2 ^ 59
def prefixEnd_2899860 : Nat := 4983230072969 + 3 ^ 40 * 2899860 * 2
def baseEnd_2899860 : Nat := 110297926722009593934355

theorem tailTrace_2899860 : CollatzResearch.WordTrace tailWord_2899860 prefixEnd_2899860 110297926722009593934355 := by
  unfold tailWord_2899860
  simp only [CollatzResearch.WordTrace]
  refine ⟨52883291637154975751856517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70511055516206634335808689 52883291637154975751856517)
  ·
    refine ⟨9915617181966557953473097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52883291637154975751856517 9915617181966557953473097)
    ·
      refine ⟨7436712886474918465104823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9915617181966557953473097 7436712886474918465104823)
      ·
        refine ⟨11155069329712377697657235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436712886474918465104823 11155069329712377697657235)
        ·
          refine ⟨16732603994568566546485853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11155069329712377697657235 16732603994568566546485853)
          ·
            refine ⟨6274726497963212454932195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16732603994568566546485853 6274726497963212454932195)
            ·
              refine ⟨9412089746944818682398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274726497963212454932195 9412089746944818682398293)
              ·
                refine ⟨110297926722009593934355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9412089746944818682398293 110297926722009593934355)
                ·
                  rfl

theorem cell22_2899860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_2899860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899860 prefixEnd_2899860 := by exact prefixLift 2899860
  have htrace : WordTrace (prefixWord ++ tailWord_2899860) baseStart_2899860 baseEnd_2899860 := by
    simpa [prefixWord, tailWord_2899860, baseEnd_2899860] using wordTrace_append hprefix tailTrace_2899860
  have hstable : (prefixWord ++ tailWord_2899860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899860).length < 2 ^ (prefixWord ++ tailWord_2899860).sum := by decide
  have hdescent : baseEnd_2899860 < baseStart_2899860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899903 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_2899903 : Nat := 118140960795 + 2899903 * 2 ^ 59
def prefixEnd_2899903 : Nat := 4983230072969 + 3 ^ 40 * 2899903 * 2
def baseEnd_2899903 : Nat := 992696060276848566584063

theorem tailTrace_2899903 : CollatzResearch.WordTrace tailWord_2899903 prefixEnd_2899903 992696060276848566584063 := by
  unfold tailWord_2899903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105768151613154169847528363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70512101075436113231685575 105768151613154169847528363)
  ·
    refine ⟨158652227419731254771292545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105768151613154169847528363 158652227419731254771292545)
    ·
      refine ⟨118989170564798441078469409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158652227419731254771292545 118989170564798441078469409)
      ·
        refine ⟨89241877923598830808852057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118989170564798441078469409 89241877923598830808852057)
        ·
          refine ⟨66931408442699123106639043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89241877923598830808852057 66931408442699123106639043)
          ·
            refine ⟨100397112664048684659958565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66931408442699123106639043 100397112664048684659958565)
            ·
              refine ⟨18824458624509128373742231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100397112664048684659958565 18824458624509128373742231)
              ·
                refine ⟨28236687936763692560613347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18824458624509128373742231 28236687936763692560613347)
                ·
                  refine ⟨42355031905145538840920021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28236687936763692560613347 42355031905145538840920021)
                  ·
                    refine ⟨992696060276848566584063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42355031905145538840920021 992696060276848566584063)
                    ·
                      rfl

theorem cell22_2899903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_2899903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899903 prefixEnd_2899903 := by exact prefixLift 2899903
  have htrace : WordTrace (prefixWord ++ tailWord_2899903) baseStart_2899903 baseEnd_2899903 := by
    simpa [prefixWord, tailWord_2899903, baseEnd_2899903] using wordTrace_append hprefix tailTrace_2899903
  have hstable : (prefixWord ++ tailWord_2899903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899903).length < 2 ^ (prefixWord ++ tailWord_2899903).sum := by decide
  have hdescent : baseEnd_2899903 < baseStart_2899903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899943 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2899943 : Nat := 118140960795 + 2899943 * 2 ^ 59
def prefixEnd_2899943 : Nat := 4983230072969 + 3 ^ 40 * 2899943 * 2
def baseEnd_2899943 : Nat := 992709753094301795583941

theorem tailTrace_2899943 : CollatzResearch.WordTrace tailWord_2899943 prefixEnd_2899943 992709753094301795583941 := by
  unfold tailWord_2899943
  simp only [CollatzResearch.WordTrace]
  refine ⟨105769610533009256678984483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513073688672837785989655 105769610533009256678984483)
  ·
    refine ⟨158654415799513885018476725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105769610533009256678984483 158654415799513885018476725)
    ·
      refine ⟨14873851481204426720482193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158654415799513885018476725 14873851481204426720482193)
      ·
        refine ⟨11155388610903320040361645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14873851481204426720482193 11155388610903320040361645)
        ·
          refine ⟨4183270729088745015135617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11155388610903320040361645 4183270729088745015135617)
          ·
            refine ⟨3137453046816558761351713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183270729088745015135617 3137453046816558761351713)
            ·
              refine ⟨2353089785112419071013785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137453046816558761351713 2353089785112419071013785)
              ·
                refine ⟨1764817338834314303260339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353089785112419071013785 1764817338834314303260339)
                ·
                  refine ⟨2647226008251471454890509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764817338834314303260339 2647226008251471454890509)
                  ·
                    refine ⟨992709753094301795583941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2647226008251471454890509 992709753094301795583941)
                    ·
                      rfl

theorem cell22_2899943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2899943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899943 prefixEnd_2899943 := by exact prefixLift 2899943
  have htrace : WordTrace (prefixWord ++ tailWord_2899943) baseStart_2899943 baseEnd_2899943 := by
    simpa [prefixWord, tailWord_2899943, baseEnd_2899943] using wordTrace_append hprefix tailTrace_2899943
  have hstable : (prefixWord ++ tailWord_2899943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899943).length < 2 ^ (prefixWord ++ tailWord_2899943).sum := by decide
  have hdescent : baseEnd_2899943 < baseStart_2899943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899965 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2899965 : Nat := 118140960795 + 2899965 * 2 ^ 59
def prefixEnd_2899965 : Nat := 4983230072969 + 3 ^ 40 * 2899965 * 2
def baseEnd_2899965 : Nat := 992717284143901071533873

theorem tailTrace_2899965 : CollatzResearch.WordTrace tailWord_2899965 prefixEnd_2899965 992717284143901071533873 := by
  unfold tailWord_2899965
  simp only [CollatzResearch.WordTrace]
  refine ⟨105770412938929554436285349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513608625953036290856899 105770412938929554436285349)
  ·
    refine ⟨19831952426049291456803503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105770412938929554436285349 19831952426049291456803503)
    ·
      refine ⟨29747928639073937185205255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19831952426049291456803503 29747928639073937185205255)
      ·
        refine ⟨44621892958610905777807883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29747928639073937185205255 44621892958610905777807883)
        ·
          refine ⟨66932839437916358666711825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44621892958610905777807883 66932839437916358666711825)
          ·
            refine ⟨50199629578437269000033869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66932839437916358666711825 50199629578437269000033869)
            ·
              refine ⟨18824861091913975875012701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50199629578437269000033869 18824861091913975875012701)
              ·
                refine ⟨7059322909467740953129763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18824861091913975875012701 7059322909467740953129763)
                ·
                  refine ⟨10588984364201611429694645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059322909467740953129763 10588984364201611429694645)
                  ·
                    refine ⟨992717284143901071533873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10588984364201611429694645 992717284143901071533873)
                    ·
                      rfl

theorem cell22_2899965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2899965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899965 prefixEnd_2899965 := by exact prefixLift 2899965
  have htrace : WordTrace (prefixWord ++ tailWord_2899965) baseStart_2899965 baseEnd_2899965 := by
    simpa [prefixWord, tailWord_2899965, baseEnd_2899965] using wordTrace_append hprefix tailTrace_2899965
  have hstable : (prefixWord ++ tailWord_2899965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899965).length < 2 ^ (prefixWord ++ tailWord_2899965).sum := by decide
  have hdescent : baseEnd_2899965 < baseStart_2899965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899980 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2899980 : Nat := 118140960795 + 2899980 * 2 ^ 59
def prefixEnd_2899980 : Nat := 4983230072969 + 3 ^ 40 * 2899980 * 2
def baseEnd_2899980 : Nat := 992722418950446032408827

theorem tailTrace_2899980 : CollatzResearch.WordTrace tailWord_2899980 prefixEnd_2899980 992722418950446032408827 := by
  unfold tailWord_2899980
  simp only [CollatzResearch.WordTrace]
  refine ⟨52885480016937605999040697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70513973355916807998720929 52885480016937605999040697)
  ·
    refine ⟨39664110012703204499280523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52885480016937605999040697 39664110012703204499280523)
    ·
      refine ⟨59496165019054806748920785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39664110012703204499280523 59496165019054806748920785)
      ·
        refine ⟨44622123764291105061690589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59496165019054806748920785 44622123764291105061690589)
        ·
          refine ⟨16733296411609164398133971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44622123764291105061690589 16733296411609164398133971)
          ·
            refine ⟨25099944617413746597200957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733296411609164398133971 25099944617413746597200957)
            ·
              refine ⟨9412479231530154973950359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25099944617413746597200957 9412479231530154973950359)
              ·
                refine ⟨14118718847295232460925539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412479231530154973950359 14118718847295232460925539)
                ·
                  refine ⟨21178078270942848691388309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14118718847295232460925539 21178078270942848691388309)
                  ·
                    refine ⟨992722418950446032408827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21178078270942848691388309 992722418950446032408827)
                    ·
                      rfl

theorem cell22_2899980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2899980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899980 prefixEnd_2899980 := by exact prefixLift 2899980
  have htrace : WordTrace (prefixWord ++ tailWord_2899980) baseStart_2899980 baseEnd_2899980 := by
    simpa [prefixWord, tailWord_2899980, baseEnd_2899980] using wordTrace_append hprefix tailTrace_2899980
  have hstable : (prefixWord ++ tailWord_2899980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899980).length < 2 ^ (prefixWord ++ tailWord_2899980).sum := by decide
  have hdescent : baseEnd_2899980 < baseStart_2899980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899982 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_2899982 : Nat := 118140960795 + 2899982 * 2 ^ 59
def prefixEnd_2899982 : Nat := 4983230072969 + 3 ^ 40 * 2899982 * 2
def baseEnd_2899982 : Nat := 992723103591318693858821

theorem tailTrace_2899982 : CollatzResearch.WordTrace tailWord_2899982 prefixEnd_2899982 992723103591318693858821 := by
  unfold tailWord_2899982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221379122483495792456775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70514021986578644226436133 13221379122483495792456775)
  ·
    refine ⟨19832068683725243688685163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13221379122483495792456775 19832068683725243688685163)
    ·
      refine ⟨29748103025587865533027745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19832068683725243688685163 29748103025587865533027745)
      ·
        refine ⟨22311077269190899149770809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29748103025587865533027745 22311077269190899149770809)
        ·
          refine ⟨16733307951893174362328107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22311077269190899149770809 16733307951893174362328107)
          ·
            refine ⟨25099961927839761543492161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733307951893174362328107 25099961927839761543492161)
            ·
              refine ⟨18824971445879821157619121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25099961927839761543492161 18824971445879821157619121)
              ·
                refine ⟨14118728584409865868214341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18824971445879821157619121 14118728584409865868214341)
                ·
                  refine ⟨2647261609576849850290189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14118728584409865868214341 2647261609576849850290189)
                  ·
                    refine ⟨992723103591318693858821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2647261609576849850290189 992723103591318693858821)
                    ·
                      rfl

theorem cell22_2899982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_2899982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2899982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2899982 prefixEnd_2899982 := by exact prefixLift 2899982
  have htrace : WordTrace (prefixWord ++ tailWord_2899982) baseStart_2899982 baseEnd_2899982 := by
    simpa [prefixWord, tailWord_2899982, baseEnd_2899982] using wordTrace_append hprefix tailTrace_2899982
  have hstable : (prefixWord ++ tailWord_2899982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899982).length < 2 ^ (prefixWord ++ tailWord_2899982).sum := by decide
  have hdescent : baseEnd_2899982 < baseStart_2899982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
