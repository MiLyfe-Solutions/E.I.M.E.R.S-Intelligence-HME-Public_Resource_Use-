import V185TrunkScan20Chunk040

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_249626 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_249626 : Nat := 118140960795 + 249626 * 2 ^ 59
def prefixEnd_249626 : Nat := 4983230072969 + 3 ^ 40 * 249626 * 2
def baseEnd_249626 : Nat := 113936108319418285179553

theorem tailTrace_249626 : CollatzResearch.WordTrace tailWord_249626 prefixEnd_249626 113936108319418285179553 := by
  unfold tailWord_249626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2276152048413777392936183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6069738795770073047829821 2276152048413777392936183)
  ·
    refine ⟨3414228072620666089404275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2276152048413777392936183 3414228072620666089404275)
    ·
      refine ⟨5121342108930999134106413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414228072620666089404275 5121342108930999134106413)
      ·
        refine ⟨1920503290849124675289905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5121342108930999134106413 1920503290849124675289905)
        ·
          refine ⟨1440377468136843506467429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1920503290849124675289905 1440377468136843506467429)
          ·
            refine ⟨270070775275658157462643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1440377468136843506467429 270070775275658157462643)
            ·
              refine ⟨405106162913487236193965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270070775275658157462643 405106162913487236193965)
              ·
                refine ⟨151914811092557713572737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405106162913487236193965 151914811092557713572737)
                ·
                  refine ⟨113936108319418285179553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151914811092557713572737 113936108319418285179553)
                  ·
                    rfl

theorem cell20_249626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_249626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249626 prefixEnd_249626 := by exact prefixLift 249626
  have htrace : WordTrace (prefixWord ++ tailWord_249626) baseStart_249626 baseEnd_249626 := by
    simpa [prefixWord, tailWord_249626, baseEnd_249626] using wordTrace_append hprefix tailTrace_249626
  have hstable : (prefixWord ++ tailWord_249626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249626).length < 2 ^ (prefixWord ++ tailWord_249626).sum := by decide
  have hdescent : baseEnd_249626 < baseStart_249626 := by decide
  rcases family_descends (prefixWord ++ tailWord_249626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249637 : List Nat := [1, 3, 1, 2, 3, 4, 6]
def baseStart_249637 : Nat := 118140960795 + 249637 * 2 ^ 59
def prefixEnd_249637 : Nat := 4983230072969 + 3 ^ 40 * 249637 * 2
def baseEnd_249637 : Nat := 12660125446572348423649

theorem tailTrace_249637 : CollatzResearch.WordTrace tailWord_249637 prefixEnd_249637 12660125446572348423649 := by
  unfold tailWord_249637
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105009396615258450395165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6070006264410172300263443 9105009396615258450395165)
  ·
    refine ⟨3414378523730721918898187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9105009396615258450395165 3414378523730721918898187)
    ·
      refine ⟨5121567785596082878347281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414378523730721918898187 5121567785596082878347281)
      ·
        refine ⟨3841175839197062158760461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121567785596082878347281 3841175839197062158760461)
        ·
          refine ⟨1440440939698898309535173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3841175839197062158760461 1440440939698898309535173)
          ·
            refine ⟨270082676193543433037845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1440440939698898309535173 270082676193543433037845)
            ·
              refine ⟨12660125446572348423649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270082676193543433037845 12660125446572348423649)
              ·
                rfl

theorem cell20_249637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_249637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249637 prefixEnd_249637 := by exact prefixLift 249637
  have htrace : WordTrace (prefixWord ++ tailWord_249637) baseStart_249637 baseEnd_249637 := by
    simpa [prefixWord, tailWord_249637, baseEnd_249637] using wordTrace_append hprefix tailTrace_249637
  have hstable : (prefixWord ++ tailWord_249637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249637).length < 2 ^ (prefixWord ++ tailWord_249637).sum := by decide
  have hdescent : baseEnd_249637 < baseStart_249637 := by decide
  rcases family_descends (prefixWord ++ tailWord_249637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249644 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_249644 : Nat := 118140960795 + 249644 * 2 ^ 59
def prefixEnd_249644 : Nat := 4983230072969 + 3 ^ 40 * 249644 * 2
def baseEnd_249644 : Nat := 113944324009890222579479

theorem tailTrace_249644 : CollatzResearch.WordTrace tailWord_249644 prefixEnd_249644 113944324009890222579479 := by
  unfold tailWord_249644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552632353794949322949993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6070176471726599097266657 4552632353794949322949993)
  ·
    refine ⟨3414474265346211992212495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4552632353794949322949993 3414474265346211992212495)
    ·
      refine ⟨5121711398019317988318743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414474265346211992212495 5121711398019317988318743)
      ·
        refine ⟨7682567097028976982478115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121711398019317988318743 7682567097028976982478115)
        ·
          refine ⟨11523850645543465473717173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682567097028976982478115 11523850645543465473717173)
          ·
            refine ⟨1080360998019699888160985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11523850645543465473717173 1080360998019699888160985)
            ·
              refine ⟨810270748514774916120739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080360998019699888160985 810270748514774916120739)
              ·
                refine ⟨1215406122772162374181109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810270748514774916120739 1215406122772162374181109)
                ·
                  refine ⟨113944324009890222579479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1215406122772162374181109 113944324009890222579479)
                  ·
                    rfl

theorem cell20_249644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_249644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249644 prefixEnd_249644 := by exact prefixLift 249644
  have htrace : WordTrace (prefixWord ++ tailWord_249644) baseStart_249644 baseEnd_249644 := by
    simpa [prefixWord, tailWord_249644, baseEnd_249644] using wordTrace_append hprefix tailTrace_249644
  have hstable : (prefixWord ++ tailWord_249644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249644).length < 2 ^ (prefixWord ++ tailWord_249644).sum := by decide
  have hdescent : baseEnd_249644 < baseStart_249644 := by decide
  rcases family_descends (prefixWord ++ tailWord_249644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249654 : List Nat := [5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_249654 : Nat := 118140960795 + 249654 * 2 ^ 59
def prefixEnd_249654 : Nat := 4983230072969 + 3 ^ 40 * 249654 * 2
def baseEnd_249654 : Nat := 37982962760791544082035

theorem tailTrace_249654 : CollatzResearch.WordTrace tailWord_249654 prefixEnd_249654 37982962760791544082035 := by
  unfold tailWord_249654
  simp only [CollatzResearch.WordTrace]
  refine ⟨569101839847104397110251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6070419625035780235842677 569101839847104397110251)
  ·
    refine ⟨853652759770656595665377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569101839847104397110251 853652759770656595665377)
    ·
      refine ⟨640239569827992446749033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 853652759770656595665377 640239569827992446749033)
      ·
        refine ⟨480179677370994335061775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640239569827992446749033 480179677370994335061775)
        ·
          refine ⟨720269516056491502592663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480179677370994335061775 720269516056491502592663)
          ·
            refine ⟨1080404274084737253888995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720269516056491502592663 1080404274084737253888995)
            ·
              refine ⟨1620606411127105880833493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080404274084737253888995 1620606411127105880833493)
              ·
                refine ⟨37982962760791544082035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1620606411127105880833493 37982962760791544082035)
                ·
                  rfl

theorem cell20_249654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_249654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249654 prefixEnd_249654 := by exact prefixLift 249654
  have htrace : WordTrace (prefixWord ++ tailWord_249654) baseStart_249654 baseEnd_249654 := by
    simpa [prefixWord, tailWord_249654, baseEnd_249654] using wordTrace_append hprefix tailTrace_249654
  have hstable : (prefixWord ++ tailWord_249654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249654).length < 2 ^ (prefixWord ++ tailWord_249654).sum := by decide
  have hdescent : baseEnd_249654 < baseStart_249654 := by decide
  rcases family_descends (prefixWord ++ tailWord_249654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249692 : List Nat := [2, 2, 4, 2, 3, 7]
def baseStart_249692 : Nat := 118140960795 + 249692 * 2 ^ 59
def prefixEnd_249692 : Nat := 4983230072969 + 3 ^ 40 * 249692 * 2
def baseEnd_249692 : Nat := 4220971574733903295529

theorem tailTrace_249692 : CollatzResearch.WordTrace tailWord_249692 prefixEnd_249692 4220971574733903295529 := by
  unfold tailWord_249692
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553507705708001421823665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6071343607610668562431553 4553507705708001421823665)
  ·
    refine ⟨3415130779281001066367749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4553507705708001421823665 3415130779281001066367749)
    ·
      refine ⟨640337021115187699943953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3415130779281001066367749 640337021115187699943953)
      ·
        refine ⟨480252765836390774957965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640337021115187699943953 480252765836390774957965)
        ·
          refine ⟨180094787188646540609237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480252765836390774957965 180094787188646540609237)
          ·
            refine ⟨4220971574733903295529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180094787188646540609237 4220971574733903295529)
            ·
              rfl

theorem cell20_249692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 7].length) (baseStart_249692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249692 prefixEnd_249692 := by exact prefixLift 249692
  have htrace : WordTrace (prefixWord ++ tailWord_249692) baseStart_249692 baseEnd_249692 := by
    simpa [prefixWord, tailWord_249692, baseEnd_249692] using wordTrace_append hprefix tailTrace_249692
  have hstable : (prefixWord ++ tailWord_249692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249692).length < 2 ^ (prefixWord ++ tailWord_249692).sum := by decide
  have hdescent : baseEnd_249692 < baseStart_249692 := by decide
  rcases family_descends (prefixWord ++ tailWord_249692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249696 : List Nat := [2, 1, 1, 3, 3, 10]
def baseStart_249696 : Nat := 118140960795 + 249696 * 2 ^ 59
def prefixEnd_249696 : Nat := 4983230072969 + 3 ^ 40 * 249696 * 2
def baseEnd_249696 : Nat := 4221039193585524179479

theorem tailTrace_249696 : CollatzResearch.WordTrace tailWord_249696 prefixEnd_249696 4221039193585524179479 := by
  unfold tailWord_249696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553580651700755763396471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6071440868934341017861961 4553580651700755763396471)
  ·
    refine ⟨6830370977551133645094707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553580651700755763396471 6830370977551133645094707)
    ·
      refine ⟨10245556466326700467642061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830370977551133645094707 10245556466326700467642061)
      ·
        refine ⟨3842083674872512675365773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10245556466326700467642061 3842083674872512675365773)
        ·
          refine ⟨1440781378077192253262165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3842083674872512675365773 1440781378077192253262165)
          ·
            refine ⟨4221039193585524179479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1440781378077192253262165 4221039193585524179479)
            ·
              rfl

theorem cell20_249696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 10].length) (baseStart_249696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249696 prefixEnd_249696 := by exact prefixLift 249696
  have htrace : WordTrace (prefixWord ++ tailWord_249696) baseStart_249696 baseEnd_249696 := by
    simpa [prefixWord, tailWord_249696, baseEnd_249696] using wordTrace_append hprefix tailTrace_249696
  have hstable : (prefixWord ++ tailWord_249696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249696).length < 2 ^ (prefixWord ++ tailWord_249696).sum := by decide
  have hdescent : baseEnd_249696 < baseStart_249696 := by decide
  rcases family_descends (prefixWord ++ tailWord_249696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249744 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_249744 : Nat := 118140960795 + 249744 * 2 ^ 59
def prefixEnd_249744 : Nat := 4983230072969 + 3 ^ 40 * 249744 * 2
def baseEnd_249744 : Nat := 113989966734734319245737

theorem tailTrace_249744 : CollatzResearch.WordTrace tailWord_249744 prefixEnd_249744 113989966734734319245737 := by
  unfold tailWord_249744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554456003613807862270143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6072608004818410483026857 4554456003613807862270143)
  ·
    refine ⟨6831684005420711793405215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4554456003613807862270143 6831684005420711793405215)
    ·
      refine ⟨10247526008131067690107823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831684005420711793405215 10247526008131067690107823)
      ·
        refine ⟨15371289012196601535161735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247526008131067690107823 15371289012196601535161735)
        ·
          refine ⟨23056933518294902302742603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371289012196601535161735 23056933518294902302742603)
          ·
            refine ⟨34585400277442353454113905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23056933518294902302742603 34585400277442353454113905)
            ·
              refine ⟨25939050208081765090585429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34585400277442353454113905 25939050208081765090585429)
              ·
                refine ⟨151986622312979092327649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25939050208081765090585429 151986622312979092327649)
                ·
                  refine ⟨113989966734734319245737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151986622312979092327649 113989966734734319245737)
                  ·
                    rfl

theorem cell20_249744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_249744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249744 prefixEnd_249744 := by exact prefixLift 249744
  have htrace : WordTrace (prefixWord ++ tailWord_249744) baseStart_249744 baseEnd_249744 := by
    simpa [prefixWord, tailWord_249744, baseEnd_249744] using wordTrace_append hprefix tailTrace_249744
  have hstable : (prefixWord ++ tailWord_249744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249744).length < 2 ^ (prefixWord ++ tailWord_249744).sum := by decide
  have hdescent : baseEnd_249744 < baseStart_249744 := by decide
  rcases family_descends (prefixWord ++ tailWord_249744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249754 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_249754 : Nat := 118140960795 + 249754 * 2 ^ 59
def prefixEnd_249754 : Nat := 4983230072969 + 3 ^ 40 * 249754 * 2
def baseEnd_249754 : Nat := 113994531007218728912363

theorem tailTrace_249754 : CollatzResearch.WordTrace tailWord_249754 prefixEnd_249754 113994531007218728912363 := by
  unfold tailWord_249754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277319184297846858101079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6072851158127591621602877 2277319184297846858101079)
  ·
    refine ⟨3415978776446770287151619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2277319184297846858101079 3415978776446770287151619)
    ·
      refine ⟨5123968164670155430727429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415978776446770287151619 5123968164670155430727429)
      ·
        refine ⟨960744030875654143261393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5123968164670155430727429 960744030875654143261393)
        ·
          refine ⟨720558023156740607446045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960744030875654143261393 720558023156740607446045)
          ·
            refine ⟨270209258683777727792267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 720558023156740607446045 270209258683777727792267)
            ·
              refine ⟨405313888025666591688401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270209258683777727792267 405313888025666591688401)
              ·
                refine ⟨303985416019249943766301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405313888025666591688401 303985416019249943766301)
                ·
                  refine ⟨113994531007218728912363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303985416019249943766301 113994531007218728912363)
                  ·
                    rfl

theorem cell20_249754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_249754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249754 prefixEnd_249754 := by exact prefixLift 249754
  have htrace : WordTrace (prefixWord ++ tailWord_249754) baseStart_249754 baseEnd_249754 := by
    simpa [prefixWord, tailWord_249754, baseEnd_249754] using wordTrace_append hprefix tailTrace_249754
  have hstable : (prefixWord ++ tailWord_249754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249754).length < 2 ^ (prefixWord ++ tailWord_249754).sum := by decide
  have hdescent : baseEnd_249754 < baseStart_249754 := by decide
  rcases family_descends (prefixWord ++ tailWord_249754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249761 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_249761 : Nat := 118140960795 + 249761 * 2 ^ 59
def prefixEnd_249761 : Nat := 4983230072969 + 3 ^ 40 * 249761 * 2
def baseEnd_249761 : Nat := 113997725997957815679001

theorem tailTrace_249761 : CollatzResearch.WordTrace tailWord_249761 prefixEnd_249761 113997725997957815679001 := by
  unfold tailWord_249761
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109532048166027627909137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6073021365444018418606091 9109532048166027627909137)
  ·
    refine ⟨6832149036124520720931853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9109532048166027627909137 6832149036124520720931853)
    ·
      refine ⟨2562055888546695270349445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6832149036124520720931853 2562055888546695270349445)
      ·
        refine ⟨480385479102505363190521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2562055888546695270349445 480385479102505363190521)
        ·
          refine ⟨360289109326879022392891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480385479102505363190521 360289109326879022392891)
          ·
            refine ⟨540433663990318533589337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360289109326879022392891 540433663990318533589337)
            ·
              refine ⟨405325247992738900192003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540433663990318533589337 405325247992738900192003)
              ·
                refine ⟨607987871989108350288005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405325247992738900192003 607987871989108350288005)
                ·
                  refine ⟨113997725997957815679001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607987871989108350288005 113997725997957815679001)
                  ·
                    rfl

theorem cell20_249761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_249761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249761 prefixEnd_249761 := by exact prefixLift 249761
  have htrace : WordTrace (prefixWord ++ tailWord_249761) baseStart_249761 baseEnd_249761 := by
    simpa [prefixWord, tailWord_249761, baseEnd_249761] using wordTrace_append hprefix tailTrace_249761
  have hstable : (prefixWord ++ tailWord_249761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249761).length < 2 ^ (prefixWord ++ tailWord_249761).sum := by decide
  have hdescent : baseEnd_249761 < baseStart_249761 := by decide
  rcases family_descends (prefixWord ++ tailWord_249761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249775 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 3]
def baseStart_249775 : Nat := 118140960795 + 249775 * 2 ^ 59
def prefixEnd_249775 : Nat := 4983230072969 + 3 ^ 40 * 249775 * 2
def baseEnd_249775 : Nat := 114004115979435989212277

theorem tailTrace_249775 : CollatzResearch.WordTrace tailWord_249775 prefixEnd_249775 114004115979435989212277 := by
  unfold tailWord_249775
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110042670115308018918779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6073361780076872012612519 9110042670115308018918779)
  ·
    refine ⟨13665064005172962028378169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110042670115308018918779 13665064005172962028378169)
    ·
      refine ⟨10248798003879721521283627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13665064005172962028378169 10248798003879721521283627)
      ·
        refine ⟨15373197005819582281925441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10248798003879721521283627 15373197005819582281925441)
        ·
          refine ⟨11529897754364686711444081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15373197005819582281925441 11529897754364686711444081)
          ·
            refine ⟨8647423315773515033583061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11529897754364686711444081 8647423315773515033583061)
            ·
              refine ⟨202673983963441758599603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8647423315773515033583061 202673983963441758599603)
              ·
                refine ⟨304010975945162637899405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202673983963441758599603 304010975945162637899405)
                ·
                  refine ⟨114004115979435989212277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304010975945162637899405 114004115979435989212277)
                  ·
                    rfl

theorem cell20_249775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_249775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249775 prefixEnd_249775 := by exact prefixLift 249775
  have htrace : WordTrace (prefixWord ++ tailWord_249775) baseStart_249775 baseEnd_249775 := by
    simpa [prefixWord, tailWord_249775, baseEnd_249775] using wordTrace_append hprefix tailTrace_249775
  have hstable : (prefixWord ++ tailWord_249775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249775).length < 2 ^ (prefixWord ++ tailWord_249775).sum := by decide
  have hdescent : baseEnd_249775 < baseStart_249775 := by decide
  rcases family_descends (prefixWord ++ tailWord_249775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249789 : List Nat := [1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_249789 : Nat := 118140960795 + 249789 * 2 ^ 59
def prefixEnd_249789 : Nat := 4983230072969 + 3 ^ 40 * 249789 * 2
def baseEnd_249789 : Nat := 38003501986971387581851

theorem tailTrace_249789 : CollatzResearch.WordTrace tailWord_249789 prefixEnd_249789 38003501986971387581851 := by
  unfold tailWord_249789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110553292064588409928421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6073702194709725606618947 9110553292064588409928421)
  ·
    refine ⟨1708228742262110326861579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9110553292064588409928421 1708228742262110326861579)
    ·
      refine ⟨2562343113393165490292369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708228742262110326861579 2562343113393165490292369)
      ·
        refine ⟨1921757335044874117719277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2562343113393165490292369 1921757335044874117719277)
        ·
          refine ⟨720659000641827794144729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1921757335044874117719277 720659000641827794144729)
          ·
            refine ⟨540494250481370845608547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720659000641827794144729 540494250481370845608547)
            ·
              refine ⟨810741375722056268412821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540494250481370845608547 810741375722056268412821)
              ·
                refine ⟨38003501986971387581851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 810741375722056268412821 38003501986971387581851)
                ·
                  rfl

theorem cell20_249789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_249789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249789 prefixEnd_249789 := by exact prefixLift 249789
  have htrace : WordTrace (prefixWord ++ tailWord_249789) baseStart_249789 baseEnd_249789 := by
    simpa [prefixWord, tailWord_249789, baseEnd_249789] using wordTrace_append hprefix tailTrace_249789
  have hstable : (prefixWord ++ tailWord_249789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249789).length < 2 ^ (prefixWord ++ tailWord_249789).sum := by decide
  have hdescent : baseEnd_249789 < baseStart_249789 := by decide
  rcases family_descends (prefixWord ++ tailWord_249789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249826 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_249826 : Nat := 118140960795 + 249826 * 2 ^ 59
def prefixEnd_249826 : Nat := 4983230072969 + 3 ^ 40 * 249826 * 2
def baseEnd_249826 : Nat := 114027393769106478512069

theorem tailTrace_249826 : CollatzResearch.WordTrace tailWord_249826 prefixEnd_249826 114027393769106478512069 := by
  unfold tailWord_249826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277975698232635932256333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6074601861953695819350221 2277975698232635932256333)
  ·
    refine ⟨854240886837238474596125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2277975698232635932256333 854240886837238474596125)
    ·
      refine ⟨320340332563964427973547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 854240886837238474596125 320340332563964427973547)
      ·
        refine ⟨480510498845946641960321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320340332563964427973547 480510498845946641960321)
        ·
          refine ⟨360382874134459981470241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480510498845946641960321 360382874134459981470241)
          ·
            refine ⟨270287155600844986102681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360382874134459981470241 270287155600844986102681)
            ·
              refine ⟨202715366700633739577011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270287155600844986102681 202715366700633739577011)
              ·
                refine ⟨304073050050950609365517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202715366700633739577011 304073050050950609365517)
                ·
                  refine ⟨114027393769106478512069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304073050050950609365517 114027393769106478512069)
                  ·
                    rfl

theorem cell20_249826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_249826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249826 prefixEnd_249826 := by exact prefixLift 249826
  have htrace : WordTrace (prefixWord ++ tailWord_249826) baseStart_249826 baseEnd_249826 := by
    simpa [prefixWord, tailWord_249826, baseEnd_249826] using wordTrace_append hprefix tailTrace_249826
  have hstable : (prefixWord ++ tailWord_249826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249826).length < 2 ^ (prefixWord ++ tailWord_249826).sum := by decide
  have hdescent : baseEnd_249826 < baseStart_249826 := by decide
  rcases family_descends (prefixWord ++ tailWord_249826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249827 : List Nat := [1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_249827 : Nat := 118140960795 + 249827 * 2 ^ 59
def prefixEnd_249827 : Nat := 4983230072969 + 3 ^ 40 * 249827 * 2
def baseEnd_249827 : Nat := 38009283398784973159577

theorem tailTrace_249827 : CollatzResearch.WordTrace tailWord_249827 prefixEnd_249827 38009283398784973159577 := by
  unfold tailWord_249827
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111939265926920899811735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6074626177284613933207823 9111939265926920899811735)
  ·
    refine ⟨13667908898890381349717603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9111939265926920899811735 13667908898890381349717603)
    ·
      refine ⟨20501863348335572024576405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667908898890381349717603 20501863348335572024576405)
      ·
        refine ⟨961024844453229938652019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20501863348335572024576405 961024844453229938652019)
        ·
          refine ⟨1441537266679844907978029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961024844453229938652019 1441537266679844907978029)
          ·
            refine ⟨540576475004941840491761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1441537266679844907978029 540576475004941840491761)
            ·
              refine ⟨405432356253706380368821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540576475004941840491761 405432356253706380368821)
              ·
                refine ⟨38009283398784973159577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405432356253706380368821 38009283398784973159577)
                ·
                  rfl

theorem cell20_249827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_249827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249827 prefixEnd_249827 := by exact prefixLift 249827
  have htrace : WordTrace (prefixWord ++ tailWord_249827) baseStart_249827 baseEnd_249827 := by
    simpa [prefixWord, tailWord_249827, baseEnd_249827] using wordTrace_append hprefix tailTrace_249827
  have hstable : (prefixWord ++ tailWord_249827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249827).length < 2 ^ (prefixWord ++ tailWord_249827).sum := by decide
  have hdescent : baseEnd_249827 < baseStart_249827 := by decide
  rcases family_descends (prefixWord ++ tailWord_249827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249848 : List Nat := [2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_249848 : Nat := 118140960795 + 249848 * 2 ^ 59
def prefixEnd_249848 : Nat := 4983230072969 + 3 ^ 40 * 249848 * 2
def baseEnd_249848 : Nat := 38012478389524059926215

theorem tailTrace_249848 : CollatzResearch.WordTrace tailWord_249848 prefixEnd_249848 38012478389524059926215 := by
  unfold tailWord_249848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556352599425420743163099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6075136799233894324217465 4556352599425420743163099)
  ·
    refine ⟨6834528899138131114744649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556352599425420743163099 6834528899138131114744649)
    ·
      refine ⟨5125896674353598336058487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834528899138131114744649 5125896674353598336058487)
      ·
        refine ⟨7688845011530397504087731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125896674353598336058487 7688845011530397504087731)
        ·
          refine ⟨11533267517295596256131597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688845011530397504087731 11533267517295596256131597)
          ·
            refine ⟨4324975318985848596049349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11533267517295596256131597 4324975318985848596049349)
            ·
              refine ⟨810932872309846611759253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4324975318985848596049349 810932872309846611759253)
              ·
                refine ⟨38012478389524059926215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 810932872309846611759253 38012478389524059926215)
                ·
                  rfl

theorem cell20_249848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_249848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249848 prefixEnd_249848 := by exact prefixLift 249848
  have htrace : WordTrace (prefixWord ++ tailWord_249848) baseStart_249848 baseEnd_249848 := by
    simpa [prefixWord, tailWord_249848, baseEnd_249848] using wordTrace_append hprefix tailTrace_249848
  have hstable : (prefixWord ++ tailWord_249848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249848).length < 2 ^ (prefixWord ++ tailWord_249848).sum := by decide
  have hdescent : baseEnd_249848 < baseStart_249848 := by decide
  rcases family_descends (prefixWord ++ tailWord_249848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249855 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_249855 : Nat := 118140960795 + 249855 * 2 ^ 59
def prefixEnd_249855 : Nat := 4983230072969 + 3 ^ 40 * 249855 * 2
def baseEnd_249855 : Nat := 114040630159311266545283

theorem tailTrace_249855 : CollatzResearch.WordTrace tailWord_249855 prefixEnd_249855 114040630159311266545283 := by
  unfold tailWord_249855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112960509825481681831019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6075307006550321121220679 9112960509825481681831019)
  ·
    refine ⟨13669440764738222522746529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9112960509825481681831019 13669440764738222522746529)
    ·
      refine ⟨10252080573553666892059897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13669440764738222522746529 10252080573553666892059897)
      ·
        refine ⟨7689060430165250169044923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10252080573553666892059897 7689060430165250169044923)
        ·
          refine ⟨11533590645247875253567385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689060430165250169044923 11533590645247875253567385)
          ·
            refine ⟨8650192983935906440175539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11533590645247875253567385 8650192983935906440175539)
            ·
              refine ⟨12975289475903859660263309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650192983935906440175539 12975289475903859660263309)
              ·
                refine ⟨4865733553463947372598741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12975289475903859660263309 4865733553463947372598741)
                ·
                  refine ⟨114040630159311266545283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4865733553463947372598741 114040630159311266545283)
                  ·
                    rfl

theorem cell20_249855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_249855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249855 prefixEnd_249855 := by exact prefixLift 249855
  have htrace : WordTrace (prefixWord ++ tailWord_249855) baseStart_249855 baseEnd_249855 := by
    simpa [prefixWord, tailWord_249855, baseEnd_249855] using wordTrace_append hprefix tailTrace_249855
  have hstable : (prefixWord ++ tailWord_249855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249855).length < 2 ^ (prefixWord ++ tailWord_249855).sum := by decide
  have hdescent : baseEnd_249855 < baseStart_249855 := by decide
  rcases family_descends (prefixWord ++ tailWord_249855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249875 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 2]
def baseStart_249875 : Nat := 118140960795 + 249875 * 2 ^ 59
def prefixEnd_249875 : Nat := 4983230072969 + 3 ^ 40 * 249875 * 2
def baseEnd_249875 : Nat := 114049758704280085878535

theorem tailTrace_249875 : CollatzResearch.WordTrace tailWord_249875 prefixEnd_249875 114049758704280085878535 := by
  unfold tailWord_249875
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113689969753025097559079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6075793313168683398372719 9113689969753025097559079)
  ·
    refine ⟨13670534954629537646338619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113689969753025097559079 13670534954629537646338619)
    ·
      refine ⟨20505802431944306469507929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670534954629537646338619 20505802431944306469507929)
      ·
        refine ⟨15379351823958229852130947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20505802431944306469507929 15379351823958229852130947)
        ·
          refine ⟨23069027735937344778196421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15379351823958229852130947 23069027735937344778196421)
          ·
            refine ⟨4325442700488252145911829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23069027735937344778196421 4325442700488252145911829)
            ·
              refine ⟨202755126585386819339617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4325442700488252145911829 202755126585386819339617)
              ·
                refine ⟨152066344939040114504713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202755126585386819339617 152066344939040114504713)
                ·
                  refine ⟨114049758704280085878535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152066344939040114504713 114049758704280085878535)
                  ·
                    rfl

theorem cell20_249875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2].length) (baseStart_249875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249875 prefixEnd_249875 := by exact prefixLift 249875
  have htrace : WordTrace (prefixWord ++ tailWord_249875) baseStart_249875 baseEnd_249875 := by
    simpa [prefixWord, tailWord_249875, baseEnd_249875] using wordTrace_append hprefix tailTrace_249875
  have hstable : (prefixWord ++ tailWord_249875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249875).length < 2 ^ (prefixWord ++ tailWord_249875).sum := by decide
  have hdescent : baseEnd_249875 < baseStart_249875 := by decide
  rcases family_descends (prefixWord ++ tailWord_249875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249917 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_249917 : Nat := 118140960795 + 249917 * 2 ^ 59
def prefixEnd_249917 : Nat := 4983230072969 + 3 ^ 40 * 249917 * 2
def baseEnd_249917 : Nat := 114068928648714606478363

theorem tailTrace_249917 : CollatzResearch.WordTrace tailWord_249917 prefixEnd_249917 114068928648714606478363 := by
  unfold tailWord_249917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115221835600866270588005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6076814557067244180392003 9115221835600866270588005)
  ·
    refine ⟨1709104094175162425735251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9115221835600866270588005 1709104094175162425735251)
    ·
      refine ⟨2563656141262743638602877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709104094175162425735251 2563656141262743638602877)
      ·
        refine ⟨961371052973528864476079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2563656141262743638602877 961371052973528864476079)
        ·
          refine ⟨1442056579460293296714119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961371052973528864476079 1442056579460293296714119)
          ·
            refine ⟨2163084869190439945071179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442056579460293296714119 2163084869190439945071179)
            ·
              refine ⟨3244627303785659917606769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163084869190439945071179 3244627303785659917606769)
              ·
                refine ⟨2433470477839244938205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244627303785659917606769 2433470477839244938205077)
                ·
                  refine ⟨114068928648714606478363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2433470477839244938205077 114068928648714606478363)
                  ·
                    rfl

theorem cell20_249917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_249917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249917 prefixEnd_249917 := by exact prefixLift 249917
  have htrace : WordTrace (prefixWord ++ tailWord_249917) baseStart_249917 baseEnd_249917 := by
    simpa [prefixWord, tailWord_249917, baseEnd_249917] using wordTrace_append hprefix tailTrace_249917
  have hstable : (prefixWord ++ tailWord_249917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249917).length < 2 ^ (prefixWord ++ tailWord_249917).sum := by decide
  have hdescent : baseEnd_249917 < baseStart_249917 := by decide
  rcases family_descends (prefixWord ++ tailWord_249917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249931 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_249931 : Nat := 118140960795 + 249931 * 2 ^ 59
def prefixEnd_249931 : Nat := 4983230072969 + 3 ^ 40 * 249931 * 2
def baseEnd_249931 : Nat := 114075318630192780011639

theorem tailTrace_249931 : CollatzResearch.WordTrace tailWord_249931 prefixEnd_249931 114075318630192780011639 := by
  unfold tailWord_249931
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115732457550146661597647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6077154971700097774398431 9115732457550146661597647)
  ·
    refine ⟨13673598686325219992396471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9115732457550146661597647 13673598686325219992396471)
    ·
      refine ⟨20510398029487829988594707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673598686325219992396471 20510398029487829988594707)
      ·
        refine ⟨30765597044231744982892061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20510398029487829988594707 30765597044231744982892061)
        ·
          refine ⟨11537098891586904368584523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30765597044231744982892061 11537098891586904368584523)
          ·
            refine ⟨17305648337380356552876785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537098891586904368584523 17305648337380356552876785)
            ·
              refine ⟨12979236253035267414657589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17305648337380356552876785 12979236253035267414657589)
              ·
                refine ⟨1216803398722056320124149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12979236253035267414657589 1216803398722056320124149)
                ·
                  refine ⟨114075318630192780011639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216803398722056320124149 114075318630192780011639)
                  ·
                    rfl

theorem cell20_249931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_249931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249931 prefixEnd_249931 := by exact prefixLift 249931
  have htrace : WordTrace (prefixWord ++ tailWord_249931) baseStart_249931 baseEnd_249931 := by
    simpa [prefixWord, tailWord_249931, baseEnd_249931] using wordTrace_append hprefix tailTrace_249931
  have hstable : (prefixWord ++ tailWord_249931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249931).length < 2 ^ (prefixWord ++ tailWord_249931).sum := by decide
  have hdescent : baseEnd_249931 < baseStart_249931 := by decide
  rcases family_descends (prefixWord ++ tailWord_249931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249934 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_249934 : Nat := 118140960795 + 249934 * 2 ^ 59
def prefixEnd_249934 : Nat := 4983230072969 + 3 ^ 40 * 249934 * 2
def baseEnd_249934 : Nat := 114076687911938102911627

theorem tailTrace_249934 : CollatzResearch.WordTrace tailWord_249934 prefixEnd_249934 114076687911938102911627 := by
  unfold tailWord_249934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139480234567409771744607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6077227917692852115971237 1139480234567409771744607)
  ·
    refine ⟨1709220351851114657616911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139480234567409771744607 1709220351851114657616911)
    ·
      refine ⟨2563830527776671986425367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709220351851114657616911 2563830527776671986425367)
      ·
        refine ⟨3845745791665007979638051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563830527776671986425367 3845745791665007979638051)
        ·
          refine ⟨5768618687497511969457077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845745791665007979638051 5768618687497511969457077)
          ·
            refine ⟨540808001952891747136601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5768618687497511969457077 540808001952891747136601)
            ·
              refine ⟨405606001464668810352451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540808001952891747136601 405606001464668810352451)
              ·
                refine ⟨608409002197003215528677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405606001464668810352451 608409002197003215528677)
                ·
                  refine ⟨114076687911938102911627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608409002197003215528677 114076687911938102911627)
                  ·
                    rfl

theorem cell20_249934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_249934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249934 prefixEnd_249934 := by exact prefixLift 249934
  have htrace : WordTrace (prefixWord ++ tailWord_249934) baseStart_249934 baseEnd_249934 := by
    simpa [prefixWord, tailWord_249934, baseEnd_249934] using wordTrace_append hprefix tailTrace_249934
  have hstable : (prefixWord ++ tailWord_249934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249934).length < 2 ^ (prefixWord ++ tailWord_249934).sum := by decide
  have hdescent : baseEnd_249934 < baseStart_249934 := by decide
  rcases family_descends (prefixWord ++ tailWord_249934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249954 : List Nat := [3, 3, 2, 2, 3, 1, 2, 4]
def baseStart_249954 : Nat := 118140960795 + 249954 * 2 ^ 59
def prefixEnd_249954 : Nat := 4983230072969 + 3 ^ 40 * 249954 * 2
def baseEnd_249954 : Nat := 38028605485635640748293

theorem tailTrace_249954 : CollatzResearch.WordTrace tailWord_249954 prefixEnd_249954 38028605485635640748293 := by
  unfold tailWord_249954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279142834116705397421229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6077714224311214393123277 2279142834116705397421229)
  ·
    refine ⟨854678562793764524032961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2279142834116705397421229 854678562793764524032961)
    ·
      refine ⟨641008922095323393024721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 854678562793764524032961 641008922095323393024721)
      ·
        refine ⟨480756691571492544768541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641008922095323393024721 480756691571492544768541)
        ·
          refine ⟨180283759339309704288203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480756691571492544768541 180283759339309704288203)
          ·
            refine ⟨270425639008964556432305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180283759339309704288203 270425639008964556432305)
            ·
              refine ⟨202819229256723417324229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270425639008964556432305 202819229256723417324229)
              ·
                refine ⟨38028605485635640748293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202819229256723417324229 38028605485635640748293)
                ·
                  rfl

theorem cell20_249954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_249954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249954 prefixEnd_249954 := by exact prefixLift 249954
  have htrace : WordTrace (prefixWord ++ tailWord_249954) baseStart_249954 baseEnd_249954 := by
    simpa [prefixWord, tailWord_249954, baseEnd_249954] using wordTrace_append hprefix tailTrace_249954
  have hstable : (prefixWord ++ tailWord_249954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249954).length < 2 ^ (prefixWord ++ tailWord_249954).sum := by decide
  have hdescent : baseEnd_249954 < baseStart_249954 := by decide
  rcases family_descends (prefixWord ++ tailWord_249954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249955 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_249955 : Nat := 118140960795 + 249955 * 2 ^ 59
def prefixEnd_249955 : Nat := 4983230072969 + 3 ^ 40 * 249955 * 2
def baseEnd_249955 : Nat := 114086272884155363211541

theorem tailTrace_249955 : CollatzResearch.WordTrace tailWord_249955 prefixEnd_249955 114086272884155363211541 := by
  unfold tailWord_249955
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116607809463198760471319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6077738539642132506980879 9116607809463198760471319)
  ·
    refine ⟨13674911714194798140706979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9116607809463198760471319 13674911714194798140706979)
    ·
      refine ⟨20512367571292197211060469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13674911714194798140706979 20512367571292197211060469)
      ·
        refine ⟨1923034459808643488536919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20512367571292197211060469 1923034459808643488536919)
        ·
          refine ⟨2884551689712965232805379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923034459808643488536919 2884551689712965232805379)
          ·
            refine ⟨4326827534569447849208069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884551689712965232805379 4326827534569447849208069)
            ·
              refine ⟨811280162731771471726513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4326827534569447849208069 811280162731771471726513)
              ·
                refine ⟨608460122048828603794885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811280162731771471726513 608460122048828603794885)
                ·
                  refine ⟨114086272884155363211541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608460122048828603794885 114086272884155363211541)
                  ·
                    rfl

theorem cell20_249955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_249955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249955 prefixEnd_249955 := by exact prefixLift 249955
  have htrace : WordTrace (prefixWord ++ tailWord_249955) baseStart_249955 baseEnd_249955 := by
    simpa [prefixWord, tailWord_249955, baseEnd_249955] using wordTrace_append hprefix tailTrace_249955
  have hstable : (prefixWord ++ tailWord_249955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249955).length < 2 ^ (prefixWord ++ tailWord_249955).sum := by decide
  have hdescent : baseEnd_249955 < baseStart_249955 := by decide
  rcases family_descends (prefixWord ++ tailWord_249955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249969 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_249969 : Nat := 118140960795 + 249969 * 2 ^ 59
def prefixEnd_249969 : Nat := 4983230072969 + 3 ^ 40 * 249969 * 2
def baseEnd_249969 : Nat := 114092662865633536744817

theorem tailTrace_249969 : CollatzResearch.WordTrace tailWord_249969 prefixEnd_249969 114092662865633536744817 := by
  unfold tailWord_249969
  simp only [CollatzResearch.WordTrace]
  refine ⟨9117118431412479151480961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6078078954274986100987307 9117118431412479151480961)
  ·
    refine ⟨6837838823559359363610721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9117118431412479151480961 6837838823559359363610721)
    ·
      refine ⟨5128379117669519522708041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6837838823559359363610721 5128379117669519522708041)
      ·
        refine ⟨3846284338252139642031031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5128379117669519522708041 3846284338252139642031031)
        ·
          refine ⟨5769426507378209463046547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846284338252139642031031 5769426507378209463046547)
          ·
            refine ⟨8654139761067314194569821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769426507378209463046547 8654139761067314194569821)
            ·
              refine ⟨3245302410400242822963683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8654139761067314194569821 3245302410400242822963683)
              ·
                refine ⟨4867953615600364234445525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245302410400242822963683 4867953615600364234445525)
                ·
                  refine ⟨114092662865633536744817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4867953615600364234445525 114092662865633536744817)
                  ·
                    rfl

theorem cell20_249969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_249969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249969 prefixEnd_249969 := by exact prefixLift 249969
  have htrace : WordTrace (prefixWord ++ tailWord_249969) baseStart_249969 baseEnd_249969 := by
    simpa [prefixWord, tailWord_249969, baseEnd_249969] using wordTrace_append hprefix tailTrace_249969
  have hstable : (prefixWord ++ tailWord_249969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249969).length < 2 ^ (prefixWord ++ tailWord_249969).sum := by decide
  have hdescent : baseEnd_249969 < baseStart_249969 := by decide
  rcases family_descends (prefixWord ++ tailWord_249969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250000 : List Nat := [2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_250000 : Nat := 118140960795 + 250000 * 2 ^ 59
def prefixEnd_250000 : Nat := 4983230072969 + 3 ^ 40 * 250000 * 2
def baseEnd_250000 : Nat := 38035604036778402237119

theorem tailTrace_250000 : CollatzResearch.WordTrace tailWord_250000 prefixEnd_250000 38035604036778402237119 := by
  unfold tailWord_250000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559124547150085722929727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6078832729533447630572969 4559124547150085722929727)
  ·
    refine ⟨6838686820725128584394591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4559124547150085722929727 6838686820725128584394591)
    ·
      refine ⟨10258030231087692876591887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838686820725128584394591 10258030231087692876591887)
      ·
        refine ⟨15387045346631539314887831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258030231087692876591887 15387045346631539314887831)
        ·
          refine ⟨23080568019947308972331747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387045346631539314887831 23080568019947308972331747)
          ·
            refine ⟨34620852029920963458497621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23080568019947308972331747 34620852029920963458497621)
            ·
              refine ⟨405713109725636290529269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 34620852029920963458497621 405713109725636290529269)
              ·
                refine ⟨38035604036778402237119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405713109725636290529269 38035604036778402237119)
                ·
                  rfl

theorem cell20_250000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_250000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250000 prefixEnd_250000 := by exact prefixLift 250000
  have htrace : WordTrace (prefixWord ++ tailWord_250000) baseStart_250000 baseEnd_250000 := by
    simpa [prefixWord, tailWord_250000, baseEnd_250000] using wordTrace_append hprefix tailTrace_250000
  have hstable : (prefixWord ++ tailWord_250000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250000).length < 2 ^ (prefixWord ++ tailWord_250000).sum := by decide
  have hdescent : baseEnd_250000 < baseStart_250000 := by decide
  rcases family_descends (prefixWord ++ tailWord_250000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250036 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_250036 : Nat := 118140960795 + 250036 * 2 ^ 59
def prefixEnd_250036 : Nat := 4983230072969 + 3 ^ 40 * 250036 * 2
def baseEnd_250036 : Nat := 114123243491279081511211

theorem tailTrace_250036 : CollatzResearch.WordTrace tailWord_250036 prefixEnd_250036 114123243491279081511211 := by
  unfold tailWord_250036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559781061084874797084981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6079708081446499729446641 4559781061084874797084981)
  ·
    refine ⟨427479474476707012226717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4559781061084874797084981 427479474476707012226717)
    ·
      refine ⟨160304802928765129585019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427479474476707012226717 160304802928765129585019)
      ·
        refine ⟨240457204393147694377529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160304802928765129585019 240457204393147694377529)
        ·
          refine ⟨180342903294860770783147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240457204393147694377529 180342903294860770783147)
          ·
            refine ⟨270514354942291156174721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180342903294860770783147 270514354942291156174721)
            ·
              refine ⟨202885766206718367131041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270514354942291156174721 202885766206718367131041)
              ·
                refine ⟨152164324655038775348281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202885766206718367131041 152164324655038775348281)
                ·
                  refine ⟨114123243491279081511211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152164324655038775348281 114123243491279081511211)
                  ·
                    rfl

theorem cell20_250036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_250036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250036 prefixEnd_250036 := by exact prefixLift 250036
  have htrace : WordTrace (prefixWord ++ tailWord_250036) baseStart_250036 baseEnd_250036 := by
    simpa [prefixWord, tailWord_250036, baseEnd_250036] using wordTrace_append hprefix tailTrace_250036
  have hstable : (prefixWord ++ tailWord_250036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250036).length < 2 ^ (prefixWord ++ tailWord_250036).sum := by decide
  have hdescent : baseEnd_250036 < baseStart_250036 := by decide
  rcases family_descends (prefixWord ++ tailWord_250036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250093 : List Nat := [1, 5, 1, 2, 3, 1, 7]
def baseStart_250093 : Nat := 118140960795 + 250093 * 2 ^ 59
def prefixEnd_250093 : Nat := 4983230072969 + 3 ^ 40 * 250093 * 2
def baseEnd_250093 : Nat := 12683251093826690734553

theorem tailTrace_250093 : CollatzResearch.WordTrace tailWord_250093 prefixEnd_250093 12683251093826690734553 := by
  unfold tailWord_250093
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121641082963248328994933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6081094055308832219329955 9121641082963248328994933)
  ·
    refine ⟨855153851527804530843275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9121641082963248328994933 855153851527804530843275)
    ·
      refine ⟨1282730777291706796264913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855153851527804530843275 1282730777291706796264913)
      ·
        refine ⟨962048082968780097198685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1282730777291706796264913 962048082968780097198685)
        ·
          refine ⟨360768031113292536449507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 962048082968780097198685 360768031113292536449507)
          ·
            refine ⟨541152046669938804674261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360768031113292536449507 541152046669938804674261)
            ·
              refine ⟨12683251093826690734553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 541152046669938804674261 12683251093826690734553)
              ·
                rfl

theorem cell20_250093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_250093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250093 prefixEnd_250093 := by exact prefixLift 250093
  have htrace : WordTrace (prefixWord ++ tailWord_250093) baseStart_250093 baseEnd_250093 := by
    simpa [prefixWord, tailWord_250093, baseEnd_250093] using wordTrace_append hprefix tailTrace_250093
  have hstable : (prefixWord ++ tailWord_250093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250093).length < 2 ^ (prefixWord ++ tailWord_250093).sum := by decide
  have hdescent : baseEnd_250093 < baseStart_250093 := by decide
  rcases family_descends (prefixWord ++ tailWord_250093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250158 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_250158 : Nat := 118140960795 + 250158 * 2 ^ 59
def prefixEnd_250158 : Nat := 4983230072969 + 3 ^ 40 * 250158 * 2
def baseEnd_250158 : Nat := 114178927615588879444045

theorem tailTrace_250158 : CollatzResearch.WordTrace tailWord_250158 prefixEnd_250158 114178927615588879444045 := by
  unfold tailWord_250158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140501478465970553763891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6082674551818509620074085 1140501478465970553763891)
  ·
    refine ⟨1710752217698955830645837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1140501478465970553763891 1710752217698955830645837)
    ·
      refine ⟨641532081637108436492189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1710752217698955830645837 641532081637108436492189)
      ·
        refine ⟨240574530613915663684571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641532081637108436492189 240574530613915663684571)
        ·
          refine ⟨360861795920873495526857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240574530613915663684571 360861795920873495526857)
          ·
            refine ⟨270646346940655121645143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360861795920873495526857 270646346940655121645143)
            ·
              refine ⟨405969520410982682467715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270646346940655121645143 405969520410982682467715)
              ·
                refine ⟨608954280616474023701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405969520410982682467715 608954280616474023701573)
                ·
                  refine ⟨114178927615588879444045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608954280616474023701573 114178927615588879444045)
                  ·
                    rfl

theorem cell20_250158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_250158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250158 prefixEnd_250158 := by exact prefixLift 250158
  have htrace : WordTrace (prefixWord ++ tailWord_250158) baseStart_250158 baseEnd_250158 := by
    simpa [prefixWord, tailWord_250158, baseEnd_250158] using wordTrace_append hprefix tailTrace_250158
  have hstable : (prefixWord ++ tailWord_250158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250158).length < 2 ^ (prefixWord ++ tailWord_250158).sum := by decide
  have hdescent : baseEnd_250158 < baseStart_250158 := by decide
  rcases family_descends (prefixWord ++ tailWord_250158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250159 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_250159 : Nat := 118140960795 + 250159 * 2 ^ 59
def prefixEnd_250159 : Nat := 4983230072969 + 3 ^ 40 * 250159 * 2
def baseEnd_250159 : Nat := 114179384042837320410707

theorem tailTrace_250159 : CollatzResearch.WordTrace tailWord_250159 prefixEnd_250159 114179384042837320410707 := by
  unfold tailWord_250159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124048300724141600897531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6082698867149427733931687 9124048300724141600897531)
  ·
    refine ⟨13686072451086212401346297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9124048300724141600897531 13686072451086212401346297)
    ·
      refine ⟨10264554338314659301009723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13686072451086212401346297 10264554338314659301009723)
      ·
        refine ⟨15396831507471988951514585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264554338314659301009723 15396831507471988951514585)
        ·
          refine ⟨11547623630603991713635939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15396831507471988951514585 11547623630603991713635939)
          ·
            refine ⟨17321435445905987570453909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547623630603991713635939 17321435445905987570453909)
            ·
              refine ⟨811942286526843167365027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17321435445905987570453909 811942286526843167365027)
              ·
                refine ⟨1217913429790264751047541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811942286526843167365027 1217913429790264751047541)
                ·
                  refine ⟨114179384042837320410707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1217913429790264751047541 114179384042837320410707)
                  ·
                    rfl

theorem cell20_250159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_250159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250159 prefixEnd_250159 := by exact prefixLift 250159
  have htrace : WordTrace (prefixWord ++ tailWord_250159) baseStart_250159 baseEnd_250159 := by
    simpa [prefixWord, tailWord_250159, baseEnd_250159] using wordTrace_append hprefix tailTrace_250159
  have hstable : (prefixWord ++ tailWord_250159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250159).length < 2 ^ (prefixWord ++ tailWord_250159).sum := by decide
  have hdescent : baseEnd_250159 < baseStart_250159 := by decide
  rcases family_descends (prefixWord ++ tailWord_250159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250169 : List Nat := [1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_250169 : Nat := 118140960795 + 250169 * 2 ^ 59
def prefixEnd_250169 : Nat := 4983230072969 + 3 ^ 40 * 250169 * 2
def baseEnd_250169 : Nat := 38061316105107243359111

theorem tailTrace_250169 : CollatzResearch.WordTrace tailWord_250169 prefixEnd_250169 38061316105107243359111 := by
  unfold tailWord_250169
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124413030687913308761561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6082942020458608872507707 9124413030687913308761561)
  ·
    refine ⟨6843309773015934981571171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9124413030687913308761561 6843309773015934981571171)
    ·
      refine ⟨10264964659523902472356757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843309773015934981571171 10264964659523902472356757)
      ·
        refine ⟨481170218415182928391723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10264964659523902472356757 481170218415182928391723)
        ·
          refine ⟨721755327622774392587585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481170218415182928391723 721755327622774392587585)
          ·
            refine ⟨541316495717080794440689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721755327622774392587585 541316495717080794440689)
            ·
              refine ⟨405987371787810595830517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541316495717080794440689 405987371787810595830517)
              ·
                refine ⟨38061316105107243359111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405987371787810595830517 38061316105107243359111)
                ·
                  rfl

theorem cell20_250169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_250169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250169 prefixEnd_250169 := by exact prefixLift 250169
  have htrace : WordTrace (prefixWord ++ tailWord_250169) baseStart_250169 baseEnd_250169 := by
    simpa [prefixWord, tailWord_250169, baseEnd_250169] using wordTrace_append hprefix tailTrace_250169
  have hstable : (prefixWord ++ tailWord_250169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250169).length < 2 ^ (prefixWord ++ tailWord_250169).sum := by decide
  have hdescent : baseEnd_250169 < baseStart_250169 := by decide
  rcases family_descends (prefixWord ++ tailWord_250169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250221 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_250221 : Nat := 118140960795 + 250221 * 2 ^ 59
def prefixEnd_250221 : Nat := 4983230072969 + 3 ^ 40 * 250221 * 2
def baseEnd_250221 : Nat := 114207682532240660343787

theorem tailTrace_250221 : CollatzResearch.WordTrace tailWord_250221 prefixEnd_250221 114207682532240660343787 := by
  unfold tailWord_250221
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126309626499526189654517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6084206417666350793103011 9126309626499526189654517)
  ·
    refine ⟨855591527484330580280111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9126309626499526189654517 855591527484330580280111)
    ·
      refine ⟨1283387291226495870420167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855591527484330580280111 1283387291226495870420167)
      ·
        refine ⟨1925080936839743805630251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283387291226495870420167 1925080936839743805630251)
        ·
          refine ⟨2887621405259615708445377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925080936839743805630251 2887621405259615708445377)
          ·
            refine ⟨2165716053944711781334033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887621405259615708445377 2165716053944711781334033)
            ·
              refine ⟨1624287040458533836000525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165716053944711781334033 1624287040458533836000525)
              ·
                refine ⟨609107640171950188500197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624287040458533836000525 609107640171950188500197)
                ·
                  refine ⟨114207682532240660343787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609107640171950188500197 114207682532240660343787)
                  ·
                    rfl

theorem cell20_250221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_250221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250221 prefixEnd_250221 := by exact prefixLift 250221
  have htrace : WordTrace (prefixWord ++ tailWord_250221) baseStart_250221 baseEnd_250221 := by
    simpa [prefixWord, tailWord_250221, baseEnd_250221] using wordTrace_append hprefix tailTrace_250221
  have hstable : (prefixWord ++ tailWord_250221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250221).length < 2 ^ (prefixWord ++ tailWord_250221).sum := by decide
  have hdescent : baseEnd_250221 < baseStart_250221 := by decide
  rcases family_descends (prefixWord ++ tailWord_250221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250266 : List Nat := [3, 1, 1, 4, 1, 3, 7]
def baseStart_250266 : Nat := 118140960795 + 250266 * 2 ^ 59
def prefixEnd_250266 : Nat := 4983230072969 + 3 ^ 40 * 250266 * 2
def baseEnd_250266 : Nat := 12692024639824500427067

theorem tailTrace_250266 : CollatzResearch.WordTrace tailWord_250266 prefixEnd_250266 12692024639824500427067 := by
  unfold tailWord_250266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281987727834124718760663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6085300607557665916695101 2281987727834124718760663)
  ·
    refine ⟨3422981591751187078140995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281987727834124718760663 3422981591751187078140995)
    ·
      refine ⟨5134472387626780617211493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422981591751187078140995 5134472387626780617211493)
      ·
        refine ⟨962713572680021365727155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5134472387626780617211493 962713572680021365727155)
        ·
          refine ⟨1444070359020032048590733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962713572680021365727155 1444070359020032048590733)
          ·
            refine ⟨541526384632512018221525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1444070359020032048590733 541526384632512018221525)
            ·
              refine ⟨12692024639824500427067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 541526384632512018221525 12692024639824500427067)
              ·
                rfl

theorem cell20_250266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_250266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250266 prefixEnd_250266 := by exact prefixLift 250266
  have htrace : WordTrace (prefixWord ++ tailWord_250266) baseStart_250266 baseEnd_250266 := by
    simpa [prefixWord, tailWord_250266, baseEnd_250266] using wordTrace_append hprefix tailTrace_250266
  have hstable : (prefixWord ++ tailWord_250266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250266).length < 2 ^ (prefixWord ++ tailWord_250266).sum := by decide
  have hdescent : baseEnd_250266 < baseStart_250266 := by decide
  rcases family_descends (prefixWord ++ tailWord_250266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250276 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_250276 : Nat := 118140960795 + 250276 * 2 ^ 59
def prefixEnd_250276 : Nat := 4983230072969 + 3 ^ 40 * 250276 * 2
def baseEnd_250276 : Nat := 114232786030904913510229

theorem tailTrace_250276 : CollatzResearch.WordTrace tailWord_250276 prefixEnd_250276 114232786030904913510229 := by
  unfold tailWord_250276
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564157820650135291453341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6085543760866847055271121 4564157820650135291453341)
  ·
    refine ⟨1711559182743800734295003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4564157820650135291453341 1711559182743800734295003)
    ·
      refine ⟨2567338774115701101442505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711559182743800734295003 2567338774115701101442505)
      ·
        refine ⟨1925504080586775826081879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567338774115701101442505 1925504080586775826081879)
        ·
          refine ⟨2888256120880163739122819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925504080586775826081879 2888256120880163739122819)
          ·
            refine ⟨4332384181320245608684229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888256120880163739122819 4332384181320245608684229)
            ·
              refine ⟨812322033997546051628293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4332384181320245608684229 812322033997546051628293)
              ·
                refine ⟨152310381374539884680305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812322033997546051628293 152310381374539884680305)
                ·
                  refine ⟨114232786030904913510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152310381374539884680305 114232786030904913510229)
                  ·
                    rfl

theorem cell20_250276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_250276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250276 prefixEnd_250276 := by exact prefixLift 250276
  have htrace : WordTrace (prefixWord ++ tailWord_250276) baseStart_250276 baseEnd_250276 := by
    simpa [prefixWord, tailWord_250276, baseEnd_250276] using wordTrace_append hprefix tailTrace_250276
  have hstable : (prefixWord ++ tailWord_250276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250276).length < 2 ^ (prefixWord ++ tailWord_250276).sum := by decide
  have hdescent : baseEnd_250276 < baseStart_250276 := by decide
  rcases family_descends (prefixWord ++ tailWord_250276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250282 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_250282 : Nat := 118140960795 + 250282 * 2 ^ 59
def prefixEnd_250282 : Nat := 4983230072969 + 3 ^ 40 * 250282 * 2
def baseEnd_250282 : Nat := 114235524594395559310205

theorem tailTrace_250282 : CollatzResearch.WordTrace tailWord_250282 prefixEnd_250282 114235524594395559310205 := by
  unfold tailWord_250282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282133619819633401906275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6085689652852355738416733 2282133619819633401906275)
  ·
    refine ⟨3423200429729450102859413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2282133619819633401906275 3423200429729450102859413)
    ·
      refine ⟨160462520143567973571535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3423200429729450102859413 160462520143567973571535)
      ·
        refine ⟨240693780215351960357303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160462520143567973571535 240693780215351960357303)
        ·
          refine ⟨361040670323027940535955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240693780215351960357303 361040670323027940535955)
          ·
            refine ⟨541561005484541910803933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361040670323027940535955 541561005484541910803933)
            ·
              refine ⟨203085377056703216551475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541561005484541910803933 203085377056703216551475)
              ·
                refine ⟨304628065585054824827213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203085377056703216551475 304628065585054824827213)
                ·
                  refine ⟨114235524594395559310205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304628065585054824827213 114235524594395559310205)
                  ·
                    rfl

theorem cell20_250282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_250282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250282 prefixEnd_250282 := by exact prefixLift 250282
  have htrace : WordTrace (prefixWord ++ tailWord_250282) baseStart_250282 baseEnd_250282 := by
    simpa [prefixWord, tailWord_250282, baseEnd_250282] using wordTrace_append hprefix tailTrace_250282
  have hstable : (prefixWord ++ tailWord_250282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250282).length < 2 ^ (prefixWord ++ tailWord_250282).sum := by decide
  have hdescent : baseEnd_250282 < baseStart_250282 := by decide
  rcases family_descends (prefixWord ++ tailWord_250282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250297 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_250297 : Nat := 118140960795 + 250297 * 2 ^ 59
def prefixEnd_250297 : Nat := 4983230072969 + 3 ^ 40 * 250297 * 2
def baseEnd_250297 : Nat := 114242371003122173810143

theorem tailTrace_250297 : CollatzResearch.WordTrace tailWord_250297 prefixEnd_250297 114242371003122173810143 := by
  unfold tailWord_250297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129081574224191169421145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6086054382816127446280763 9129081574224191169421145)
  ·
    refine ⟨6846811180668143377065859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9129081574224191169421145 6846811180668143377065859)
    ·
      refine ⟨10270216771002215065598789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846811180668143377065859 10270216771002215065598789)
      ·
        refine ⟨1925665644562915324799773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10270216771002215065598789 1925665644562915324799773)
        ·
          refine ⟨722124616711093246799915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1925665644562915324799773 722124616711093246799915)
          ·
            refine ⟨1083186925066639870199873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722124616711093246799915 1083186925066639870199873)
            ·
              refine ⟨812390193799979902649905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083186925066639870199873 812390193799979902649905)
              ·
                refine ⟨609292645349984926987429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812390193799979902649905 609292645349984926987429)
                ·
                  refine ⟨114242371003122173810143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609292645349984926987429 114242371003122173810143)
                  ·
                    rfl

theorem cell20_250297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_250297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250297 prefixEnd_250297 := by exact prefixLift 250297
  have htrace : WordTrace (prefixWord ++ tailWord_250297) baseStart_250297 baseEnd_250297 := by
    simpa [prefixWord, tailWord_250297, baseEnd_250297] using wordTrace_append hprefix tailTrace_250297
  have hstable : (prefixWord ++ tailWord_250297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250297).length < 2 ^ (prefixWord ++ tailWord_250297).sum := by decide
  have hdescent : baseEnd_250297 < baseStart_250297 := by decide
  rcases family_descends (prefixWord ++ tailWord_250297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250300 : List Nat := [2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_250300 : Nat := 118140960795 + 250300 * 2 ^ 59
def prefixEnd_250300 : Nat := 4983230072969 + 3 ^ 40 * 250300 * 2
def baseEnd_250300 : Nat := 38081246761622498903377

theorem tailTrace_250300 : CollatzResearch.WordTrace tailWord_250300 prefixEnd_250300 38081246761622498903377 := by
  unfold tailWord_250300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564595496606661340890177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6086127328808881787853569 4564595496606661340890177)
  ·
    refine ⟨3423446622454996005667633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4564595496606661340890177 3423446622454996005667633)
    ·
      refine ⟨2567584966841247004250725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3423446622454996005667633 2567584966841247004250725)
      ·
        refine ⟨481422181282733813297011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2567584966841247004250725 481422181282733813297011)
        ·
          refine ⟨722133271924100719945517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481422181282733813297011 722133271924100719945517)
          ·
            refine ⟨270799976971537769979569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722133271924100719945517 270799976971537769979569)
            ·
              refine ⟨203099982728653327484677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270799976971537769979569 203099982728653327484677)
              ·
                refine ⟨38081246761622498903377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203099982728653327484677 38081246761622498903377)
                ·
                  rfl

theorem cell20_250300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_250300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250300 prefixEnd_250300 := by exact prefixLift 250300
  have htrace : WordTrace (prefixWord ++ tailWord_250300) baseStart_250300 baseEnd_250300 := by
    simpa [prefixWord, tailWord_250300, baseEnd_250300] using wordTrace_append hprefix tailTrace_250300
  have hstable : (prefixWord ++ tailWord_250300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250300).length < 2 ^ (prefixWord ++ tailWord_250300).sum := by decide
  have hdescent : baseEnd_250300 < baseStart_250300 := by decide
  rcases family_descends (prefixWord ++ tailWord_250300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250311 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_250311 : Nat := 118140960795 + 250311 * 2 ^ 59
def prefixEnd_250311 : Nat := 4983230072969 + 3 ^ 40 * 250311 * 2
def baseEnd_250311 : Nat := 114248760984600347343419

theorem tailTrace_250311 : CollatzResearch.WordTrace tailWord_250311 prefixEnd_250311 114248760984600347343419 := by
  unfold tailWord_250311
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129592196173471560430787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6086394797448981040287191 9129592196173471560430787)
  ·
    refine ⟨13694388294260207340646181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9129592196173471560430787 13694388294260207340646181)
    ·
      refine ⟨2567697805173788876371159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13694388294260207340646181 2567697805173788876371159)
      ·
        refine ⟨3851546707760683314556739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567697805173788876371159 3851546707760683314556739)
        ·
          refine ⟨5777320061641024971835109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851546707760683314556739 5777320061641024971835109)
          ·
            refine ⟨1083247511557692182219083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5777320061641024971835109 1083247511557692182219083)
            ·
              refine ⟨1624871267336538273328625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083247511557692182219083 1624871267336538273328625)
              ·
                refine ⟨1218653450502403704996469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624871267336538273328625 1218653450502403704996469)
                ·
                  refine ⟨114248760984600347343419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218653450502403704996469 114248760984600347343419)
                  ·
                    rfl

theorem cell20_250311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_250311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250311 prefixEnd_250311 := by exact prefixLift 250311
  have htrace : WordTrace (prefixWord ++ tailWord_250311) baseStart_250311 baseEnd_250311 := by
    simpa [prefixWord, tailWord_250311, baseEnd_250311] using wordTrace_append hprefix tailTrace_250311
  have hstable : (prefixWord ++ tailWord_250311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250311).length < 2 ^ (prefixWord ++ tailWord_250311).sum := by decide
  have hdescent : baseEnd_250311 < baseStart_250311 := by decide
  rcases family_descends (prefixWord ++ tailWord_250311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250335 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_250335 : Nat := 118140960795 + 250335 * 2 ^ 59
def prefixEnd_250335 : Nat := 4983230072969 + 3 ^ 40 * 250335 * 2
def baseEnd_250335 : Nat := 114259715238562930543321

theorem tailTrace_250335 : CollatzResearch.WordTrace tailWord_250335 prefixEnd_250335 114259715238562930543321 := by
  unfold tailWord_250335
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130467548086523659304459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6086978365391015772869639 9130467548086523659304459)
  ·
    refine ⟨13695701322129785488956689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130467548086523659304459 13695701322129785488956689)
    ·
      refine ⟨10271775991597339116717517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13695701322129785488956689 10271775991597339116717517)
      ·
        refine ⟨3851915996849002168769069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10271775991597339116717517 3851915996849002168769069)
        ·
          refine ⟨1444468498818375813288401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3851915996849002168769069 1444468498818375813288401)
          ·
            refine ⟨1083351374113781859966301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444468498818375813288401 1083351374113781859966301)
            ·
              refine ⟨406256765292668197487363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1083351374113781859966301 406256765292668197487363)
              ·
                refine ⟨609385147939002296231045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406256765292668197487363 609385147939002296231045)
                ·
                  refine ⟨114259715238562930543321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609385147939002296231045 114259715238562930543321)
                  ·
                    rfl

theorem cell20_250335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_250335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250335 prefixEnd_250335 := by exact prefixLift 250335
  have htrace : WordTrace (prefixWord ++ tailWord_250335) baseStart_250335 baseEnd_250335 := by
    simpa [prefixWord, tailWord_250335, baseEnd_250335] using wordTrace_append hprefix tailTrace_250335
  have hstable : (prefixWord ++ tailWord_250335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250335).length < 2 ^ (prefixWord ++ tailWord_250335).sum := by decide
  have hdescent : baseEnd_250335 < baseStart_250335 := by decide
  rcases family_descends (prefixWord ++ tailWord_250335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250341 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 3]
def baseStart_250341 : Nat := 118140960795 + 250341 * 2 ^ 59
def prefixEnd_250341 : Nat := 4983230072969 + 3 ^ 40 * 250341 * 2
def baseEnd_250341 : Nat := 114262453802053576343297

theorem tailTrace_250341 : CollatzResearch.WordTrace tailWord_250341 prefixEnd_250341 114262453802053576343297 := by
  unfold tailWord_250341
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130686386064786684022877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6087124257376524456015251 9130686386064786684022877)
  ·
    refine ⟨3424007394774295006508579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9130686386064786684022877 3424007394774295006508579)
    ·
      refine ⟨5136011092161442509762869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424007394774295006508579 5136011092161442509762869)
      ·
        refine ⟨481501039890135235290269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5136011092161442509762869 481501039890135235290269)
        ·
          refine ⟨180562889958800713233851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481501039890135235290269 180562889958800713233851)
          ·
            refine ⟨270844334938201069850777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180562889958800713233851 270844334938201069850777)
            ·
              refine ⟨203133251203650802388083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270844334938201069850777 203133251203650802388083)
              ·
                refine ⟨304699876805476203582125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203133251203650802388083 304699876805476203582125)
                ·
                  refine ⟨114262453802053576343297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304699876805476203582125 114262453802053576343297)
                  ·
                    rfl

theorem cell20_250341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_250341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250341 prefixEnd_250341 := by exact prefixLift 250341
  have htrace : WordTrace (prefixWord ++ tailWord_250341) baseStart_250341 baseEnd_250341 := by
    simpa [prefixWord, tailWord_250341, baseEnd_250341] using wordTrace_append hprefix tailTrace_250341
  have hstable : (prefixWord ++ tailWord_250341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250341).length < 2 ^ (prefixWord ++ tailWord_250341).sum := by decide
  have hdescent : baseEnd_250341 < baseStart_250341 := by decide
  rcases family_descends (prefixWord ++ tailWord_250341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250397 : List Nat := [1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_250397 : Nat := 118140960795 + 250397 * 2 ^ 59
def prefixEnd_250397 : Nat := 4983230072969 + 3 ^ 40 * 250397 * 2
def baseEnd_250397 : Nat := 38096004575988756825467

theorem tailTrace_250397 : CollatzResearch.WordTrace tailWord_250397 prefixEnd_250397 38096004575988756825467 := by
  unfold tailWord_250397
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132728873861908248061445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6088485915907938832040963 9132728873861908248061445)
  ·
    refine ⟨1712386663849107796511521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9132728873861908248061445 1712386663849107796511521)
    ·
      refine ⟨1284289997886830847383641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1712386663849107796511521 1284289997886830847383641)
      ·
        refine ⟨963217498415123135537731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1284289997886830847383641 963217498415123135537731)
        ·
          refine ⟨1444826247622684703306597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963217498415123135537731 1444826247622684703306597)
          ·
            refine ⟨270904921429253381869987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1444826247622684703306597 270904921429253381869987)
            ·
              refine ⟨406357382143880072804981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270904921429253381869987 406357382143880072804981)
              ·
                refine ⟨38096004575988756825467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406357382143880072804981 38096004575988756825467)
                ·
                  rfl

theorem cell20_250397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_250397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250397 prefixEnd_250397 := by exact prefixLift 250397
  have htrace : WordTrace (prefixWord ++ tailWord_250397) baseStart_250397 baseEnd_250397 := by
    simpa [prefixWord, tailWord_250397, baseEnd_250397] using wordTrace_append hprefix tailTrace_250397
  have hstable : (prefixWord ++ tailWord_250397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250397).length < 2 ^ (prefixWord ++ tailWord_250397).sum := by decide
  have hdescent : baseEnd_250397 < baseStart_250397 := by decide
  rcases family_descends (prefixWord ++ tailWord_250397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250407 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_250407 : Nat := 118140960795 + 250407 * 2 ^ 59
def prefixEnd_250407 : Nat := 4983230072969 + 3 ^ 40 * 250407 * 2
def baseEnd_250407 : Nat := 114292578000450680143027

theorem tailTrace_250407 : CollatzResearch.WordTrace tailWord_250407 prefixEnd_250407 114292578000450680143027 := by
  unfold tailWord_250407
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133093603825679955925475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6088729069217119970616983 9133093603825679955925475)
  ·
    refine ⟨13699640405738519933888213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133093603825679955925475 13699640405738519933888213)
    ·
      refine ⟨321085322009496560950505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13699640405738519933888213 321085322009496560950505)
      ·
        refine ⟨240813991507122420712879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321085322009496560950505 240813991507122420712879)
        ·
          refine ⟨361220987260683631069319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240813991507122420712879 361220987260683631069319)
          ·
            refine ⟨541831480891025446603979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361220987260683631069319 541831480891025446603979)
            ·
              refine ⟨812747221336538169905969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541831480891025446603979 812747221336538169905969)
              ·
                refine ⟨609560416002403627429477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812747221336538169905969 609560416002403627429477)
                ·
                  refine ⟨114292578000450680143027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609560416002403627429477 114292578000450680143027)
                  ·
                    rfl

theorem cell20_250407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_250407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250407 prefixEnd_250407 := by exact prefixLift 250407
  have htrace : WordTrace (prefixWord ++ tailWord_250407) baseStart_250407 baseEnd_250407 := by
    simpa [prefixWord, tailWord_250407, baseEnd_250407] using wordTrace_append hprefix tailTrace_250407
  have hstable : (prefixWord ++ tailWord_250407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250407).length < 2 ^ (prefixWord ++ tailWord_250407).sum := by decide
  have hdescent : baseEnd_250407 < baseStart_250407 := by decide
  rcases family_descends (prefixWord ++ tailWord_250407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250414 : List Nat := [4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_250414 : Nat := 118140960795 + 250414 * 2 ^ 59
def prefixEnd_250414 : Nat := 4983230072969 + 3 ^ 40 * 250414 * 2
def baseEnd_250414 : Nat := 38098590997063255636555

theorem tailTrace_250414 : CollatzResearch.WordTrace tailWord_250414 prefixEnd_250414 38098590997063255636555 := by
  unfold tailWord_250414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141668614350040018928787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6088899276533546767620197 1141668614350040018928787)
  ·
    refine ⟨1712502921525060028393181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141668614350040018928787 1712502921525060028393181)
    ·
      refine ⟨642188595571897510647443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1712502921525060028393181 642188595571897510647443)
      ·
        refine ⟨963282893357846265971165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642188595571897510647443 963282893357846265971165)
        ·
          refine ⟨361231085009192349739187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 963282893357846265971165 361231085009192349739187)
          ·
            refine ⟨541846627513788524608781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361231085009192349739187 541846627513788524608781)
            ·
              refine ⟨203192485317670696728293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541846627513788524608781 203192485317670696728293)
              ·
                refine ⟨38098590997063255636555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203192485317670696728293 38098590997063255636555)
                ·
                  rfl

theorem cell20_250414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_250414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250414 prefixEnd_250414 := by exact prefixLift 250414
  have htrace : WordTrace (prefixWord ++ tailWord_250414) baseStart_250414 baseEnd_250414 := by
    simpa [prefixWord, tailWord_250414, baseEnd_250414] using wordTrace_append hprefix tailTrace_250414
  have hstable : (prefixWord ++ tailWord_250414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250414).length < 2 ^ (prefixWord ++ tailWord_250414).sum := by decide
  have hdescent : baseEnd_250414 < baseStart_250414 := by decide
  rcases family_descends (prefixWord ++ tailWord_250414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250425 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_250425 : Nat := 118140960795 + 250425 * 2 ^ 59
def prefixEnd_250425 : Nat := 4983230072969 + 3 ^ 40 * 250425 * 2
def baseEnd_250425 : Nat := 114300793690922617542953

theorem tailTrace_250425 : CollatzResearch.WordTrace tailWord_250425 prefixEnd_250425 114300793690922617542953 := by
  unfold tailWord_250425
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133750117760469030080729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6089166745173646020053819 9133750117760469030080729)
  ·
    refine ⟨6850312588320351772560547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133750117760469030080729 6850312588320351772560547)
    ·
      refine ⟨10275468882480527658840821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850312588320351772560547 10275468882480527658840821)
      ·
        refine ⟨963325207732549468016327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10275468882480527658840821 963325207732549468016327)
        ·
          refine ⟨1444987811598824202024491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963325207732549468016327 1444987811598824202024491)
          ·
            refine ⟨2167481717398236303036737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444987811598824202024491 2167481717398236303036737)
            ·
              refine ⟨1625611288048677227277553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167481717398236303036737 1625611288048677227277553)
              ·
                refine ⟨1219208466036507920458165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625611288048677227277553 1219208466036507920458165)
                ·
                  refine ⟨114300793690922617542953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1219208466036507920458165 114300793690922617542953)
                  ·
                    rfl

theorem cell20_250425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_250425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250425 prefixEnd_250425 := by exact prefixLift 250425
  have htrace : WordTrace (prefixWord ++ tailWord_250425) baseStart_250425 baseEnd_250425 := by
    simpa [prefixWord, tailWord_250425, baseEnd_250425] using wordTrace_append hprefix tailTrace_250425
  have hstable : (prefixWord ++ tailWord_250425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250425).length < 2 ^ (prefixWord ++ tailWord_250425).sum := by decide
  have hdescent : baseEnd_250425 < baseStart_250425 := by decide
  rcases family_descends (prefixWord ++ tailWord_250425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250428 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_250428 : Nat := 118140960795 + 250428 * 2 ^ 59
def prefixEnd_250428 : Nat := 4983230072969 + 3 ^ 40 * 250428 * 2
def baseEnd_250428 : Nat := 114302162972667940442941

theorem tailTrace_250428 : CollatzResearch.WordTrace tailWord_250428 prefixEnd_250428 114302162972667940442941 := by
  unfold tailWord_250428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566929768374800271219969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6089239691166400361626625 4566929768374800271219969)
  ·
    refine ⟨3425197326281100203414977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4566929768374800271219969 3425197326281100203414977)
    ·
      refine ⟨2568897994710825152561233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425197326281100203414977 2568897994710825152561233)
      ·
        refine ⟨1926673496033118864420925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2568897994710825152561233 1926673496033118864420925)
        ·
          refine ⟨722502561012419574157847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926673496033118864420925 722502561012419574157847)
          ·
            refine ⟨1083753841518629361236771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722502561012419574157847 1083753841518629361236771)
            ·
              refine ⟨1625630762277944041855157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083753841518629361236771 1625630762277944041855157)
              ·
                refine ⟨152402883963557253923921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1625630762277944041855157 152402883963557253923921)
                ·
                  refine ⟨114302162972667940442941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152402883963557253923921 114302162972667940442941)
                  ·
                    rfl

theorem cell20_250428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_250428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250428 prefixEnd_250428 := by exact prefixLift 250428
  have htrace : WordTrace (prefixWord ++ tailWord_250428) baseStart_250428 baseEnd_250428 := by
    simpa [prefixWord, tailWord_250428, baseEnd_250428] using wordTrace_append hprefix tailTrace_250428
  have hstable : (prefixWord ++ tailWord_250428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250428).length < 2 ^ (prefixWord ++ tailWord_250428).sum := by decide
  have hdescent : baseEnd_250428 < baseStart_250428 := by decide
  rcases family_descends (prefixWord ++ tailWord_250428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250438 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_250438 : Nat := 118140960795 + 250438 * 2 ^ 59
def prefixEnd_250438 : Nat := 4983230072969 + 3 ^ 40 * 250438 * 2
def baseEnd_250438 : Nat := 114306727245152350109567

theorem tailTrace_250438 : CollatzResearch.WordTrace tailWord_250438 prefixEnd_250438 114306727245152350109567 := by
  unfold tailWord_250438
  simp only [CollatzResearch.WordTrace]
  refine ⟨285444508334792882821999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6089482844475581500202645 285444508334792882821999)
  ·
    refine ⟨428166762502189324232999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285444508334792882821999 428166762502189324232999)
    ·
      refine ⟨642250143753283986349499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428166762502189324232999 642250143753283986349499)
      ·
        refine ⟨963375215629925979524249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642250143753283986349499 963375215629925979524249)
        ·
          refine ⟨722531411722444484643187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963375215629925979524249 722531411722444484643187)
          ·
            refine ⟨1083797117583666726964781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722531411722444484643187 1083797117583666726964781)
            ·
              refine ⟨406423919093875022611793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1083797117583666726964781 406423919093875022611793)
              ·
                refine ⟨304817939320406266958845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406423919093875022611793 304817939320406266958845)
                ·
                  refine ⟨114306727245152350109567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304817939320406266958845 114306727245152350109567)
                  ·
                    rfl

theorem cell20_250438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_250438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250438 prefixEnd_250438 := by exact prefixLift 250438
  have htrace : WordTrace (prefixWord ++ tailWord_250438) baseStart_250438 baseEnd_250438 := by
    simpa [prefixWord, tailWord_250438, baseEnd_250438] using wordTrace_append hprefix tailTrace_250438
  have hstable : (prefixWord ++ tailWord_250438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250438).length < 2 ^ (prefixWord ++ tailWord_250438).sum := by decide
  have hdescent : baseEnd_250438 < baseStart_250438 := by decide
  rcases family_descends (prefixWord ++ tailWord_250438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250442 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_250442 : Nat := 118140960795 + 250442 * 2 ^ 59
def prefixEnd_250442 : Nat := 4983230072969 + 3 ^ 40 * 250442 * 2
def baseEnd_250442 : Nat := 114308552954146113976217

theorem tailTrace_250442 : CollatzResearch.WordTrace tailWord_250442 prefixEnd_250442 114308552954146113976217 := by
  unfold tailWord_250442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283592539674720233362395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6089580105799253955633053 2283592539674720233362395)
  ·
    refine ⟨3425388809512080350043593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283592539674720233362395 3425388809512080350043593)
    ·
      refine ⟨2569041607134060262532695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425388809512080350043593 2569041607134060262532695)
      ·
        refine ⟨3853562410701090393799043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569041607134060262532695 3853562410701090393799043)
        ·
          refine ⟨5780343616051635590698565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853562410701090393799043 5780343616051635590698565)
          ·
            refine ⟨1083814428009681673255981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5780343616051635590698565 1083814428009681673255981)
            ·
              refine ⟨406430410503630627470993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1083814428009681673255981 406430410503630627470993)
              ·
                refine ⟨304822807877722970603245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406430410503630627470993 304822807877722970603245)
                ·
                  refine ⟨114308552954146113976217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304822807877722970603245 114308552954146113976217)
                  ·
                    rfl

theorem cell20_250442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_250442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250442 prefixEnd_250442 := by exact prefixLift 250442
  have htrace : WordTrace (prefixWord ++ tailWord_250442) baseStart_250442 baseEnd_250442 := by
    simpa [prefixWord, tailWord_250442, baseEnd_250442] using wordTrace_append hprefix tailTrace_250442
  have hstable : (prefixWord ++ tailWord_250442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250442).length < 2 ^ (prefixWord ++ tailWord_250442).sum := by decide
  have hdescent : baseEnd_250442 < baseStart_250442 := by decide
  rcases family_descends (prefixWord ++ tailWord_250442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250445 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 2]
def baseStart_250445 : Nat := 118140960795 + 250445 * 2 ^ 59
def prefixEnd_250445 : Nat := 4983230072969 + 3 ^ 40 * 250445 * 2
def baseEnd_250445 : Nat := 114309922235891436876205

theorem tailTrace_250445 : CollatzResearch.WordTrace tailWord_250445 prefixEnd_250445 114309922235891436876205 := by
  unfold tailWord_250445
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134479577688012445808789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6089653051792008297205859 9134479577688012445808789)
  ·
    refine ⟨428178730204125583397287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9134479577688012445808789 428178730204125583397287)
    ·
      refine ⟨642268095306188375095931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428178730204125583397287 642268095306188375095931)
      ·
        refine ⟨963402142959282562643897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642268095306188375095931 963402142959282562643897)
        ·
          refine ⟨722551607219461921982923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963402142959282562643897 722551607219461921982923)
          ·
            refine ⟨1083827410829192882974385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722551607219461921982923 1083827410829192882974385)
            ·
              refine ⟨812870558121894662230789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083827410829192882974385 812870558121894662230789)
              ·
                refine ⟨152413229647855249168273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812870558121894662230789 152413229647855249168273)
                ·
                  refine ⟨114309922235891436876205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152413229647855249168273 114309922235891436876205)
                  ·
                    rfl

theorem cell20_250445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_250445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250445 prefixEnd_250445 := by exact prefixLift 250445
  have htrace : WordTrace (prefixWord ++ tailWord_250445) baseStart_250445 baseEnd_250445 := by
    simpa [prefixWord, tailWord_250445, baseEnd_250445] using wordTrace_append hprefix tailTrace_250445
  have hstable : (prefixWord ++ tailWord_250445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250445).length < 2 ^ (prefixWord ++ tailWord_250445).sum := by decide
  have hdescent : baseEnd_250445 < baseStart_250445 := by decide
  rcases family_descends (prefixWord ++ tailWord_250445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250449 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_250449 : Nat := 118140960795 + 250449 * 2 ^ 59
def prefixEnd_250449 : Nat := 4983230072969 + 3 ^ 40 * 250449 * 2
def baseEnd_250449 : Nat := 114311747944885200742855

theorem tailTrace_250449 : CollatzResearch.WordTrace tailWord_250449 prefixEnd_250449 114311747944885200742855 := by
  unfold tailWord_250449
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134625469673521128954401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6089750313115680752636267 9134625469673521128954401)
  ·
    refine ⟨6850969102255140846715801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9134625469673521128954401 6850969102255140846715801)
    ·
      refine ⟨5138226826691355635036851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6850969102255140846715801 5138226826691355635036851)
      ·
        refine ⟨7707340240037033452555277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138226826691355635036851 7707340240037033452555277)
        ·
          refine ⟨2890252590013887544708229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7707340240037033452555277 2890252590013887544708229)
          ·
            refine ⟨541922360627603914632793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2890252590013887544708229 541922360627603914632793)
            ·
              refine ⟨406441770470702935974595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541922360627603914632793 406441770470702935974595)
              ·
                refine ⟨609662655706054403961893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406441770470702935974595 609662655706054403961893)
                ·
                  refine ⟨114311747944885200742855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609662655706054403961893 114311747944885200742855)
                  ·
                    rfl

theorem cell20_250449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_250449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250449 prefixEnd_250449 := by exact prefixLift 250449
  have htrace : WordTrace (prefixWord ++ tailWord_250449) baseStart_250449 baseEnd_250449 := by
    simpa [prefixWord, tailWord_250449, baseEnd_250449] using wordTrace_append hprefix tailTrace_250449
  have hstable : (prefixWord ++ tailWord_250449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250449).length < 2 ^ (prefixWord ++ tailWord_250449).sum := by decide
  have hdescent : baseEnd_250449 < baseStart_250449 := by decide
  rcases family_descends (prefixWord ++ tailWord_250449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250463 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_250463 : Nat := 118140960795 + 250463 * 2 ^ 59
def prefixEnd_250463 : Nat := 4983230072969 + 3 ^ 40 * 250463 * 2
def baseEnd_250463 : Nat := 114318137926363374276131

theorem tailTrace_250463 : CollatzResearch.WordTrace tailWord_250463 prefixEnd_250463 114318137926363374276131 := by
  unfold tailWord_250463
  simp only [CollatzResearch.WordTrace]
  refine ⟨9135136091622801519964043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6090090727748534346642695 9135136091622801519964043)
  ·
    refine ⟨13702704137434202279946065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9135136091622801519964043 13702704137434202279946065)
    ·
      refine ⟨10277028103075651709959549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13702704137434202279946065 10277028103075651709959549)
      ·
        refine ⟨3853885538653369391234831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10277028103075651709959549 3853885538653369391234831)
        ·
          refine ⟨5780828307980054086852247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853885538653369391234831 5780828307980054086852247)
          ·
            refine ⟨8671242461970081130278371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780828307980054086852247 8671242461970081130278371)
            ·
              refine ⟨13006863692955121695417557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671242461970081130278371 13006863692955121695417557)
              ·
                refine ⟨304848367803635664736349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13006863692955121695417557 304848367803635664736349)
                ·
                  refine ⟨114318137926363374276131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304848367803635664736349 114318137926363374276131)
                  ·
                    rfl

theorem cell20_250463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_250463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250463 prefixEnd_250463 := by exact prefixLift 250463
  have htrace : WordTrace (prefixWord ++ tailWord_250463) baseStart_250463 baseEnd_250463 := by
    simpa [prefixWord, tailWord_250463, baseEnd_250463] using wordTrace_append hprefix tailTrace_250463
  have hstable : (prefixWord ++ tailWord_250463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250463).length < 2 ^ (prefixWord ++ tailWord_250463).sum := by decide
  have hdescent : baseEnd_250463 < baseStart_250463 := by decide
  rcases family_descends (prefixWord ++ tailWord_250463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250501 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_250501 : Nat := 118140960795 + 250501 * 2 ^ 59
def prefixEnd_250501 : Nat := 4983230072969 + 3 ^ 40 * 250501 * 2
def baseEnd_250501 : Nat := 114335482161804131009309

theorem tailTrace_250501 : CollatzResearch.WordTrace tailWord_250501 prefixEnd_250501 114335482161804131009309 := by
  unfold tailWord_250501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136522065485134009847357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6091014710323422673231571 9136522065485134009847357)
  ·
    refine ⟨3426195774556925253692759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9136522065485134009847357 3426195774556925253692759)
    ·
      refine ⟨5139293661835387880539139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426195774556925253692759 5139293661835387880539139)
      ·
        refine ⟨7708940492753081820808709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139293661835387880539139 7708940492753081820808709)
        ·
          refine ⟨1445426342391202841401633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7708940492753081820808709 1445426342391202841401633)
          ·
            refine ⟨1084069756793402131051225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445426342391202841401633 1084069756793402131051225)
            ·
              refine ⟨813052317595051598288419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084069756793402131051225 813052317595051598288419)
              ·
                refine ⟨1219578476392577397432629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813052317595051598288419 1219578476392577397432629)
                ·
                  refine ⟨114335482161804131009309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1219578476392577397432629 114335482161804131009309)
                  ·
                    rfl

theorem cell20_250501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_250501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250501 prefixEnd_250501 := by exact prefixLift 250501
  have htrace : WordTrace (prefixWord ++ tailWord_250501) baseStart_250501 baseEnd_250501 := by
    simpa [prefixWord, tailWord_250501, baseEnd_250501] using wordTrace_append hprefix tailTrace_250501
  have hstable : (prefixWord ++ tailWord_250501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250501).length < 2 ^ (prefixWord ++ tailWord_250501).sum := by decide
  have hdescent : baseEnd_250501 < baseStart_250501 := by decide
  rcases family_descends (prefixWord ++ tailWord_250501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250508 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_250508 : Nat := 118140960795 + 250508 * 2 ^ 59
def prefixEnd_250508 : Nat := 4983230072969 + 3 ^ 40 * 250508 * 2
def baseEnd_250508 : Nat := 114338677152543217775947

theorem tailTrace_250508 : CollatzResearch.WordTrace tailWord_250508 prefixEnd_250508 114338677152543217775947 := by
  unfold tailWord_250508
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568388688229887102676089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6091184917639849470234785 4568388688229887102676089)
  ·
    refine ⟨3426291516172415327007067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4568388688229887102676089 3426291516172415327007067)
    ·
      refine ⟨5139437274258622990510601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426291516172415327007067 5139437274258622990510601)
      ·
        refine ⟨3854577955693967242882951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5139437274258622990510601 3854577955693967242882951)
        ·
          refine ⟨5781866933540950864324427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854577955693967242882951 5781866933540950864324427)
          ·
            refine ⟨8672800400311426296486641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781866933540950864324427 8672800400311426296486641)
            ·
              refine ⟨6504600300233569722364981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672800400311426296486641 6504600300233569722364981)
              ·
                refine ⟨609806278146897161471717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6504600300233569722364981 609806278146897161471717)
                ·
                  refine ⟨114338677152543217775947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609806278146897161471717 114338677152543217775947)
                  ·
                    rfl

theorem cell20_250508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_250508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250508 prefixEnd_250508 := by exact prefixLift 250508
  have htrace : WordTrace (prefixWord ++ tailWord_250508) baseStart_250508 baseEnd_250508 := by
    simpa [prefixWord, tailWord_250508, baseEnd_250508] using wordTrace_append hprefix tailTrace_250508
  have hstable : (prefixWord ++ tailWord_250508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250508).length < 2 ^ (prefixWord ++ tailWord_250508).sum := by decide
  have hdescent : baseEnd_250508 < baseStart_250508 := by decide
  rcases family_descends (prefixWord ++ tailWord_250508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250514 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_250514 : Nat := 118140960795 + 250514 * 2 ^ 59
def prefixEnd_250514 : Nat := 4983230072969 + 3 ^ 40 * 250514 * 2
def baseEnd_250514 : Nat := 114341415716033863575923

theorem tailTrace_250514 : CollatzResearch.WordTrace tailWord_250514 prefixEnd_250514 114341415716033863575923 := by
  unfold tailWord_250514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284249053609509307517649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6091330809625358153380397 2284249053609509307517649)
  ·
    refine ⟨1713186790207131980638237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2284249053609509307517649 1713186790207131980638237)
    ·
      refine ⟨642445046327674492739339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1713186790207131980638237 642445046327674492739339)
      ·
        refine ⟨963667569491511739109009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642445046327674492739339 963667569491511739109009)
        ·
          refine ⟨722750677118633804331757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963667569491511739109009 722750677118633804331757)
          ·
            refine ⟨271031503919487676624409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722750677118633804331757 271031503919487676624409)
            ·
              refine ⟨203273627939615757468307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271031503919487676624409 203273627939615757468307)
              ·
                refine ⟨304910441909423636202461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203273627939615757468307 304910441909423636202461)
                ·
                  refine ⟨114341415716033863575923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304910441909423636202461 114341415716033863575923)
                  ·
                    rfl

theorem cell20_250514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_250514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250514 prefixEnd_250514 := by exact prefixLift 250514
  have htrace : WordTrace (prefixWord ++ tailWord_250514) baseStart_250514 baseEnd_250514 := by
    simpa [prefixWord, tailWord_250514, baseEnd_250514] using wordTrace_append hprefix tailTrace_250514
  have hstable : (prefixWord ++ tailWord_250514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250514).length < 2 ^ (prefixWord ++ tailWord_250514).sum := by decide
  have hdescent : baseEnd_250514 < baseStart_250514 := by decide
  rcases family_descends (prefixWord ++ tailWord_250514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250556 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_250556 : Nat := 118140960795 + 250556 * 2 ^ 59
def prefixEnd_250556 : Nat := 4983230072969 + 3 ^ 40 * 250556 * 2
def baseEnd_250556 : Nat := 114360585660468384175751

theorem tailTrace_250556 : CollatzResearch.WordTrace tailWord_250556 prefixEnd_250556 114360585660468384175751 := by
  unfold tailWord_250556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569264040142939201549761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6092352053523918935399681 4569264040142939201549761)
  ·
    refine ⟨3426948030107204401162321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4569264040142939201549761 3426948030107204401162321)
    ·
      refine ⟨2570211022580403300871741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3426948030107204401162321 2570211022580403300871741)
      ·
        refine ⟨963829133467651237826903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2570211022580403300871741 963829133467651237826903)
        ·
          refine ⟨1445743700201476856740355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963829133467651237826903 1445743700201476856740355)
          ·
            refine ⟨2168615550302215285110533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445743700201476856740355 2168615550302215285110533)
            ·
              refine ⟨406615415681665365958225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2168615550302215285110533 406615415681665365958225)
              ·
                refine ⟨304961561761249024468669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406615415681665365958225 304961561761249024468669)
                ·
                  refine ⟨114360585660468384175751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304961561761249024468669 114360585660468384175751)
                  ·
                    rfl

theorem cell20_250556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_250556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250556 prefixEnd_250556 := by exact prefixLift 250556
  have htrace : WordTrace (prefixWord ++ tailWord_250556) baseStart_250556 baseEnd_250556 := by
    simpa [prefixWord, tailWord_250556, baseEnd_250556] using wordTrace_append hprefix tailTrace_250556
  have hstable : (prefixWord ++ tailWord_250556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250556).length < 2 ^ (prefixWord ++ tailWord_250556).sum := by decide
  have hdescent : baseEnd_250556 < baseStart_250556 := by decide
  rcases family_descends (prefixWord ++ tailWord_250556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250559 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 2]
def baseStart_250559 : Nat := 118140960795 + 250559 * 2 ^ 59
def prefixEnd_250559 : Nat := 4983230072969 + 3 ^ 40 * 250559 * 2
def baseEnd_250559 : Nat := 114361954942213707075739

theorem tailTrace_250559 : CollatzResearch.WordTrace tailWord_250559 prefixEnd_250559 114361954942213707075739 := by
  unfold tailWord_250559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138637499275009915458731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6092424999516673276972487 9138637499275009915458731)
  ·
    refine ⟨13707956248912514873188097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138637499275009915458731 13707956248912514873188097)
    ·
      refine ⟨10280967186684386154891073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13707956248912514873188097 10280967186684386154891073)
      ·
        refine ⟨7710725390013289616168305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10280967186684386154891073 7710725390013289616168305)
        ·
          refine ⟨5783044042509967212126229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710725390013289616168305 5783044042509967212126229)
          ·
            refine ⟨271080189492654713068417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5783044042509967212126229 271080189492654713068417)
            ·
              refine ⟨203310142119491034801313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271080189492654713068417 203310142119491034801313)
              ·
                refine ⟨152482606589618276100985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203310142119491034801313 152482606589618276100985)
                ·
                  refine ⟨114361954942213707075739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152482606589618276100985 114361954942213707075739)
                  ·
                    rfl

theorem cell20_250559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2].length) (baseStart_250559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250559 prefixEnd_250559 := by exact prefixLift 250559
  have htrace : WordTrace (prefixWord ++ tailWord_250559) baseStart_250559 baseEnd_250559 := by
    simpa [prefixWord, tailWord_250559, baseEnd_250559] using wordTrace_append hprefix tailTrace_250559
  have hstable : (prefixWord ++ tailWord_250559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250559).length < 2 ^ (prefixWord ++ tailWord_250559).sum := by decide
  have hdescent : baseEnd_250559 < baseStart_250559 := by decide
  rcases family_descends (prefixWord ++ tailWord_250559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250570 : List Nat := [3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_250570 : Nat := 118140960795 + 250570 * 2 ^ 59
def prefixEnd_250570 : Nat := 4983230072969 + 3 ^ 40 * 250570 * 2
def baseEnd_250570 : Nat := 38122325213982185903009

theorem tailTrace_250570 : CollatzResearch.WordTrace tailWord_250570 prefixEnd_250570 38122325213982185903009 := by
  unfold tailWord_250570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284759675558789698527291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6092692468156772529406109 2284759675558789698527291)
  ·
    refine ⟨3427139513338184547790937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284759675558789698527291 3427139513338184547790937)
    ·
      refine ⟨2570354635003638410843203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3427139513338184547790937 2570354635003638410843203)
      ·
        refine ⟨3855531952505457616264805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570354635003638410843203 3855531952505457616264805)
        ·
          refine ⟨722912241094773303049651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3855531952505457616264805 722912241094773303049651)
          ·
            refine ⟨1084368361642159954574477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722912241094773303049651 1084368361642159954574477)
            ·
              refine ⟨406638135615809982965429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084368361642159954574477 406638135615809982965429)
              ·
                refine ⟨38122325213982185903009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406638135615809982965429 38122325213982185903009)
                ·
                  rfl

theorem cell20_250570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_250570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250570 prefixEnd_250570 := by exact prefixLift 250570
  have htrace : WordTrace (prefixWord ++ tailWord_250570) baseStart_250570 baseEnd_250570 := by
    simpa [prefixWord, tailWord_250570, baseEnd_250570] using wordTrace_append hprefix tailTrace_250570
  have hstable : (prefixWord ++ tailWord_250570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250570).length < 2 ^ (prefixWord ++ tailWord_250570).sum := by decide
  have hdescent : baseEnd_250570 < baseStart_250570 := by decide
  rcases family_descends (prefixWord ++ tailWord_250570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250577 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_250577 : Nat := 118140960795 + 250577 * 2 ^ 59
def prefixEnd_250577 : Nat := 4983230072969 + 3 ^ 40 * 250577 * 2
def baseEnd_250577 : Nat := 114370170632685644475665

theorem tailTrace_250577 : CollatzResearch.WordTrace tailWord_250577 prefixEnd_250577 114370170632685644475665 := by
  unfold tailWord_250577
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139294013209798989613985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6092862675473199326409323 9139294013209798989613985)
  ·
    refine ⟨6854470509907349242210489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9139294013209798989613985 6854470509907349242210489)
    ·
      refine ⟨5140852882430511931657867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6854470509907349242210489 5140852882430511931657867)
      ·
        refine ⟨7711279323645767897486801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140852882430511931657867 7711279323645767897486801)
        ·
          refine ⟨5783459492734325923115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711279323645767897486801 5783459492734325923115101)
          ·
            refine ⟨2168797309775372221168163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5783459492734325923115101 2168797309775372221168163)
            ·
              refine ⟨3253195964663058331752245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168797309775372221168163 3253195964663058331752245)
              ·
                refine ⟨304987121687161718601773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3253195964663058331752245 304987121687161718601773)
                ·
                  refine ⟨114370170632685644475665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304987121687161718601773 114370170632685644475665)
                  ·
                    rfl

theorem cell20_250577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_250577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250577 prefixEnd_250577 := by exact prefixLift 250577
  have htrace : WordTrace (prefixWord ++ tailWord_250577) baseStart_250577 baseEnd_250577 := by
    simpa [prefixWord, tailWord_250577, baseEnd_250577] using wordTrace_append hprefix tailTrace_250577
  have hstable : (prefixWord ++ tailWord_250577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250577).length < 2 ^ (prefixWord ++ tailWord_250577).sum := by decide
  have hdescent : baseEnd_250577 < baseStart_250577 := by decide
  rcases family_descends (prefixWord ++ tailWord_250577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250580 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_250580 : Nat := 118140960795 + 250580 * 2 ^ 59
def prefixEnd_250580 : Nat := 4983230072969 + 3 ^ 40 * 250580 * 2
def baseEnd_250580 : Nat := 114371539914430967375653

theorem tailTrace_250580 : CollatzResearch.WordTrace tailWord_250580 prefixEnd_250580 114371539914430967375653 := by
  unfold tailWord_250580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569701716099465250986597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6092935621465953667982129 4569701716099465250986597)
  ·
    refine ⟨856819071768649734559987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4569701716099465250986597 856819071768649734559987)
    ·
      refine ⟨1285228607652974601839981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856819071768649734559987 1285228607652974601839981)
      ·
        refine ⟨481960727869865475689993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1285228607652974601839981 481960727869865475689993)
        ·
          refine ⟨361470545902399106767495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481960727869865475689993 361470545902399106767495)
          ·
            refine ⟨542205818853598660151243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361470545902399106767495 542205818853598660151243)
            ·
              refine ⟨813308728280397990226865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542205818853598660151243 813308728280397990226865)
              ·
                refine ⟨609981546210298492670149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813308728280397990226865 609981546210298492670149)
                ·
                  refine ⟨114371539914430967375653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609981546210298492670149 114371539914430967375653)
                  ·
                    rfl

theorem cell20_250580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_250580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250580 prefixEnd_250580 := by exact prefixLift 250580
  have htrace : WordTrace (prefixWord ++ tailWord_250580) baseStart_250580 baseEnd_250580 := by
    simpa [prefixWord, tailWord_250580, baseEnd_250580] using wordTrace_append hprefix tailTrace_250580
  have hstable : (prefixWord ++ tailWord_250580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250580).length < 2 ^ (prefixWord ++ tailWord_250580).sum := by decide
  have hdescent : baseEnd_250580 < baseStart_250580 := by decide
  rcases family_descends (prefixWord ++ tailWord_250580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250584 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_250584 : Nat := 118140960795 + 250584 * 2 ^ 59
def prefixEnd_250584 : Nat := 4983230072969 + 3 ^ 40 * 250584 * 2
def baseEnd_250584 : Nat := 114373365623424731242303

theorem tailTrace_250584 : CollatzResearch.WordTrace tailWord_250584 prefixEnd_250584 114373365623424731242303 := by
  unfold tailWord_250584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569774662092219592559403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6093032882789626123412537 4569774662092219592559403)
  ·
    refine ⟨6854661993138329388839105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4569774662092219592559403 6854661993138329388839105)
    ·
      refine ⟨5140996494853747041629329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6854661993138329388839105 5140996494853747041629329)
      ·
        refine ⟨3855747371140310281221997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5140996494853747041629329 3855747371140310281221997)
        ·
          refine ⟨1445905264177616355458249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3855747371140310281221997 1445905264177616355458249)
          ·
            refine ⟨1084428948133212266593687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445905264177616355458249 1084428948133212266593687)
            ·
              refine ⟨1626643422199818399890531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084428948133212266593687 1626643422199818399890531)
              ·
                refine ⟨2439965133299727599835797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626643422199818399890531 2439965133299727599835797)
                ·
                  refine ⟨114373365623424731242303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2439965133299727599835797 114373365623424731242303)
                  ·
                    rfl

theorem cell20_250584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_250584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250584 prefixEnd_250584 := by exact prefixLift 250584
  have htrace : WordTrace (prefixWord ++ tailWord_250584) baseStart_250584 baseEnd_250584 := by
    simpa [prefixWord, tailWord_250584, baseEnd_250584] using wordTrace_append hprefix tailTrace_250584
  have hstable : (prefixWord ++ tailWord_250584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250584).length < 2 ^ (prefixWord ++ tailWord_250584).sum := by decide
  have hdescent : baseEnd_250584 < baseStart_250584 := by decide
  rcases family_descends (prefixWord ++ tailWord_250584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250601 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 2]
def baseStart_250601 : Nat := 118140960795 + 250601 * 2 ^ 59
def prefixEnd_250601 : Nat := 4983230072969 + 3 ^ 40 * 250601 * 2
def baseEnd_250601 : Nat := 114381124886648227675567

theorem tailTrace_250601 : CollatzResearch.WordTrace tailWord_250601 prefixEnd_250601 114381124886648227675567 := by
  unfold tailWord_250601
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140169365122851088487657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6093446243415234058991771 9140169365122851088487657)
  ·
    refine ⟨6855127023842138316365743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9140169365122851088487657 6855127023842138316365743)
    ·
      refine ⟨10282690535763207474548615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855127023842138316365743 10282690535763207474548615)
      ·
        refine ⟨15424035803644811211822923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10282690535763207474548615 15424035803644811211822923)
        ·
          refine ⟨23136053705467216817734385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15424035803644811211822923 23136053705467216817734385)
          ·
            refine ⟨17352040279100412613300789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23136053705467216817734385 17352040279100412613300789)
            ·
              refine ⟨1626753776165663682496949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17352040279100412613300789 1626753776165663682496949)
              ·
                refine ⟨152508166515530970234089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1626753776165663682496949 152508166515530970234089)
                ·
                  refine ⟨114381124886648227675567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152508166515530970234089 114381124886648227675567)
                  ·
                    rfl

theorem cell20_250601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_250601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250601 prefixEnd_250601 := by exact prefixLift 250601
  have htrace : WordTrace (prefixWord ++ tailWord_250601) baseStart_250601 baseEnd_250601 := by
    simpa [prefixWord, tailWord_250601, baseEnd_250601] using wordTrace_append hprefix tailTrace_250601
  have hstable : (prefixWord ++ tailWord_250601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250601).length < 2 ^ (prefixWord ++ tailWord_250601).sum := by decide
  have hdescent : baseEnd_250601 < baseStart_250601 := by decide
  rcases family_descends (prefixWord ++ tailWord_250601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250656 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_250656 : Nat := 118140960795 + 250656 * 2 ^ 59
def prefixEnd_250656 : Nat := 4983230072969 + 3 ^ 40 * 250656 * 2
def baseEnd_250656 : Nat := 114406228385312480842009

theorem tailTrace_250656 : CollatzResearch.WordTrace tailWord_250656 prefixEnd_250656 114406228385312480842009 := by
  unfold tailWord_250656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571087689961797740869911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6094783586615730321159881 4571087689961797740869911)
  ·
    refine ⟨6856631534942696611304867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571087689961797740869911 6856631534942696611304867)
    ·
      refine ⟨10284947302414044916957301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856631534942696611304867 10284947302414044916957301)
      ·
        refine ⟨964213809601316710964747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10284947302414044916957301 964213809601316710964747)
        ·
          refine ⟨1446320714401975066447121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964213809601316710964747 1446320714401975066447121)
          ·
            refine ⟨1084740535801481299835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446320714401975066447121 1084740535801481299835341)
            ·
              refine ⟨406777700925555487438253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084740535801481299835341 406777700925555487438253)
              ·
                refine ⟨152541637847083307789345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406777700925555487438253 152541637847083307789345)
                ·
                  refine ⟨114406228385312480842009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152541637847083307789345 114406228385312480842009)
                  ·
                    rfl

theorem cell20_250656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_250656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250656 prefixEnd_250656 := by exact prefixLift 250656
  have htrace : WordTrace (prefixWord ++ tailWord_250656) baseStart_250656 baseEnd_250656 := by
    simpa [prefixWord, tailWord_250656, baseEnd_250656] using wordTrace_append hprefix tailTrace_250656
  have hstable : (prefixWord ++ tailWord_250656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250656).length < 2 ^ (prefixWord ++ tailWord_250656).sum := by decide
  have hdescent : baseEnd_250656 < baseStart_250656 := by decide
  rcases family_descends (prefixWord ++ tailWord_250656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250669 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 2]
def baseStart_250669 : Nat := 118140960795 + 250669 * 2 ^ 59
def prefixEnd_250669 : Nat := 4983230072969 + 3 ^ 40 * 250669 * 2
def baseEnd_250669 : Nat := 114412161939542213408623

theorem tailTrace_250669 : CollatzResearch.WordTrace tailWord_250669 prefixEnd_250669 114412161939542213408623 := by
  unfold tailWord_250669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142649528876498701963061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095099685917665801308707 9142649528876498701963061)
  ·
    refine ⟨857123393332171753309037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9142649528876498701963061 857123393332171753309037)
    ·
      refine ⟨321421272499564407490889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 857123393332171753309037 321421272499564407490889)
      ·
        refine ⟨241065954374673305618167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321421272499564407490889 241065954374673305618167)
        ·
          refine ⟨361598931562009958427251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241065954374673305618167 361598931562009958427251)
          ·
            refine ⟨542398397343014937640877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361598931562009958427251 542398397343014937640877)
            ·
              refine ⟨203399399003630601615329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542398397343014937640877 203399399003630601615329)
              ·
                refine ⟨152549549252722951211497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203399399003630601615329 152549549252722951211497)
                ·
                  refine ⟨114412161939542213408623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152549549252722951211497 114412161939542213408623)
                  ·
                    rfl

theorem cell20_250669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_250669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250669 prefixEnd_250669 := by exact prefixLift 250669
  have htrace : WordTrace (prefixWord ++ tailWord_250669) baseStart_250669 baseEnd_250669 := by
    simpa [prefixWord, tailWord_250669, baseEnd_250669] using wordTrace_append hprefix tailTrace_250669
  have hstable : (prefixWord ++ tailWord_250669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250669).length < 2 ^ (prefixWord ++ tailWord_250669).sum := by decide
  have hdescent : baseEnd_250669 < baseStart_250669 := by decide
  rcases family_descends (prefixWord ++ tailWord_250669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250670 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_250670 : Nat := 118140960795 + 250670 * 2 ^ 59
def prefixEnd_250670 : Nat := 4983230072969 + 3 ^ 40 * 250670 * 2
def baseEnd_250670 : Nat := 114412618366790654375285

theorem tailTrace_250670 : CollatzResearch.WordTrace tailWord_250670 prefixEnd_250670 114412618366790654375285 := by
  unfold tailWord_250670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142835750234109484093683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6095124001248583915166309 1142835750234109484093683)
  ·
    refine ⟨1714253625351164226140525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142835750234109484093683 1714253625351164226140525)
    ·
      refine ⟨642845109506686584802697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1714253625351164226140525 642845109506686584802697)
      ·
        refine ⟨482133832130014938602023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642845109506686584802697 482133832130014938602023)
        ·
          refine ⟨723200748195022407903035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482133832130014938602023 723200748195022407903035)
          ·
            refine ⟨1084801122292533611854553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723200748195022407903035 1084801122292533611854553)
            ·
              refine ⟨813600841719400208890915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084801122292533611854553 813600841719400208890915)
              ·
                refine ⟨1220401262579100313336373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813600841719400208890915 1220401262579100313336373)
                ·
                  refine ⟨114412618366790654375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1220401262579100313336373 114412618366790654375285)
                  ·
                    rfl

theorem cell20_250670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_250670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250670 prefixEnd_250670 := by exact prefixLift 250670
  have htrace : WordTrace (prefixWord ++ tailWord_250670) baseStart_250670 baseEnd_250670 := by
    simpa [prefixWord, tailWord_250670, baseEnd_250670] using wordTrace_append hprefix tailTrace_250670
  have hstable : (prefixWord ++ tailWord_250670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250670).length < 2 ^ (prefixWord ++ tailWord_250670).sum := by decide
  have hdescent : baseEnd_250670 < baseStart_250670 := by decide
  rcases family_descends (prefixWord ++ tailWord_250670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250677 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_250677 : Nat := 118140960795 + 250677 * 2 ^ 59
def prefixEnd_250677 : Nat := 4983230072969 + 3 ^ 40 * 250677 * 2
def baseEnd_250677 : Nat := 114415813357529741141923

theorem tailTrace_250677 : CollatzResearch.WordTrace tailWord_250677 prefixEnd_250677 114415813357529741141923 := by
  unfold tailWord_250677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142941312847516068254285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095294208565010712169523 9142941312847516068254285)
  ·
    refine ⟨3428602992317818525595357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9142941312847516068254285 3428602992317818525595357)
    ·
      refine ⟨1285726122119181947098259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3428602992317818525595357 1285726122119181947098259)
      ·
        refine ⟨1928589183178772920647389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285726122119181947098259 1928589183178772920647389)
        ·
          refine ⟨723220943692039845242771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1928589183178772920647389 723220943692039845242771)
          ·
            refine ⟨1084831415538059767864157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723220943692039845242771 1084831415538059767864157)
            ·
              refine ⟨406811780826772412949059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084831415538059767864157 406811780826772412949059)
              ·
                refine ⟨610217671240158619423589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406811780826772412949059 610217671240158619423589)
                ·
                  refine ⟨114415813357529741141923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610217671240158619423589 114415813357529741141923)
                  ·
                    rfl

theorem cell20_250677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_250677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250677 prefixEnd_250677 := by exact prefixLift 250677
  have htrace : WordTrace (prefixWord ++ tailWord_250677) baseStart_250677 baseEnd_250677 := by
    simpa [prefixWord, tailWord_250677, baseEnd_250677] using wordTrace_append hprefix tailTrace_250677
  have hstable : (prefixWord ++ tailWord_250677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250677).length < 2 ^ (prefixWord ++ tailWord_250677).sum := by decide
  have hdescent : baseEnd_250677 < baseStart_250677 := by decide
  rcases family_descends (prefixWord ++ tailWord_250677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250687 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 3]
def baseStart_250687 : Nat := 118140960795 + 250687 * 2 ^ 59
def prefixEnd_250687 : Nat := 4983230072969 + 3 ^ 40 * 250687 * 2
def baseEnd_250687 : Nat := 114420377630014150808549

theorem tailTrace_250687 : CollatzResearch.WordTrace tailWord_250687 prefixEnd_250687 114420377630014150808549 := by
  unfold tailWord_250687
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143306042811287776118315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095537361874191850745543 9143306042811287776118315)
  ·
    refine ⟨13714959064216931664177473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143306042811287776118315 13714959064216931664177473)
    ·
      refine ⟨10286219298162698748133105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13714959064216931664177473 10286219298162698748133105)
      ·
        refine ⟨7714664473622024061099829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10286219298162698748133105 7714664473622024061099829)
        ·
          refine ⟨723249794402064755728109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7714664473622024061099829 723249794402064755728109)
          ·
            refine ⟨271218672900774283398041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 723249794402064755728109 271218672900774283398041)
            ·
              refine ⟨203414004675580712548531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271218672900774283398041 203414004675580712548531)
              ·
                refine ⟨305121007013371068822797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203414004675580712548531 305121007013371068822797)
                ·
                  refine ⟨114420377630014150808549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305121007013371068822797 114420377630014150808549)
                  ·
                    rfl

theorem cell20_250687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_250687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250687 prefixEnd_250687 := by exact prefixLift 250687
  have htrace : WordTrace (prefixWord ++ tailWord_250687) baseStart_250687 baseEnd_250687 := by
    simpa [prefixWord, tailWord_250687, baseEnd_250687] using wordTrace_append hprefix tailTrace_250687
  have hstable : (prefixWord ++ tailWord_250687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250687).length < 2 ^ (prefixWord ++ tailWord_250687).sum := by decide
  have hdescent : baseEnd_250687 < baseStart_250687 := by decide
  rcases family_descends (prefixWord ++ tailWord_250687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250691 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_250691 : Nat := 118140960795 + 250691 * 2 ^ 59
def prefixEnd_250691 : Nat := 4983230072969 + 3 ^ 40 * 250691 * 2
def baseEnd_250691 : Nat := 114422203339007914675199

theorem tailTrace_250691 : CollatzResearch.WordTrace tailWord_250691 prefixEnd_250691 114422203339007914675199 := by
  unfold tailWord_250691
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143451934796796459263927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095634623197864306175951 9143451934796796459263927)
  ·
    refine ⟨13715177902195194688895891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143451934796796459263927 13715177902195194688895891)
    ·
      refine ⟨20572766853292792033343837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13715177902195194688895891 20572766853292792033343837)
      ·
        refine ⟨7714787569984797012503939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20572766853292792033343837 7714787569984797012503939)
        ·
          refine ⟨11572181354977195518755909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714787569984797012503939 11572181354977195518755909)
          ·
            refine ⟨2169784004058224159766733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11572181354977195518755909 2169784004058224159766733)
            ·
              refine ⟨813669001521834059912525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2169784004058224159766733 813669001521834059912525)
              ·
                refine ⟨305125875570687772467197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813669001521834059912525 305125875570687772467197)
                ·
                  refine ⟨114422203339007914675199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305125875570687772467197 114422203339007914675199)
                  ·
                    rfl

theorem cell20_250691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_250691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250691 prefixEnd_250691 := by exact prefixLift 250691
  have htrace : WordTrace (prefixWord ++ tailWord_250691) baseStart_250691 baseEnd_250691 := by
    simpa [prefixWord, tailWord_250691, baseEnd_250691] using wordTrace_append hprefix tailTrace_250691
  have hstable : (prefixWord ++ tailWord_250691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250691).length < 2 ^ (prefixWord ++ tailWord_250691).sum := by decide
  have hdescent : baseEnd_250691 < baseStart_250691 := by decide
  rcases family_descends (prefixWord ++ tailWord_250691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250712 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_250712 : Nat := 118140960795 + 250712 * 2 ^ 59
def prefixEnd_250712 : Nat := 4983230072969 + 3 ^ 40 * 250712 * 2
def baseEnd_250712 : Nat := 114431788311225174975113

theorem tailTrace_250712 : CollatzResearch.WordTrace tailWord_250712 prefixEnd_250712 114431788311225174975113 := by
  unfold tailWord_250712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572108933860358522889195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6096145245147144697185593 4572108933860358522889195)
  ·
    refine ⟨6858163400790537784333793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572108933860358522889195 6858163400790537784333793)
    ·
      refine ⟨5143622550592903338250345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6858163400790537784333793 5143622550592903338250345)
      ·
        refine ⟨3857716912944677503687759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5143622550592903338250345 3857716912944677503687759)
        ·
          refine ⟨5786575369417016255531639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857716912944677503687759 5786575369417016255531639)
          ·
            refine ⟨8679863054125524383297459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786575369417016255531639 8679863054125524383297459)
            ·
              refine ⟨13019794581188286574946189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679863054125524383297459 13019794581188286574946189)
              ·
                refine ⟨4882422967945607465604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13019794581188286574946189 4882422967945607465604821)
                ·
                  refine ⟨114431788311225174975113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4882422967945607465604821 114431788311225174975113)
                  ·
                    rfl

theorem cell20_250712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_250712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250712 prefixEnd_250712 := by exact prefixLift 250712
  have htrace : WordTrace (prefixWord ++ tailWord_250712) baseStart_250712 baseEnd_250712 := by
    simpa [prefixWord, tailWord_250712, baseEnd_250712] using wordTrace_append hprefix tailTrace_250712
  have hstable : (prefixWord ++ tailWord_250712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250712).length < 2 ^ (prefixWord ++ tailWord_250712).sum := by decide
  have hdescent : baseEnd_250712 < baseStart_250712 := by decide
  rcases family_descends (prefixWord ++ tailWord_250712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250722 : List Nat := [3, 3, 2, 1, 3, 8]
def baseStart_250722 : Nat := 118140960795 + 250722 * 2 ^ 59
def prefixEnd_250722 : Nat := 4983230072969 + 3 ^ 40 * 250722 * 2
def baseEnd_250722 : Nat := 4238383429026280912657

theorem tailTrace_250722 : CollatzResearch.WordTrace tailWord_250722 prefixEnd_250722 4238383429026280912657 := by
  unfold tailWord_250722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286145649421122188410605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6096388398456325835761613 2286145649421122188410605)
  ·
    refine ⟨857304618532920820653977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2286145649421122188410605 857304618532920820653977)
    ·
      refine ⟨642978463899690615490483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 857304618532920820653977 642978463899690615490483)
      ·
        refine ⟨964467695849535923235725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642978463899690615490483 964467695849535923235725)
        ·
          refine ⟨361675385943575971213397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 964467695849535923235725 361675385943575971213397)
          ·
            refine ⟨4238383429026280912657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 361675385943575971213397 4238383429026280912657)
            ·
              rfl

theorem cell20_250722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 8].length) (baseStart_250722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250722 prefixEnd_250722 := by exact prefixLift 250722
  have htrace : WordTrace (prefixWord ++ tailWord_250722) baseStart_250722 baseEnd_250722 := by
    simpa [prefixWord, tailWord_250722, baseEnd_250722] using wordTrace_append hprefix tailTrace_250722
  have hstable : (prefixWord ++ tailWord_250722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250722).length < 2 ^ (prefixWord ++ tailWord_250722).sum := by decide
  have hdescent : baseEnd_250722 < baseStart_250722 := by decide
  rcases family_descends (prefixWord ++ tailWord_250722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250780 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_250780 : Nat := 118140960795 + 250780 * 2 ^ 59
def prefixEnd_250780 : Nat := 4983230072969 + 3 ^ 40 * 250780 * 2
def baseEnd_250780 : Nat := 114462825364119160708169

theorem tailTrace_250780 : CollatzResearch.WordTrace tailWord_250780 prefixEnd_250780 114462825364119160708169 := by
  unfold tailWord_250780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4573349015737182329626897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6097798687649576439502529 4573349015737182329626897)
  ·
    refine ⟨3430011761802886747220173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4573349015737182329626897 3430011761802886747220173)
    ·
      refine ⟨1286254410676082530207565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3430011761802886747220173 1286254410676082530207565)
      ·
        refine ⟨482345404003530948827837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1286254410676082530207565 482345404003530948827837)
        ·
          refine ⟨180879526501324105810439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482345404003530948827837 180879526501324105810439)
          ·
            refine ⟨271319289751986158715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180879526501324105810439 271319289751986158715659)
            ·
              refine ⟨406978934627979238073489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271319289751986158715659 406978934627979238073489)
              ·
                refine ⟨305234200970984428555117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406978934627979238073489 305234200970984428555117)
                ·
                  refine ⟨114462825364119160708169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305234200970984428555117 114462825364119160708169)
                  ·
                    rfl

theorem cell20_250780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_250780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250780 prefixEnd_250780 := by exact prefixLift 250780
  have htrace : WordTrace (prefixWord ++ tailWord_250780) baseStart_250780 baseEnd_250780 := by
    simpa [prefixWord, tailWord_250780, baseEnd_250780] using wordTrace_append hprefix tailTrace_250780
  have hstable : (prefixWord ++ tailWord_250780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250780).length < 2 ^ (prefixWord ++ tailWord_250780).sum := by decide
  have hdescent : baseEnd_250780 < baseStart_250780 := by decide
  rcases family_descends (prefixWord ++ tailWord_250780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250781 : List Nat := [1, 4, 2, 1, 2, 1, 9]
def baseStart_250781 : Nat := 118140960795 + 250781 * 2 ^ 59
def prefixEnd_250781 : Nat := 4983230072969 + 3 ^ 40 * 250781 * 2
def baseEnd_250781 : Nat := 12718142421263066852759

theorem tailTrace_250781 : CollatzResearch.WordTrace tailWord_250781 prefixEnd_250781 12718142421263066852759 := by
  unfold tailWord_250781
  simp only [CollatzResearch.WordTrace]
  refine ⟨9146734504470741830040197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6097823002980494553360131 9146734504470741830040197)
  ·
    refine ⟨1715012719588264093132537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9146734504470741830040197 1715012719588264093132537)
    ·
      refine ⟨1286259539691198069849403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1715012719588264093132537 1286259539691198069849403)
      ·
        refine ⟨1929389309536797104774105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286259539691198069849403 1929389309536797104774105)
        ·
          refine ⟨1447041982152597828580579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929389309536797104774105 1447041982152597828580579)
          ·
            refine ⟨2170562973228896742870869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447041982152597828580579 2170562973228896742870869)
            ·
              refine ⟨12718142421263066852759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2170562973228896742870869 12718142421263066852759)
              ·
                rfl

theorem cell20_250781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_250781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250781 prefixEnd_250781 := by exact prefixLift 250781
  have htrace : WordTrace (prefixWord ++ tailWord_250781) baseStart_250781 baseEnd_250781 := by
    simpa [prefixWord, tailWord_250781, baseEnd_250781] using wordTrace_append hprefix tailTrace_250781
  have hstable : (prefixWord ++ tailWord_250781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250781).length < 2 ^ (prefixWord ++ tailWord_250781).sum := by decide
  have hdescent : baseEnd_250781 < baseStart_250781 := by decide
  rcases family_descends (prefixWord ++ tailWord_250781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250795 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_250795 : Nat := 118140960795 + 250795 * 2 ^ 59
def prefixEnd_250795 : Nat := 4983230072969 + 3 ^ 40 * 250795 * 2
def baseEnd_250795 : Nat := 114469671772845775208107

theorem tailTrace_250795 : CollatzResearch.WordTrace tailWord_250795 prefixEnd_250795 114469671772845775208107 := by
  unfold tailWord_250795
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147245126420022221049839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6098163417613348147366559 9147245126420022221049839)
  ·
    refine ⟨13720867689630033331574759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9147245126420022221049839 13720867689630033331574759)
    ·
      refine ⟨20581301534445049997362139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13720867689630033331574759 20581301534445049997362139)
      ·
        refine ⟨30871952301667574996043209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20581301534445049997362139 30871952301667574996043209)
        ·
          refine ⟨23153964226250681247032407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30871952301667574996043209 23153964226250681247032407)
          ·
            refine ⟨34730946339376021870548611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153964226250681247032407 34730946339376021870548611)
            ·
              refine ⟨52096419509064032805822917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34730946339376021870548611 52096419509064032805822917)
              ·
                refine ⟨9768078657949506151091797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52096419509064032805822917 9768078657949506151091797)
                ·
                  refine ⟨114469671772845775208107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9768078657949506151091797 114469671772845775208107)
                  ·
                    rfl

theorem cell20_250795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_250795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250795 prefixEnd_250795 := by exact prefixLift 250795
  have htrace : WordTrace (prefixWord ++ tailWord_250795) baseStart_250795 baseEnd_250795 := by
    simpa [prefixWord, tailWord_250795, baseEnd_250795] using wordTrace_append hprefix tailTrace_250795
  have hstable : (prefixWord ++ tailWord_250795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250795).length < 2 ^ (prefixWord ++ tailWord_250795).sum := by decide
  have hdescent : baseEnd_250795 < baseStart_250795 := by decide
  rcases family_descends (prefixWord ++ tailWord_250795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250801 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 3]
def baseStart_250801 : Nat := 118140960795 + 250801 * 2 ^ 59
def prefixEnd_250801 : Nat := 4983230072969 + 3 ^ 40 * 250801 * 2
def baseEnd_250801 : Nat := 114472410336336421008083

theorem tailTrace_250801 : CollatzResearch.WordTrace tailWord_250801 prefixEnd_250801 114472410336336421008083 := by
  unfold tailWord_250801
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147463964398285245768257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6098309309598856830512171 9147463964398285245768257)
  ·
    refine ⟨6860597973298713934326193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9147463964398285245768257 6860597973298713934326193)
    ·
      refine ⟨5145448479974035450744645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6860597973298713934326193 5145448479974035450744645)
      ·
        refine ⟨964771589995131647014621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5145448479974035450744645 964771589995131647014621)
        ·
          refine ⟨361789346248174367630483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 964771589995131647014621 361789346248174367630483)
          ·
            refine ⟨542684019372261551445725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361789346248174367630483 542684019372261551445725)
            ·
              refine ⟨203506507264598081792147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542684019372261551445725 203506507264598081792147)
              ·
                refine ⟨305259760896897122688221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203506507264598081792147 305259760896897122688221)
                ·
                  refine ⟨114472410336336421008083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305259760896897122688221 114472410336336421008083)
                  ·
                    rfl

theorem cell20_250801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_250801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250801 prefixEnd_250801 := by exact prefixLift 250801
  have htrace : WordTrace (prefixWord ++ tailWord_250801) baseStart_250801 baseEnd_250801 := by
    simpa [prefixWord, tailWord_250801, baseEnd_250801] using wordTrace_append hprefix tailTrace_250801
  have hstable : (prefixWord ++ tailWord_250801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250801).length < 2 ^ (prefixWord ++ tailWord_250801).sum := by decide
  have hdescent : baseEnd_250801 < baseStart_250801 := by decide
  rcases family_descends (prefixWord ++ tailWord_250801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250836 : List Nat := [2, 4, 1, 2, 1, 4, 6]
def baseStart_250836 : Nat := 118140960795 + 250836 * 2 ^ 59
def prefixEnd_250836 : Nat := 4983230072969 + 3 ^ 40 * 250836 * 2
def baseEnd_250836 : Nat := 12720931698892428315697

theorem tailTrace_250836 : CollatzResearch.WordTrace tailWord_250836 prefixEnd_250836 12720931698892428315697 := by
  unfold tailWord_250836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574370259635743111646181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6099160346180990815528241 4574370259635743111646181)
  ·
    refine ⟨857694423681701833433659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4574370259635743111646181 857694423681701833433659)
    ·
      refine ⟨1286541635522552750150489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857694423681701833433659 1286541635522552750150489)
      ·
        refine ⟨964906226641914562612867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286541635522552750150489 964906226641914562612867)
        ·
          refine ⟨1447359339962871843919301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964906226641914562612867 1447359339962871843919301)
          ·
            refine ⟨271379876243038470734869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1447359339962871843919301 271379876243038470734869)
            ·
              refine ⟨12720931698892428315697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271379876243038470734869 12720931698892428315697)
              ·
                rfl

theorem cell20_250836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_250836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250836 prefixEnd_250836 := by exact prefixLift 250836
  have htrace : WordTrace (prefixWord ++ tailWord_250836) baseStart_250836 baseEnd_250836 := by
    simpa [prefixWord, tailWord_250836, baseEnd_250836] using wordTrace_append hprefix tailTrace_250836
  have hstable : (prefixWord ++ tailWord_250836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250836).length < 2 ^ (prefixWord ++ tailWord_250836).sum := by decide
  have hdescent : baseEnd_250836 < baseStart_250836 := by decide
  rcases family_descends (prefixWord ++ tailWord_250836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250853 : List Nat := [1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_250853 : Nat := 118140960795 + 250853 * 2 ^ 59
def prefixEnd_250853 : Nat := 4983230072969 + 3 ^ 40 * 250853 * 2
def baseEnd_250853 : Nat := 38165381517751783758179

theorem tailTrace_250853 : CollatzResearch.WordTrace tailWord_250853 prefixEnd_250853 38165381517751783758179 := by
  unfold tailWord_250853
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149360560209898126661213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6099573706806598751107475 9149360560209898126661213)
  ·
    refine ⟨3431010210078711797497955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9149360560209898126661213 3431010210078711797497955)
    ·
      refine ⟨5146515315118067696246933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431010210078711797497955 5146515315118067696246933)
      ·
        refine ⟨241242905396159423261575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5146515315118067696246933 241242905396159423261575)
        ·
          refine ⟨361864358094239134892363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241242905396159423261575 361864358094239134892363)
          ·
            refine ⟨542796537141358702338545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361864358094239134892363 542796537141358702338545)
            ·
              refine ⟨407097402856019026753909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542796537141358702338545 407097402856019026753909)
              ·
                refine ⟨38165381517751783758179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407097402856019026753909 38165381517751783758179)
                ·
                  rfl

theorem cell20_250853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_250853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250853 prefixEnd_250853 := by exact prefixLift 250853
  have htrace : WordTrace (prefixWord ++ tailWord_250853) baseStart_250853 baseEnd_250853 := by
    simpa [prefixWord, tailWord_250853, baseEnd_250853] using wordTrace_append hprefix tailTrace_250853
  have hstable : (prefixWord ++ tailWord_250853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250853).length < 2 ^ (prefixWord ++ tailWord_250853).sum := by decide
  have hdescent : baseEnd_250853 < baseStart_250853 := by decide
  rcases family_descends (prefixWord ++ tailWord_250853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250901 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 2]
def baseStart_250901 : Nat := 118140960795 + 250901 * 2 ^ 59
def prefixEnd_250901 : Nat := 4983230072969 + 3 ^ 40 * 250901 * 2
def baseEnd_250901 : Nat := 114518053061180517674341

theorem tailTrace_250901 : CollatzResearch.WordTrace tailWord_250901 prefixEnd_250901 114518053061180517674341 := by
  unfold tailWord_250901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151111264036002324408557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6100740842690668216272371 9151111264036002324408557)
  ·
    refine ⟨3431666724013500871653209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9151111264036002324408557 3431666724013500871653209)
    ·
      refine ⟨2573750043010125653739907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3431666724013500871653209 2573750043010125653739907)
      ·
        refine ⟨3860625064515188480609861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573750043010125653739907 3860625064515188480609861)
        ·
          refine ⟨723867199596597840114349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3860625064515188480609861 723867199596597840114349)
          ·
            refine ⟨271450199848724190042881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 723867199596597840114349 271450199848724190042881)
            ·
              refine ⟨203587649886543142532161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271450199848724190042881 203587649886543142532161)
              ·
                refine ⟨152690737414907356899121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203587649886543142532161 152690737414907356899121)
                ·
                  refine ⟨114518053061180517674341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152690737414907356899121 114518053061180517674341)
                  ·
                    rfl

theorem cell20_250901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_250901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250901 prefixEnd_250901 := by exact prefixLift 250901
  have htrace : WordTrace (prefixWord ++ tailWord_250901) baseStart_250901 baseEnd_250901 := by
    simpa [prefixWord, tailWord_250901, baseEnd_250901] using wordTrace_append hprefix tailTrace_250901
  have hstable : (prefixWord ++ tailWord_250901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250901).length < 2 ^ (prefixWord ++ tailWord_250901).sum := by decide
  have hdescent : baseEnd_250901 < baseStart_250901 := by decide
  rcases family_descends (prefixWord ++ tailWord_250901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250947 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_250947 : Nat := 118140960795 + 250947 * 2 ^ 59
def prefixEnd_250947 : Nat := 4983230072969 + 3 ^ 40 * 250947 * 2
def baseEnd_250947 : Nat := 114539048714608802140819

theorem tailTrace_250947 : CollatzResearch.WordTrace tailWord_250947 prefixEnd_250947 114539048714608802140819 := by
  unfold tailWord_250947
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152789021869352180583095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6101859347912901453722063 9152789021869352180583095)
  ·
    refine ⟨13729183532804028270874643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9152789021869352180583095 13729183532804028270874643)
    ·
      refine ⟨20593775299206042406311965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13729183532804028270874643 20593775299206042406311965)
      ·
        refine ⟨7722665737202265902366987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20593775299206042406311965 7722665737202265902366987)
        ·
          refine ⟨11583998605803398853550481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722665737202265902366987 11583998605803398853550481)
          ·
            refine ⟨8687998954352549140162861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11583998605803398853550481 8687998954352549140162861)
            ·
              refine ⟨3257999607882205927561073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8687998954352549140162861 3257999607882205927561073)
              ·
                refine ⟨2443499705911654445670805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257999607882205927561073 2443499705911654445670805)
                ·
                  refine ⟨114539048714608802140819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2443499705911654445670805 114539048714608802140819)
                  ·
                    rfl

theorem cell20_250947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_250947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250947 prefixEnd_250947 := by exact prefixLift 250947
  have htrace : WordTrace (prefixWord ++ tailWord_250947) baseStart_250947 baseEnd_250947 := by
    simpa [prefixWord, tailWord_250947, baseEnd_250947] using wordTrace_append hprefix tailTrace_250947
  have hstable : (prefixWord ++ tailWord_250947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250947).length < 2 ^ (prefixWord ++ tailWord_250947).sum := by decide
  have hdescent : baseEnd_250947 < baseStart_250947 := by decide
  rcases family_descends (prefixWord ++ tailWord_250947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250964 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_250964 : Nat := 118140960795 + 250964 * 2 ^ 59
def prefixEnd_250964 : Nat := 4983230072969 + 3 ^ 40 * 250964 * 2
def baseEnd_250964 : Nat := 114546807977832298574083

theorem tailTrace_250964 : CollatzResearch.WordTrace tailWord_250964 prefixEnd_250964 114546807977832298574083 := by
  unfold tailWord_250964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576704531403882041975973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6102272708538509389301297 4576704531403882041975973)
  ·
    refine ⟨858132099638227882870495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4576704531403882041975973 858132099638227882870495)
    ·
      refine ⟨1287198149457341824305743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858132099638227882870495 1287198149457341824305743)
      ·
        refine ⟨1930797224186012736458615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287198149457341824305743 1930797224186012736458615)
        ·
          refine ⟨2896195836279019104687923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930797224186012736458615 2896195836279019104687923)
          ·
            refine ⟨4344293754418528657031885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896195836279019104687923 4344293754418528657031885)
            ·
              refine ⟨1629110157906948246386957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4344293754418528657031885 1629110157906948246386957)
              ·
                refine ⟨610916309215105592395109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629110157906948246386957 610916309215105592395109)
                ·
                  refine ⟨114546807977832298574083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610916309215105592395109 114546807977832298574083)
                  ·
                    rfl

theorem cell20_250964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_250964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250964 prefixEnd_250964 := by exact prefixLift 250964
  have htrace : WordTrace (prefixWord ++ tailWord_250964) baseStart_250964 baseEnd_250964 := by
    simpa [prefixWord, tailWord_250964, baseEnd_250964] using wordTrace_append hprefix tailTrace_250964
  have hstable : (prefixWord ++ tailWord_250964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250964).length < 2 ^ (prefixWord ++ tailWord_250964).sum := by decide
  have hdescent : baseEnd_250964 < baseStart_250964 := by decide
  rcases family_descends (prefixWord ++ tailWord_250964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250984 : List Nat := [2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_250984 : Nat := 118140960795 + 250984 * 2 ^ 59
def prefixEnd_250984 : Nat := 4983230072969 + 3 ^ 40 * 250984 * 2
def baseEnd_250984 : Nat := 38185312174267039302445

theorem tailTrace_250984 : CollatzResearch.WordTrace tailWord_250984 prefixEnd_250984 38185312174267039302445 := by
  unfold tailWord_250984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577069261367653749840003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6102759015156871666453337 4577069261367653749840003)
  ·
    refine ⟨6865603892051480624760005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577069261367653749840003 6865603892051480624760005)
    ·
      refine ⟨1287300729759652617142501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6865603892051480624760005 1287300729759652617142501)
      ·
        refine ⟨241368886829934865714219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1287300729759652617142501 241368886829934865714219)
        ·
          refine ⟨362053330244902298571329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241368886829934865714219 362053330244902298571329)
          ·
            refine ⟨271539997683676723928497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362053330244902298571329 271539997683676723928497)
            ·
              refine ⟨203654998262757542946373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271539997683676723928497 203654998262757542946373)
              ·
                refine ⟨38185312174267039302445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203654998262757542946373 38185312174267039302445)
                ·
                  rfl

theorem cell20_250984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_250984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_250984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_250984 prefixEnd_250984 := by exact prefixLift 250984
  have htrace : WordTrace (prefixWord ++ tailWord_250984) baseStart_250984 baseEnd_250984 := by
    simpa [prefixWord, tailWord_250984, baseEnd_250984] using wordTrace_append hprefix tailTrace_250984
  have hstable : (prefixWord ++ tailWord_250984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250984).length < 2 ^ (prefixWord ++ tailWord_250984).sum := by decide
  have hdescent : baseEnd_250984 < baseStart_250984 := by decide
  rcases family_descends (prefixWord ++ tailWord_250984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251009 : List Nat := [1, 2, 4, 2, 2, 1, 8]
def baseStart_251009 : Nat := 118140960795 + 251009 * 2 ^ 59
def prefixEnd_251009 : Nat := 4983230072969 + 3 ^ 40 * 251009 * 2
def baseEnd_251009 : Nat := 12729705244890238008211

theorem tailTrace_251009 : CollatzResearch.WordTrace tailWord_251009 prefixEnd_251009 12729705244890238008211 := by
  unfold tailWord_251009
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155050347644736769340081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6103366898429824512893387 9155050347644736769340081)
  ·
    refine ⟨6866287760733552577005061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9155050347644736769340081 6866287760733552577005061)
    ·
      refine ⟨1287428955137541108188449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6866287760733552577005061 1287428955137541108188449)
      ·
        refine ⟨965571716353155831141337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1287428955137541108188449 965571716353155831141337)
        ·
          refine ⟨724178787264866873356003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965571716353155831141337 724178787264866873356003)
          ·
            refine ⟨1086268180897300310034005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724178787264866873356003 1086268180897300310034005)
            ·
              refine ⟨12729705244890238008211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1086268180897300310034005 12729705244890238008211)
              ·
                rfl

theorem cell20_251009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_251009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251009 prefixEnd_251009 := by exact prefixLift 251009
  have htrace : WordTrace (prefixWord ++ tailWord_251009) baseStart_251009 baseEnd_251009 := by
    simpa [prefixWord, tailWord_251009, baseEnd_251009] using wordTrace_append hprefix tailTrace_251009
  have hstable : (prefixWord ++ tailWord_251009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251009).length < 2 ^ (prefixWord ++ tailWord_251009).sum := by decide
  have hdescent : baseEnd_251009 < baseStart_251009 := by decide
  rcases family_descends (prefixWord ++ tailWord_251009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251026 : List Nat := [3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_251026 : Nat := 118140960795 + 251026 * 2 ^ 59
def prefixEnd_251026 : Nat := 4983230072969 + 3 ^ 40 * 251026 * 2
def baseEnd_251026 : Nat := 38191702155745212835721

theorem tailTrace_251026 : CollatzResearch.WordTrace tailWord_251026 prefixEnd_251026 38191702155745212835721 := by
  unfold tailWord_251026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288917597145787168177233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6103780259055432448472621 2288917597145787168177233)
  ·
    refine ⟨1716688197859340376132925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2288917597145787168177233 1716688197859340376132925)
    ·
      refine ⟨643758074197252641049847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1716688197859340376132925 643758074197252641049847)
      ·
        refine ⟨965637111295878961574771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643758074197252641049847 965637111295878961574771)
        ·
          refine ⟨1448455666943818442362157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965637111295878961574771 1448455666943818442362157)
          ·
            refine ⟨543170875103931915885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1448455666943818442362157 543170875103931915885809)
            ·
              refine ⟨407378156327948936914357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543170875103931915885809 407378156327948936914357)
              ·
                refine ⟨38191702155745212835721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407378156327948936914357 38191702155745212835721)
                ·
                  rfl

theorem cell20_251026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_251026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251026 prefixEnd_251026 := by exact prefixLift 251026
  have htrace : WordTrace (prefixWord ++ tailWord_251026) baseStart_251026 baseEnd_251026 := by
    simpa [prefixWord, tailWord_251026, baseEnd_251026] using wordTrace_append hprefix tailTrace_251026
  have hstable : (prefixWord ++ tailWord_251026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251026).length < 2 ^ (prefixWord ++ tailWord_251026).sum := by decide
  have hdescent : baseEnd_251026 < baseStart_251026 := by decide
  rcases family_descends (prefixWord ++ tailWord_251026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251130 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_251130 : Nat := 118140960795 + 251130 * 2 ^ 59
def prefixEnd_251130 : Nat := 4983230072969 + 3 ^ 40 * 251130 * 2
def baseEnd_251130 : Nat := 114622574901073499040071

theorem tailTrace_251130 : CollatzResearch.WordTrace tailWord_251130 prefixEnd_251130 114622574901073499040071 := by
  unfold tailWord_251130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289865895051593608623711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6106309053470916289663229 2289865895051593608623711)
  ·
    refine ⟨3434798842577390412935567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289865895051593608623711 3434798842577390412935567)
    ·
      refine ⟨5152198263866085619403351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434798842577390412935567 5152198263866085619403351)
      ·
        refine ⟨7728297395799128429105027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152198263866085619403351 7728297395799128429105027)
        ·
          refine ⟨11592446093698692643657541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728297395799128429105027 11592446093698692643657541)
          ·
            refine ⟨2173583642568504870685789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11592446093698692643657541 2173583642568504870685789)
            ·
              refine ⟨815093865963189326507171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2173583642568504870685789 815093865963189326507171)
              ·
                refine ⟨1222640798944783989760757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815093865963189326507171 1222640798944783989760757)
                ·
                  refine ⟨114622574901073499040071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222640798944783989760757 114622574901073499040071)
                  ·
                    rfl

theorem cell20_251130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_251130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251130 prefixEnd_251130 := by exact prefixLift 251130
  have htrace : WordTrace (prefixWord ++ tailWord_251130) baseStart_251130 baseEnd_251130 := by
    simpa [prefixWord, tailWord_251130, baseEnd_251130] using wordTrace_append hprefix tailTrace_251130
  have hstable : (prefixWord ++ tailWord_251130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251130).length < 2 ^ (prefixWord ++ tailWord_251130).sum := by decide
  have hdescent : baseEnd_251130 < baseStart_251130 := by decide
  rcases family_descends (prefixWord ++ tailWord_251130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251167 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 2]
def baseStart_251167 : Nat := 118140960795 + 251167 * 2 ^ 59
def prefixEnd_251167 : Nat := 4983230072969 + 3 ^ 40 * 251167 * 2
def baseEnd_251167 : Nat := 114639462709265814806587

theorem tailTrace_251167 : CollatzResearch.WordTrace tailWord_251167 prefixEnd_251167 114639462709265814806587 := by
  unfold tailWord_251167
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160813081072329753591755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6107208720714886502394503 9160813081072329753591755)
  ·
    refine ⟨13741219621608494630387633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9160813081072329753591755 13741219621608494630387633)
    ·
      refine ⟨10305914716206370972790725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13741219621608494630387633 10305914716206370972790725)
      ·
        refine ⟨1932359009288694557398261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10305914716206370972790725 1932359009288694557398261)
        ·
          refine ⟨181158657120815114756087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1932359009288694557398261 181158657120815114756087)
          ·
            refine ⟨271737985681222672134131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181158657120815114756087 271737985681222672134131)
            ·
              refine ⟨407606978521834008201197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271737985681222672134131 407606978521834008201197)
              ·
                refine ⟨152852616945687753075449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407606978521834008201197 152852616945687753075449)
                ·
                  refine ⟨114639462709265814806587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152852616945687753075449 114639462709265814806587)
                  ·
                    rfl

theorem cell20_251167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2].length) (baseStart_251167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251167 prefixEnd_251167 := by exact prefixLift 251167
  have htrace : WordTrace (prefixWord ++ tailWord_251167) baseStart_251167 baseEnd_251167 := by
    simpa [prefixWord, tailWord_251167, baseEnd_251167] using wordTrace_append hprefix tailTrace_251167
  have hstable : (prefixWord ++ tailWord_251167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251167).length < 2 ^ (prefixWord ++ tailWord_251167).sum := by decide
  have hdescent : baseEnd_251167 < baseStart_251167 := by decide
  rcases family_descends (prefixWord ++ tailWord_251167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251171 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 2]
def baseStart_251171 : Nat := 118140960795 + 251171 * 2 ^ 59
def prefixEnd_251171 : Nat := 4983230072969 + 3 ^ 40 * 251171 * 2
def baseEnd_251171 : Nat := 114641288418259578673237

theorem tailTrace_251171 : CollatzResearch.WordTrace tailWord_251171 prefixEnd_251171 114641288418259578673237 := by
  unfold tailWord_251171
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160958973057838436737367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6107305982038558957824911 9160958973057838436737367)
  ·
    refine ⟨13741438459586757655106051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9160958973057838436737367 13741438459586757655106051)
    ·
      refine ⟨20612157689380136482659077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13741438459586757655106051 20612157689380136482659077)
      ·
        refine ⟨3864779566758775590498577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20612157689380136482659077 3864779566758775590498577)
        ·
          refine ⟨2898584675069081692873933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864779566758775590498577 2898584675069081692873933)
          ·
            refine ⟨1086969253150905634827725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2898584675069081692873933 1086969253150905634827725)
            ·
              refine ⟨407613469931589613060397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1086969253150905634827725 407613469931589613060397)
              ·
                refine ⟨152855051224346104897649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407613469931589613060397 152855051224346104897649)
                ·
                  refine ⟨114641288418259578673237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152855051224346104897649 114641288418259578673237)
                  ·
                    rfl

theorem cell20_251171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2].length) (baseStart_251171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251171 prefixEnd_251171 := by exact prefixLift 251171
  have htrace : WordTrace (prefixWord ++ tailWord_251171) baseStart_251171 baseEnd_251171 := by
    simpa [prefixWord, tailWord_251171, baseEnd_251171] using wordTrace_append hprefix tailTrace_251171
  have hstable : (prefixWord ++ tailWord_251171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251171).length < 2 ^ (prefixWord ++ tailWord_251171).sum := by decide
  have hdescent : baseEnd_251171 < baseStart_251171 := by decide
  rcases family_descends (prefixWord ++ tailWord_251171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251178 : List Nat := [3, 1, 4, 2, 1, 3, 6]
def baseStart_251178 : Nat := 118140960795 + 251178 * 2 ^ 59
def prefixEnd_251178 : Nat := 4983230072969 + 3 ^ 40 * 251178 * 2
def baseEnd_251178 : Nat := 12738275934333185048875

theorem tailTrace_251178 : CollatzResearch.WordTrace tailWord_251178 prefixEnd_251178 12738275934333185048875 := by
  unfold tailWord_251178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290303571008119658060547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6107476189354985754828125 2290303571008119658060547)
  ·
    refine ⟨3435455356512179487090821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2290303571008119658060547 3435455356512179487090821)
    ·
      refine ⟨644147879346033653829529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3435455356512179487090821 644147879346033653829529)
      ·
        refine ⟨483110909509525240372147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644147879346033653829529 483110909509525240372147)
        ·
          refine ⟨724666364264287860558221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483110909509525240372147 724666364264287860558221)
          ·
            refine ⟨271749886599107947709333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724666364264287860558221 271749886599107947709333)
            ·
              refine ⟨12738275934333185048875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271749886599107947709333 12738275934333185048875)
              ·
                rfl

theorem cell20_251178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_251178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251178 prefixEnd_251178 := by exact prefixLift 251178
  have htrace : WordTrace (prefixWord ++ tailWord_251178) baseStart_251178 baseEnd_251178 := by
    simpa [prefixWord, tailWord_251178, baseEnd_251178] using wordTrace_append hprefix tailTrace_251178
  have hstable : (prefixWord ++ tailWord_251178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251178).length < 2 ^ (prefixWord ++ tailWord_251178).sum := by decide
  have hdescent : baseEnd_251178 < baseStart_251178 := by decide
  rcases family_descends (prefixWord ++ tailWord_251178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251199 : List Nat := [1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_251199 : Nat := 118140960795 + 251199 * 2 ^ 59
def prefixEnd_251199 : Nat := 4983230072969 + 3 ^ 40 * 251199 * 2
def baseEnd_251199 : Nat := 38218022793738641913263

theorem tailTrace_251199 : CollatzResearch.WordTrace tailWord_251199 prefixEnd_251199 38218022793738641913263 := by
  unfold tailWord_251199
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161980216956399218756651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6107986811304266145837767 9161980216956399218756651)
  ·
    refine ⟨13742970325434598828134977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9161980216956399218756651 13742970325434598828134977)
    ·
      refine ⟨10307227744075949121101233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13742970325434598828134977 10307227744075949121101233)
      ·
        refine ⟨7730420808056961840825925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307227744075949121101233 7730420808056961840825925)
        ·
          refine ⟨1449453901510680345154861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7730420808056961840825925 1449453901510680345154861)
          ·
            refine ⟨543545213066505129433073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1449453901510680345154861 543545213066505129433073)
            ·
              refine ⟨407658909799878847074805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543545213066505129433073 407658909799878847074805)
              ·
                refine ⟨38218022793738641913263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407658909799878847074805 38218022793738641913263)
                ·
                  rfl

theorem cell20_251199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_251199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251199 prefixEnd_251199 := by exact prefixLift 251199
  have htrace : WordTrace (prefixWord ++ tailWord_251199) baseStart_251199 baseEnd_251199 := by
    simpa [prefixWord, tailWord_251199, baseEnd_251199] using wordTrace_append hprefix tailTrace_251199
  have hstable : (prefixWord ++ tailWord_251199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251199).length < 2 ^ (prefixWord ++ tailWord_251199).sum := by decide
  have hdescent : baseEnd_251199 < baseStart_251199 := by decide
  rcases family_descends (prefixWord ++ tailWord_251199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251240 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_251240 : Nat := 118140960795 + 251240 * 2 ^ 59
def prefixEnd_251240 : Nat := 4983230072969 + 3 ^ 40 * 251240 * 2
def baseEnd_251240 : Nat := 114672781898402005372955

theorem tailTrace_251240 : CollatzResearch.WordTrace tailWord_251240 prefixEnd_251240 114672781898402005372955 := by
  unfold tailWord_251240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581737804903931610499587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6108983739871908813999449 4581737804903931610499587)
  ·
    refine ⟨6872606707355897415749381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581737804903931610499587 6872606707355897415749381)
    ·
      refine ⟨1288613757629230765453009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6872606707355897415749381 1288613757629230765453009)
      ·
        refine ⟨966460318221923074089757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1288613757629230765453009 966460318221923074089757)
        ·
          refine ⟨362422619333221152783659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966460318221923074089757 362422619333221152783659)
          ·
            refine ⟨543633928999831729175489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362422619333221152783659 543633928999831729175489)
            ·
              refine ⟨407725446749873796881617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543633928999831729175489 407725446749873796881617)
              ·
                refine ⟨305794085062405347661213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407725446749873796881617 305794085062405347661213)
                ·
                  refine ⟨114672781898402005372955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305794085062405347661213 114672781898402005372955)
                  ·
                    rfl

theorem cell20_251240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_251240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251240 prefixEnd_251240 := by exact prefixLift 251240
  have htrace : WordTrace (prefixWord ++ tailWord_251240) baseStart_251240 baseEnd_251240 := by
    simpa [prefixWord, tailWord_251240, baseEnd_251240] using wordTrace_append hprefix tailTrace_251240
  have hstable : (prefixWord ++ tailWord_251240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251240).length < 2 ^ (prefixWord ++ tailWord_251240).sum := by decide
  have hdescent : baseEnd_251240 < baseStart_251240 := by decide
  rcases family_descends (prefixWord ++ tailWord_251240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251268 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_251268 : Nat := 118140960795 + 251268 * 2 ^ 59
def prefixEnd_251268 : Nat := 4983230072969 + 3 ^ 40 * 251268 * 2
def baseEnd_251268 : Nat := 114685561861358352439507

theorem tailTrace_251268 : CollatzResearch.WordTrace tailWord_251268 prefixEnd_251268 114685561861358352439507 := by
  unfold tailWord_251268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582248426853212001509229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6109664569137616002012305 4582248426853212001509229)
  ·
    refine ⟨1718343160069954500565961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4582248426853212001509229 1718343160069954500565961)
    ·
      refine ⟨1288757370052465875424471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1718343160069954500565961 1288757370052465875424471)
      ·
        refine ⟨1933136055078698813136707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288757370052465875424471 1933136055078698813136707)
        ·
          refine ⟨2899704082618048219705061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933136055078698813136707 2899704082618048219705061)
          ·
            refine ⟨543694515490884041194699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2899704082618048219705061 543694515490884041194699)
            ·
              refine ⟨815541773236326061792049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543694515490884041194699 815541773236326061792049)
              ·
                refine ⟨611656329927244546344037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815541773236326061792049 611656329927244546344037)
                ·
                  refine ⟨114685561861358352439507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611656329927244546344037 114685561861358352439507)
                  ·
                    rfl

theorem cell20_251268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_251268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251268 prefixEnd_251268 := by exact prefixLift 251268
  have htrace : WordTrace (prefixWord ++ tailWord_251268) baseStart_251268 baseEnd_251268 := by
    simpa [prefixWord, tailWord_251268, baseEnd_251268] using wordTrace_append hprefix tailTrace_251268
  have hstable : (prefixWord ++ tailWord_251268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251268).length < 2 ^ (prefixWord ++ tailWord_251268).sum := by decide
  have hdescent : baseEnd_251268 < baseStart_251268 := by decide
  rcases family_descends (prefixWord ++ tailWord_251268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251275 : List Nat := [1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_251275 : Nat := 118140960795 + 251275 * 2 ^ 59
def prefixEnd_251275 : Nat := 4983230072969 + 3 ^ 40 * 251275 * 2
def baseEnd_251275 : Nat := 38229585617365813068715

theorem tailTrace_251275 : CollatzResearch.WordTrace tailWord_251275 prefixEnd_251275 38229585617365813068715 := by
  unfold tailWord_251275
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164752164681064198523279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6109834776454042799015519 9164752164681064198523279)
  ·
    refine ⟨13747128247021596297784919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9164752164681064198523279 13747128247021596297784919)
    ·
      refine ⟨20620692370532394446677379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13747128247021596297784919 20620692370532394446677379)
      ·
        refine ⟨30931038555798591670016069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20620692370532394446677379 30931038555798591670016069)
        ·
          refine ⟨5799569729212235938128013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30931038555798591670016069 5799569729212235938128013)
          ·
            refine ⟨2174838648454588476798005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5799569729212235938128013 2174838648454588476798005)
            ·
              refine ⟨203891123292617669699813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2174838648454588476798005 203891123292617669699813)
              ·
                refine ⟨38229585617365813068715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203891123292617669699813 38229585617365813068715)
                ·
                  rfl

theorem cell20_251275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_251275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251275 prefixEnd_251275 := by exact prefixLift 251275
  have htrace : WordTrace (prefixWord ++ tailWord_251275) baseStart_251275 baseEnd_251275 := by
    simpa [prefixWord, tailWord_251275, baseEnd_251275] using wordTrace_append hprefix tailTrace_251275
  have hstable : (prefixWord ++ tailWord_251275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251275).length < 2 ^ (prefixWord ++ tailWord_251275).sum := by decide
  have hdescent : baseEnd_251275 < baseStart_251275 := by decide
  rcases family_descends (prefixWord ++ tailWord_251275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251292 : List Nat := [2, 2, 3, 4, 1, 1, 7]
def baseStart_251292 : Nat := 118140960795 + 251292 * 2 ^ 59
def prefixEnd_251292 : Nat := 4983230072969 + 3 ^ 40 * 251292 * 2
def baseEnd_251292 : Nat := 12744057346146770626601

theorem tailTrace_251292 : CollatzResearch.WordTrace tailWord_251292 prefixEnd_251292 12744057346146770626601 := by
  unfold tailWord_251292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582686102809738050946065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6110248137079650734594753 4582686102809738050946065)
  ·
    refine ⟨3437014577107303538209549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4582686102809738050946065 3437014577107303538209549)
    ·
      refine ⟨1288880466415238826828581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3437014577107303538209549 1288880466415238826828581)
      ·
        refine ⟨241665087452857280030359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1288880466415238826828581 241665087452857280030359)
        ·
          refine ⟨362497631179285920045539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241665087452857280030359 362497631179285920045539)
          ·
            refine ⟨543746446768928880068309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362497631179285920045539 543746446768928880068309)
            ·
              refine ⟨12744057346146770626601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 543746446768928880068309 12744057346146770626601)
              ·
                rfl

theorem cell20_251292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_251292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251292 prefixEnd_251292 := by exact prefixLift 251292
  have htrace : WordTrace (prefixWord ++ tailWord_251292) baseStart_251292 baseEnd_251292 := by
    simpa [prefixWord, tailWord_251292, baseEnd_251292] using wordTrace_append hprefix tailTrace_251292
  have hstable : (prefixWord ++ tailWord_251292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251292).length < 2 ^ (prefixWord ++ tailWord_251292).sum := by decide
  have hdescent : baseEnd_251292 < baseStart_251292 := by decide
  rcases family_descends (prefixWord ++ tailWord_251292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251296 : List Nat := [2, 1, 1, 4, 1, 2, 9]
def baseStart_251296 : Nat := 118140960795 + 251296 * 2 ^ 59
def prefixEnd_251296 : Nat := 4983230072969 + 3 ^ 40 * 251296 * 2
def baseEnd_251296 : Nat := 12744260202701633278451

theorem tailTrace_251296 : CollatzResearch.WordTrace tailWord_251296 prefixEnd_251296 12744260202701633278451 := by
  unfold tailWord_251296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582759048802492392518871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6110345398403323190025161 4582759048802492392518871)
  ·
    refine ⟨6874138573203738588778307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4582759048802492392518871 6874138573203738588778307)
    ·
      refine ⟨10311207859805607883167461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874138573203738588778307 10311207859805607883167461)
      ·
        refine ⟨1933351473713551478093899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10311207859805607883167461 1933351473713551478093899)
        ·
          refine ⟨2900027210570327217140849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933351473713551478093899 2900027210570327217140849)
          ·
            refine ⟨2175020407927745412855637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2900027210570327217140849 2175020407927745412855637)
            ·
              refine ⟨12744260202701633278451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2175020407927745412855637 12744260202701633278451)
              ·
                rfl

theorem cell20_251296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_251296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251296 prefixEnd_251296 := by exact prefixLift 251296
  have htrace : WordTrace (prefixWord ++ tailWord_251296) baseStart_251296 baseEnd_251296 := by
    simpa [prefixWord, tailWord_251296, baseEnd_251296] using wordTrace_append hprefix tailTrace_251296
  have hstable : (prefixWord ++ tailWord_251296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251296).length < 2 ^ (prefixWord ++ tailWord_251296).sum := by decide
  have hdescent : baseEnd_251296 < baseStart_251296 := by decide
  rcases family_descends (prefixWord ++ tailWord_251296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251320 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_251320 : Nat := 118140960795 + 251320 * 2 ^ 59
def prefixEnd_251320 : Nat := 4983230072969 + 3 ^ 40 * 251320 * 2
def baseEnd_251320 : Nat := 114709296078277282705961

theorem tailTrace_251320 : CollatzResearch.WordTrace tailWord_251320 prefixEnd_251320 114709296078277282705961 := by
  unfold tailWord_251320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583196724759018441955707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6110928966345357922607609 4583196724759018441955707)
  ·
    refine ⟨6874795087138527662933561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583196724759018441955707 6874795087138527662933561)
    ·
      refine ⟨5156096315353895747200171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6874795087138527662933561 5156096315353895747200171)
      ·
        refine ⟨7734144473030843620800257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156096315353895747200171 7734144473030843620800257)
        ·
          refine ⟨5800608354773132715600193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7734144473030843620800257 5800608354773132715600193)
          ·
            refine ⟨4350456266079849536700145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800608354773132715600193 4350456266079849536700145)
            ·
              refine ⟨3262842199559887152525109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350456266079849536700145 3262842199559887152525109)
              ·
                refine ⟨305891456208739420549229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3262842199559887152525109 305891456208739420549229)
                ·
                  refine ⟨114709296078277282705961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305891456208739420549229 114709296078277282705961)
                  ·
                    rfl

theorem cell20_251320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_251320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251320 prefixEnd_251320 := by exact prefixLift 251320
  have htrace : WordTrace (prefixWord ++ tailWord_251320) baseStart_251320 baseEnd_251320 := by
    simpa [prefixWord, tailWord_251320, baseEnd_251320] using wordTrace_append hprefix tailTrace_251320
  have hstable : (prefixWord ++ tailWord_251320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251320).length < 2 ^ (prefixWord ++ tailWord_251320).sum := by decide
  have hdescent : baseEnd_251320 < baseStart_251320 := by decide
  rcases family_descends (prefixWord ++ tailWord_251320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251340 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_251340 : Nat := 118140960795 + 251340 * 2 ^ 59
def prefixEnd_251340 : Nat := 4983230072969 + 3 ^ 40 * 251340 * 2
def baseEnd_251340 : Nat := 114718424623246102039213

theorem tailTrace_251340 : CollatzResearch.WordTrace tailWord_251340 prefixEnd_251340 114718424623246102039213 := by
  unfold tailWord_251340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583561454722790149819737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6111415272963720199759649 4583561454722790149819737)
  ·
    refine ⟨3437671091042092612364803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4583561454722790149819737 3437671091042092612364803)
    ·
      refine ⟨5156506636563138918547205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437671091042092612364803 5156506636563138918547205)
      ·
        refine ⟨966844994355588547227601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5156506636563138918547205 966844994355588547227601)
        ·
          refine ⟨725133745766691410420701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966844994355588547227601 725133745766691410420701)
          ·
            refine ⟨271925154662509278907763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725133745766691410420701 271925154662509278907763)
            ·
              refine ⟨407887731993763918361645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271925154662509278907763 407887731993763918361645)
              ·
                refine ⟨152957899497661469385617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407887731993763918361645 152957899497661469385617)
                ·
                  refine ⟨114718424623246102039213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152957899497661469385617 114718424623246102039213)
                  ·
                    rfl

theorem cell20_251340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_251340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251340 prefixEnd_251340 := by exact prefixLift 251340
  have htrace : WordTrace (prefixWord ++ tailWord_251340) baseStart_251340 baseEnd_251340 := by
    simpa [prefixWord, tailWord_251340, baseEnd_251340] using wordTrace_append hprefix tailTrace_251340
  have hstable : (prefixWord ++ tailWord_251340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251340).length < 2 ^ (prefixWord ++ tailWord_251340).sum := by decide
  have hdescent : baseEnd_251340 < baseStart_251340 := by decide
  rcases family_descends (prefixWord ++ tailWord_251340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251375 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 3]
def baseStart_251375 : Nat := 118140960795 + 251375 * 2 ^ 59
def prefixEnd_251375 : Nat := 4983230072969 + 3 ^ 40 * 251375 * 2
def baseEnd_251375 : Nat := 114734399576941535872403

theorem tailTrace_251375 : CollatzResearch.WordTrace tailWord_251375 prefixEnd_251375 114734399576941535872403 := by
  unfold tailWord_251375
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168399464318781277163579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6112266309545854184775719 9168399464318781277163579)
  ·
    refine ⟨13752599196478171915745369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168399464318781277163579 13752599196478171915745369)
    ·
      refine ⟨10314449397358628936809027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13752599196478171915745369 10314449397358628936809027)
      ·
        refine ⟨15471674096037943405213541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10314449397358628936809027 15471674096037943405213541)
        ·
          refine ⟨2900938893007114388477539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15471674096037943405213541 2900938893007114388477539)
          ·
            refine ⟨4351408339510671582716309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900938893007114388477539 4351408339510671582716309)
            ·
              refine ⟨203972265914562730439827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4351408339510671582716309 203972265914562730439827)
              ·
                refine ⟨305958398871844095659741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203972265914562730439827 305958398871844095659741)
                ·
                  refine ⟨114734399576941535872403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305958398871844095659741 114734399576941535872403)
                  ·
                    rfl

theorem cell20_251375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_251375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251375 prefixEnd_251375 := by exact prefixLift 251375
  have htrace : WordTrace (prefixWord ++ tailWord_251375) baseStart_251375 baseEnd_251375 := by
    simpa [prefixWord, tailWord_251375, baseEnd_251375] using wordTrace_append hprefix tailTrace_251375
  have hstable : (prefixWord ++ tailWord_251375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251375).length < 2 ^ (prefixWord ++ tailWord_251375).sum := by decide
  have hdescent : baseEnd_251375 < baseStart_251375 := by decide
  rcases family_descends (prefixWord ++ tailWord_251375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251379 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_251379 : Nat := 118140960795 + 251379 * 2 ^ 59
def prefixEnd_251379 : Nat := 4983230072969 + 3 ^ 40 * 251379 * 2
def baseEnd_251379 : Nat := 114736225285935299739053

theorem tailTrace_251379 : CollatzResearch.WordTrace tailWord_251379 prefixEnd_251379 114736225285935299739053 := by
  unfold tailWord_251379
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168545356304289960309191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6112363570869526640206127 9168545356304289960309191)
  ·
    refine ⟨13752818034456434940463787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168545356304289960309191 13752818034456434940463787)
    ·
      refine ⟨20629227051684652410695681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13752818034456434940463787 20629227051684652410695681)
      ·
        refine ⟨15471920288763489308021761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20629227051684652410695681 15471920288763489308021761)
        ·
          refine ⟨11603940216572616981016321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15471920288763489308021761 11603940216572616981016321)
          ·
            refine ⟨8702955162429462735762241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11603940216572616981016321 8702955162429462735762241)
            ·
              refine ⟨6527216371822097051821681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702955162429462735762241 6527216371822097051821681)
              ·
                refine ⟨4895412278866572788866261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527216371822097051821681 4895412278866572788866261)
                ·
                  refine ⟨114736225285935299739053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4895412278866572788866261 114736225285935299739053)
                  ·
                    rfl

theorem cell20_251379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_251379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251379 prefixEnd_251379 := by exact prefixLift 251379
  have htrace : WordTrace (prefixWord ++ tailWord_251379) baseStart_251379 baseEnd_251379 := by
    simpa [prefixWord, tailWord_251379, baseEnd_251379] using wordTrace_append hprefix tailTrace_251379
  have hstable : (prefixWord ++ tailWord_251379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251379).length < 2 ^ (prefixWord ++ tailWord_251379).sum := by decide
  have hdescent : baseEnd_251379 < baseStart_251379 := by decide
  rcases family_descends (prefixWord ++ tailWord_251379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251412 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_251412 : Nat := 118140960795 + 251412 * 2 ^ 59
def prefixEnd_251412 : Nat := 4983230072969 + 3 ^ 40 * 251412 * 2
def baseEnd_251412 : Nat := 114751287385133851638919

theorem tailTrace_251412 : CollatzResearch.WordTrace tailWord_251412 prefixEnd_251412 114751287385133851638919 := by
  unfold tailWord_251412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584874482592368298130245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6113165976789824397506993 4584874482592368298130245)
  ·
    refine ⟨859663965486069055899421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4584874482592368298130245 859663965486069055899421)
    ·
      refine ⟨322373987057275895962283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 859663965486069055899421 322373987057275895962283)
      ·
        refine ⟨483560980585913843943425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322373987057275895962283 483560980585913843943425)
        ·
          refine ⟨362670735439435382957569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483560980585913843943425 362670735439435382957569)
          ·
            refine ⟨272003051579576537218177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362670735439435382957569 272003051579576537218177)
            ·
              refine ⟨204002288684682402913633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272003051579576537218177 204002288684682402913633)
              ·
                refine ⟨153001716513511802185225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204002288684682402913633 153001716513511802185225)
                ·
                  refine ⟨114751287385133851638919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153001716513511802185225 114751287385133851638919)
                  ·
                    rfl

theorem cell20_251412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_251412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251412 prefixEnd_251412 := by exact prefixLift 251412
  have htrace : WordTrace (prefixWord ++ tailWord_251412) baseStart_251412 baseEnd_251412 := by
    simpa [prefixWord, tailWord_251412, baseEnd_251412] using wordTrace_append hprefix tailTrace_251412
  have hstable : (prefixWord ++ tailWord_251412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251412).length < 2 ^ (prefixWord ++ tailWord_251412).sum := by decide
  have hdescent : baseEnd_251412 < baseStart_251412 := by decide
  rcases family_descends (prefixWord ++ tailWord_251412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251413 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_251413 : Nat := 118140960795 + 251413 * 2 ^ 59
def prefixEnd_251413 : Nat := 4983230072969 + 3 ^ 40 * 251413 * 2
def baseEnd_251413 : Nat := 114751743812382292605581

theorem tailTrace_251413 : CollatzResearch.WordTrace tailWord_251413 prefixEnd_251413 114751743812382292605581 := by
  unfold tailWord_251413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169785438181113767046893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6113190292120742511364595 9169785438181113767046893)
  ·
    refine ⟨3438669539317917662642585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9169785438181113767046893 3438669539317917662642585)
    ·
      refine ⟨2579002154488438246981939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3438669539317917662642585 2579002154488438246981939)
      ·
        refine ⟨3868503231732657370472909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579002154488438246981939 3868503231732657370472909)
        ·
          refine ⟨1450688711899746513927341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3868503231732657370472909 1450688711899746513927341)
          ·
            refine ⟨544008266962404942722753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1450688711899746513927341 544008266962404942722753)
            ·
              refine ⟨408006200221803707042065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544008266962404942722753 408006200221803707042065)
              ·
                refine ⟨306004650166352780281549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408006200221803707042065 306004650166352780281549)
                ·
                  refine ⟨114751743812382292605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306004650166352780281549 114751743812382292605581)
                  ·
                    rfl

theorem cell20_251413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_251413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251413 prefixEnd_251413 := by exact prefixLift 251413
  have htrace : WordTrace (prefixWord ++ tailWord_251413) baseStart_251413 baseEnd_251413 := by
    simpa [prefixWord, tailWord_251413, baseEnd_251413] using wordTrace_append hprefix tailTrace_251413
  have hstable : (prefixWord ++ tailWord_251413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251413).length < 2 ^ (prefixWord ++ tailWord_251413).sum := by decide
  have hdescent : baseEnd_251413 < baseStart_251413 := by decide
  rcases family_descends (prefixWord ++ tailWord_251413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251479 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_251479 : Nat := 118140960795 + 251479 * 2 ^ 59
def prefixEnd_251479 : Nat := 4983230072969 + 3 ^ 40 * 251479 * 2
def baseEnd_251479 : Nat := 114781868010779396405311

theorem tailTrace_251479 : CollatzResearch.WordTrace tailWord_251479 prefixEnd_251479 114781868010779396405311 := by
  unfold tailWord_251479
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172192655942007038949491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6114795103961338025966327 9172192655942007038949491)
  ·
    refine ⟨13758288983913010558424237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9172192655942007038949491 13758288983913010558424237)
    ·
      refine ⟨5159358368967378959409089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13758288983913010558424237 5159358368967378959409089)
      ·
        refine ⟨3869518776725534219556817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5159358368967378959409089 3869518776725534219556817)
        ·
          refine ⟨2902139082544150664667613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3869518776725534219556817 2902139082544150664667613)
          ·
            refine ⟨1088302155954056499250355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2902139082544150664667613 1088302155954056499250355)
            ·
              refine ⟨1632453233931084748875533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088302155954056499250355 1632453233931084748875533)
              ·
                refine ⟨612169962724156780828325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632453233931084748875533 612169962724156780828325)
                ·
                  refine ⟨114781868010779396405311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612169962724156780828325 114781868010779396405311)
                  ·
                    rfl

theorem cell20_251479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_251479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251479 prefixEnd_251479 := by exact prefixLift 251479
  have htrace : WordTrace (prefixWord ++ tailWord_251479) baseStart_251479 baseEnd_251479 := by
    simpa [prefixWord, tailWord_251479, baseEnd_251479] using wordTrace_append hprefix tailTrace_251479
  have hstable : (prefixWord ++ tailWord_251479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251479).length < 2 ^ (prefixWord ++ tailWord_251479).sum := by decide
  have hdescent : baseEnd_251479 < baseStart_251479 := by decide
  rcases family_descends (prefixWord ++ tailWord_251479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251489 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 3]
def baseStart_251489 : Nat := 118140960795 + 251489 * 2 ^ 59
def prefixEnd_251489 : Nat := 4983230072969 + 3 ^ 40 * 251489 * 2
def baseEnd_251489 : Nat := 114786432283263806071937

theorem tailTrace_251489 : CollatzResearch.WordTrace tailWord_251489 prefixEnd_251489 114786432283263806071937 := by
  unfold tailWord_251489
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172557385905778746813521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6115038257270519164542347 9172557385905778746813521)
  ·
    refine ⟨6879418039429334060110141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9172557385905778746813521 6879418039429334060110141)
    ·
      refine ⟨2579781764786000272541303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6879418039429334060110141 2579781764786000272541303)
      ·
        refine ⟨3869672647179000408811955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579781764786000272541303 3869672647179000408811955)
        ·
          refine ⟨5804508970768500613217933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869672647179000408811955 5804508970768500613217933)
          ·
            refine ⟨2176690864038187729956725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5804508970768500613217933 2176690864038187729956725)
            ·
              refine ⟨204064768503580099683443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2176690864038187729956725 204064768503580099683443)
              ·
                refine ⟨306097152755370149525165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204064768503580099683443 306097152755370149525165)
                ·
                  refine ⟨114786432283263806071937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306097152755370149525165 114786432283263806071937)
                  ·
                    rfl

theorem cell20_251489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_251489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251489 prefixEnd_251489 := by exact prefixLift 251489
  have htrace : WordTrace (prefixWord ++ tailWord_251489) baseStart_251489 baseEnd_251489 := by
    simpa [prefixWord, tailWord_251489, baseEnd_251489] using wordTrace_append hprefix tailTrace_251489
  have hstable : (prefixWord ++ tailWord_251489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251489).length < 2 ^ (prefixWord ++ tailWord_251489).sum := by decide
  have hdescent : baseEnd_251489 < baseStart_251489 := by decide
  rcases family_descends (prefixWord ++ tailWord_251489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251496 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_251496 : Nat := 118140960795 + 251496 * 2 ^ 59
def prefixEnd_251496 : Nat := 4983230072969 + 3 ^ 40 * 251496 * 2
def baseEnd_251496 : Nat := 114789627274002892838575

theorem tailTrace_251496 : CollatzResearch.WordTrace tailWord_251496 prefixEnd_251496 114789627274002892838575 := by
  unfold tailWord_251496
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586406348440209471159171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6115208464586945961545561 4586406348440209471159171)
  ·
    refine ⟨6879609522660314206738757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586406348440209471159171 6879609522660314206738757)
    ·
      refine ⟨1289926785498808913763517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6879609522660314206738757 1289926785498808913763517)
      ·
        refine ⟨483722544562053342661319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1289926785498808913763517 483722544562053342661319)
        ·
          refine ⟨725583816843080013991979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483722544562053342661319 725583816843080013991979)
          ·
            refine ⟨1088375725264620020987969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725583816843080013991979 1088375725264620020987969)
            ·
              refine ⟨816281793948465015740977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088375725264620020987969 816281793948465015740977)
              ·
                refine ⟨612211345461348761805733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816281793948465015740977 612211345461348761805733)
                ·
                  refine ⟨114789627274002892838575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612211345461348761805733 114789627274002892838575)
                  ·
                    rfl

theorem cell20_251496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_251496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251496 prefixEnd_251496 := by exact prefixLift 251496
  have htrace : WordTrace (prefixWord ++ tailWord_251496) baseStart_251496 baseEnd_251496 := by
    simpa [prefixWord, tailWord_251496, baseEnd_251496] using wordTrace_append hprefix tailTrace_251496
  have hstable : (prefixWord ++ tailWord_251496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251496).length < 2 ^ (prefixWord ++ tailWord_251496).sum := by decide
  have hdescent : baseEnd_251496 < baseStart_251496 := by decide
  rcases family_descends (prefixWord ++ tailWord_251496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251530 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_251530 : Nat := 118140960795 + 251530 * 2 ^ 59
def prefixEnd_251530 : Nat := 4983230072969 + 3 ^ 40 * 251530 * 2
def baseEnd_251530 : Nat := 114805145800449885705103

theorem tailTrace_251530 : CollatzResearch.WordTrace tailWord_251530 prefixEnd_251530 114805145800449885705103 := by
  unfold tailWord_251530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293513194689310687264011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6116035185838161832704029 2293513194689310687264011)
  ·
    refine ⟨3440269792033966030896017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2293513194689310687264011 3440269792033966030896017)
    ·
      refine ⟨2580202344025474523172013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3440269792033966030896017 2580202344025474523172013)
      ·
        refine ⟨967575879009552946189505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2580202344025474523172013 967575879009552946189505)
        ·
          refine ⟨725681909257164709642129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967575879009552946189505 725681909257164709642129)
          ·
            refine ⟨544261431942873532231597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725681909257164709642129 544261431942873532231597)
            ·
              refine ⟨204098036978577574586849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544261431942873532231597 204098036978577574586849)
              ·
                refine ⟨153073527733933180940137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204098036978577574586849 153073527733933180940137)
                ·
                  refine ⟨114805145800449885705103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153073527733933180940137 114805145800449885705103)
                  ·
                    rfl

theorem cell20_251530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_251530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251530 prefixEnd_251530 := by exact prefixLift 251530
  have htrace : WordTrace (prefixWord ++ tailWord_251530) baseStart_251530 baseEnd_251530 := by
    simpa [prefixWord, tailWord_251530, baseEnd_251530] using wordTrace_append hprefix tailTrace_251530
  have hstable : (prefixWord ++ tailWord_251530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251530).length < 2 ^ (prefixWord ++ tailWord_251530).sum := by decide
  have hdescent : baseEnd_251530 < baseStart_251530 := by decide
  rcases family_descends (prefixWord ++ tailWord_251530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251531 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_251531 : Nat := 118140960795 + 251531 * 2 ^ 59
def prefixEnd_251531 : Nat := 4983230072969 + 3 ^ 40 * 251531 * 2
def baseEnd_251531 : Nat := 114805602227698326671765

theorem tailTrace_251531 : CollatzResearch.WordTrace tailWord_251531 prefixEnd_251531 114805602227698326671765 := by
  unfold tailWord_251531
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174089251753619919842447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6116059501169079946561631 9174089251753619919842447)
  ·
    refine ⟨13761133877630429879763671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174089251753619919842447 13761133877630429879763671)
    ·
      refine ⟨20641700816445644819645507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13761133877630429879763671 20641700816445644819645507)
      ·
        refine ⟨30962551224668467229468261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20641700816445644819645507 30962551224668467229468261)
        ·
          refine ⟨5805478354625337605525299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30962551224668467229468261 5805478354625337605525299)
          ·
            refine ⟨8708217531938006408287949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805478354625337605525299 8708217531938006408287949)
            ·
              refine ⟨3265581574476752403107981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8708217531938006408287949 3265581574476752403107981)
              ·
                refine ⟨1224593090428782151165493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3265581574476752403107981 1224593090428782151165493)
                ·
                  refine ⟨114805602227698326671765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224593090428782151165493 114805602227698326671765)
                  ·
                    rfl

theorem cell20_251531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_251531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251531 prefixEnd_251531 := by exact prefixLift 251531
  have htrace : WordTrace (prefixWord ++ tailWord_251531) baseStart_251531 baseEnd_251531 := by
    simpa [prefixWord, tailWord_251531, baseEnd_251531] using wordTrace_append hprefix tailTrace_251531
  have hstable : (prefixWord ++ tailWord_251531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251531).length < 2 ^ (prefixWord ++ tailWord_251531).sum := by decide
  have hdescent : baseEnd_251531 < baseStart_251531 := by decide
  rcases family_descends (prefixWord ++ tailWord_251531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251534 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_251534 : Nat := 118140960795 + 251534 * 2 ^ 59
def prefixEnd_251534 : Nat := 4983230072969 + 3 ^ 40 * 251534 * 2
def baseEnd_251534 : Nat := 114806971509443649571753

theorem tailTrace_251534 : CollatzResearch.WordTrace tailWord_251534 prefixEnd_251534 114806971509443649571753 := by
  unfold tailWord_251534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146774833842843929025207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6116132447161834288134437 1146774833842843929025207)
  ·
    refine ⟨1720162250764265893537811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146774833842843929025207 1720162250764265893537811)
    ·
      refine ⟨2580243376146398840306717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720162250764265893537811 2580243376146398840306717)
      ·
        refine ⟨967591266054899565115019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2580243376146398840306717 967591266054899565115019)
        ·
          refine ⟨1451386899082349347672529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967591266054899565115019 1451386899082349347672529)
          ·
            refine ⟨1088540174311762010754397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451386899082349347672529 1088540174311762010754397)
            ·
              refine ⟨408202565366910754032899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1088540174311762010754397 408202565366910754032899)
              ·
                refine ⟨612303848050366131049349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408202565366910754032899 612303848050366131049349)
                ·
                  refine ⟨114806971509443649571753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612303848050366131049349 114806971509443649571753)
                  ·
                    rfl

theorem cell20_251534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_251534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251534 prefixEnd_251534 := by exact prefixLift 251534
  have htrace : WordTrace (prefixWord ++ tailWord_251534) baseStart_251534 baseEnd_251534 := by
    simpa [prefixWord, tailWord_251534, baseEnd_251534] using wordTrace_append hprefix tailTrace_251534
  have hstable : (prefixWord ++ tailWord_251534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251534).length < 2 ^ (prefixWord ++ tailWord_251534).sum := by decide
  have hdescent : baseEnd_251534 < baseStart_251534 := by decide
  rcases family_descends (prefixWord ++ tailWord_251534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251540 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_251540 : Nat := 118140960795 + 251540 * 2 ^ 59
def prefixEnd_251540 : Nat := 4983230072969 + 3 ^ 40 * 251540 * 2
def baseEnd_251540 : Nat := 114809710072934295371729

theorem tailTrace_251540 : CollatzResearch.WordTrace tailWord_251540 prefixEnd_251540 114809710072934295371729 := by
  unfold tailWord_251540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587208754360507228460037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6116278339147342971280049 4587208754360507228460037)
  ·
    refine ⟨860101641442595105336257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4587208754360507228460037 860101641442595105336257)
    ·
      refine ⟨645076231081946329002193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 860101641442595105336257 645076231081946329002193)
      ·
        refine ⟨483807173311459746751645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645076231081946329002193 483807173311459746751645)
        ·
          refine ⟨181427689991797405031867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483807173311459746751645 181427689991797405031867)
          ·
            refine ⟨272141534987696107547801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181427689991797405031867 272141534987696107547801)
            ·
              refine ⟨204106151240772080660851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272141534987696107547801 204106151240772080660851)
              ·
                refine ⟨306159226861158120991277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204106151240772080660851 306159226861158120991277)
                ·
                  refine ⟨114809710072934295371729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306159226861158120991277 114809710072934295371729)
                  ·
                    rfl

theorem cell20_251540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_251540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251540 prefixEnd_251540 := by exact prefixLift 251540
  have htrace : WordTrace (prefixWord ++ tailWord_251540) baseStart_251540 baseEnd_251540 := by
    simpa [prefixWord, tailWord_251540, baseEnd_251540] using wordTrace_append hprefix tailTrace_251540
  have hstable : (prefixWord ++ tailWord_251540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251540).length < 2 ^ (prefixWord ++ tailWord_251540).sum := by decide
  have hdescent : baseEnd_251540 < baseStart_251540 := by decide
  rcases family_descends (prefixWord ++ tailWord_251540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251544 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_251544 : Nat := 118140960795 + 251544 * 2 ^ 59
def prefixEnd_251544 : Nat := 4983230072969 + 3 ^ 40 * 251544 * 2
def baseEnd_251544 : Nat := 114811535781928059238379

theorem tailTrace_251544 : CollatzResearch.WordTrace tailWord_251544 prefixEnd_251544 114811535781928059238379 := by
  unfold tailWord_251544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587281700353261570032843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6116375600471015426710457 4587281700353261570032843)
  ·
    refine ⟨6880922550529892355049265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4587281700353261570032843 6880922550529892355049265)
    ·
      refine ⟨5160691912897419266286949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6880922550529892355049265 5160691912897419266286949)
      ·
        refine ⟨967629733668266112428803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5160691912897419266286949 967629733668266112428803)
        ·
          refine ⟨1451444600502399168643205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967629733668266112428803 1451444600502399168643205)
          ·
            refine ⟨272145862594199844120601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1451444600502399168643205 272145862594199844120601)
            ·
              refine ⟨204109396945649883090451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272145862594199844120601 204109396945649883090451)
              ·
                refine ⟨306164095418474824635677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204109396945649883090451 306164095418474824635677)
                ·
                  refine ⟨114811535781928059238379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306164095418474824635677 114811535781928059238379)
                  ·
                    rfl

theorem cell20_251544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_251544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251544 prefixEnd_251544 := by exact prefixLift 251544
  have htrace : WordTrace (prefixWord ++ tailWord_251544) baseStart_251544 baseEnd_251544 := by
    simpa [prefixWord, tailWord_251544, baseEnd_251544] using wordTrace_append hprefix tailTrace_251544
  have hstable : (prefixWord ++ tailWord_251544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251544).length < 2 ^ (prefixWord ++ tailWord_251544).sum := by decide
  have hdescent : baseEnd_251544 < baseStart_251544 := by decide
  rcases family_descends (prefixWord ++ tailWord_251544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251596 : List Nat := [2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_251596 : Nat := 118140960795 + 251596 * 2 ^ 59
def prefixEnd_251596 : Nat := 4983230072969 + 3 ^ 40 * 251596 * 2
def baseEnd_251596 : Nat := 38278423332948996501611

theorem tailTrace_251596 : CollatzResearch.WordTrace tailWord_251596 prefixEnd_251596 38278423332948996501611 := by
  unfold tailWord_251596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588229998259068010479321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6117639997678757347305761 4588229998259068010479321)
  ·
    refine ⟨3441172498694301007859491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4588229998259068010479321 3441172498694301007859491)
    ·
      refine ⟨5161758748041451511789237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441172498694301007859491 5161758748041451511789237)
      ·
        refine ⟨483914882628886079230241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5161758748041451511789237 483914882628886079230241)
        ·
          refine ⟨362936161971664559422681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483914882628886079230241 362936161971664559422681)
          ·
            refine ⟨272202121478748419567011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362936161971664559422681 272202121478748419567011)
            ·
              refine ⟨408303182218122629350517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272202121478748419567011 408303182218122629350517)
              ·
                refine ⟨38278423332948996501611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408303182218122629350517 38278423332948996501611)
                ·
                  rfl

theorem cell20_251596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_251596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251596 prefixEnd_251596 := by exact prefixLift 251596
  have htrace : WordTrace (prefixWord ++ tailWord_251596) baseStart_251596 baseEnd_251596 := by
    simpa [prefixWord, tailWord_251596, baseEnd_251596] using wordTrace_append hprefix tailTrace_251596
  have hstable : (prefixWord ++ tailWord_251596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251596).length < 2 ^ (prefixWord ++ tailWord_251596).sum := by decide
  have hdescent : baseEnd_251596 < baseStart_251596 := by decide
  rcases family_descends (prefixWord ++ tailWord_251596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251606 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_251606 : Nat := 118140960795 + 251606 * 2 ^ 59
def prefixEnd_251606 : Nat := 4983230072969 + 3 ^ 40 * 251606 * 2
def baseEnd_251606 : Nat := 114839834271331399171459

theorem tailTrace_251606 : CollatzResearch.WordTrace tailWord_251606 prefixEnd_251606 114839834271331399171459 := by
  unfold tailWord_251606
  simp only [CollatzResearch.WordTrace]
  refine ⟨573551545405119233051417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6117883150987938485881781 573551545405119233051417)
  ·
    refine ⟨430163659053839424788563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 573551545405119233051417 430163659053839424788563)
    ·
      refine ⟨645245488580759137182845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430163659053839424788563 645245488580759137182845)
      ·
        refine ⟨241967058217784676443567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645245488580759137182845 241967058217784676443567)
        ·
          refine ⟨362950587326677014665351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241967058217784676443567 362950587326677014665351)
          ·
            refine ⟨544425880990015521998027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362950587326677014665351 544425880990015521998027)
            ·
              refine ⟨816638821485023282997041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544425880990015521998027 816638821485023282997041)
              ·
                refine ⟨612479116113767462247781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816638821485023282997041 612479116113767462247781)
                ·
                  refine ⟨114839834271331399171459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612479116113767462247781 114839834271331399171459)
                  ·
                    rfl

theorem cell20_251606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_251606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251606 prefixEnd_251606 := by exact prefixLift 251606
  have htrace : WordTrace (prefixWord ++ tailWord_251606) baseStart_251606 baseEnd_251606 := by
    simpa [prefixWord, tailWord_251606, baseEnd_251606] using wordTrace_append hprefix tailTrace_251606
  have hstable : (prefixWord ++ tailWord_251606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251606).length < 2 ^ (prefixWord ++ tailWord_251606).sum := by decide
  have hdescent : baseEnd_251606 < baseStart_251606 := by decide
  rcases family_descends (prefixWord ++ tailWord_251606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251613 : List Nat := [1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_251613 : Nat := 118140960795 + 251613 * 2 ^ 59
def prefixEnd_251613 : Nat := 4983230072969 + 3 ^ 40 * 251613 * 2
def baseEnd_251613 : Nat := 38281009754023495312699

theorem tailTrace_251613 : CollatzResearch.WordTrace tailWord_251613 prefixEnd_251613 38281009754023495312699 := by
  unfold tailWord_251613
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177080037456547924327493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6118053358304365282884995 9177080037456547924327493)
  ·
    refine ⟨1720702507023102735811405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9177080037456547924327493 1720702507023102735811405)
    ·
      refine ⟨645263440133663525929277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1720702507023102735811405 645263440133663525929277)
      ·
        refine ⟨241973790050123822223479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645263440133663525929277 241973790050123822223479)
        ·
          refine ⟨362960685075185733335219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241973790050123822223479 362960685075185733335219)
          ·
            refine ⟨544441027612778600002829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362960685075185733335219 544441027612778600002829)
            ·
              refine ⟨204165385354791975001061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544441027612778600002829 204165385354791975001061)
              ·
                refine ⟨38281009754023495312699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204165385354791975001061 38281009754023495312699)
                ·
                  rfl

theorem cell20_251613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_251613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251613 prefixEnd_251613 := by exact prefixLift 251613
  have htrace : WordTrace (prefixWord ++ tailWord_251613) baseStart_251613 baseEnd_251613 := by
    simpa [prefixWord, tailWord_251613, baseEnd_251613] using wordTrace_append hprefix tailTrace_251613
  have hstable : (prefixWord ++ tailWord_251613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251613).length < 2 ^ (prefixWord ++ tailWord_251613).sum := by decide
  have hdescent : baseEnd_251613 < baseStart_251613 := by decide
  rcases family_descends (prefixWord ++ tailWord_251613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251662 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_251662 : Nat := 118140960795 + 251662 * 2 ^ 59
def prefixEnd_251662 : Nat := 4983230072969 + 3 ^ 40 * 251662 * 2
def baseEnd_251662 : Nat := 114865394197244093304563

theorem tailTrace_251662 : CollatzResearch.WordTrace tailWord_251662 prefixEnd_251662 114865394197244093304563 := by
  unfold tailWord_251662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147358401784878661607655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6119244809519352861907493 1147358401784878661607655)
  ·
    refine ⟨1721037602677317992411483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147358401784878661607655 1721037602677317992411483)
    ·
      refine ⟨2581556404015976988617225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721037602677317992411483 2581556404015976988617225)
      ·
        refine ⟨1936167303011982741462919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581556404015976988617225 1936167303011982741462919)
        ·
          refine ⟨2904250954517974112194379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936167303011982741462919 2904250954517974112194379)
          ·
            refine ⟨4356376431776961168291569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904250954517974112194379 4356376431776961168291569)
            ·
              refine ⟨3267282323832720876218677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356376431776961168291569 3267282323832720876218677)
              ·
                refine ⟨306307717859317582145501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3267282323832720876218677 306307717859317582145501)
                ·
                  refine ⟨114865394197244093304563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306307717859317582145501 114865394197244093304563)
                  ·
                    rfl

theorem cell20_251662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_251662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251662 prefixEnd_251662 := by exact prefixLift 251662
  have htrace : WordTrace (prefixWord ++ tailWord_251662) baseStart_251662 baseEnd_251662 := by
    simpa [prefixWord, tailWord_251662, baseEnd_251662] using wordTrace_append hprefix tailTrace_251662
  have hstable : (prefixWord ++ tailWord_251662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251662).length < 2 ^ (prefixWord ++ tailWord_251662).sum := by decide
  have hdescent : baseEnd_251662 < baseStart_251662 := by decide
  rcases family_descends (prefixWord ++ tailWord_251662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251669 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_251669 : Nat := 118140960795 + 251669 * 2 ^ 59
def prefixEnd_251669 : Nat := 4983230072969 + 3 ^ 40 * 251669 * 2
def baseEnd_251669 : Nat := 114868589187983180071201

theorem tailTrace_251669 : CollatzResearch.WordTrace tailWord_251669 prefixEnd_251669 114868589187983180071201 := by
  unfold tailWord_251669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179122525253669488366061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6119415016835779658910707 9179122525253669488366061)
  ·
    refine ⟨3442170946970126058137273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9179122525253669488366061 3442170946970126058137273)
    ·
      refine ⟨2581628210227594543602955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3442170946970126058137273 2581628210227594543602955)
      ·
        refine ⟨3872442315341391815404433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581628210227594543602955 3872442315341391815404433)
        ·
          refine ⟨2904331736506043861553325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872442315341391815404433 2904331736506043861553325)
          ·
            refine ⟨1089124401189766448082497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2904331736506043861553325 1089124401189766448082497)
            ·
              refine ⟨816843300892324836061873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089124401189766448082497 816843300892324836061873)
              ·
                refine ⟨612632475669243627046405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816843300892324836061873 612632475669243627046405)
                ·
                  refine ⟨114868589187983180071201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612632475669243627046405 114868589187983180071201)
                  ·
                    rfl

theorem cell20_251669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_251669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251669 prefixEnd_251669 := by exact prefixLift 251669
  have htrace : WordTrace (prefixWord ++ tailWord_251669) baseStart_251669 baseEnd_251669 := by
    simpa [prefixWord, tailWord_251669, baseEnd_251669] using wordTrace_append hprefix tailTrace_251669
  have hstable : (prefixWord ++ tailWord_251669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251669).length < 2 ^ (prefixWord ++ tailWord_251669).sum := by decide
  have hdescent : baseEnd_251669 < baseStart_251669 := by decide
  rcases family_descends (prefixWord ++ tailWord_251669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251676 : List Nat := [2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_251676 : Nat := 118140960795 + 251676 * 2 ^ 59
def prefixEnd_251676 : Nat := 4983230072969 + 3 ^ 40 * 251676 * 2
def baseEnd_251676 : Nat := 38290594726240755612613

theorem tailTrace_251676 : CollatzResearch.WordTrace tailWord_251676 prefixEnd_251676 38290594726240755612613 := by
  unfold tailWord_251676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589688918114154841935441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6119585224152206455913921 4589688918114154841935441)
  ·
    refine ⟨3442266688585616131451581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4589688918114154841935441 3442266688585616131451581)
    ·
      refine ⟨1290850008219606049294343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3442266688585616131451581 1290850008219606049294343)
      ·
        refine ⟨1936275012329409073941515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290850008219606049294343 1936275012329409073941515)
        ·
          refine ⟨2904412518494113610912273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936275012329409073941515 2904412518494113610912273)
          ·
            refine ⟨2178309388870585208184205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2904412518494113610912273 2178309388870585208184205)
            ·
              refine ⟨816866020826469453069077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178309388870585208184205 816866020826469453069077)
              ·
                refine ⟨38290594726240755612613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 816866020826469453069077 38290594726240755612613)
                ·
                  rfl

theorem cell20_251676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_251676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251676 prefixEnd_251676 := by exact prefixLift 251676
  have htrace : WordTrace (prefixWord ++ tailWord_251676) baseStart_251676 baseEnd_251676 := by
    simpa [prefixWord, tailWord_251676, baseEnd_251676] using wordTrace_append hprefix tailTrace_251676
  have hstable : (prefixWord ++ tailWord_251676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251676).length < 2 ^ (prefixWord ++ tailWord_251676).sum := by decide
  have hdescent : baseEnd_251676 < baseStart_251676 := by decide
  rcases family_descends (prefixWord ++ tailWord_251676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251678 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_251678 : Nat := 118140960795 + 251678 * 2 ^ 59
def prefixEnd_251678 : Nat := 4983230072969 + 3 ^ 40 * 251678 * 2
def baseEnd_251678 : Nat := 114872697033219148771165

theorem tailTrace_251678 : CollatzResearch.WordTrace tailWord_251678 prefixEnd_251678 114872697033219148771165 := by
  unfold tailWord_251678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147431347777633003180461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6119633854814042683629125 1147431347777633003180461)
  ·
    refine ⟨430286755416612376192673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1147431347777633003180461 430286755416612376192673)
    ·
      refine ⟨322715066562459282144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430286755416612376192673 322715066562459282144505)
      ·
        refine ⟨242036299921844461608379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322715066562459282144505 242036299921844461608379)
        ·
          refine ⟨363054449882766692412569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242036299921844461608379 363054449882766692412569)
          ·
            refine ⟨272290837412075019309427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363054449882766692412569 272290837412075019309427)
            ·
              refine ⟨408436256118112528964141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272290837412075019309427 408436256118112528964141)
              ·
                refine ⟨153163596044292198361553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408436256118112528964141 153163596044292198361553)
                ·
                  refine ⟨114872697033219148771165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153163596044292198361553 114872697033219148771165)
                  ·
                    rfl

theorem cell20_251678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_251678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251678 prefixEnd_251678 := by exact prefixLift 251678
  have htrace : WordTrace (prefixWord ++ tailWord_251678) baseStart_251678 baseEnd_251678 := by
    simpa [prefixWord, tailWord_251678, baseEnd_251678] using wordTrace_append hprefix tailTrace_251678
  have hstable : (prefixWord ++ tailWord_251678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251678).length < 2 ^ (prefixWord ++ tailWord_251678).sum := by decide
  have hdescent : baseEnd_251678 < baseStart_251678 := by decide
  rcases family_descends (prefixWord ++ tailWord_251678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251683 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_251683 : Nat := 118140960795 + 251683 * 2 ^ 59
def prefixEnd_251683 : Nat := 4983230072969 + 3 ^ 40 * 251683 * 2
def baseEnd_251683 : Nat := 114874979169461353604477

theorem tailTrace_251683 : CollatzResearch.WordTrace tailWord_251683 prefixEnd_251683 114874979169461353604477 := by
  unfold tailWord_251683
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179633147202949879375703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6119755431468633252917135 9179633147202949879375703)
  ·
    refine ⟨13769449720804424819063555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9179633147202949879375703 13769449720804424819063555)
    ·
      refine ⟨20654174581206637228595333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769449720804424819063555 20654174581206637228595333)
      ·
        refine ⟨3872657733976244480361625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20654174581206637228595333 3872657733976244480361625)
        ·
          refine ⟨2904493300482183360271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872657733976244480361625 2904493300482183360271219)
          ·
            refine ⟨4356739950723275040406829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904493300482183360271219 4356739950723275040406829)
            ·
              refine ⟨1633777481521228140152561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4356739950723275040406829 1633777481521228140152561)
              ·
                refine ⟨1225333111140921105114421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633777481521228140152561 1225333111140921105114421)
                ·
                  refine ⟨114874979169461353604477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1225333111140921105114421 114874979169461353604477)
                  ·
                    rfl

theorem cell20_251683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_251683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251683 prefixEnd_251683 := by exact prefixLift 251683
  have htrace : WordTrace (prefixWord ++ tailWord_251683) baseStart_251683 baseEnd_251683 := by
    simpa [prefixWord, tailWord_251683, baseEnd_251683] using wordTrace_append hprefix tailTrace_251683
  have hstable : (prefixWord ++ tailWord_251683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251683).length < 2 ^ (prefixWord ++ tailWord_251683).sum := by decide
  have hdescent : baseEnd_251683 < baseStart_251683 := by decide
  rcases family_descends (prefixWord ++ tailWord_251683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251728 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_251728 : Nat := 118140960795 + 251728 * 2 ^ 59
def prefixEnd_251728 : Nat := 4983230072969 + 3 ^ 40 * 251728 * 2
def baseEnd_251728 : Nat := 114895518395641197104293

theorem tailTrace_251728 : CollatzResearch.WordTrace tailWord_251728 prefixEnd_251728 114895518395641197104293 := by
  unfold tailWord_251728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590637216019961282381919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6120849621359948376509225 4590637216019961282381919)
  ·
    refine ⟨6885955824029941923572879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4590637216019961282381919 6885955824029941923572879)
    ·
      refine ⟨10328933736044912885359319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885955824029941923572879 10328933736044912885359319)
      ·
        refine ⟨15493400604067369328038979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328933736044912885359319 15493400604067369328038979)
        ·
          refine ⟨23240100906101053992058469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15493400604067369328038979 23240100906101053992058469)
          ·
            refine ⟨4357518919893947623510963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23240100906101053992058469 4357518919893947623510963)
            ·
              refine ⟨6536278379840921435266445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357518919893947623510963 6536278379840921435266445)
              ·
                refine ⟨2451104392440345538224917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6536278379840921435266445 2451104392440345538224917)
                ·
                  refine ⟨114895518395641197104293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2451104392440345538224917 114895518395641197104293)
                  ·
                    rfl

theorem cell20_251728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_251728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251728 prefixEnd_251728 := by exact prefixLift 251728
  have htrace : WordTrace (prefixWord ++ tailWord_251728) baseStart_251728 baseEnd_251728 := by
    simpa [prefixWord, tailWord_251728, baseEnd_251728] using wordTrace_append hprefix tailTrace_251728
  have hstable : (prefixWord ++ tailWord_251728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251728).length < 2 ^ (prefixWord ++ tailWord_251728).sum := by decide
  have hdescent : baseEnd_251728 < baseStart_251728 := by decide
  rcases family_descends (prefixWord ++ tailWord_251728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251754 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_251754 : Nat := 118140960795 + 251754 * 2 ^ 59
def prefixEnd_251754 : Nat := 4983230072969 + 3 ^ 40 * 251754 * 2
def baseEnd_251754 : Nat := 114907385504100662237521

theorem tailTrace_251754 : CollatzResearch.WordTrace tailWord_251754 prefixEnd_251754 114907385504100662237521 := by
  unfold tailWord_251754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295555682486432251302579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6121481819963819336806877 2295555682486432251302579)
  ·
    refine ⟨3443333523729648376953869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295555682486432251302579 3443333523729648376953869)
    ·
      refine ⟨1291250071398618141357701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3443333523729648376953869 1291250071398618141357701)
      ·
        refine ⟨242109388387240901504569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1291250071398618141357701 242109388387240901504569)
        ·
          refine ⟨181582041290430676128427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242109388387240901504569 181582041290430676128427)
          ·
            refine ⟨272373061935646014192641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181582041290430676128427 272373061935646014192641)
            ·
              refine ⟨204279796451734510644481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272373061935646014192641 204279796451734510644481)
              ·
                refine ⟨153209847338800882983361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204279796451734510644481 153209847338800882983361)
                ·
                  refine ⟨114907385504100662237521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153209847338800882983361 114907385504100662237521)
                  ·
                    rfl

theorem cell20_251754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_251754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251754 prefixEnd_251754 := by exact prefixLift 251754
  have htrace : WordTrace (prefixWord ++ tailWord_251754) baseStart_251754 baseEnd_251754 := by
    simpa [prefixWord, tailWord_251754, baseEnd_251754] using wordTrace_append hprefix tailTrace_251754
  have hstable : (prefixWord ++ tailWord_251754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251754).length < 2 ^ (prefixWord ++ tailWord_251754).sum := by decide
  have hdescent : baseEnd_251754 < baseStart_251754 := by decide
  rcases family_descends (prefixWord ++ tailWord_251754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251758 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_251758 : Nat := 118140960795 + 251758 * 2 ^ 59
def prefixEnd_251758 : Nat := 4983230072969 + 3 ^ 40 * 251758 * 2
def baseEnd_251758 : Nat := 114909211213094426104171

theorem tailTrace_251758 : CollatzResearch.WordTrace tailWord_251758 prefixEnd_251758 114909211213094426104171 := by
  unfold tailWord_251758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147796077741404711044491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6121579081287491792237285 1147796077741404711044491)
  ·
    refine ⟨1721694116612107066566737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147796077741404711044491 1721694116612107066566737)
    ·
      refine ⟨1291270587459080299925053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1721694116612107066566737 1291270587459080299925053)
      ·
        refine ⟨484226470297155112471895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1291270587459080299925053 484226470297155112471895)
        ·
          refine ⟨726339705445732668707843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484226470297155112471895 726339705445732668707843)
          ·
            refine ⟨1089509558168599003061765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726339705445732668707843 1089509558168599003061765)
            ·
              refine ⟨204283042156612313074081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1089509558168599003061765 204283042156612313074081)
              ·
                refine ⟨153212281617459234805561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204283042156612313074081 153212281617459234805561)
                ·
                  refine ⟨114909211213094426104171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153212281617459234805561 114909211213094426104171)
                  ·
                    rfl

theorem cell20_251758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_251758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251758 prefixEnd_251758 := by exact prefixLift 251758
  have htrace : WordTrace (prefixWord ++ tailWord_251758) baseStart_251758 baseEnd_251758 := by
    simpa [prefixWord, tailWord_251758, baseEnd_251758] using wordTrace_append hprefix tailTrace_251758
  have hstable : (prefixWord ++ tailWord_251758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251758).length < 2 ^ (prefixWord ++ tailWord_251758).sum := by decide
  have hdescent : baseEnd_251758 < baseStart_251758 := by decide
  rcases family_descends (prefixWord ++ tailWord_251758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251786 : List Nat := [3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_251786 : Nat := 118140960795 + 251786 * 2 ^ 59
def prefixEnd_251786 : Nat := 4983230072969 + 3 ^ 40 * 251786 * 2
def baseEnd_251786 : Nat := 38307330392016924390241

theorem tailTrace_251786 : CollatzResearch.WordTrace tailWord_251786 prefixEnd_251786 38307330392016924390241 := by
  unfold tailWord_251786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295847466457449617593803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6122259910553198980250141 2295847466457449617593803)
  ·
    refine ⟨3443771199686174426390705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295847466457449617593803 3443771199686174426390705)
    ·
      refine ⟨2582828399764630819793029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443771199686174426390705 2582828399764630819793029)
      ·
        refine ⟨484280324955868278711193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2582828399764630819793029 484280324955868278711193)
        ·
          refine ⟨363210243716901209033395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484280324955868278711193 363210243716901209033395)
          ·
            refine ⟨544815365575351813550093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363210243716901209033395 544815365575351813550093)
            ·
              refine ⟨204305762090756930081285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544815365575351813550093 204305762090756930081285)
              ·
                refine ⟨38307330392016924390241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204305762090756930081285 38307330392016924390241)
                ·
                  rfl

theorem cell20_251786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_251786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251786 prefixEnd_251786 := by exact prefixLift 251786
  have htrace : WordTrace (prefixWord ++ tailWord_251786) baseStart_251786 baseEnd_251786 := by
    simpa [prefixWord, tailWord_251786, baseEnd_251786] using wordTrace_append hprefix tailTrace_251786
  have hstable : (prefixWord ++ tailWord_251786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251786).length < 2 ^ (prefixWord ++ tailWord_251786).sum := by decide
  have hdescent : baseEnd_251786 < baseStart_251786 := by decide
  rcases family_descends (prefixWord ++ tailWord_251786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251797 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_251797 : Nat := 118140960795 + 251797 * 2 ^ 59
def prefixEnd_251797 : Nat := 4983230072969 + 3 ^ 40 * 251797 * 2
def baseEnd_251797 : Nat := 114927011875783623804011

theorem tailTrace_251797 : CollatzResearch.WordTrace tailWord_251797 prefixEnd_251797 114927011875783623804011 := by
  unfold tailWord_251797
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183791068789947349025645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6122527379193298232683763 9183791068789947349025645)
  ·
    refine ⟨3443921650796230255884617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9183791068789947349025645 3443921650796230255884617)
    ·
      refine ⟨2582941238097172691913463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443921650796230255884617 2582941238097172691913463)
      ·
        refine ⟨3874411857145759037870195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582941238097172691913463 3874411857145759037870195)
        ·
          refine ⟨5811617785718638556805293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874411857145759037870195 5811617785718638556805293)
          ·
            refine ⟨2179356669644489458801985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5811617785718638556805293 2179356669644489458801985)
            ·
              refine ⟨1634517502233367094101489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179356669644489458801985 1634517502233367094101489)
              ·
                refine ⟨1225888126675025320576117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634517502233367094101489 1225888126675025320576117)
                ·
                  refine ⟨114927011875783623804011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1225888126675025320576117 114927011875783623804011)
                  ·
                    rfl

theorem cell20_251797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_251797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251797 prefixEnd_251797 := by exact prefixLift 251797
  have htrace : WordTrace (prefixWord ++ tailWord_251797) baseStart_251797 baseEnd_251797 := by
    simpa [prefixWord, tailWord_251797, baseEnd_251797] using wordTrace_append hprefix tailTrace_251797
  have hstable : (prefixWord ++ tailWord_251797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251797).length < 2 ^ (prefixWord ++ tailWord_251797).sum := by decide
  have hdescent : baseEnd_251797 < baseStart_251797 := by decide
  rcases family_descends (prefixWord ++ tailWord_251797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251806 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_251806 : Nat := 118140960795 + 251806 * 2 ^ 59
def prefixEnd_251806 : Nat := 4983230072969 + 3 ^ 40 * 251806 * 2
def baseEnd_251806 : Nat := 114931119721019592503975

theorem tailTrace_251806 : CollatzResearch.WordTrace tailWord_251806 prefixEnd_251806 114931119721019592503975 := by
  unfold tailWord_251806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148014915719667735762909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6122746217171561257402181 1148014915719667735762909)
  ·
    refine ⟨430505593394875400911091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1148014915719667735762909 430505593394875400911091)
    ·
      refine ⟨645758390092313101366637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430505593394875400911091 645758390092313101366637)
      ·
        refine ⟨242159396284617413012489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645758390092313101366637 242159396284617413012489)
        ·
          refine ⟨181619547213463059759367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242159396284617413012489 181619547213463059759367)
          ·
            refine ⟨272429320820194589639051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181619547213463059759367 272429320820194589639051)
            ·
              refine ⟨408643981230291884458577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272429320820194589639051 408643981230291884458577)
              ·
                refine ⟨306482985922718913343933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408643981230291884458577 306482985922718913343933)
                ·
                  refine ⟨114931119721019592503975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306482985922718913343933 114931119721019592503975)
                  ·
                    rfl

theorem cell20_251806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_251806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251806 prefixEnd_251806 := by exact prefixLift 251806
  have htrace : WordTrace (prefixWord ++ tailWord_251806) baseStart_251806 baseEnd_251806 := by
    simpa [prefixWord, tailWord_251806, baseEnd_251806] using wordTrace_append hprefix tailTrace_251806
  have hstable : (prefixWord ++ tailWord_251806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251806).length < 2 ^ (prefixWord ++ tailWord_251806).sum := by decide
  have hdescent : baseEnd_251806 < baseStart_251806 := by decide
  rcases family_descends (prefixWord ++ tailWord_251806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251810 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_251810 : Nat := 118140960795 + 251810 * 2 ^ 59
def prefixEnd_251810 : Nat := 4983230072969 + 3 ^ 40 * 251810 * 2
def baseEnd_251810 : Nat := 114932945430013356370625

theorem tailTrace_251810 : CollatzResearch.WordTrace tailWord_251810 prefixEnd_251810 114932945430013356370625 := by
  unfold tailWord_251810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296066304435712642312221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6122843478495233712832589 2296066304435712642312221)
  ·
    refine ⟨861024864163392240867083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2296066304435712642312221 861024864163392240867083)
    ·
      refine ⟨1291537296245088361300625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861024864163392240867083 1291537296245088361300625)
      ·
        refine ⟨968652972183816270975469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1291537296245088361300625 968652972183816270975469)
        ·
          refine ⟨363244864568931101615801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968652972183816270975469 363244864568931101615801)
          ·
            refine ⟨272433648426698326211851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363244864568931101615801 272433648426698326211851)
            ·
              refine ⟨408650472640047489317777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272433648426698326211851 408650472640047489317777)
              ·
                refine ⟨306487854480035616988333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408650472640047489317777 306487854480035616988333)
                ·
                  refine ⟨114932945430013356370625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306487854480035616988333 114932945430013356370625)
                  ·
                    rfl

theorem cell20_251810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_251810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251810 prefixEnd_251810 := by exact prefixLift 251810
  have htrace : WordTrace (prefixWord ++ tailWord_251810) baseStart_251810 baseEnd_251810 := by
    simpa [prefixWord, tailWord_251810, baseEnd_251810] using wordTrace_append hprefix tailTrace_251810
  have hstable : (prefixWord ++ tailWord_251810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251810).length < 2 ^ (prefixWord ++ tailWord_251810).sum := by decide
  have hdescent : baseEnd_251810 < baseStart_251810 := by decide
  rcases family_descends (prefixWord ++ tailWord_251810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251849 : List Nat := [1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_251849 : Nat := 118140960795 + 251849 * 2 ^ 59
def prefixEnd_251849 : Nat := 4983230072969 + 3 ^ 40 * 251849 * 2
def baseEnd_251849 : Nat := 38316915364234184690155

theorem tailTrace_251849 : CollatzResearch.WordTrace tailWord_251849 prefixEnd_251849 38316915364234184690155 := by
  unfold tailWord_251849
  simp only [CollatzResearch.WordTrace]
  refine ⟨9185687664601560229918601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6123791776401040153279067 9185687664601560229918601)
  ·
    refine ⟨6889265748451170172438951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9185687664601560229918601 6889265748451170172438951)
    ·
      refine ⟨10333898622676755258658427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889265748451170172438951 10333898622676755258658427)
      ·
        refine ⟨15500847934015132887987641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10333898622676755258658427 15500847934015132887987641)
        ·
          refine ⟨11625635950511349665990731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15500847934015132887987641 11625635950511349665990731)
          ·
            refine ⟨17438453925767024498986097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11625635950511349665990731 17438453925767024498986097)
            ·
              refine ⟨13078840444325268374239573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17438453925767024498986097 13078840444325268374239573)
              ·
                refine ⟨38316915364234184690155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13078840444325268374239573 38316915364234184690155)
                ·
                  rfl

theorem cell20_251849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_251849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251849 prefixEnd_251849 := by exact prefixLift 251849
  have htrace : WordTrace (prefixWord ++ tailWord_251849) baseStart_251849 baseEnd_251849 := by
    simpa [prefixWord, tailWord_251849, baseEnd_251849] using wordTrace_append hprefix tailTrace_251849
  have hstable : (prefixWord ++ tailWord_251849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251849).length < 2 ^ (prefixWord ++ tailWord_251849).sum := by decide
  have hdescent : baseEnd_251849 < baseStart_251849 := by decide
  rcases family_descends (prefixWord ++ tailWord_251849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251862 : List Nat := [5, 2, 1, 1, 3, 2, 6]
def baseStart_251862 : Nat := 118140960795 + 251862 * 2 ^ 59
def prefixEnd_251862 : Nat := 4983230072969 + 3 ^ 40 * 251862 * 2
def baseEnd_251862 : Nat := 12772964405214698515231

theorem tailTrace_251862 : CollatzResearch.WordTrace tailWord_251862 prefixEnd_251862 12772964405214698515231 := by
  unfold tailWord_251862
  simp only [CollatzResearch.WordTrace]
  refine ⟨574135113347153965633865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6124107875702975633427893 574135113347153965633865)
  ·
    refine ⟨430601335010365474225399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 574135113347153965633865 430601335010365474225399)
    ·
      refine ⟨645902002515548211338099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430601335010365474225399 645902002515548211338099)
      ·
        refine ⟨968853003773322317007149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645902002515548211338099 968853003773322317007149)
        ·
          refine ⟨363319876414995868877681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968853003773322317007149 363319876414995868877681)
          ·
            refine ⟨272489907311246901658261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363319876414995868877681 272489907311246901658261)
            ·
              refine ⟨12772964405214698515231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272489907311246901658261 12772964405214698515231)
              ·
                rfl

theorem cell20_251862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_251862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251862 prefixEnd_251862 := by exact prefixLift 251862
  have htrace : WordTrace (prefixWord ++ tailWord_251862) baseStart_251862 baseEnd_251862 := by
    simpa [prefixWord, tailWord_251862, baseEnd_251862] using wordTrace_append hprefix tailTrace_251862
  have hstable : (prefixWord ++ tailWord_251862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251862).length < 2 ^ (prefixWord ++ tailWord_251862).sum := by decide
  have hdescent : baseEnd_251862 < baseStart_251862 := by decide
  rcases family_descends (prefixWord ++ tailWord_251862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251868 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_251868 : Nat := 118140960795 + 251868 * 2 ^ 59
def prefixEnd_251868 : Nat := 4983230072969 + 3 ^ 40 * 251868 * 2
def baseEnd_251868 : Nat := 114959418210422932437055

theorem tailTrace_251868 : CollatzResearch.WordTrace tailWord_251868 prefixEnd_251868 114959418210422932437055 := by
  unfold tailWord_251868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4593190325766363237430129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6124253767688484316573505 4593190325766363237430129)
  ·
    refine ⟨3444892744324772428072597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4593190325766363237430129 3444892744324772428072597)
    ·
      refine ⟨161479347390223707565903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3444892744324772428072597 161479347390223707565903)
      ·
        refine ⟨242219021085335561348855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161479347390223707565903 242219021085335561348855)
        ·
          refine ⟨363328531628003342023283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242219021085335561348855 363328531628003342023283)
          ·
            refine ⟨544992797442005013034925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363328531628003342023283 544992797442005013034925)
            ·
              refine ⟨204372299040751879888097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544992797442005013034925 204372299040751879888097)
              ·
                refine ⟨153279224280563909916073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204372299040751879888097 153279224280563909916073)
                ·
                  refine ⟨114959418210422932437055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153279224280563909916073 114959418210422932437055)
                  ·
                    rfl

theorem cell20_251868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_251868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251868 prefixEnd_251868 := by exact prefixLift 251868
  have htrace : WordTrace (prefixWord ++ tailWord_251868) baseStart_251868 baseEnd_251868 := by
    simpa [prefixWord, tailWord_251868, baseEnd_251868] using wordTrace_append hprefix tailTrace_251868
  have hstable : (prefixWord ++ tailWord_251868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251868).length < 2 ^ (prefixWord ++ tailWord_251868).sum := by decide
  have hdescent : baseEnd_251868 < baseStart_251868 := by decide
  rcases family_descends (prefixWord ++ tailWord_251868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251873 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_251873 : Nat := 118140960795 + 251873 * 2 ^ 59
def prefixEnd_251873 : Nat := 4983230072969 + 3 ^ 40 * 251873 * 2
def baseEnd_251873 : Nat := 114961700346665137270367

theorem tailTrace_251873 : CollatzResearch.WordTrace tailWord_251873 prefixEnd_251873 114961700346665137270367 := by
  unfold tailWord_251873
  simp only [CollatzResearch.WordTrace]
  refine ⟨9186563016514612328792273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6124375344343074885861515 9186563016514612328792273)
  ·
    refine ⟨6889922262385959246594205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9186563016514612328792273 6889922262385959246594205)
    ·
      refine ⟨2583720848394734717472827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6889922262385959246594205 2583720848394734717472827)
      ·
        refine ⟨3875581272592102076209241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583720848394734717472827 3875581272592102076209241)
        ·
          refine ⟨2906685954444076557156931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3875581272592102076209241 2906685954444076557156931)
          ·
            refine ⟨4360028931666114835735397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906685954444076557156931 4360028931666114835735397)
            ·
              refine ⟨817505424687396531700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4360028931666114835735397 817505424687396531700387)
              ·
                refine ⟨1226258137031094797550581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817505424687396531700387 1226258137031094797550581)
                ·
                  refine ⟨114961700346665137270367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226258137031094797550581 114961700346665137270367)
                  ·
                    rfl

theorem cell20_251873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_251873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251873 prefixEnd_251873 := by exact prefixLift 251873
  have htrace : WordTrace (prefixWord ++ tailWord_251873) baseStart_251873 baseEnd_251873 := by
    simpa [prefixWord, tailWord_251873, baseEnd_251873] using wordTrace_append hprefix tailTrace_251873
  have hstable : (prefixWord ++ tailWord_251873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251873).length < 2 ^ (prefixWord ++ tailWord_251873).sum := by decide
  have hdescent : baseEnd_251873 < baseStart_251873 := by decide
  rcases family_descends (prefixWord ++ tailWord_251873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251886 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_251886 : Nat := 118140960795 + 251886 * 2 ^ 59
def prefixEnd_251886 : Nat := 4983230072969 + 3 ^ 40 * 251886 * 2
def baseEnd_251886 : Nat := 114967633900894869836981

theorem tailTrace_251886 : CollatzResearch.WordTrace tailWord_251886 prefixEnd_251886 114967633900894869836981 := by
  unfold tailWord_251886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148379645683439443626939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6124691443645010366010341 1148379645683439443626939)
  ·
    refine ⟨1722569468525159165440409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1148379645683439443626939 1722569468525159165440409)
    ·
      refine ⟨1291927101393869374080307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1722569468525159165440409 1291927101393869374080307)
      ·
        refine ⟨1937890652090804061120461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291927101393869374080307 1937890652090804061120461)
        ·
          refine ⟨726708994534051522920173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1937890652090804061120461 726708994534051522920173)
          ·
            refine ⟨272515872950269321095065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726708994534051522920173 272515872950269321095065)
            ·
              refine ⟨204386904712701990821299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272515872950269321095065 204386904712701990821299)
              ·
                refine ⟨306580357069052986231949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204386904712701990821299 306580357069052986231949)
                ·
                  refine ⟨114967633900894869836981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306580357069052986231949 114967633900894869836981)
                  ·
                    rfl

theorem cell20_251886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_251886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251886 prefixEnd_251886 := by exact prefixLift 251886
  have htrace : WordTrace (prefixWord ++ tailWord_251886) baseStart_251886 baseEnd_251886 := by
    simpa [prefixWord, tailWord_251886, baseEnd_251886] using wordTrace_append hprefix tailTrace_251886
  have hstable : (prefixWord ++ tailWord_251886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251886).length < 2 ^ (prefixWord ++ tailWord_251886).sum := by decide
  have hdescent : baseEnd_251886 < baseStart_251886 := by decide
  rcases family_descends (prefixWord ++ tailWord_251886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251917 : List Nat := [1, 7, 1, 2, 2, 7]
def baseStart_251917 : Nat := 118140960795 + 251917 * 2 ^ 59
def prefixEnd_251917 : Nat := 4983230072969 + 3 ^ 40 * 251917 * 2
def baseEnd_251917 : Nat := 4258584560948019992723

theorem tailTrace_251917 : CollatzResearch.WordTrace tailWord_251917 prefixEnd_251917 4258584560948019992723 := by
  unfold tailWord_251917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188167828355207843394005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6125445218903471895596003 9188167828355207843394005)
  ·
    refine ⟨215347683477075183829547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9188167828355207843394005 215347683477075183829547)
    ·
      refine ⟨323021525215612775744321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215347683477075183829547 323021525215612775744321)
      ·
        refine ⟨242266143911709581808241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323021525215612775744321 242266143911709581808241)
        ·
          refine ⟨181699607933782186356181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242266143911709581808241 181699607933782186356181)
          ·
            refine ⟨4258584560948019992723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 181699607933782186356181 4258584560948019992723)
            ·
              rfl

theorem cell20_251917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 7].length) (baseStart_251917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251917 prefixEnd_251917 := by exact prefixLift 251917
  have htrace : WordTrace (prefixWord ++ tailWord_251917) baseStart_251917 baseEnd_251917 := by
    simpa [prefixWord, tailWord_251917, baseEnd_251917] using wordTrace_append hprefix tailTrace_251917
  have hstable : (prefixWord ++ tailWord_251917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251917).length < 2 ^ (prefixWord ++ tailWord_251917).sum := by decide
  have hdescent : baseEnd_251917 < baseStart_251917 := by decide
  rcases family_descends (prefixWord ++ tailWord_251917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251925 : List Nat := [1, 3, 2, 1, 13]
def baseStart_251925 : Nat := 118140960795 + 251925 * 2 ^ 59
def prefixEnd_251925 : Nat := 4983230072969 + 3 ^ 40 * 251925 * 2
def baseEnd_251925 : Nat := 1419573266217087253541

theorem tailTrace_251925 : CollatzResearch.WordTrace tailWord_251925 prefixEnd_251925 1419573266217087253541 := by
  unfold tailWord_251925
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188459612326225209685229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6125639741550816806456819 9188459612326225209685229)
  ·
    refine ⟨3445672354622334453631961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9188459612326225209685229 3445672354622334453631961)
    ·
      refine ⟨2584254265966750840223971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3445672354622334453631961 2584254265966750840223971)
      ·
        refine ⟨3876381398950126260335957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584254265966750840223971 3876381398950126260335957)
        ·
          refine ⟨1419573266217087253541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3876381398950126260335957 1419573266217087253541)
          ·
            rfl

theorem cell20_251925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 13].length) (baseStart_251925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251925 prefixEnd_251925 := by exact prefixLift 251925
  have htrace : WordTrace (prefixWord ++ tailWord_251925) baseStart_251925 baseEnd_251925 := by
    simpa [prefixWord, tailWord_251925, baseEnd_251925] using wordTrace_append hprefix tailTrace_251925
  have hstable : (prefixWord ++ tailWord_251925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251925).length < 2 ^ (prefixWord ++ tailWord_251925).sum := by decide
  have hdescent : baseEnd_251925 < baseStart_251925 := by decide
  rcases family_descends (prefixWord ++ tailWord_251925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251927 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 2]
def baseStart_251927 : Nat := 118140960795 + 251927 * 2 ^ 59
def prefixEnd_251927 : Nat := 4983230072969 + 3 ^ 40 * 251927 * 2
def baseEnd_251927 : Nat := 114986347418080949470147

theorem tailTrace_251927 : CollatzResearch.WordTrace tailWord_251927 prefixEnd_251927 114986347418080949470147 := by
  unfold tailWord_251927
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188532558318979551258035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6125688372212653034172023 9188532558318979551258035)
  ·
    refine ⟨13782798837478469326887053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9188532558318979551258035 13782798837478469326887053)
    ·
      refine ⟨5168549564054425997582645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13782798837478469326887053 5168549564054425997582645)
      ·
        refine ⟨484551521630102437273373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5168549564054425997582645 484551521630102437273373)
        ·
          refine ⟨181706820611288413977515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484551521630102437273373 181706820611288413977515)
          ·
            refine ⟨272560230916932620966273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181706820611288413977515 272560230916932620966273)
            ·
              refine ⟨204420173187699465724705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272560230916932620966273 204420173187699465724705)
              ·
                refine ⟨153315129890774599293529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204420173187699465724705 153315129890774599293529)
                ·
                  refine ⟨114986347418080949470147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153315129890774599293529 114986347418080949470147)
                  ·
                    rfl

theorem cell20_251927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2].length) (baseStart_251927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251927 prefixEnd_251927 := by exact prefixLift 251927
  have htrace : WordTrace (prefixWord ++ tailWord_251927) baseStart_251927 baseEnd_251927 := by
    simpa [prefixWord, tailWord_251927, baseEnd_251927] using wordTrace_append hprefix tailTrace_251927
  have hstable : (prefixWord ++ tailWord_251927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251927).length < 2 ^ (prefixWord ++ tailWord_251927).sum := by decide
  have hdescent : baseEnd_251927 < baseStart_251927 := by decide
  rcases family_descends (prefixWord ++ tailWord_251927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251928 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_251928 : Nat := 118140960795 + 251928 * 2 ^ 59
def prefixEnd_251928 : Nat := 4983230072969 + 3 ^ 40 * 251928 * 2
def baseEnd_251928 : Nat := 114986803845329390436809

theorem tailTrace_251928 : CollatzResearch.WordTrace tailWord_251928 prefixEnd_251928 114986803845329390436809 := by
  unfold tailWord_251928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594284515657678361022219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6125712687543571148029625 4594284515657678361022219)
  ·
    refine ⟨6891426773486517541533329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4594284515657678361022219 6891426773486517541533329)
    ·
      refine ⟨5168570080114888156149997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6891426773486517541533329 5168570080114888156149997)
      ·
        refine ⟨1938213780043083058556249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5168570080114888156149997 1938213780043083058556249)
        ·
          refine ⟨1453660335032312293917187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938213780043083058556249 1453660335032312293917187)
          ·
            refine ⟨2180490502548468440875781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453660335032312293917187 2180490502548468440875781)
            ·
              refine ⟨408841969227837832664209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2180490502548468440875781 408841969227837832664209)
              ·
                refine ⟨306631476920878374498157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408841969227837832664209 306631476920878374498157)
                ·
                  refine ⟨114986803845329390436809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306631476920878374498157 114986803845329390436809)
                  ·
                    rfl

theorem cell20_251928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_251928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251928 prefixEnd_251928 := by exact prefixLift 251928
  have htrace : WordTrace (prefixWord ++ tailWord_251928) baseStart_251928 baseEnd_251928 := by
    simpa [prefixWord, tailWord_251928, baseEnd_251928] using wordTrace_append hprefix tailTrace_251928
  have hstable : (prefixWord ++ tailWord_251928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251928).length < 2 ^ (prefixWord ++ tailWord_251928).sum := by decide
  have hdescent : baseEnd_251928 < baseStart_251928 := by decide
  rcases family_descends (prefixWord ++ tailWord_251928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251969 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 2]
def baseStart_251969 : Nat := 118140960795 + 251969 * 2 ^ 59
def prefixEnd_251969 : Nat := 4983230072969 + 3 ^ 40 * 251969 * 2
def baseEnd_251969 : Nat := 115005517362515470069975

theorem tailTrace_251969 : CollatzResearch.WordTrace tailWord_251969 prefixEnd_251969 115005517362515470069975 := by
  unfold tailWord_251969
  simp only [CollatzResearch.WordTrace]
  refine ⟨9190064424166820724286961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6126709616111213816191307 9190064424166820724286961)
  ·
    refine ⟨6892548318125115543215221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9190064424166820724286961 6892548318125115543215221)
    ·
      refine ⟨646176404824229582176427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6892548318125115543215221 646176404824229582176427)
      ·
        refine ⟨969264607236344373264641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646176404824229582176427 969264607236344373264641)
        ·
          refine ⟨726948455427258279948481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969264607236344373264641 726948455427258279948481)
          ·
            refine ⟨545211341570443709961361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726948455427258279948481 545211341570443709961361)
            ·
              refine ⟨408908506177832782471021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545211341570443709961361 408908506177832782471021)
              ·
                refine ⟨153340689816687293426633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408908506177832782471021 153340689816687293426633)
                ·
                  refine ⟨115005517362515470069975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153340689816687293426633 115005517362515470069975)
                  ·
                    rfl

theorem cell20_251969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_251969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_251969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_251969 prefixEnd_251969 := by exact prefixLift 251969
  have htrace : WordTrace (prefixWord ++ tailWord_251969) baseStart_251969 baseEnd_251969 := by
    simpa [prefixWord, tailWord_251969, baseEnd_251969] using wordTrace_append hprefix tailTrace_251969
  have hstable : (prefixWord ++ tailWord_251969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251969).length < 2 ^ (prefixWord ++ tailWord_251969).sum := by decide
  have hdescent : baseEnd_251969 < baseStart_251969 := by decide
  rcases family_descends (prefixWord ++ tailWord_251969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252001 : List Nat := [1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_252001 : Nat := 118140960795 + 252001 * 2 ^ 59
def prefixEnd_252001 : Nat := 4983230072969 + 3 ^ 40 * 252001 * 2
def baseEnd_252001 : Nat := 38340041011488527001059

theorem tailTrace_252001 : CollatzResearch.WordTrace tailWord_252001 prefixEnd_252001 38340041011488527001059 := by
  unfold tailWord_252001
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191231560050890189451857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6127487706700593459634571 9191231560050890189451857)
  ·
    refine ⟨6893423670038167642088893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9191231560050890189451857 6893423670038167642088893)
    ·
      refine ⟨2585033876264312865783335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6893423670038167642088893 2585033876264312865783335)
      ·
        refine ⟨3877550814396469298675003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2585033876264312865783335 3877550814396469298675003)
        ·
          refine ⟨5816326221594703948012505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877550814396469298675003 5816326221594703948012505)
          ·
            refine ⟨4362244666196027961009379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5816326221594703948012505 4362244666196027961009379)
            ·
              refine ⟨6543366999294041941514069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362244666196027961009379 6543366999294041941514069)
              ·
                refine ⟨38340041011488527001059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6543366999294041941514069 38340041011488527001059)
                ·
                  rfl

theorem cell20_252001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_252001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252001 prefixEnd_252001 := by exact prefixLift 252001
  have htrace : WordTrace (prefixWord ++ tailWord_252001) baseStart_252001 baseEnd_252001 := by
    simpa [prefixWord, tailWord_252001, baseEnd_252001] using wordTrace_append hprefix tailTrace_252001
  have hstable : (prefixWord ++ tailWord_252001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252001).length < 2 ^ (prefixWord ++ tailWord_252001).sum := by decide
  have hdescent : baseEnd_252001 < baseStart_252001 := by decide
  rcases family_descends (prefixWord ++ tailWord_252001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252018 : List Nat := [3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_252018 : Nat := 118140960795 + 252018 * 2 ^ 59
def prefixEnd_252018 : Nat := 4983230072969 + 3 ^ 40 * 252018 * 2
def baseEnd_252018 : Nat := 38342627432563025812147

theorem tailTrace_252018 : CollatzResearch.WordTrace tailWord_252018 prefixEnd_252018 38342627432563025812147 := by
  unfold tailWord_252018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297962900247325523205177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6127901067326201395213805 2297962900247325523205177)
  ·
    refine ⟨1723472175185494142403883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2297962900247325523205177 1723472175185494142403883)
    ·
      refine ⟨2585208262778241213605825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723472175185494142403883 2585208262778241213605825)
      ·
        refine ⟨1938906197083680910204369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585208262778241213605825 1938906197083680910204369)
        ·
          refine ⟨1454179647812760682653277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938906197083680910204369 1454179647812760682653277)
          ·
            refine ⟨545317367929785255994979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1454179647812760682653277 545317367929785255994979)
            ·
              refine ⟨817976051894677883992469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545317367929785255994979 817976051894677883992469)
              ·
                refine ⟨38342627432563025812147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 817976051894677883992469 38342627432563025812147)
                ·
                  rfl

theorem cell20_252018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_252018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252018 prefixEnd_252018 := by exact prefixLift 252018
  have htrace : WordTrace (prefixWord ++ tailWord_252018) baseStart_252018 baseEnd_252018 := by
    simpa [prefixWord, tailWord_252018, baseEnd_252018] using wordTrace_append hprefix tailTrace_252018
  have hstable : (prefixWord ++ tailWord_252018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252018).length < 2 ^ (prefixWord ++ tailWord_252018).sum := by decide
  have hdescent : baseEnd_252018 < baseStart_252018 := by decide
  rcases family_descends (prefixWord ++ tailWord_252018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252025 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_252025 : Nat := 118140960795 + 252025 * 2 ^ 59
def prefixEnd_252025 : Nat := 4983230072969 + 3 ^ 40 * 252025 * 2
def baseEnd_252025 : Nat := 115031077288428164203079

theorem tailTrace_252025 : CollatzResearch.WordTrace tailWord_252025 prefixEnd_252025 115031077288428164203079 := by
  unfold tailWord_252025
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192106911963942288325529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6128071274642628192217019 9192106911963942288325529)
  ·
    refine ⟨6894080183972956716244147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9192106911963942288325529 6894080183972956716244147)
    ·
      refine ⟨10341120275959435074366221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894080183972956716244147 10341120275959435074366221)
      ·
        refine ⟨3877920103484788152887333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10341120275959435074366221 3877920103484788152887333)
        ·
          refine ⟨727110019403397778666375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3877920103484788152887333 727110019403397778666375)
          ·
            refine ⟨1090665029105096667999563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727110019403397778666375 1090665029105096667999563)
            ·
              refine ⟨1635997543657645001999345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090665029105096667999563 1635997543657645001999345)
              ·
                refine ⟨1226998157743233751499509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635997543657645001999345 1226998157743233751499509)
                ·
                  refine ⟨115031077288428164203079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226998157743233751499509 115031077288428164203079)
                  ·
                    rfl

theorem cell20_252025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_252025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252025 prefixEnd_252025 := by exact prefixLift 252025
  have htrace : WordTrace (prefixWord ++ tailWord_252025) baseStart_252025 baseEnd_252025 := by
    simpa [prefixWord, tailWord_252025, baseEnd_252025] using wordTrace_append hprefix tailTrace_252025
  have hstable : (prefixWord ++ tailWord_252025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252025).length < 2 ^ (prefixWord ++ tailWord_252025).sum := by decide
  have hdescent : baseEnd_252025 < baseStart_252025 := by decide
  rcases family_descends (prefixWord ++ tailWord_252025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252028 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_252028 : Nat := 118140960795 + 252028 * 2 ^ 59
def prefixEnd_252028 : Nat := 4983230072969 + 3 ^ 40 * 252028 * 2
def baseEnd_252028 : Nat := 115032446570173487103067

theorem tailTrace_252028 : CollatzResearch.WordTrace tailWord_252028 prefixEnd_252028 115032446570173487103067 := by
  unfold tailWord_252028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596108165476536900342369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6128144220635382533789825 4596108165476536900342369)
  ·
    refine ⟨3447081124107402675256777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4596108165476536900342369 3447081124107402675256777)
    ·
      refine ⟨2585310843080552006442583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3447081124107402675256777 2585310843080552006442583)
      ·
        refine ⟨3877966264620828009663875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2585310843080552006442583 3877966264620828009663875)
        ·
          refine ⟨5816949396931242014495813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877966264620828009663875 5816949396931242014495813)
          ·
            refine ⟨1090678011924607877717965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5816949396931242014495813 1090678011924607877717965)
            ·
              refine ⟨409004254471727954144237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090678011924607877717965 409004254471727954144237)
              ·
                refine ⟨153376595426897982804089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409004254471727954144237 153376595426897982804089)
                ·
                  refine ⟨115032446570173487103067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153376595426897982804089 115032446570173487103067)
                  ·
                    rfl

theorem cell20_252028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_252028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252028 prefixEnd_252028 := by exact prefixLift 252028
  have htrace : WordTrace (prefixWord ++ tailWord_252028) baseStart_252028 baseEnd_252028 := by
    simpa [prefixWord, tailWord_252028, baseEnd_252028] using wordTrace_append hprefix tailTrace_252028
  have hstable : (prefixWord ++ tailWord_252028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252028).length < 2 ^ (prefixWord ++ tailWord_252028).sum := by decide
  have hdescent : baseEnd_252028 < baseStart_252028 := by decide
  rcases family_descends (prefixWord ++ tailWord_252028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252039 : List Nat := [1, 1, 4, 2, 1, 1, 10]
def baseStart_252039 : Nat := 118140960795 + 252039 * 2 ^ 59
def prefixEnd_252039 : Nat := 4983230072969 + 3 ^ 40 * 252039 * 2
def baseEnd_252039 : Nat := 12781940807767370859595

theorem tailTrace_252039 : CollatzResearch.WordTrace tailWord_252039 prefixEnd_252039 12781940807767370859595 := by
  unfold tailWord_252039
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192617533913222679335171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6128411689275481786223447 9192617533913222679335171)
  ·
    refine ⟨13788926300869834019002757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9192617533913222679335171 13788926300869834019002757)
    ·
      refine ⟨2585423681413093878563017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13788926300869834019002757 2585423681413093878563017)
      ·
        refine ⟨1939067761059820408922263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585423681413093878563017 1939067761059820408922263)
        ·
          refine ⟨2908601641589730613383395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939067761059820408922263 2908601641589730613383395)
          ·
            refine ⟨4362902462384595920075093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908601641589730613383395 4362902462384595920075093)
            ·
              refine ⟨12781940807767370859595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4362902462384595920075093 12781940807767370859595)
              ·
                rfl

theorem cell20_252039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_252039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252039 prefixEnd_252039 := by exact prefixLift 252039
  have htrace : WordTrace (prefixWord ++ tailWord_252039) baseStart_252039 baseEnd_252039 := by
    simpa [prefixWord, tailWord_252039, baseEnd_252039] using wordTrace_append hprefix tailTrace_252039
  have hstable : (prefixWord ++ tailWord_252039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252039).length < 2 ^ (prefixWord ++ tailWord_252039).sum := by decide
  have hdescent : baseEnd_252039 < baseStart_252039 := by decide
  rcases family_descends (prefixWord ++ tailWord_252039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252052 : List Nat := [2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_252052 : Nat := 118140960795 + 252052 * 2 ^ 59
def prefixEnd_252052 : Nat := 4983230072969 + 3 ^ 40 * 252052 * 2
def baseEnd_252052 : Nat := 38347800274712023434323

theorem tailTrace_252052 : CollatzResearch.WordTrace tailWord_252052 prefixEnd_252052 38347800274712023434323 := by
  unfold tailWord_252052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596545841433062949779205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6128727788577417266372273 4596545841433062949779205)
  ·
    refine ⟨861852345268699303083601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4596545841433062949779205 861852345268699303083601)
    ·
      refine ⟨646389258951524477312701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861852345268699303083601 646389258951524477312701)
      ·
        refine ⟨242395972106821678992263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646389258951524477312701 242395972106821678992263)
        ·
          refine ⟨363593958160232518488395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242395972106821678992263 363593958160232518488395)
          ·
            refine ⟨545390937240348777732593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363593958160232518488395 545390937240348777732593)
            ·
              refine ⟨409043202930261583299445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545390937240348777732593 409043202930261583299445)
              ·
                refine ⟨38347800274712023434323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409043202930261583299445 38347800274712023434323)
                ·
                  rfl

theorem cell20_252052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_252052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252052 prefixEnd_252052 := by exact prefixLift 252052
  have htrace : WordTrace (prefixWord ++ tailWord_252052) baseStart_252052 baseEnd_252052 := by
    simpa [prefixWord, tailWord_252052, baseEnd_252052] using wordTrace_append hprefix tailTrace_252052
  have hstable : (prefixWord ++ tailWord_252052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252052).length < 2 ^ (prefixWord ++ tailWord_252052).sum := by decide
  have hdescent : baseEnd_252052 < baseStart_252052 := by decide
  rcases family_descends (prefixWord ++ tailWord_252052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252094 : List Nat := [4, 2, 1, 1, 4, 8]
def baseStart_252094 : Nat := 118140960795 + 252094 * 2 ^ 59
def prefixEnd_252094 : Nat := 4983230072969 + 3 ^ 40 * 252094 * 2
def baseEnd_252094 : Nat := 4261576695132244107511

theorem tailTrace_252094 : CollatzResearch.WordTrace tailWord_252094 prefixEnd_252094 4261576695132244107511 := by
  unfold tailWord_252094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149327943589245884073417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6129749032475978048391557 1149327943589245884073417)
  ·
    refine ⟨861995957691934413055063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1149327943589245884073417 861995957691934413055063)
    ·
      refine ⟨1292993936537901619582595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861995957691934413055063 1292993936537901619582595)
      ·
        refine ⟨1939490904806852429373893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292993936537901619582595 1939490904806852429373893)
        ·
          refine ⟨363654544651284830507605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1939490904806852429373893 363654544651284830507605)
          ·
            refine ⟨4261576695132244107511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 363654544651284830507605 4261576695132244107511)
            ·
              rfl

theorem cell20_252094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 8].length) (baseStart_252094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252094 prefixEnd_252094 := by exact prefixLift 252094
  have htrace : WordTrace (prefixWord ++ tailWord_252094) baseStart_252094 baseEnd_252094 := by
    simpa [prefixWord, tailWord_252094, baseEnd_252094] using wordTrace_append hprefix tailTrace_252094
  have hstable : (prefixWord ++ tailWord_252094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252094).length < 2 ^ (prefixWord ++ tailWord_252094).sum := by decide
  have hdescent : baseEnd_252094 < baseStart_252094 := by decide
  rcases family_descends (prefixWord ++ tailWord_252094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252100 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_252100 : Nat := 118140960795 + 252100 * 2 ^ 59
def prefixEnd_252100 : Nat := 4983230072969 + 3 ^ 40 * 252100 * 2
def baseEnd_252100 : Nat := 115065309332061236702773

theorem tailTrace_252100 : CollatzResearch.WordTrace tailWord_252100 prefixEnd_252100 115065309332061236702773 := by
  unfold tailWord_252100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597421193346115048652877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6129894924461486731537169 4597421193346115048652877)
  ·
    refine ⟨1724032947504793143244829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4597421193346115048652877 1724032947504793143244829)
    ·
      refine ⟨646512355314297428716811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1724032947504793143244829 646512355314297428716811)
      ·
        refine ⟨969768532971446143075217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646512355314297428716811 969768532971446143075217)
        ·
          refine ⟨727326399728584607306413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969768532971446143075217 727326399728584607306413)
          ·
            refine ⟨272747399898219227739905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727326399728584607306413 272747399898219227739905)
            ·
              refine ⟨204560549923664420804929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272747399898219227739905 204560549923664420804929)
              ·
                refine ⟨153420412442748315603697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204560549923664420804929 153420412442748315603697)
                ·
                  refine ⟨115065309332061236702773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153420412442748315603697 115065309332061236702773)
                  ·
                    rfl

theorem cell20_252100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_252100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252100 prefixEnd_252100 := by exact prefixLift 252100
  have htrace : WordTrace (prefixWord ++ tailWord_252100) baseStart_252100 baseEnd_252100 := by
    simpa [prefixWord, tailWord_252100, baseEnd_252100] using wordTrace_append hprefix tailTrace_252100
  have hstable : (prefixWord ++ tailWord_252100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252100).length < 2 ^ (prefixWord ++ tailWord_252100).sum := by decide
  have hdescent : baseEnd_252100 < baseStart_252100 := by decide
  rcases family_descends (prefixWord ++ tailWord_252100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252101 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_252101 : Nat := 118140960795 + 252101 * 2 ^ 59
def prefixEnd_252101 : Nat := 4983230072969 + 3 ^ 40 * 252101 * 2
def baseEnd_252101 : Nat := 115065765759309677669435

theorem tailTrace_252101 : CollatzResearch.WordTrace tailWord_252101 prefixEnd_252101 115065765759309677669435 := by
  unfold tailWord_252101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194878859688607268092157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6129919239792404845394771 9194878859688607268092157)
  ·
    refine ⟨3448079572383227725534559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9194878859688607268092157 3448079572383227725534559)
    ·
      refine ⟨5172119358574841588301839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448079572383227725534559 5172119358574841588301839)
      ·
        refine ⟨7758179037862262382452759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172119358574841588301839 7758179037862262382452759)
        ·
          refine ⟨11637268556793393573679139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758179037862262382452759 11637268556793393573679139)
          ·
            refine ⟨17455902835190090360518709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637268556793393573679139 17455902835190090360518709)
            ·
              refine ⟨1636490890799070971298629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17455902835190090360518709 1636490890799070971298629)
              ·
                refine ⟨306842042024825807118493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1636490890799070971298629 306842042024825807118493)
                ·
                  refine ⟨115065765759309677669435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306842042024825807118493 115065765759309677669435)
                  ·
                    rfl

theorem cell20_252101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_252101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252101 prefixEnd_252101 := by exact prefixLift 252101
  have htrace : WordTrace (prefixWord ++ tailWord_252101) baseStart_252101 baseEnd_252101 := by
    simpa [prefixWord, tailWord_252101, baseEnd_252101] using wordTrace_append hprefix tailTrace_252101
  have hstable : (prefixWord ++ tailWord_252101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252101).length < 2 ^ (prefixWord ++ tailWord_252101).sum := by decide
  have hdescent : baseEnd_252101 < baseStart_252101 := by decide
  rcases family_descends (prefixWord ++ tailWord_252101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252125 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_252125 : Nat := 118140960795 + 252125 * 2 ^ 59
def prefixEnd_252125 : Nat := 4983230072969 + 3 ^ 40 * 252125 * 2
def baseEnd_252125 : Nat := 115076720013272260869337

theorem tailTrace_252125 : CollatzResearch.WordTrace tailWord_252125 prefixEnd_252125 115076720013272260869337 := by
  unfold tailWord_252125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195754211601659366965829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6130502807734439577977219 9195754211601659366965829)
  ·
    refine ⟨1724203914675311131306093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9195754211601659366965829 1724203914675311131306093)
    ·
      refine ⟨646576468003241674239785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1724203914675311131306093 646576468003241674239785)
      ·
        refine ⟨484932351002431255679839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646576468003241674239785 484932351002431255679839)
        ·
          refine ⟨727398526503646883519759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484932351002431255679839 727398526503646883519759)
          ·
            refine ⟨1091097789755470325279639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727398526503646883519759 1091097789755470325279639)
            ·
              refine ⟨1636646684633205487919459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091097789755470325279639 1636646684633205487919459)
              ·
                refine ⟨2454970026949808231879189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636646684633205487919459 2454970026949808231879189)
                ·
                  refine ⟨115076720013272260869337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2454970026949808231879189 115076720013272260869337)
                  ·
                    rfl

theorem cell20_252125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_252125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252125 prefixEnd_252125 := by exact prefixLift 252125
  have htrace : WordTrace (prefixWord ++ tailWord_252125) baseStart_252125 baseEnd_252125 := by
    simpa [prefixWord, tailWord_252125, baseEnd_252125] using wordTrace_append hprefix tailTrace_252125
  have hstable : (prefixWord ++ tailWord_252125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252125).length < 2 ^ (prefixWord ++ tailWord_252125).sum := by decide
  have hdescent : baseEnd_252125 < baseStart_252125 := by decide
  rcases family_descends (prefixWord ++ tailWord_252125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252156 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_252156 : Nat := 118140960795 + 252156 * 2 ^ 59
def prefixEnd_252156 : Nat := 4983230072969 + 3 ^ 40 * 252156 * 2
def baseEnd_252156 : Nat := 115090869257973930835877

theorem tailTrace_252156 : CollatzResearch.WordTrace tailWord_252156 prefixEnd_252156 115090869257973930835877 := by
  unfold tailWord_252156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598442437244675830672161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6131256582992901107562881 4598442437244675830672161)
  ·
    refine ⟨3448831827933506873004121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4598442437244675830672161 3448831827933506873004121)
    ·
      refine ⟨2586623870950130154753091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448831827933506873004121 2586623870950130154753091)
      ·
        refine ⟨3879935806425195232129637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586623870950130154753091 3879935806425195232129637)
        ·
          refine ⟨727487963704724106024307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3879935806425195232129637 727487963704724106024307)
          ·
            refine ⟨1091231945557086159036461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727487963704724106024307 1091231945557086159036461)
            ·
              refine ⟨409211979583907309638673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091231945557086159036461 409211979583907309638673)
              ·
                refine ⟨306908984687930482229005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409211979583907309638673 306908984687930482229005)
                ·
                  refine ⟨115090869257973930835877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306908984687930482229005 115090869257973930835877)
                  ·
                    rfl

theorem cell20_252156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_252156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252156 prefixEnd_252156 := by exact prefixLift 252156
  have htrace : WordTrace (prefixWord ++ tailWord_252156) baseStart_252156 baseEnd_252156 := by
    simpa [prefixWord, tailWord_252156, baseEnd_252156] using wordTrace_append hprefix tailTrace_252156
  have hstable : (prefixWord ++ tailWord_252156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252156).length < 2 ^ (prefixWord ++ tailWord_252156).sum := by decide
  have hdescent : baseEnd_252156 < baseStart_252156 := by decide
  rcases family_descends (prefixWord ++ tailWord_252156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252163 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 2]
def baseStart_252163 : Nat := 118140960795 + 252163 * 2 ^ 59
def prefixEnd_252163 : Nat := 4983230072969 + 3 ^ 40 * 252163 * 2
def baseEnd_252163 : Nat := 115094064248713017602515

theorem tailTrace_252163 : CollatzResearch.WordTrace tailWord_252163 prefixEnd_252163 115094064248713017602515 := by
  unfold tailWord_252163
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197140185463991856849143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6131426790309327904566095 9197140185463991856849143)
  ·
    refine ⟨13795710278195987785273715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197140185463991856849143 13795710278195987785273715)
    ·
      refine ⟨20693565417293981677910573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13795710278195987785273715 20693565417293981677910573)
      ·
        refine ⟨7760087031485243129216465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20693565417293981677910573 7760087031485243129216465)
        ·
          refine ⟨5820065273613932346912349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760087031485243129216465 5820065273613932346912349)
          ·
            refine ⟨2182524477605224630092131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5820065273613932346912349 2182524477605224630092131)
            ·
              refine ⟨3273786716407836945138197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182524477605224630092131 3273786716407836945138197)
              ·
                refine ⟨153458752331617356803353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3273786716407836945138197 153458752331617356803353)
                ·
                  refine ⟨115094064248713017602515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153458752331617356803353 115094064248713017602515)
                  ·
                    rfl

theorem cell20_252163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2].length) (baseStart_252163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252163 prefixEnd_252163 := by exact prefixLift 252163
  have htrace : WordTrace (prefixWord ++ tailWord_252163) baseStart_252163 baseEnd_252163 := by
    simpa [prefixWord, tailWord_252163, baseEnd_252163] using wordTrace_append hprefix tailTrace_252163
  have hstable : (prefixWord ++ tailWord_252163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252163).length < 2 ^ (prefixWord ++ tailWord_252163).sum := by decide
  have hdescent : baseEnd_252163 < baseStart_252163 := by decide
  rcases family_descends (prefixWord ++ tailWord_252163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252184 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_252184 : Nat := 118140960795 + 252184 * 2 ^ 59
def prefixEnd_252184 : Nat := 4983230072969 + 3 ^ 40 * 252184 * 2
def baseEnd_252184 : Nat := 115103649220930277902429

theorem tailTrace_252184 : CollatzResearch.WordTrace tailWord_252184 prefixEnd_252184 115103649220930277902429 := by
  unfold tailWord_252184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598953059193956221681803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6131937412258608295575737 4598953059193956221681803)
  ·
    refine ⟨6898429588790934332522705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4598953059193956221681803 6898429588790934332522705)
    ·
      refine ⟨5173822191593200749392029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6898429588790934332522705 5173822191593200749392029)
      ·
        refine ⟨1940183321847450281022011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5173822191593200749392029 1940183321847450281022011)
        ·
          refine ⟨2910274982771175421533017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940183321847450281022011 2910274982771175421533017)
          ·
            refine ⟨2182706237078381566149763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910274982771175421533017 2182706237078381566149763)
            ·
              refine ⟨3274059355617572349224645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182706237078381566149763 3274059355617572349224645)
              ·
                refine ⟨613886129178294815479621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3274059355617572349224645 613886129178294815479621)
                ·
                  refine ⟨115103649220930277902429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613886129178294815479621 115103649220930277902429)
                  ·
                    rfl

theorem cell20_252184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_252184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252184 prefixEnd_252184 := by exact prefixLift 252184
  have htrace : WordTrace (prefixWord ++ tailWord_252184) baseStart_252184 baseEnd_252184 := by
    simpa [prefixWord, tailWord_252184, baseEnd_252184] using wordTrace_append hprefix tailTrace_252184
  have hstable : (prefixWord ++ tailWord_252184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252184).length < 2 ^ (prefixWord ++ tailWord_252184).sum := by decide
  have hdescent : baseEnd_252184 < baseStart_252184 := by decide
  rcases family_descends (prefixWord ++ tailWord_252184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252197 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 2]
def baseStart_252197 : Nat := 118140960795 + 252197 * 2 ^ 59
def prefixEnd_252197 : Nat := 4983230072969 + 3 ^ 40 * 252197 * 2
def baseEnd_252197 : Nat := 115109582775160010469043

theorem tailTrace_252197 : CollatzResearch.WordTrace tailWord_252197 prefixEnd_252197 115109582775160010469043 := by
  unfold tailWord_252197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198380267340815663586845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6132253511560543775724563 9198380267340815663586845)
  ·
    refine ⟨3449392600252805873845067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9198380267340815663586845 3449392600252805873845067)
    ·
      refine ⟨5174088900379208810767601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449392600252805873845067 5174088900379208810767601)
      ·
        refine ⟨3880566675284406608075701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5174088900379208810767601 3880566675284406608075701)
        ·
          refine ⟨363803125807913119507097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3880566675284406608075701 363803125807913119507097)
          ·
            refine ⟨272852344355934839630323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363803125807913119507097 272852344355934839630323)
            ·
              refine ⟨409278516533902259445485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272852344355934839630323 409278516533902259445485)
              ·
                refine ⟨153479443700213347292057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409278516533902259445485 153479443700213347292057)
                ·
                  refine ⟨115109582775160010469043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153479443700213347292057 115109582775160010469043)
                  ·
                    rfl

theorem cell20_252197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_252197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252197 prefixEnd_252197 := by exact prefixLift 252197
  have htrace : WordTrace (prefixWord ++ tailWord_252197) baseStart_252197 baseEnd_252197 := by
    simpa [prefixWord, tailWord_252197, baseEnd_252197] using wordTrace_append hprefix tailTrace_252197
  have hstable : (prefixWord ++ tailWord_252197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252197).length < 2 ^ (prefixWord ++ tailWord_252197).sum := by decide
  have hdescent : baseEnd_252197 < baseStart_252197 := by decide
  rcases family_descends (prefixWord ++ tailWord_252197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252225 : List Nat := [1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_252225 : Nat := 118140960795 + 252225 * 2 ^ 59
def prefixEnd_252225 : Nat := 4983230072969 + 3 ^ 40 * 252225 * 2
def baseEnd_252225 : Nat := 38374120912705452511865

theorem tailTrace_252225 : CollatzResearch.WordTrace tailWord_252225 prefixEnd_252225 38374120912705452511865 := by
  unfold tailWord_252225
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199401511239376445606129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6132934340826250963737419 9199401511239376445606129)
  ·
    refine ⟨6899551133429532334204597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9199401511239376445606129 6899551133429532334204597)
    ·
      refine ⟨646832918759018656331681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6899551133429532334204597 646832918759018656331681)
      ·
        refine ⟨485124689069263992248761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646832918759018656331681 485124689069263992248761)
        ·
          refine ⟨363843516801947994186571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485124689069263992248761 363843516801947994186571)
          ·
            refine ⟨545765275202921991279857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363843516801947994186571 545765275202921991279857)
            ·
              refine ⟨409323956402191493459893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545765275202921991279857 409323956402191493459893)
              ·
                refine ⟨38374120912705452511865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409323956402191493459893 38374120912705452511865)
                ·
                  rfl

theorem cell20_252225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_252225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252225 prefixEnd_252225 := by exact prefixLift 252225
  have htrace : WordTrace (prefixWord ++ tailWord_252225) baseStart_252225 baseEnd_252225 := by
    simpa [prefixWord, tailWord_252225, baseEnd_252225] using wordTrace_append hprefix tailTrace_252225
  have hstable : (prefixWord ++ tailWord_252225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252225).length < 2 ^ (prefixWord ++ tailWord_252225).sum := by decide
  have hdescent : baseEnd_252225 < baseStart_252225 := by decide
  rcases family_descends (prefixWord ++ tailWord_252225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252232 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_252232 : Nat := 118140960795 + 252232 * 2 ^ 59
def prefixEnd_252232 : Nat := 4983230072969 + 3 ^ 40 * 252232 * 2
def baseEnd_252232 : Nat := 115125557728855444302233

theorem tailTrace_252232 : CollatzResearch.WordTrace tailWord_252232 prefixEnd_252232 115125557728855444302233 := by
  unfold tailWord_252232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599828411107008320555475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6133104548142677760740633 4599828411107008320555475)
  ·
    refine ⟨6899742616660512480833213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4599828411107008320555475 6899742616660512480833213)
    ·
      refine ⟨2587403481247692180312455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6899742616660512480833213 2587403481247692180312455)
      ·
        refine ⟨3881105221871538270468683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587403481247692180312455 3881105221871538270468683)
        ·
          refine ⟨5821657832807307405703025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881105221871538270468683 5821657832807307405703025)
          ·
            refine ⟨4366243374605480554277269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821657832807307405703025 4366243374605480554277269)
            ·
              refine ⟨204667658184631900981747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4366243374605480554277269 204667658184631900981747)
              ·
                refine ⟨307001487276947851472621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204667658184631900981747 307001487276947851472621)
                ·
                  refine ⟨115125557728855444302233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307001487276947851472621 115125557728855444302233)
                  ·
                    rfl

theorem cell20_252232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_252232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252232 prefixEnd_252232 := by exact prefixLift 252232
  have htrace : WordTrace (prefixWord ++ tailWord_252232) baseStart_252232 baseEnd_252232 := by
    simpa [prefixWord, tailWord_252232, baseEnd_252232] using wordTrace_append hprefix tailTrace_252232
  have hstable : (prefixWord ++ tailWord_252232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252232).length < 2 ^ (prefixWord ++ tailWord_252232).sum := by decide
  have hdescent : baseEnd_252232 < baseStart_252232 := by decide
  rcases family_descends (prefixWord ++ tailWord_252232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252356 : List Nat := [2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_252356 : Nat := 118140960795 + 252356 * 2 ^ 59
def prefixEnd_252356 : Nat := 4983230072969 + 3 ^ 40 * 252356 * 2
def baseEnd_252356 : Nat := 38394051569220708056131

theorem tailTrace_252356 : CollatzResearch.WordTrace tailWord_252356 prefixEnd_252356 38394051569220708056131 := by
  unfold tailWord_252356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602089736882392909312461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6136119649176523879083281 4602089736882392909312461)
  ·
    refine ⟨1725783651330897340992173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4602089736882392909312461 1725783651330897340992173)
    ·
      refine ⟨647168869249086502872065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1725783651330897340992173 647168869249086502872065)
      ·
        refine ⟨485376651936814877154049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647168869249086502872065 485376651936814877154049)
        ·
          refine ⟨364032488952611157865537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485376651936814877154049 364032488952611157865537)
          ·
            refine ⟨273024366714458368399153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364032488952611157865537 273024366714458368399153)
            ·
              refine ⟨204768275035843776299365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273024366714458368399153 204768275035843776299365)
              ·
                refine ⟨38394051569220708056131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204768275035843776299365 38394051569220708056131)
                ·
                  rfl

theorem cell20_252356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_252356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252356 prefixEnd_252356 := by exact prefixLift 252356
  have htrace : WordTrace (prefixWord ++ tailWord_252356) baseStart_252356 baseEnd_252356 := by
    simpa [prefixWord, tailWord_252356, baseEnd_252356] using wordTrace_append hprefix tailTrace_252356
  have hstable : (prefixWord ++ tailWord_252356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252356).length < 2 ^ (prefixWord ++ tailWord_252356).sum := by decide
  have hdescent : baseEnd_252356 < baseStart_252356 := by decide
  rcases family_descends (prefixWord ++ tailWord_252356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252360 : List Nat := [2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_252360 : Nat := 118140960795 + 252360 * 2 ^ 59
def prefixEnd_252360 : Nat := 4983230072969 + 3 ^ 40 * 252360 * 2
def baseEnd_252360 : Nat := 38394660138885296011681

theorem tailTrace_252360 : CollatzResearch.WordTrace tailWord_252360 prefixEnd_252360 38394660138885296011681 := by
  unfold tailWord_252360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602162682875147250885267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6136216910500196334513689 4602162682875147250885267)
  ·
    refine ⟨6903244024312720876327901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602162682875147250885267 6903244024312720876327901)
    ·
      refine ⟨2588716509117270328622963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6903244024312720876327901 2588716509117270328622963)
      ·
        refine ⟨3883074763675905492934445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588716509117270328622963 3883074763675905492934445)
        ·
          refine ⟨1456153036378464559850417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3883074763675905492934445 1456153036378464559850417)
          ·
            refine ⟨1092114777283848419887813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456153036378464559850417 1092114777283848419887813)
            ·
              refine ⟨204771520740721578728965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1092114777283848419887813 204771520740721578728965)
              ·
                refine ⟨38394660138885296011681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204771520740721578728965 38394660138885296011681)
                ·
                  rfl

theorem cell20_252360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_252360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252360 prefixEnd_252360 := by exact prefixLift 252360
  have htrace : WordTrace (prefixWord ++ tailWord_252360) baseStart_252360 baseEnd_252360 := by
    simpa [prefixWord, tailWord_252360, baseEnd_252360] using wordTrace_append hprefix tailTrace_252360
  have hstable : (prefixWord ++ tailWord_252360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252360).length < 2 ^ (prefixWord ++ tailWord_252360).sum := by decide
  have hdescent : baseEnd_252360 < baseStart_252360 := by decide
  rcases family_descends (prefixWord ++ tailWord_252360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252387 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 2]
def baseStart_252387 : Nat := 118140960795 + 252387 * 2 ^ 59
def prefixEnd_252387 : Nat := 4983230072969 + 3 ^ 40 * 252387 * 2
def baseEnd_252387 : Nat := 115196303952363794134933

theorem tailTrace_252387 : CollatzResearch.WordTrace tailWord_252387 prefixEnd_252387 115196303952363794134933 := by
  unfold tailWord_252387
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205310136652478113003415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6136873424434985408668943 9205310136652478113003415)
  ·
    refine ⟨13807965204978717169505123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9205310136652478113003415 13807965204978717169505123)
    ·
      refine ⟨20711947807468075754257685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13807965204978717169505123 20711947807468075754257685)
      ·
        refine ⟨970872553475066050980829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20711947807468075754257685 970872553475066050980829)
        ·
          refine ⟨364077207553149769117811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 970872553475066050980829 364077207553149769117811)
          ·
            refine ⟨546115811329724653676717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364077207553149769117811 546115811329724653676717)
            ·
              refine ⟨204793429248646745128769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546115811329724653676717 204793429248646745128769)
              ·
                refine ⟨153595071936485058846577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204793429248646745128769 153595071936485058846577)
                ·
                  refine ⟨115196303952363794134933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153595071936485058846577 115196303952363794134933)
                  ·
                    rfl

theorem cell20_252387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2].length) (baseStart_252387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252387 prefixEnd_252387 := by exact prefixLift 252387
  have htrace : WordTrace (prefixWord ++ tailWord_252387) baseStart_252387 baseEnd_252387 := by
    simpa [prefixWord, tailWord_252387, baseEnd_252387] using wordTrace_append hprefix tailTrace_252387
  have hstable : (prefixWord ++ tailWord_252387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252387).length < 2 ^ (prefixWord ++ tailWord_252387).sum := by decide
  have hdescent : baseEnd_252387 < baseStart_252387 := by decide
  rcases family_descends (prefixWord ++ tailWord_252387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252398 : List Nat := [4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_252398 : Nat := 118140960795 + 252398 * 2 ^ 59
def prefixEnd_252398 : Nat := 4983230072969 + 3 ^ 40 * 252398 * 2
def baseEnd_252398 : Nat := 38400441550698881589407

theorem tailTrace_252398 : CollatzResearch.WordTrace tailWord_252398 prefixEnd_252398 38400441550698881589407 := by
  unfold tailWord_252398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150713917451578373956731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6137140893075084661102565 1150713917451578373956731)
  ·
    refine ⟨1726070876177367560935097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1150713917451578373956731 1726070876177367560935097)
    ·
      refine ⟨1294553157133025670701323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1726070876177367560935097 1294553157133025670701323)
      ·
        refine ⟨1941829735699538506051985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294553157133025670701323 1941829735699538506051985)
        ·
          refine ⟨1456372301774653879538989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941829735699538506051985 1456372301774653879538989)
          ·
            refine ⟨546139613165495204827121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1456372301774653879538989 546139613165495204827121)
            ·
              refine ⟨409604709874121403620341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546139613165495204827121 409604709874121403620341)
              ·
                refine ⟨38400441550698881589407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409604709874121403620341 38400441550698881589407)
                ·
                  rfl

theorem cell20_252398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_252398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252398 prefixEnd_252398 := by exact prefixLift 252398
  have htrace : WordTrace (prefixWord ++ tailWord_252398) baseStart_252398 baseEnd_252398 := by
    simpa [prefixWord, tailWord_252398, baseEnd_252398] using wordTrace_append hprefix tailTrace_252398
  have hstable : (prefixWord ++ tailWord_252398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252398).length < 2 ^ (prefixWord ++ tailWord_252398).sum := by decide
  have hdescent : baseEnd_252398 < baseStart_252398 := by decide
  rcases family_descends (prefixWord ++ tailWord_252398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252433 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_252433 : Nat := 118140960795 + 252433 * 2 ^ 59
def prefixEnd_252433 : Nat := 4983230072969 + 3 ^ 40 * 252433 * 2
def baseEnd_252433 : Nat := 115217299605792078601411

theorem tailTrace_252433 : CollatzResearch.WordTrace tailWord_252433 prefixEnd_252433 115217299605792078601411 := by
  unfold tailWord_252433
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206987894485827969177953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6137991929657218646118635 9206987894485827969177953)
  ·
    refine ⟨6905240920864370976883465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9206987894485827969177953 6905240920864370976883465)
    ·
      refine ⟨5178930690648278232662599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6905240920864370976883465 5178930690648278232662599)
      ·
        refine ⟨7768396035972417348993899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178930690648278232662599 7768396035972417348993899)
        ·
          refine ⟨11652594053958626023490849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768396035972417348993899 11652594053958626023490849)
          ·
            refine ⟨8739445540468969517618137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11652594053958626023490849 8739445540468969517618137)
            ·
              refine ⟨6554584155351727138213603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739445540468969517618137 6554584155351727138213603)
              ·
                refine ⟨9831876233027590707320405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554584155351727138213603 9831876233027590707320405)
                ·
                  refine ⟨115217299605792078601411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9831876233027590707320405 115217299605792078601411)
                  ·
                    rfl

theorem cell20_252433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_252433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252433 prefixEnd_252433 := by exact prefixLift 252433
  have htrace : WordTrace (prefixWord ++ tailWord_252433) baseStart_252433 baseEnd_252433 := by
    simpa [prefixWord, tailWord_252433, baseEnd_252433] using wordTrace_append hprefix tailTrace_252433
  have hstable : (prefixWord ++ tailWord_252433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252433).length < 2 ^ (prefixWord ++ tailWord_252433).sum := by decide
  have hdescent : baseEnd_252433 < baseStart_252433 := by decide
  rcases family_descends (prefixWord ++ tailWord_252433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252436 : List Nat := [2, 4, 3, 1, 1, 9]
def baseStart_252436 : Nat := 118140960795 + 252436 * 2 ^ 59
def prefixEnd_252436 : Nat := 4983230072969 + 3 ^ 40 * 252436 * 2
def baseEnd_252436 : Nat := 4267358106945829685237

theorem tailTrace_252436 : CollatzResearch.WordTrace tailWord_252436 prefixEnd_252436 4267358106945829685237 := by
  unfold tailWord_252436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603548656737479740768581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6138064875649972987691441 4603548656737479740768581)
  ·
    refine ⟨863165373138277451394109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4603548656737479740768581 863165373138277451394109)
    ·
      refine ⟨323687014926854044272791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 863165373138277451394109 323687014926854044272791)
      ·
        refine ⟨485530522390281066409187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323687014926854044272791 485530522390281066409187)
        ·
          refine ⟨728295783585421599613781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485530522390281066409187 728295783585421599613781)
          ·
            refine ⟨4267358106945829685237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 728295783585421599613781 4267358106945829685237)
            ·
              rfl

theorem cell20_252436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 9].length) (baseStart_252436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252436 prefixEnd_252436 := by exact prefixLift 252436
  have htrace : WordTrace (prefixWord ++ tailWord_252436) baseStart_252436 baseEnd_252436 := by
    simpa [prefixWord, tailWord_252436, baseEnd_252436] using wordTrace_append hprefix tailTrace_252436
  have hstable : (prefixWord ++ tailWord_252436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252436).length < 2 ^ (prefixWord ++ tailWord_252436).sum := by decide
  have hdescent : baseEnd_252436 < baseStart_252436 := by decide
  rcases family_descends (prefixWord ++ tailWord_252436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252439 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_252439 : Nat := 118140960795 + 252439 * 2 ^ 59
def prefixEnd_252439 : Nat := 4983230072969 + 3 ^ 40 * 252439 * 2
def baseEnd_252439 : Nat := 115220038169282724401387

theorem tailTrace_252439 : CollatzResearch.WordTrace tailWord_252439 prefixEnd_252439 115220038169282724401387 := by
  unfold tailWord_252439
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207206732464090993896371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6138137821642727329264247 9207206732464090993896371)
  ·
    refine ⟨13810810098696136490844557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9207206732464090993896371 13810810098696136490844557)
    ·
      refine ⟨5179053787011051184066709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13810810098696136490844557 5179053787011051184066709)
      ·
        refine ⟨242768146266143024253127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5179053787011051184066709 242768146266143024253127)
        ·
          refine ⟨364152219399214536379691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242768146266143024253127 364152219399214536379691)
          ·
            refine ⟨546228329098821804569537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364152219399214536379691 546228329098821804569537)
            ·
              refine ⟨409671246824116353427153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546228329098821804569537 409671246824116353427153)
              ·
                refine ⟨307253435118087265070365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409671246824116353427153 307253435118087265070365)
                ·
                  refine ⟨115220038169282724401387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307253435118087265070365 115220038169282724401387)
                  ·
                    rfl

theorem cell20_252439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_252439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252439 prefixEnd_252439 := by exact prefixLift 252439
  have htrace : WordTrace (prefixWord ++ tailWord_252439) baseStart_252439 baseEnd_252439 := by
    simpa [prefixWord, tailWord_252439, baseEnd_252439] using wordTrace_append hprefix tailTrace_252439
  have hstable : (prefixWord ++ tailWord_252439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252439).length < 2 ^ (prefixWord ++ tailWord_252439).sum := by decide
  have hdescent : baseEnd_252439 < baseStart_252439 := by decide
  rcases family_descends (prefixWord ++ tailWord_252439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252450 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_252450 : Nat := 118140960795 + 252450 * 2 ^ 59
def prefixEnd_252450 : Nat := 4983230072969 + 3 ^ 40 * 252450 * 2
def baseEnd_252450 : Nat := 115225058869015575034675

theorem tailTrace_252450 : CollatzResearch.WordTrace tailWord_252450 prefixEnd_252450 115225058869015575034675 := by
  unfold tailWord_252450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301901983856059968136701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6138405290282826581697869 2301901983856059968136701)
  ·
    refine ⟨863213243946022488051263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2301901983856059968136701 863213243946022488051263)
    ·
      refine ⟨1294819865919033732076895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863213243946022488051263 1294819865919033732076895)
      ·
        refine ⟨1942229798878550598115343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294819865919033732076895 1942229798878550598115343)
        ·
          refine ⟨2913344698317825897173015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942229798878550598115343 2913344698317825897173015)
          ·
            refine ⟨4370017047476738845759523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913344698317825897173015 4370017047476738845759523)
            ·
              refine ⟨6555025571215108268639285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370017047476738845759523 6555025571215108268639285)
              ·
                refine ⟨614533647301416400184933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6555025571215108268639285 614533647301416400184933)
                ·
                  refine ⟨115225058869015575034675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614533647301416400184933 115225058869015575034675)
                  ·
                    rfl

theorem cell20_252450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_252450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252450 prefixEnd_252450 := by exact prefixLift 252450
  have htrace : WordTrace (prefixWord ++ tailWord_252450) baseStart_252450 baseEnd_252450 := by
    simpa [prefixWord, tailWord_252450, baseEnd_252450] using wordTrace_append hprefix tailTrace_252450
  have hstable : (prefixWord ++ tailWord_252450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252450).length < 2 ^ (prefixWord ++ tailWord_252450).sum := by decide
  have hdescent : baseEnd_252450 < baseStart_252450 := by decide
  rcases family_descends (prefixWord ++ tailWord_252450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252474 : List Nat := [3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_252474 : Nat := 118140960795 + 252474 * 2 ^ 59
def prefixEnd_252474 : Nat := 4983230072969 + 3 ^ 40 * 252474 * 2
def baseEnd_252474 : Nat := 38412004374326052744859

theorem tailTrace_252474 : CollatzResearch.WordTrace tailWord_252474 prefixEnd_252474 38412004374326052744859 := by
  unfold tailWord_252474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302120821834322992855119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6138988858224861314280317 2302120821834322992855119)
  ·
    refine ⟨3453181232751484489282679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302120821834322992855119 3453181232751484489282679)
    ·
      refine ⟨5179771849127226733924019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453181232751484489282679 5179771849127226733924019)
      ·
        refine ⟨7769657773690840100886029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179771849127226733924019 7769657773690840100886029)
        ·
          refine ⟨2913621665134065037832261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7769657773690840100886029 2913621665134065037832261)
          ·
            refine ⟨546304062212637194593549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2913621665134065037832261 546304062212637194593549)
            ·
              refine ⟨204864023329738947972581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546304062212637194593549 204864023329738947972581)
              ·
                refine ⟨38412004374326052744859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204864023329738947972581 38412004374326052744859)
                ·
                  rfl

theorem cell20_252474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_252474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252474 prefixEnd_252474 := by exact prefixLift 252474
  have htrace : WordTrace (prefixWord ++ tailWord_252474) baseStart_252474 baseEnd_252474 := by
    simpa [prefixWord, tailWord_252474, baseEnd_252474] using wordTrace_append hprefix tailTrace_252474
  have hstable : (prefixWord ++ tailWord_252474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252474).length < 2 ^ (prefixWord ++ tailWord_252474).sum := by decide
  have hdescent : baseEnd_252474 < baseStart_252474 := by decide
  rcases family_descends (prefixWord ++ tailWord_252474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252540 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_252540 : Nat := 118140960795 + 252540 * 2 ^ 59
def prefixEnd_252540 : Nat := 4983230072969 + 3 ^ 40 * 252540 * 2
def baseEnd_252540 : Nat := 115266137321375262034307

theorem tailTrace_252540 : CollatzResearch.WordTrace tailWord_252540 prefixEnd_252540 115266137321375262034307 := by
  unfold tailWord_252540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605445252549092621661537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6140593670065456828882049 4605445252549092621661537)
  ·
    refine ⟨3454083939411819466246153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4605445252549092621661537 3454083939411819466246153)
    ·
      refine ⟨2590562954558864599684615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3454083939411819466246153 2590562954558864599684615)
      ·
        refine ⟨3885844431838296899526923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590562954558864599684615 3885844431838296899526923)
        ·
          refine ⟨5828766647757445349290385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885844431838296899526923 5828766647757445349290385)
          ·
            refine ⟨4371574985818084011967789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5828766647757445349290385 4371574985818084011967789)
            ·
              refine ⟨1639340619681781504487921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4371574985818084011967789 1639340619681781504487921)
              ·
                refine ⟨1229505464761336128365941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639340619681781504487921 1229505464761336128365941)
                ·
                  refine ⟨115266137321375262034307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1229505464761336128365941 115266137321375262034307)
                  ·
                    rfl

theorem cell20_252540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_252540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252540 prefixEnd_252540 := by exact prefixLift 252540
  have htrace : WordTrace (prefixWord ++ tailWord_252540) baseStart_252540 baseEnd_252540 := by
    simpa [prefixWord, tailWord_252540, baseEnd_252540] using wordTrace_append hprefix tailTrace_252540
  have hstable : (prefixWord ++ tailWord_252540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252540).length < 2 ^ (prefixWord ++ tailWord_252540).sum := by decide
  have hdescent : baseEnd_252540 < baseStart_252540 := by decide
  rcases family_descends (prefixWord ++ tailWord_252540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252547 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_252547 : Nat := 118140960795 + 252547 * 2 ^ 59
def prefixEnd_252547 : Nat := 4983230072969 + 3 ^ 40 * 252547 * 2
def baseEnd_252547 : Nat := 115269332312114348800945

theorem tailTrace_252547 : CollatzResearch.WordTrace tailWord_252547 prefixEnd_252547 115269332312114348800945 := by
  unfold tailWord_252547
  simp only [CollatzResearch.WordTrace]
  refine ⟨9211145816072825438827895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6140763877381883625885263 9211145816072825438827895)
  ·
    refine ⟨13816718724109238158241843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9211145816072825438827895 13816718724109238158241843)
    ·
      refine ⟨20725078086163857237362765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13816718724109238158241843 20725078086163857237362765)
      ·
        refine ⟨7771904282311446464011037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20725078086163857237362765 7771904282311446464011037)
        ·
          refine ⟨2914464105866792424004139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7771904282311446464011037 2914464105866792424004139)
          ·
            refine ⟨4371696158800188636006209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914464105866792424004139 4371696158800188636006209)
            ·
              refine ⟨3278772119100141477004657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371696158800188636006209 3278772119100141477004657)
              ·
                refine ⟨2459079089325106107753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278772119100141477004657 2459079089325106107753493)
                ·
                  refine ⟨115269332312114348800945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2459079089325106107753493 115269332312114348800945)
                  ·
                    rfl

theorem cell20_252547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_252547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252547 prefixEnd_252547 := by exact prefixLift 252547
  have htrace : WordTrace (prefixWord ++ tailWord_252547) baseStart_252547 baseEnd_252547 := by
    simpa [prefixWord, tailWord_252547, baseEnd_252547] using wordTrace_append hprefix tailTrace_252547
  have hstable : (prefixWord ++ tailWord_252547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252547).length < 2 ^ (prefixWord ++ tailWord_252547).sum := by decide
  have hdescent : baseEnd_252547 < baseStart_252547 := by decide
  rcases family_descends (prefixWord ++ tailWord_252547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252570 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_252570 : Nat := 118140960795 + 252570 * 2 ^ 59
def prefixEnd_252570 : Nat := 4983230072969 + 3 ^ 40 * 252570 * 2
def baseEnd_252570 : Nat := 115279830138828491034185

theorem tailTrace_252570 : CollatzResearch.WordTrace tailWord_252570 prefixEnd_252570 115279830138828491034185 := by
  unfold tailWord_252570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302996173747375091728791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6141323129993000244610109 2302996173747375091728791)
  ·
    refine ⟨3454494260621062637593187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302996173747375091728791 3454494260621062637593187)
    ·
      refine ⟨5181741390931593956389781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454494260621062637593187 5181741390931593956389781)
      ·
        refine ⟨242894127699918466705771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5181741390931593956389781 242894127699918466705771)
        ·
          refine ⟨364341191549877700058657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242894127699918466705771 364341191549877700058657)
          ·
            refine ⟨273255893662408275043993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364341191549877700058657 273255893662408275043993)
            ·
              refine ⟨204941920246806206282995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273255893662408275043993 204941920246806206282995)
              ·
                refine ⟨307412880370209309424493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204941920246806206282995 307412880370209309424493)
                ·
                  refine ⟨115279830138828491034185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307412880370209309424493 115279830138828491034185)
                  ·
                    rfl

theorem cell20_252570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_252570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252570 prefixEnd_252570 := by exact prefixLift 252570
  have htrace : WordTrace (prefixWord ++ tailWord_252570) baseStart_252570 baseEnd_252570 := by
    simpa [prefixWord, tailWord_252570, baseEnd_252570] using wordTrace_append hprefix tailTrace_252570
  have hstable : (prefixWord ++ tailWord_252570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252570).length < 2 ^ (prefixWord ++ tailWord_252570).sum := by decide
  have hdescent : baseEnd_252570 < baseStart_252570 := by decide
  rcases family_descends (prefixWord ++ tailWord_252570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252574 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_252574 : Nat := 118140960795 + 252574 * 2 ^ 59
def prefixEnd_252574 : Nat := 4983230072969 + 3 ^ 40 * 252574 * 2
def baseEnd_252574 : Nat := 115281655847822254900835

theorem tailTrace_252574 : CollatzResearch.WordTrace tailWord_252574 prefixEnd_252574 115281655847822254900835 := by
  unfold tailWord_252574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151516323371876131257597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6141420391316672700040517 1151516323371876131257597)
  ·
    refine ⟨431818621264453549221599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1151516323371876131257597 431818621264453549221599)
    ·
      refine ⟨647727931896680323832399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431818621264453549221599 647727931896680323832399)
      ·
        refine ⟨971591897845020485748599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647727931896680323832399 971591897845020485748599)
        ·
          refine ⟨1457387846767530728622899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971591897845020485748599 1457387846767530728622899)
          ·
            refine ⟨2186081770151296092934349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457387846767530728622899 2186081770151296092934349)
            ·
              refine ⟨819780663806736034850381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2186081770151296092934349 819780663806736034850381)
              ·
                refine ⟨307417748927526013068893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819780663806736034850381 307417748927526013068893)
                ·
                  refine ⟨115281655847822254900835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307417748927526013068893 115281655847822254900835)
                  ·
                    rfl

theorem cell20_252574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_252574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252574 prefixEnd_252574 := by exact prefixLift 252574
  have htrace : WordTrace (prefixWord ++ tailWord_252574) baseStart_252574 baseEnd_252574 := by
    simpa [prefixWord, tailWord_252574, baseEnd_252574] using wordTrace_append hprefix tailTrace_252574
  have hstable : (prefixWord ++ tailWord_252574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252574).length < 2 ^ (prefixWord ++ tailWord_252574).sum := by decide
  have hdescent : baseEnd_252574 < baseStart_252574 := by decide
  rcases family_descends (prefixWord ++ tailWord_252574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252612 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_252612 : Nat := 118140960795 + 252612 * 2 ^ 59
def prefixEnd_252612 : Nat := 4983230072969 + 3 ^ 40 * 252612 * 2
def baseEnd_252612 : Nat := 115299000083263011634013

theorem tailTrace_252612 : CollatzResearch.WordTrace tailWord_252612 prefixEnd_252612 115299000083263011634013 := by
  unfold tailWord_252612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606758280418670769972045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6142344373891561026629393 4606758280418670769972045)
  ·
    refine ⟨1727534355157001538739517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4606758280418670769972045 1727534355157001538739517)
    ·
      refine ⟨647825383183875577027319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1727534355157001538739517 647825383183875577027319)
      ·
        refine ⟨971738074775813365540979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647825383183875577027319 971738074775813365540979)
        ·
          refine ⟨1457607112163720048311469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971738074775813365540979 1457607112163720048311469)
          ·
            refine ⟨546602667061395018116801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1457607112163720048311469 546602667061395018116801)
            ·
              refine ⟨409952000296046263587601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546602667061395018116801 409952000296046263587601)
              ·
                refine ⟨307464000222034697690701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409952000296046263587601 307464000222034697690701)
                ·
                  refine ⟨115299000083263011634013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307464000222034697690701 115299000083263011634013)
                  ·
                    rfl

theorem cell20_252612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_252612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252612 prefixEnd_252612 := by exact prefixLift 252612
  have htrace : WordTrace (prefixWord ++ tailWord_252612) baseStart_252612 baseEnd_252612 := by
    simpa [prefixWord, tailWord_252612, baseEnd_252612] using wordTrace_append hprefix tailTrace_252612
  have hstable : (prefixWord ++ tailWord_252612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252612).length < 2 ^ (prefixWord ++ tailWord_252612).sum := by decide
  have hdescent : baseEnd_252612 < baseStart_252612 := by decide
  rcases family_descends (prefixWord ++ tailWord_252612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252657 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 2]
def baseStart_252657 : Nat := 118140960795 + 252657 * 2 ^ 59
def prefixEnd_252657 : Nat := 4983230072969 + 3 ^ 40 * 252657 * 2
def baseEnd_252657 : Nat := 115319539309442855133829

theorem tailTrace_252657 : CollatzResearch.WordTrace tailWord_252657 prefixEnd_252657 115319539309442855133829 := by
  unfold tailWord_252657
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215157845674314225332225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6143438563782876150221483 9215157845674314225332225)
  ·
    refine ⟨6911368384255735668999169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9215157845674314225332225 6911368384255735668999169)
    ·
      refine ⟨5183526288191801751749377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911368384255735668999169 5183526288191801751749377)
      ·
        refine ⟨3887644716143851313812033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5183526288191801751749377 3887644716143851313812033)
        ·
          refine ⟨2915733537107888485359025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3887644716143851313812033 2915733537107888485359025)
          ·
            refine ⟨2186800152830916364019269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915733537107888485359025 2186800152830916364019269)
            ·
              refine ⟨410025028655796818253613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2186800152830916364019269 410025028655796818253613)
              ·
                refine ⟨153759385745923806845105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410025028655796818253613 153759385745923806845105)
                ·
                  refine ⟨115319539309442855133829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153759385745923806845105 115319539309442855133829)
                  ·
                    rfl

theorem cell20_252657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_252657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252657 prefixEnd_252657 := by exact prefixLift 252657
  have htrace : WordTrace (prefixWord ++ tailWord_252657) baseStart_252657 baseEnd_252657 := by
    simpa [prefixWord, tailWord_252657, baseEnd_252657] using wordTrace_append hprefix tailTrace_252657
  have hstable : (prefixWord ++ tailWord_252657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252657).length < 2 ^ (prefixWord ++ tailWord_252657).sum := by decide
  have hdescent : baseEnd_252657 < baseStart_252657 := by decide
  rcases family_descends (prefixWord ++ tailWord_252657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252674 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_252674 : Nat := 118140960795 + 252674 * 2 ^ 59
def prefixEnd_252674 : Nat := 4983230072969 + 3 ^ 40 * 252674 * 2
def baseEnd_252674 : Nat := 115327298572666351567093

theorem tailTrace_252674 : CollatzResearch.WordTrace tailWord_252674 prefixEnd_252674 115327298572666351567093 := by
  unfold tailWord_252674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303944471653181532175269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6143851924408484085800717 2303944471653181532175269)
  ·
    refine ⟨431989588434971537282863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2303944471653181532175269 431989588434971537282863)
    ·
      refine ⟨647984382652457305924295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431989588434971537282863 647984382652457305924295)
      ·
        refine ⟨971976573978685958886443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647984382652457305924295 971976573978685958886443)
        ·
          refine ⟨1457964860968028938329665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971976573978685958886443 1457964860968028938329665)
          ·
            refine ⟨1093473645726021703747249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457964860968028938329665 1093473645726021703747249)
            ·
              refine ⟨820105234294516277810437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093473645726021703747249 820105234294516277810437)
              ·
                refine ⟨153769731430221802089457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820105234294516277810437 153769731430221802089457)
                ·
                  refine ⟨115327298572666351567093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153769731430221802089457 115327298572666351567093)
                  ·
                    rfl

theorem cell20_252674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_252674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252674 prefixEnd_252674 := by exact prefixLift 252674
  have htrace : WordTrace (prefixWord ++ tailWord_252674) baseStart_252674 baseEnd_252674 := by
    simpa [prefixWord, tailWord_252674, baseEnd_252674] using wordTrace_append hprefix tailTrace_252674
  have hstable : (prefixWord ++ tailWord_252674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252674).length < 2 ^ (prefixWord ++ tailWord_252674).sum := by decide
  have hdescent : baseEnd_252674 < baseStart_252674 := by decide
  rcases family_descends (prefixWord ++ tailWord_252674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252723 : List Nat := [1, 1, 1, 2, 6, 3, 6]
def baseStart_252723 : Nat := 118140960795 + 252723 * 2 ^ 59
def prefixEnd_252723 : Nat := 4983230072969 + 3 ^ 40 * 252723 * 2
def baseEnd_252723 : Nat := 12816629278648884325951

theorem tailTrace_252723 : CollatzResearch.WordTrace tailWord_252723 prefixEnd_252723 12816629278648884325951 := by
  unfold tailWord_252723
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217565063435207497234823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6145043375623471664823215 9217565063435207497234823)
  ·
    refine ⟨13826347595152811245852235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9217565063435207497234823 13826347595152811245852235)
    ·
      refine ⟨20739521392729216868778353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13826347595152811245852235 20739521392729216868778353)
      ·
        refine ⟨15554641044546912651583765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20739521392729216868778353 15554641044546912651583765)
        ·
          refine ⟨729123798963136530542989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15554641044546912651583765 729123798963136530542989)
          ·
            refine ⟨273421424611176198953621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729123798963136530542989 273421424611176198953621)
            ·
              refine ⟨12816629278648884325951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 273421424611176198953621 12816629278648884325951)
              ·
                rfl

theorem cell20_252723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_252723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252723 prefixEnd_252723 := by exact prefixLift 252723
  have htrace : WordTrace (prefixWord ++ tailWord_252723) baseStart_252723 baseEnd_252723 := by
    simpa [prefixWord, tailWord_252723, baseEnd_252723] using wordTrace_append hprefix tailTrace_252723
  have hstable : (prefixWord ++ tailWord_252723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252723).length < 2 ^ (prefixWord ++ tailWord_252723).sum := by decide
  have hdescent : baseEnd_252723 < baseStart_252723 := by decide
  rcases family_descends (prefixWord ++ tailWord_252723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252785 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_252785 : Nat := 118140960795 + 252785 * 2 ^ 59
def prefixEnd_252785 : Nat := 4983230072969 + 3 ^ 40 * 252785 * 2
def baseEnd_252785 : Nat := 115377961997243298866639

theorem tailTrace_252785 : CollatzResearch.WordTrace tailWord_252785 prefixEnd_252785 115377961997243298866639 := by
  unfold tailWord_252785
  simp only [CollatzResearch.WordTrace]
  refine ⟨9219826389210592085991809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6146550926140394723994539 9219826389210592085991809)
  ·
    refine ⟨6914869791907944064493857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9219826389210592085991809 6914869791907944064493857)
    ·
      refine ⟨5186152343930958048370393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6914869791907944064493857 5186152343930958048370393)
      ·
        refine ⟨3889614257948218536277795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5186152343930958048370393 3889614257948218536277795)
        ·
          refine ⟨5834421386922327804416693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889614257948218536277795 5834421386922327804416693)
          ·
            refine ⟨546977005023968231664065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5834421386922327804416693 546977005023968231664065)
            ·
              refine ⟨410232753767976173748049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546977005023968231664065 410232753767976173748049)
              ·
                refine ⟨307674565325982130311037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410232753767976173748049 307674565325982130311037)
                ·
                  refine ⟨115377961997243298866639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307674565325982130311037 115377961997243298866639)
                  ·
                    rfl

theorem cell20_252785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_252785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252785 prefixEnd_252785 := by exact prefixLift 252785
  have htrace : WordTrace (prefixWord ++ tailWord_252785) baseStart_252785 baseEnd_252785 := by
    simpa [prefixWord, tailWord_252785, baseEnd_252785] using wordTrace_append hprefix tailTrace_252785
  have hstable : (prefixWord ++ tailWord_252785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252785).length < 2 ^ (prefixWord ++ tailWord_252785).sum := by decide
  have hdescent : baseEnd_252785 < baseStart_252785 := by decide
  rcases family_descends (prefixWord ++ tailWord_252785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252822 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_252822 : Nat := 118140960795 + 252822 * 2 ^ 59
def prefixEnd_252822 : Nat := 4983230072969 + 3 ^ 40 * 252822 * 2
def baseEnd_252822 : Nat := 115394849805435614633155

theorem tailTrace_252822 : CollatzResearch.WordTrace tailWord_252822 prefixEnd_252822 115394849805435614633155 := by
  unfold tailWord_252822
  simp only [CollatzResearch.WordTrace]
  refine ⟨576323493129784212818045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6147450593384364936725813 576323493129784212818045)
  ·
    refine ⟨216121309923669079806767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 576323493129784212818045 216121309923669079806767)
    ·
      refine ⟨324181964885503619710151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216121309923669079806767 324181964885503619710151)
      ·
        refine ⟨486272947328255429565227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324181964885503619710151 486272947328255429565227)
        ·
          refine ⟨729409420992383144347841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486272947328255429565227 729409420992383144347841)
          ·
            refine ⟨547057065744287358260881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729409420992383144347841 547057065744287358260881)
            ·
              refine ⟨410292799308215518695661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547057065744287358260881 410292799308215518695661)
              ·
                refine ⟨153859799740580819510873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410292799308215518695661 153859799740580819510873)
                ·
                  refine ⟨115394849805435614633155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153859799740580819510873 115394849805435614633155)
                  ·
                    rfl

theorem cell20_252822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_252822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252822 prefixEnd_252822 := by exact prefixLift 252822
  have htrace : WordTrace (prefixWord ++ tailWord_252822) baseStart_252822 baseEnd_252822 := by
    simpa [prefixWord, tailWord_252822, baseEnd_252822] using wordTrace_append hprefix tailTrace_252822
  have hstable : (prefixWord ++ tailWord_252822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252822).length < 2 ^ (prefixWord ++ tailWord_252822).sum := by decide
  have hdescent : baseEnd_252822 < baseStart_252822 := by decide
  rcases family_descends (prefixWord ++ tailWord_252822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252826 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_252826 : Nat := 118140960795 + 252826 * 2 ^ 59
def prefixEnd_252826 : Nat := 4983230072969 + 3 ^ 40 * 252826 * 2
def baseEnd_252826 : Nat := 115396675514429378499805

theorem tailTrace_252826 : CollatzResearch.WordTrace tailWord_252826 prefixEnd_252826 115396675514429378499805 := by
  unfold tailWord_252826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305330445515514022058583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6147547854708037392156221 2305330445515514022058583)
  ·
    refine ⟨3457995668273271033087875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305330445515514022058583 3457995668273271033087875)
    ·
      refine ⟨5186993502409906549631813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457995668273271033087875 5186993502409906549631813)
      ·
        refine ⟨972561281701857478055965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5186993502409906549631813 972561281701857478055965)
        ·
          refine ⟨364710480638196554270987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972561281701857478055965 364710480638196554270987)
          ·
            refine ⟨547065720957294831406481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364710480638196554270987 547065720957294831406481)
            ·
              refine ⟨410299290717971123554861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547065720957294831406481 410299290717971123554861)
              ·
                refine ⟨153862234019239171333073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410299290717971123554861 153862234019239171333073)
                ·
                  refine ⟨115396675514429378499805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153862234019239171333073 115396675514429378499805)
                  ·
                    rfl

theorem cell20_252826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_252826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252826 prefixEnd_252826 := by exact prefixLift 252826
  have htrace : WordTrace (prefixWord ++ tailWord_252826) baseStart_252826 baseEnd_252826 := by
    simpa [prefixWord, tailWord_252826, baseEnd_252826] using wordTrace_append hprefix tailTrace_252826
  have hstable : (prefixWord ++ tailWord_252826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252826).length < 2 ^ (prefixWord ++ tailWord_252826).sum := by decide
  have hdescent : baseEnd_252826 < baseStart_252826 := by decide
  rcases family_descends (prefixWord ++ tailWord_252826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252858 : List Nat := [3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_252858 : Nat := 118140960795 + 252858 * 2 ^ 59
def prefixEnd_252858 : Nat := 4983230072969 + 3 ^ 40 * 252858 * 2
def baseEnd_252858 : Nat := 38470427062126496477669

theorem tailTrace_252858 : CollatzResearch.WordTrace tailWord_252858 prefixEnd_252858 38470427062126496477669 := by
  unfold tailWord_252858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305622229486531388349807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6148325945297417035599485 2305622229486531388349807)
  ·
    refine ⟨3458433344229797082524711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305622229486531388349807 3458433344229797082524711)
    ·
      refine ⟨5187650016344695623787067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458433344229797082524711 5187650016344695623787067)
      ·
        refine ⟨7781475024517043435680601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187650016344695623787067 7781475024517043435680601)
        ·
          refine ⟨5836106268387782576760451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7781475024517043435680601 5836106268387782576760451)
          ·
            refine ⟨8754159402581673865140677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836106268387782576760451 8754159402581673865140677)
            ·
              refine ⟨1641404887984063849713877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8754159402581673865140677 1641404887984063849713877)
              ·
                refine ⟨38470427062126496477669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1641404887984063849713877 38470427062126496477669)
                ·
                  rfl

theorem cell20_252858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_252858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252858 prefixEnd_252858 := by exact prefixLift 252858
  have htrace : WordTrace (prefixWord ++ tailWord_252858) baseStart_252858 baseEnd_252858 := by
    simpa [prefixWord, tailWord_252858, baseEnd_252858] using wordTrace_append hprefix tailTrace_252858
  have hstable : (prefixWord ++ tailWord_252858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252858).length < 2 ^ (prefixWord ++ tailWord_252858).sum := by decide
  have hdescent : baseEnd_252858 < baseStart_252858 := by decide
  rcases family_descends (prefixWord ++ tailWord_252858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252875 : List Nat := [1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_252875 : Nat := 118140960795 + 252875 * 2 ^ 59
def prefixEnd_252875 : Nat := 4983230072969 + 3 ^ 40 * 252875 * 2
def baseEnd_252875 : Nat := 38473013483200995288757

theorem tailTrace_252875 : CollatzResearch.WordTrace tailWord_252875 prefixEnd_252875 38473013483200995288757 := by
  unfold tailWord_252875
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223108958884537456768079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6148739305923024971178719 9223108958884537456768079)
  ·
    refine ⟨13834663438326806185152119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9223108958884537456768079 13834663438326806185152119)
    ·
      refine ⟨20751995157490209277728179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13834663438326806185152119 20751995157490209277728179)
      ·
        refine ⟨31127992736235313916592269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20751995157490209277728179 31127992736235313916592269)
        ·
          refine ⟨11672997276088242718722101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31127992736235313916592269 11672997276088242718722101)
          ·
            refine ⟨1094343494633272754880197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11672997276088242718722101 1094343494633272754880197)
            ·
              refine ⟨205189405243738641540037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1094343494633272754880197 205189405243738641540037)
              ·
                refine ⟨38473013483200995288757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205189405243738641540037 38473013483200995288757)
                ·
                  rfl

theorem cell20_252875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_252875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252875 prefixEnd_252875 := by exact prefixLift 252875
  have htrace : WordTrace (prefixWord ++ tailWord_252875) baseStart_252875 baseEnd_252875 := by
    simpa [prefixWord, tailWord_252875, baseEnd_252875] using wordTrace_append hprefix tailTrace_252875
  have hstable : (prefixWord ++ tailWord_252875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252875).length < 2 ^ (prefixWord ++ tailWord_252875).sum := by decide
  have hdescent : baseEnd_252875 < baseStart_252875 := by decide
  rcases family_descends (prefixWord ++ tailWord_252875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252877 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 2]
def baseStart_252877 : Nat := 118140960795 + 252877 * 2 ^ 59
def prefixEnd_252877 : Nat := 4983230072969 + 3 ^ 40 * 252877 * 2
def baseEnd_252877 : Nat := 115419953304099867799597

theorem tailTrace_252877 : CollatzResearch.WordTrace tailWord_252877 prefixEnd_252877 115419953304099867799597 := by
  unfold tailWord_252877
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223181904877291798340885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6148787936584861198893923 9223181904877291798340885)
  ·
    refine ⟨432336651791123053047229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9223181904877291798340885 432336651791123053047229)
    ·
      refine ⟨162126244421671144892711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432336651791123053047229 162126244421671144892711)
      ·
        refine ⟨243189366632506717339067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162126244421671144892711 243189366632506717339067)
        ·
          refine ⟨364784049948760076008601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243189366632506717339067 364784049948760076008601)
          ·
            refine ⟨273588037461570057006451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364784049948760076008601 273588037461570057006451)
            ·
              refine ⟨410382056192355085509677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273588037461570057006451 410382056192355085509677)
              ·
                refine ⟨153893271072133157066129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410382056192355085509677 153893271072133157066129)
                ·
                  refine ⟨115419953304099867799597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153893271072133157066129 115419953304099867799597)
                  ·
                    rfl

theorem cell20_252877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_252877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252877 prefixEnd_252877 := by exact prefixLift 252877
  have htrace : WordTrace (prefixWord ++ tailWord_252877) baseStart_252877 baseEnd_252877 := by
    simpa [prefixWord, tailWord_252877, baseEnd_252877] using wordTrace_append hprefix tailTrace_252877
  have hstable : (prefixWord ++ tailWord_252877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252877).length < 2 ^ (prefixWord ++ tailWord_252877).sum := by decide
  have hdescent : baseEnd_252877 < baseStart_252877 := by decide
  rcases family_descends (prefixWord ++ tailWord_252877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252906 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_252906 : Nat := 118140960795 + 252906 * 2 ^ 59
def prefixEnd_252906 : Nat := 4983230072969 + 3 ^ 40 * 252906 * 2
def baseEnd_252906 : Nat := 115433189694304655832811

theorem tailTrace_252906 : CollatzResearch.WordTrace tailWord_252906 prefixEnd_252906 115433189694304655832811 := by
  unfold tailWord_252906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306059905443057437786643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6149493081181486500764381 2306059905443057437786643)
  ·
    refine ⟨3459089858164586156679965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2306059905443057437786643 3459089858164586156679965)
    ·
      refine ⟨1297158696811719808754987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3459089858164586156679965 1297158696811719808754987)
      ·
        refine ⟨1945738045217579713132481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297158696811719808754987 1945738045217579713132481)
        ·
          refine ⟨1459303533913184784849361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945738045217579713132481 1459303533913184784849361)
          ·
            refine ⟨1094477650434888588637021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459303533913184784849361 1094477650434888588637021)
            ·
              refine ⟨410429118913083220738883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1094477650434888588637021 410429118913083220738883)
              ·
                refine ⟨615643678369624831108325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410429118913083220738883 615643678369624831108325)
                ·
                  refine ⟨115433189694304655832811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615643678369624831108325 115433189694304655832811)
                  ·
                    rfl

theorem cell20_252906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_252906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252906 prefixEnd_252906 := by exact prefixLift 252906
  have htrace : WordTrace (prefixWord ++ tailWord_252906) baseStart_252906 baseEnd_252906 := by
    simpa [prefixWord, tailWord_252906, baseEnd_252906] using wordTrace_append hprefix tailTrace_252906
  have hstable : (prefixWord ++ tailWord_252906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252906).length < 2 ^ (prefixWord ++ tailWord_252906).sum := by decide
  have hdescent : baseEnd_252906 < baseStart_252906 := by decide
  rcases family_descends (prefixWord ++ tailWord_252906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252913 : List Nat := [1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_252913 : Nat := 118140960795 + 252913 * 2 ^ 59
def prefixEnd_252913 : Nat := 4983230072969 + 3 ^ 40 * 252913 * 2
def baseEnd_252913 : Nat := 38478794895014580866483

theorem tailTrace_252913 : CollatzResearch.WordTrace tailWord_252913 prefixEnd_252913 38478794895014580866483 := by
  unfold tailWord_252913
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224494932746869946651393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6149663288497913297767595 9224494932746869946651393)
  ·
    refine ⟨6918371199560152459988545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9224494932746869946651393 6918371199560152459988545)
    ·
      refine ⟨5188778399670114344991409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6918371199560152459988545 5188778399670114344991409)
      ·
        refine ⟨3891583799752585758743557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5188778399670114344991409 3891583799752585758743557)
        ·
          refine ⟨729671962453609829764417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3891583799752585758743557 729671962453609829764417)
          ·
            refine ⟨547253971840207372323313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729671962453609829764417 547253971840207372323313)
            ·
              refine ⟨410440478880155529242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547253971840207372323313 410440478880155529242485)
              ·
                refine ⟨38478794895014580866483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410440478880155529242485 38478794895014580866483)
                ·
                  rfl

theorem cell20_252913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_252913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252913 prefixEnd_252913 := by exact prefixLift 252913
  have htrace : WordTrace (prefixWord ++ tailWord_252913) baseStart_252913 baseEnd_252913 := by
    simpa [prefixWord, tailWord_252913, baseEnd_252913] using wordTrace_append hprefix tailTrace_252913
  have hstable : (prefixWord ++ tailWord_252913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252913).length < 2 ^ (prefixWord ++ tailWord_252913).sum := by decide
  have hdescent : baseEnd_252913 < baseStart_252913 := by decide
  rcases family_descends (prefixWord ++ tailWord_252913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252957 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 2]
def baseStart_252957 : Nat := 118140960795 + 252957 * 2 ^ 59
def prefixEnd_252957 : Nat := 4983230072969 + 3 ^ 40 * 252957 * 2
def baseEnd_252957 : Nat := 115456467483975145132603

theorem tailTrace_252957 : CollatzResearch.WordTrace tailWord_252957 prefixEnd_252957 115456467483975145132603 := by
  unfold tailWord_252957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226099744587465461253125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6150733163058310307502083 9226099744587465461253125)
  ·
    refine ⟨1729893702110149773984961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9226099744587465461253125 1729893702110149773984961)
    ·
      refine ⟨1297420276582612330488721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1729893702110149773984961 1297420276582612330488721)
      ·
        refine ⟨973065207436959247866541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1297420276582612330488721 973065207436959247866541)
        ·
          refine ⟨364899452788859717949953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 973065207436959247866541 364899452788859717949953)
          ·
            refine ⟨273674589591644788462465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364899452788859717949953 273674589591644788462465)
            ·
              refine ⟨205255942193733591346849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273674589591644788462465 205255942193733591346849)
              ·
                refine ⟨153941956645300193510137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205255942193733591346849 153941956645300193510137)
                ·
                  refine ⟨115456467483975145132603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153941956645300193510137 115456467483975145132603)
                  ·
                    rfl

theorem cell20_252957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_252957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252957 prefixEnd_252957 := by exact prefixLift 252957
  have htrace : WordTrace (prefixWord ++ tailWord_252957) baseStart_252957 baseEnd_252957 := by
    simpa [prefixWord, tailWord_252957, baseEnd_252957] using wordTrace_append hprefix tailTrace_252957
  have hstable : (prefixWord ++ tailWord_252957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252957).length < 2 ^ (prefixWord ++ tailWord_252957).sum := by decide
  have hdescent : baseEnd_252957 < baseStart_252957 := by decide
  rcases family_descends (prefixWord ++ tailWord_252957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252961 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 2]
def baseStart_252961 : Nat := 118140960795 + 252961 * 2 ^ 59
def prefixEnd_252961 : Nat := 4983230072969 + 3 ^ 40 * 252961 * 2
def baseEnd_252961 : Nat := 115458293192968908999253

theorem tailTrace_252961 : CollatzResearch.WordTrace tailWord_252961 prefixEnd_252961 115458293192968908999253 := by
  unfold tailWord_252961
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226245636572974144398737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6150830424381982762932491 9226245636572974144398737)
  ·
    refine ⟨6919684227429730608299053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9226245636572974144398737 6919684227429730608299053)
    ·
      refine ⟨2594881585286148978112145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6919684227429730608299053 2594881585286148978112145)
      ·
        refine ⟨1946161188964611733584109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594881585286148978112145 1946161188964611733584109)
        ·
          refine ⟨729810445861729400094041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1946161188964611733584109 729810445861729400094041)
          ·
            refine ⟨547357834396297050070531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729810445861729400094041 547357834396297050070531)
            ·
              refine ⟨821036751594445575105797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547357834396297050070531 821036751594445575105797)
              ·
                refine ⟨153944390923958545332337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821036751594445575105797 153944390923958545332337)
                ·
                  refine ⟨115458293192968908999253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153944390923958545332337 115458293192968908999253)
                  ·
                    rfl

theorem cell20_252961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_252961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252961 prefixEnd_252961 := by exact prefixLift 252961
  have htrace : WordTrace (prefixWord ++ tailWord_252961) baseStart_252961 baseEnd_252961 := by
    simpa [prefixWord, tailWord_252961, baseEnd_252961] using wordTrace_append hprefix tailTrace_252961
  have hstable : (prefixWord ++ tailWord_252961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252961).length < 2 ^ (prefixWord ++ tailWord_252961).sum := by decide
  have hdescent : baseEnd_252961 < baseStart_252961 := by decide
  rcases family_descends (prefixWord ++ tailWord_252961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252965 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_252965 : Nat := 118140960795 + 252965 * 2 ^ 59
def prefixEnd_252965 : Nat := 4983230072969 + 3 ^ 40 * 252965 * 2
def baseEnd_252965 : Nat := 115460118901962672865903

theorem tailTrace_252965 : CollatzResearch.WordTrace tailWord_252965 prefixEnd_252965 115460118901962672865903 := by
  unfold tailWord_252965
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226391528558482827544349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6150927685705655218362899 9226391528558482827544349)
  ·
    refine ⟨3459896823209431060329131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9226391528558482827544349 3459896823209431060329131)
    ·
      refine ⟨5189845234814146590493697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459896823209431060329131 5189845234814146590493697)
      ·
        refine ⟨3892383926110609942870273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189845234814146590493697 3892383926110609942870273)
        ·
          refine ⟨2919287944582957457152705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3892383926110609942870273 2919287944582957457152705)
          ·
            refine ⟨2189465958437218092864529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919287944582957457152705 2189465958437218092864529)
            ·
              refine ⟨1642099468827913569648397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189465958437218092864529 1642099468827913569648397)
              ·
                refine ⟨615787300810467588618149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642099468827913569648397 615787300810467588618149)
                ·
                  refine ⟨115460118901962672865903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615787300810467588618149 115460118901962672865903)
                  ·
                    rfl

theorem cell20_252965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_252965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252965 prefixEnd_252965 := by exact prefixLift 252965
  have htrace : WordTrace (prefixWord ++ tailWord_252965) baseStart_252965 baseEnd_252965 := by
    simpa [prefixWord, tailWord_252965, baseEnd_252965] using wordTrace_append hprefix tailTrace_252965
  have hstable : (prefixWord ++ tailWord_252965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252965).length < 2 ^ (prefixWord ++ tailWord_252965).sum := by decide
  have hdescent : baseEnd_252965 < baseStart_252965 := by decide
  rcases family_descends (prefixWord ++ tailWord_252965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252979 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_252979 : Nat := 118140960795 + 252979 * 2 ^ 59
def prefixEnd_252979 : Nat := 4983230072969 + 3 ^ 40 * 252979 * 2
def baseEnd_252979 : Nat := 115466508883440846399179

theorem tailTrace_252979 : CollatzResearch.WordTrace tailWord_252979 prefixEnd_252979 115466508883440846399179 := by
  unfold tailWord_252979
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226902150507763218553991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6151268100338508812369327 9226902150507763218553991)
  ·
    refine ⟨13840353225761644827830987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226902150507763218553991 13840353225761644827830987)
    ·
      refine ⟨20760529838642467241746481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840353225761644827830987 20760529838642467241746481)
      ·
        refine ⟨15570397378981850431309861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20760529838642467241746481 15570397378981850431309861)
        ·
          refine ⟨2919449508559096955870599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15570397378981850431309861 2919449508559096955870599)
          ·
            refine ⟨4379174262838645433805899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919449508559096955870599 4379174262838645433805899)
            ·
              refine ⟨6568761394257968150708849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379174262838645433805899 6568761394257968150708849)
              ·
                refine ⟨4926571045693476113031637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568761394257968150708849 4926571045693476113031637)
                ·
                  refine ⟨115466508883440846399179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4926571045693476113031637 115466508883440846399179)
                  ·
                    rfl

theorem cell20_252979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_252979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252979 prefixEnd_252979 := by exact prefixLift 252979
  have htrace : WordTrace (prefixWord ++ tailWord_252979) baseStart_252979 baseEnd_252979 := by
    simpa [prefixWord, tailWord_252979, baseEnd_252979] using wordTrace_append hprefix tailTrace_252979
  have hstable : (prefixWord ++ tailWord_252979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252979).length < 2 ^ (prefixWord ++ tailWord_252979).sum := by decide
  have hdescent : baseEnd_252979 < baseStart_252979 := by decide
  rcases family_descends (prefixWord ++ tailWord_252979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252982 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_252982 : Nat := 118140960795 + 252982 * 2 ^ 59
def prefixEnd_252982 : Nat := 4983230072969 + 3 ^ 40 * 252982 * 2
def baseEnd_252982 : Nat := 115467878165186169299167

theorem tailTrace_252982 : CollatzResearch.WordTrace tailWord_252982 prefixEnd_252982 115467878165186169299167 := by
  unfold tailWord_252982
  simp only [CollatzResearch.WordTrace]
  refine ⟨576688223093555920682075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6151341046331263153942133 576688223093555920682075)
  ·
    refine ⟨865032334640333881023113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 576688223093555920682075 865032334640333881023113)
    ·
      refine ⟨648774250980250410767335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865032334640333881023113 648774250980250410767335)
      ·
        refine ⟨973161376470375616151003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648774250980250410767335 973161376470375616151003)
        ·
          refine ⟨1459742064705563424226505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973161376470375616151003 1459742064705563424226505)
          ·
            refine ⟨1094806548529172568169879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459742064705563424226505 1094806548529172568169879)
            ·
              refine ⟨1642209822793758852254819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094806548529172568169879 1642209822793758852254819)
              ·
                refine ⟨2463314734190638278382229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642209822793758852254819 2463314734190638278382229)
                ·
                  refine ⟨115467878165186169299167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2463314734190638278382229 115467878165186169299167)
                  ·
                    rfl

theorem cell20_252982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_252982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252982 prefixEnd_252982 := by exact prefixLift 252982
  have htrace : WordTrace (prefixWord ++ tailWord_252982) baseStart_252982 baseEnd_252982 := by
    simpa [prefixWord, tailWord_252982, baseEnd_252982] using wordTrace_append hprefix tailTrace_252982
  have hstable : (prefixWord ++ tailWord_252982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252982).length < 2 ^ (prefixWord ++ tailWord_252982).sum := by decide
  have hdescent : baseEnd_252982 < baseStart_252982 := by decide
  rcases family_descends (prefixWord ++ tailWord_252982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252999 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 2]
def baseStart_252999 : Nat := 118140960795 + 252999 * 2 ^ 59
def prefixEnd_252999 : Nat := 4983230072969 + 3 ^ 40 * 252999 * 2
def baseEnd_252999 : Nat := 115475637428409665732431

theorem tailTrace_252999 : CollatzResearch.WordTrace tailWord_252999 prefixEnd_252999 115475637428409665732431 := by
  unfold tailWord_252999
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227631610435306634282051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6151754406956871089521367 9227631610435306634282051)
  ·
    refine ⟨13841447415652959951423077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9227631610435306634282051 13841447415652959951423077)
    ·
      refine ⟨2595271390434929990891827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13841447415652959951423077 2595271390434929990891827)
      ·
        refine ⟨3892907085652394986337741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595271390434929990891827 3892907085652394986337741)
        ·
          refine ⟨1459840157119648119876653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3892907085652394986337741 1459840157119648119876653)
          ·
            refine ⟨547440058919868044953745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1459840157119648119876653 547440058919868044953745)
            ·
              refine ⟨410580044189901033715309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547440058919868044953745 410580044189901033715309)
              ·
                refine ⟨153967516571212887643241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410580044189901033715309 153967516571212887643241)
                ·
                  refine ⟨115475637428409665732431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153967516571212887643241 115475637428409665732431)
                  ·
                    rfl

theorem cell20_252999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2].length) (baseStart_252999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_252999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_252999 prefixEnd_252999 := by exact prefixLift 252999
  have htrace : WordTrace (prefixWord ++ tailWord_252999) baseStart_252999 baseEnd_252999 := by
    simpa [prefixWord, tailWord_252999, baseEnd_252999] using wordTrace_append hprefix tailTrace_252999
  have hstable : (prefixWord ++ tailWord_252999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252999).length < 2 ^ (prefixWord ++ tailWord_252999).sum := by decide
  have hdescent : baseEnd_252999 < baseStart_252999 := by decide
  rcases family_descends (prefixWord ++ tailWord_252999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253020 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_253020 : Nat := 118140960795 + 253020 * 2 ^ 59
def prefixEnd_253020 : Nat := 4983230072969 + 3 ^ 40 * 253020 * 2
def baseEnd_253020 : Nat := 115485222400626926032345

theorem tailTrace_253020 : CollatzResearch.WordTrace tailWord_253020 prefixEnd_253020 115485222400626926032345 := by
  unfold tailWord_253020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614198771679613610398257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6152265028906151480531009 4614198771679613610398257)
  ·
    refine ⟨3460649078759710207798693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4614198771679613610398257 3460649078759710207798693)
    ·
      refine ⟨648871702267445663962255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3460649078759710207798693 648871702267445663962255)
      ·
        refine ⟨973307553401168495943383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648871702267445663962255 973307553401168495943383)
        ·
          refine ⟨1459961330101752743915075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973307553401168495943383 1459961330101752743915075)
          ·
            refine ⟨2189941995152629115872613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459961330101752743915075 2189941995152629115872613)
            ·
              refine ⟨410614124091117959226115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2189941995152629115872613 410614124091117959226115)
              ·
                refine ⟨615921186136676938839173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410614124091117959226115 615921186136676938839173)
                ·
                  refine ⟨115485222400626926032345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615921186136676938839173 115485222400626926032345)
                  ·
                    rfl

theorem cell20_253020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_253020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253020 prefixEnd_253020 := by exact prefixLift 253020
  have htrace : WordTrace (prefixWord ++ tailWord_253020) baseStart_253020 baseEnd_253020 := by
    simpa [prefixWord, tailWord_253020, baseEnd_253020] using wordTrace_append hprefix tailTrace_253020
  have hstable : (prefixWord ++ tailWord_253020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253020).length < 2 ^ (prefixWord ++ tailWord_253020).sum := by decide
  have hdescent : baseEnd_253020 < baseStart_253020 := by decide
  rcases family_descends (prefixWord ++ tailWord_253020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253124 : List Nat := [2, 3, 3, 1, 11]
def baseStart_253124 : Nat := 118140960795 + 253124 * 2 ^ 59
def prefixEnd_253124 : Nat := 4983230072969 + 3 ^ 40 * 253124 * 2
def baseEnd_253124 : Nat := 1426329516474873908213

theorem tailTrace_253124 : CollatzResearch.WordTrace tailWord_253124 prefixEnd_253124 1426329516474873908213 := by
  unfold tailWord_253124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616095367491226491291213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6154793823321635321721617 4616095367491226491291213)
  ·
    refine ⟨1731035762809209934234205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4616095367491226491291213 1731035762809209934234205)
    ·
      refine ⟨649138411053453725337827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1731035762809209934234205 649138411053453725337827)
      ·
        refine ⟨973707616580180588006741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649138411053453725337827 973707616580180588006741)
        ·
          refine ⟨1426329516474873908213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 973707616580180588006741 1426329516474873908213)
          ·
            rfl

theorem cell20_253124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 11].length) (baseStart_253124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253124 prefixEnd_253124 := by exact prefixLift 253124
  have htrace : WordTrace (prefixWord ++ tailWord_253124) baseStart_253124 baseEnd_253124 := by
    simpa [prefixWord, tailWord_253124, baseEnd_253124] using wordTrace_append hprefix tailTrace_253124
  have hstable : (prefixWord ++ tailWord_253124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253124).length < 2 ^ (prefixWord ++ tailWord_253124).sum := by decide
  have hdescent : baseEnd_253124 < baseStart_253124 := by decide
  rcases family_descends (prefixWord ++ tailWord_253124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253126 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_253126 : Nat := 118140960795 + 253126 * 2 ^ 59
def prefixEnd_253126 : Nat := 4983230072969 + 3 ^ 40 * 253126 * 2
def baseEnd_253126 : Nat := 115533603688961668498579

theorem tailTrace_253126 : CollatzResearch.WordTrace tailWord_253126 prefixEnd_253126 115533603688961668498579 := by
  unfold tailWord_253126
  simp only [CollatzResearch.WordTrace]
  refine ⟨288508240030475228879851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6154842453983471549436821 288508240030475228879851)
  ·
    refine ⟨432762360045712843319777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288508240030475228879851 432762360045712843319777)
    ·
      refine ⟨324571770034284632489833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432762360045712843319777 324571770034284632489833)
      ·
        refine ⟨243428827525713474367375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324571770034284632489833 243428827525713474367375)
        ·
          refine ⟨365143241288570211551063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243428827525713474367375 365143241288570211551063)
          ·
            refine ⟨547714861932855317326595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365143241288570211551063 547714861932855317326595)
            ·
              refine ⟨821572292899282975989893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547714861932855317326595 821572292899282975989893)
              ·
                refine ⟨154044804918615557998105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821572292899282975989893 154044804918615557998105)
                ·
                  refine ⟨115533603688961668498579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154044804918615557998105 115533603688961668498579)
                  ·
                    rfl

theorem cell20_253126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_253126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253126 prefixEnd_253126 := by exact prefixLift 253126
  have htrace : WordTrace (prefixWord ++ tailWord_253126) baseStart_253126 baseEnd_253126 := by
    simpa [prefixWord, tailWord_253126, baseEnd_253126] using wordTrace_append hprefix tailTrace_253126
  have hstable : (prefixWord ++ tailWord_253126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253126).length < 2 ^ (prefixWord ++ tailWord_253126).sum := by decide
  have hdescent : baseEnd_253126 < baseStart_253126 := by decide
  rcases family_descends (prefixWord ++ tailWord_253126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253130 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_253130 : Nat := 118140960795 + 253130 * 2 ^ 59
def prefixEnd_253130 : Nat := 4983230072969 + 3 ^ 40 * 253130 * 2
def baseEnd_253130 : Nat := 115535429397955432365229

theorem tailTrace_253130 : CollatzResearch.WordTrace tailWord_253130 prefixEnd_253130 115535429397955432365229 := by
  unfold tailWord_253130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308102393240179001825211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6154939715307144004867229 2308102393240179001825211)
  ·
    refine ⟨3462153589860268502737817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308102393240179001825211 3462153589860268502737817)
    ·
      refine ⟨2596615192395201377053363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462153589860268502737817 2596615192395201377053363)
      ·
        refine ⟨3894922788592802065580045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596615192395201377053363 3894922788592802065580045)
        ·
          refine ⟨1460596045722300774592517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3894922788592802065580045 1460596045722300774592517)
          ·
            refine ⟨273861758572931395236097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1460596045722300774592517 273861758572931395236097)
            ·
              refine ⟨205396318929698546427073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273861758572931395236097 205396318929698546427073)
              ·
                refine ⟨154047239197273909820305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205396318929698546427073 154047239197273909820305)
                ·
                  refine ⟨115535429397955432365229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154047239197273909820305 115535429397955432365229)
                  ·
                    rfl

theorem cell20_253130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_253130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253130 prefixEnd_253130 := by exact prefixLift 253130
  have htrace : WordTrace (prefixWord ++ tailWord_253130) baseStart_253130 baseEnd_253130 := by
    simpa [prefixWord, tailWord_253130, baseEnd_253130] using wordTrace_append hprefix tailTrace_253130
  have hstable : (prefixWord ++ tailWord_253130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253130).length < 2 ^ (prefixWord ++ tailWord_253130).sum := by decide
  have hdescent : baseEnd_253130 < baseStart_253130 := by decide
  rcases family_descends (prefixWord ++ tailWord_253130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253141 : List Nat := [1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_253141 : Nat := 118140960795 + 253141 * 2 ^ 59
def prefixEnd_253141 : Nat := 4983230072969 + 3 ^ 40 * 253141 * 2
def baseEnd_253141 : Nat := 38513483365896094332839

theorem tailTrace_253141 : CollatzResearch.WordTrace tailWord_253141 prefixEnd_253141 38513483365896094332839 := by
  unfold tailWord_253141
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232810775920864885951277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6155207183947243257300851 9232810775920864885951277)
  ·
    refine ⟨3462304040970324332231729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9232810775920864885951277 3462304040970324332231729)
    ·
      refine ⟨2596728030727743249173797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462304040970324332231729 2596728030727743249173797)
      ·
        refine ⟨486886505761451859220087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2596728030727743249173797 486886505761451859220087)
        ·
          refine ⟨730329758642177788830131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486886505761451859220087 730329758642177788830131)
          ·
            refine ⟨1095494637963266683245197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730329758642177788830131 1095494637963266683245197)
            ·
              refine ⟨410810489236225006216949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095494637963266683245197 410810489236225006216949)
              ·
                refine ⟨38513483365896094332839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410810489236225006216949 38513483365896094332839)
                ·
                  rfl

theorem cell20_253141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_253141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253141 prefixEnd_253141 := by exact prefixLift 253141
  have htrace : WordTrace (prefixWord ++ tailWord_253141) baseStart_253141 baseEnd_253141 := by
    simpa [prefixWord, tailWord_253141, baseEnd_253141] using wordTrace_append hprefix tailTrace_253141
  have hstable : (prefixWord ++ tailWord_253141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253141).length < 2 ^ (prefixWord ++ tailWord_253141).sum := by decide
  have hdescent : baseEnd_253141 < baseStart_253141 := by decide
  rcases family_descends (prefixWord ++ tailWord_253141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253169 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_253169 : Nat := 118140960795 + 253169 * 2 ^ 59
def prefixEnd_253169 : Nat := 4983230072969 + 3 ^ 40 * 253169 * 2
def baseEnd_253169 : Nat := 115553230060644630065069

theorem tailTrace_253169 : CollatzResearch.WordTrace tailWord_253169 prefixEnd_253169 115553230060644630065069 := by
  unfold tailWord_253169
  simp only [CollatzResearch.WordTrace]
  refine ⟨9233832019819425667970561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6155888013212950445313707 9233832019819425667970561)
  ·
    refine ⟨6925374014864569250977921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9233832019819425667970561 6925374014864569250977921)
    ·
      refine ⟨5194030511148426938233441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6925374014864569250977921 5194030511148426938233441)
      ·
        refine ⟨3895522883361320203675081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5194030511148426938233441 3895522883361320203675081)
        ·
          refine ⟨2921642162520990152756311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3895522883361320203675081 2921642162520990152756311)
          ·
            refine ⟨4382463243781485229134467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921642162520990152756311 4382463243781485229134467)
            ·
              refine ⟨6573694865672227843701701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382463243781485229134467 6573694865672227843701701)
              ·
                refine ⟨1232567787313542720694069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6573694865672227843701701 1232567787313542720694069)
                ·
                  refine ⟨115553230060644630065069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1232567787313542720694069 115553230060644630065069)
                  ·
                    rfl

theorem cell20_253169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_253169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253169 prefixEnd_253169 := by exact prefixLift 253169
  have htrace : WordTrace (prefixWord ++ tailWord_253169) baseStart_253169 baseEnd_253169 := by
    simpa [prefixWord, tailWord_253169, baseEnd_253169] using wordTrace_append hprefix tailTrace_253169
  have hstable : (prefixWord ++ tailWord_253169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253169).length < 2 ^ (prefixWord ++ tailWord_253169).sum := by decide
  have hdescent : baseEnd_253169 < baseStart_253169 := by decide
  rcases family_descends (prefixWord ++ tailWord_253169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253182 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_253182 : Nat := 118140960795 + 253182 * 2 ^ 59
def prefixEnd_253182 : Nat := 4983230072969 + 3 ^ 40 * 253182 * 2
def baseEnd_253182 : Nat := 115559163614874362631683

theorem tailTrace_253182 : CollatzResearch.WordTrace tailWord_253182 prefixEnd_253182 115559163614874362631683 := by
  unfold tailWord_253182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154288271096541111024225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6156204112514885925462533 1154288271096541111024225)
  ·
    refine ⟨865716203322405833268169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1154288271096541111024225 865716203322405833268169)
    ·
      refine ⟨649287152491804374951127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865716203322405833268169 649287152491804374951127)
      ·
        refine ⟨973930728737706562426691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649287152491804374951127 973930728737706562426691)
        ·
          refine ⟨1460896093106559843640037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973930728737706562426691 1460896093106559843640037)
          ·
            refine ⟨273918017457479970682507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1460896093106559843640037 273918017457479970682507)
            ·
              refine ⟨410877026186219956023761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273918017457479970682507 410877026186219956023761)
              ·
                refine ⟨308157769639664967017821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410877026186219956023761 308157769639664967017821)
                ·
                  refine ⟨115559163614874362631683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308157769639664967017821 115559163614874362631683)
                  ·
                    rfl

theorem cell20_253182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_253182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253182 prefixEnd_253182 := by exact prefixLift 253182
  have htrace : WordTrace (prefixWord ++ tailWord_253182) baseStart_253182 baseEnd_253182 := by
    simpa [prefixWord, tailWord_253182, baseEnd_253182] using wordTrace_append hprefix tailTrace_253182
  have hstable : (prefixWord ++ tailWord_253182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253182).length < 2 ^ (prefixWord ++ tailWord_253182).sum := by decide
  have hdescent : baseEnd_253182 < baseStart_253182 := by decide
  rcases family_descends (prefixWord ++ tailWord_253182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253193 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_253193 : Nat := 118140960795 + 253193 * 2 ^ 59
def prefixEnd_253193 : Nat := 4983230072969 + 3 ^ 40 * 253193 * 2
def baseEnd_253193 : Nat := 115564184314607213264971

theorem tailTrace_253193 : CollatzResearch.WordTrace tailWord_253193 prefixEnd_253193 115564184314607213264971 := by
  unfold tailWord_253193
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234707371732477766844233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6156471581154985177896155 9234707371732477766844233)
  ·
    refine ⟨6926030528799358325133175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9234707371732477766844233 6926030528799358325133175)
    ·
      refine ⟨10389045793199037487699763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926030528799358325133175 10389045793199037487699763)
      ·
        refine ⟨15583568689798556231549645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389045793199037487699763 15583568689798556231549645)
        ·
          refine ⟨5843838258674458586831117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15583568689798556231549645 5843838258674458586831117)
          ·
            refine ⟨2191439347002921970061669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5843838258674458586831117 2191439347002921970061669)
            ·
              refine ⟨410894877563047869386563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2191439347002921970061669 410894877563047869386563)
              ·
                refine ⟨616342316344571804079845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410894877563047869386563 616342316344571804079845)
                ·
                  refine ⟨115564184314607213264971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616342316344571804079845 115564184314607213264971)
                  ·
                    rfl

theorem cell20_253193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_253193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253193 prefixEnd_253193 := by exact prefixLift 253193
  have htrace : WordTrace (prefixWord ++ tailWord_253193) baseStart_253193 baseEnd_253193 := by
    simpa [prefixWord, tailWord_253193, baseEnd_253193] using wordTrace_append hprefix tailTrace_253193
  have hstable : (prefixWord ++ tailWord_253193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253193).length < 2 ^ (prefixWord ++ tailWord_253193).sum := by decide
  have hdescent : baseEnd_253193 < baseStart_253193 := by decide
  rcases family_descends (prefixWord ++ tailWord_253193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253224 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_253224 : Nat := 118140960795 + 253224 * 2 ^ 59
def prefixEnd_253224 : Nat := 4983230072969 + 3 ^ 40 * 253224 * 2
def baseEnd_253224 : Nat := 115578333559308883231511

theorem tailTrace_253224 : CollatzResearch.WordTrace tailWord_253224 prefixEnd_253224 115578333559308883231511 := by
  unfold tailWord_253224
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617919017310085030611363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6157225356413446707481817 4617919017310085030611363)
  ·
    refine ⟨6926878525965127545917045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4617919017310085030611363 6926878525965127545917045)
    ·
      refine ⟨649394861809230707429723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6926878525965127545917045 649394861809230707429723)
      ·
        refine ⟨974092292713846061144585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649394861809230707429723 974092292713846061144585)
        ·
          refine ⟨730569219535384545858439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974092292713846061144585 730569219535384545858439)
          ·
            refine ⟨1095853829303076818787659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730569219535384545858439 1095853829303076818787659)
            ·
              refine ⟨1643780743954615228181489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095853829303076818787659 1643780743954615228181489)
              ·
                refine ⟨1232835557965961421136117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643780743954615228181489 1232835557965961421136117)
                ·
                  refine ⟨115578333559308883231511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1232835557965961421136117 115578333559308883231511)
                  ·
                    rfl

theorem cell20_253224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_253224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253224 prefixEnd_253224 := by exact prefixLift 253224
  have htrace : WordTrace (prefixWord ++ tailWord_253224) baseStart_253224 baseEnd_253224 := by
    simpa [prefixWord, tailWord_253224, baseEnd_253224] using wordTrace_append hprefix tailTrace_253224
  have hstable : (prefixWord ++ tailWord_253224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253224).length < 2 ^ (prefixWord ++ tailWord_253224).sum := by decide
  have hdescent : baseEnd_253224 < baseStart_253224 := by decide
  rcases family_descends (prefixWord ++ tailWord_253224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253262 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_253262 : Nat := 118140960795 + 253262 * 2 ^ 59
def prefixEnd_253262 : Nat := 4983230072969 + 3 ^ 40 * 253262 * 2
def baseEnd_253262 : Nat := 115595677794749639964689

theorem tailTrace_253262 : CollatzResearch.WordTrace tailWord_253262 prefixEnd_253262 115595677794749639964689 := by
  unfold tailWord_253262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154653001060312818888255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6158149338988335034070693 1154653001060312818888255)
  ·
    refine ⟨1731979501590469228332383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1154653001060312818888255 1731979501590469228332383)
    ·
      refine ⟨2597969252385703842498575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731979501590469228332383 2597969252385703842498575)
      ·
        refine ⟨3896953878578555763747863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597969252385703842498575 3896953878578555763747863)
        ·
          refine ⟨5845430817867833645621795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896953878578555763747863 5845430817867833645621795)
          ·
            refine ⟨8768146226801750468432693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845430817867833645621795 8768146226801750468432693)
            ·
              refine ⟨822013708762664106415565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8768146226801750468432693 822013708762664106415565)
              ·
                refine ⟨308255140785999039905837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822013708762664106415565 308255140785999039905837)
                ·
                  refine ⟨115595677794749639964689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308255140785999039905837 115595677794749639964689)
                  ·
                    rfl

theorem cell20_253262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_253262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253262 prefixEnd_253262 := by exact prefixLift 253262
  have htrace : WordTrace (prefixWord ++ tailWord_253262) baseStart_253262 baseEnd_253262 := by
    simpa [prefixWord, tailWord_253262, baseEnd_253262] using wordTrace_append hprefix tailTrace_253262
  have hstable : (prefixWord ++ tailWord_253262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253262).length < 2 ^ (prefixWord ++ tailWord_253262).sum := by decide
  have hdescent : baseEnd_253262 < baseStart_253262 := by decide
  rcases family_descends (prefixWord ++ tailWord_253262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253341 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 2]
def baseStart_253341 : Nat := 118140960795 + 253341 * 2 ^ 59
def prefixEnd_253341 : Nat := 4983230072969 + 3 ^ 40 * 253341 * 2
def baseEnd_253341 : Nat := 115631735547376476331033

theorem tailTrace_253341 : CollatzResearch.WordTrace tailWord_253341 prefixEnd_253341 115631735547376476331033 := by
  unfold tailWord_253341
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240105375196299043231877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6160070250130866028821251 9240105375196299043231877)
  ·
    refine ⟨1732519757849306070605977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9240105375196299043231877 1732519757849306070605977)
    ·
      refine ⟨1299389818386979552954483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1732519757849306070605977 1299389818386979552954483)
      ·
        refine ⟨1949084727580469329431725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299389818386979552954483 1949084727580469329431725)
        ·
          refine ⟨730906772842675998536897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1949084727580469329431725 730906772842675998536897)
          ·
            refine ⟨548180079632006998902673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730906772842675998536897 548180079632006998902673)
            ·
              refine ⟨411135059724005249177005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548180079632006998902673 411135059724005249177005)
              ·
                refine ⟨154175647396501968441377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411135059724005249177005 154175647396501968441377)
                ·
                  refine ⟨115631735547376476331033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154175647396501968441377 115631735547376476331033)
                  ·
                    rfl

theorem cell20_253341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_253341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253341 prefixEnd_253341 := by exact prefixLift 253341
  have htrace : WordTrace (prefixWord ++ tailWord_253341) baseStart_253341 baseEnd_253341 := by
    simpa [prefixWord, tailWord_253341, baseEnd_253341] using wordTrace_append hprefix tailTrace_253341
  have hstable : (prefixWord ++ tailWord_253341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253341).length < 2 ^ (prefixWord ++ tailWord_253341).sum := by decide
  have hdescent : baseEnd_253341 < baseStart_253341 := by decide
  rcases family_descends (prefixWord ++ tailWord_253341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253372 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_253372 : Nat := 118140960795 + 253372 * 2 ^ 59
def prefixEnd_253372 : Nat := 4983230072969 + 3 ^ 40 * 253372 * 2
def baseEnd_253372 : Nat := 115645884792078146297573

theorem tailTrace_253372 : CollatzResearch.WordTrace tailWord_253372 prefixEnd_253372 115645884792078146297573 := by
  unfold tailWord_253372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620618019041995668805185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6160824025389327558406913 4620618019041995668805185)
  ·
    refine ⟨3465463514281496751603889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4620618019041995668805185 3465463514281496751603889)
    ·
      refine ⟨2599097635711122563702917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3465463514281496751603889 2599097635711122563702917)
      ·
        refine ⟨487330806695835480694297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2599097635711122563702917 487330806695835480694297)
        ·
          refine ⟨365498105021876610520723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487330806695835480694297 365498105021876610520723)
          ·
            refine ⟨548247157532814915781085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365498105021876610520723 548247157532814915781085)
            ·
              refine ⟨205592684074805593417907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548247157532814915781085 205592684074805593417907)
              ·
                refine ⟨308389026112208390126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205592684074805593417907 308389026112208390126861)
                ·
                  refine ⟨115645884792078146297573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308389026112208390126861 115645884792078146297573)
                  ·
                    rfl

theorem cell20_253372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_253372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253372 prefixEnd_253372 := by exact prefixLift 253372
  have htrace : WordTrace (prefixWord ++ tailWord_253372) baseStart_253372 baseEnd_253372 := by
    simpa [prefixWord, tailWord_253372, baseEnd_253372] using wordTrace_append hprefix tailTrace_253372
  have hstable : (prefixWord ++ tailWord_253372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253372).length < 2 ^ (prefixWord ++ tailWord_253372).sum := by decide
  have hdescent : baseEnd_253372 < baseStart_253372 := by decide
  rcases family_descends (prefixWord ++ tailWord_253372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253378 : List Nat := [3, 5, 2, 1, 2, 1, 2, 4]
def baseStart_253378 : Nat := 118140960795 + 253378 * 2 ^ 59
def prefixEnd_253378 : Nat := 4983230072969 + 3 ^ 40 * 253378 * 2
def baseEnd_253378 : Nat := 38549541118522930699183

theorem tailTrace_253378 : CollatzResearch.WordTrace tailWord_253378 prefixEnd_253378 38549541118522930699183 := by
  unfold tailWord_253378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310363719015563590582197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6160969917374836241552525 2310363719015563590582197)
  ·
    refine ⟨216596598657709086617081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2310363719015563590582197 216596598657709086617081)
    ·
      refine ⟨162447448993281814962811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216596598657709086617081 162447448993281814962811)
      ·
        refine ⟨243671173489922722444217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162447448993281814962811 243671173489922722444217)
        ·
          refine ⟨182753380117442041833163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243671173489922722444217 182753380117442041833163)
          ·
            refine ⟨274130070176163062749745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182753380117442041833163 274130070176163062749745)
            ·
              refine ⟨205597552632122297062309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274130070176163062749745 205597552632122297062309)
              ·
                refine ⟨38549541118522930699183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205597552632122297062309 38549541118522930699183)
                ·
                  rfl

theorem cell20_253378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_253378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253378 prefixEnd_253378 := by exact prefixLift 253378
  have htrace : WordTrace (prefixWord ++ tailWord_253378) baseStart_253378 baseEnd_253378 := by
    simpa [prefixWord, tailWord_253378, baseEnd_253378] using wordTrace_append hprefix tailTrace_253378
  have hstable : (prefixWord ++ tailWord_253378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253378).length < 2 ^ (prefixWord ++ tailWord_253378).sum := by decide
  have hdescent : baseEnd_253378 < baseStart_253378 := by decide
  rcases family_descends (prefixWord ++ tailWord_253378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253396 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_253396 : Nat := 118140960795 + 253396 * 2 ^ 59
def prefixEnd_253396 : Nat := 4983230072969 + 3 ^ 40 * 253396 * 2
def baseEnd_253396 : Nat := 115656839046040729497475

theorem tailTrace_253396 : CollatzResearch.WordTrace tailWord_253396 prefixEnd_253396 115656839046040729497475 := by
  unfold tailWord_253396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621055694998521718242021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6161407593331362290989361 4621055694998521718242021)
  ·
    refine ⟨866447942812222822170379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4621055694998521718242021 866447942812222822170379)
    ·
      refine ⟨1299671914218334233255569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866447942812222822170379 1299671914218334233255569)
      ·
        refine ⟨974753935663750674941677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299671914218334233255569 974753935663750674941677)
        ·
          refine ⟨365532725873906503103129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 974753935663750674941677 365532725873906503103129)
          ·
            refine ⟨274149544405429877327347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365532725873906503103129 274149544405429877327347)
            ·
              refine ⟨411224316608144815991021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274149544405429877327347 411224316608144815991021)
              ·
                refine ⟨154209118728054305996633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411224316608144815991021 154209118728054305996633)
                ·
                  refine ⟨115656839046040729497475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154209118728054305996633 115656839046040729497475)
                  ·
                    rfl

theorem cell20_253396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_253396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253396 prefixEnd_253396 := by exact prefixLift 253396
  have htrace : WordTrace (prefixWord ++ tailWord_253396) baseStart_253396 baseEnd_253396 := by
    simpa [prefixWord, tailWord_253396, baseEnd_253396] using wordTrace_append hprefix tailTrace_253396
  have hstable : (prefixWord ++ tailWord_253396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253396).length < 2 ^ (prefixWord ++ tailWord_253396).sum := by decide
  have hdescent : baseEnd_253396 < baseStart_253396 := by decide
  rcases family_descends (prefixWord ++ tailWord_253396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253397 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_253397 : Nat := 118140960795 + 253397 * 2 ^ 59
def prefixEnd_253397 : Nat := 4983230072969 + 3 ^ 40 * 253397 * 2
def baseEnd_253397 : Nat := 115657295473289170464137

theorem tailTrace_253397 : CollatzResearch.WordTrace tailWord_253397 prefixEnd_253397 115657295473289170464137 := by
  unfold tailWord_253397
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242147862993420607270445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6161431908662280404846963 9242147862993420607270445)
  ·
    refine ⟨3465805448622532727726417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9242147862993420607270445 3465805448622532727726417)
    ·
      refine ⟨2599354086466899545794813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3465805448622532727726417 2599354086466899545794813)
      ·
        refine ⟨974757782425087329673055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2599354086466899545794813 974757782425087329673055)
        ·
          refine ⟨1462136673637630994509583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974757782425087329673055 1462136673637630994509583)
          ·
            refine ⟨2193205010456446491764375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462136673637630994509583 2193205010456446491764375)
            ·
              refine ⟨3289807515684669737646563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193205010456446491764375 3289807515684669737646563)
              ·
                refine ⟨4934711273527004606469845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289807515684669737646563 4934711273527004606469845)
                ·
                  refine ⟨115657295473289170464137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4934711273527004606469845 115657295473289170464137)
                  ·
                    rfl

theorem cell20_253397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_253397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253397 prefixEnd_253397 := by exact prefixLift 253397
  have htrace : WordTrace (prefixWord ++ tailWord_253397) baseStart_253397 baseEnd_253397 := by
    simpa [prefixWord, tailWord_253397, baseEnd_253397] using wordTrace_append hprefix tailTrace_253397
  have hstable : (prefixWord ++ tailWord_253397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253397).length < 2 ^ (prefixWord ++ tailWord_253397).sum := by decide
  have hdescent : baseEnd_253397 < baseStart_253397 := by decide
  rcases family_descends (prefixWord ++ tailWord_253397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253400 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_253400 : Nat := 118140960795 + 253400 * 2 ^ 59
def prefixEnd_253400 : Nat := 4983230072969 + 3 ^ 40 * 253400 * 2
def baseEnd_253400 : Nat := 115658664755034493364125

theorem tailTrace_253400 : CollatzResearch.WordTrace tailWord_253400 prefixEnd_253400 115658664755034493364125 := by
  unfold tailWord_253400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621128640991276059814827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6161504854655034746419769 4621128640991276059814827)
  ·
    refine ⟨6931692961486914089722241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621128640991276059814827 6931692961486914089722241)
    ·
      refine ⟨5198769721115185567291681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6931692961486914089722241 5198769721115185567291681)
      ·
        refine ⟨3899077290836389175468761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5198769721115185567291681 3899077290836389175468761)
        ·
          refine ⟨2924307968127291881601571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899077290836389175468761 2924307968127291881601571)
          ·
            refine ⟨4386461952190937822402357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924307968127291881601571 4386461952190937822402357)
            ·
              refine ⟨411230808017900420850221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4386461952190937822402357 411230808017900420850221)
              ·
                refine ⟨154211553006712657818833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411230808017900420850221 154211553006712657818833)
                ·
                  refine ⟨115658664755034493364125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154211553006712657818833 115658664755034493364125)
                  ·
                    rfl

theorem cell20_253400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_253400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253400 prefixEnd_253400 := by exact prefixLift 253400
  have htrace : WordTrace (prefixWord ++ tailWord_253400) baseStart_253400 baseEnd_253400 := by
    simpa [prefixWord, tailWord_253400, baseEnd_253400] using wordTrace_append hprefix tailTrace_253400
  have hstable : (prefixWord ++ tailWord_253400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253400).length < 2 ^ (prefixWord ++ tailWord_253400).sum := by decide
  have hdescent : baseEnd_253400 < baseStart_253400 := by decide
  rcases family_descends (prefixWord ++ tailWord_253400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253435 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_253435 : Nat := 118140960795 + 253435 * 2 ^ 59
def prefixEnd_253435 : Nat := 4983230072969 + 3 ^ 40 * 253435 * 2
def baseEnd_253435 : Nat := 115674639708729927197315

theorem tailTrace_253435 : CollatzResearch.WordTrace tailWord_253435 prefixEnd_253435 115674639708729927197315 := by
  unfold tailWord_253435
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243533836855753097153759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6162355891237168731435839 9243533836855753097153759)
  ·
    refine ⟨13865300755283629645730639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9243533836855753097153759 13865300755283629645730639)
    ·
      refine ⟨20797951132925444468595959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13865300755283629645730639 20797951132925444468595959)
      ·
        refine ⟨31196926699388166702893939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797951132925444468595959 31196926699388166702893939)
        ·
          refine ⟨46795390049082250054340909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31196926699388166702893939 46795390049082250054340909)
          ·
            refine ⟨17548271268405843770377841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46795390049082250054340909 17548271268405843770377841)
            ·
              refine ⟨13161203451304382827783381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17548271268405843770377841 13161203451304382827783381)
              ·
                refine ⟨308465705889946472526173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13161203451304382827783381 308465705889946472526173)
                ·
                  refine ⟨115674639708729927197315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308465705889946472526173 115674639708729927197315)
                  ·
                    rfl

theorem cell20_253435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_253435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253435 prefixEnd_253435 := by exact prefixLift 253435
  have htrace : WordTrace (prefixWord ++ tailWord_253435) baseStart_253435 baseEnd_253435 := by
    simpa [prefixWord, tailWord_253435, baseEnd_253435] using wordTrace_append hprefix tailTrace_253435
  have hstable : (prefixWord ++ tailWord_253435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253435).length < 2 ^ (prefixWord ++ tailWord_253435).sum := by decide
  have hdescent : baseEnd_253435 < baseStart_253435 := by decide
  rcases family_descends (prefixWord ++ tailWord_253435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253449 : List Nat := [1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_253449 : Nat := 118140960795 + 253449 * 2 ^ 59
def prefixEnd_253449 : Nat := 4983230072969 + 3 ^ 40 * 253449 * 2
def baseEnd_253449 : Nat := 38560343230069366910197

theorem tailTrace_253449 : CollatzResearch.WordTrace tailWord_253449 prefixEnd_253449 38560343230069366910197 := by
  unfold tailWord_253449
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244044458805033488163401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6162696305870022325442267 9244044458805033488163401)
  ·
    refine ⟨6933033344103775116122551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9244044458805033488163401 6933033344103775116122551)
    ·
      refine ⟨10399550016155662674183827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933033344103775116122551 10399550016155662674183827)
      ·
        refine ⟨15599325024233494011275741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399550016155662674183827 15599325024233494011275741)
        ·
          refine ⟨5849746884087560254228403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15599325024233494011275741 5849746884087560254228403)
          ·
            refine ⟨8774620326131340381342605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849746884087560254228403 8774620326131340381342605)
            ·
              refine ⟨3290482622299252643003477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8774620326131340381342605 3290482622299252643003477)
              ·
                refine ⟨38560343230069366910197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3290482622299252643003477 38560343230069366910197)
                ·
                  rfl

theorem cell20_253449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_253449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253449 prefixEnd_253449 := by exact prefixLift 253449
  have htrace : WordTrace (prefixWord ++ tailWord_253449) baseStart_253449 baseEnd_253449 := by
    simpa [prefixWord, tailWord_253449, baseEnd_253449] using wordTrace_append hprefix tailTrace_253449
  have hstable : (prefixWord ++ tailWord_253449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253449).length < 2 ^ (prefixWord ++ tailWord_253449).sum := by decide
  have hdescent : baseEnd_253449 < baseStart_253449 := by decide
  rcases family_descends (prefixWord ++ tailWord_253449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253472 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_253472 : Nat := 118140960795 + 253472 * 2 ^ 59
def prefixEnd_253472 : Nat := 4983230072969 + 3 ^ 40 * 253472 * 2
def baseEnd_253472 : Nat := 115691527516922242963831

theorem tailTrace_253472 : CollatzResearch.WordTrace tailWord_253472 prefixEnd_253472 115691527516922242963831 := by
  unfold tailWord_253472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622441668860854208125335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6163255558481138944167113 4622441668860854208125335)
  ·
    refine ⟨6933662503291281312188003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4622441668860854208125335 6933662503291281312188003)
    ·
      refine ⟨10400493754936921968282005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933662503291281312188003 10400493754936921968282005)
      ·
        refine ⟨487523144762668217263219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10400493754936921968282005 487523144762668217263219)
        ·
          refine ⟨731284717144002325894829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487523144762668217263219 731284717144002325894829)
          ·
            refine ⟨274231768929000872210561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731284717144002325894829 274231768929000872210561)
            ·
              refine ⟨205673826696750654157921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274231768929000872210561 205673826696750654157921)
              ·
                refine ⟨154255370022562990618441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205673826696750654157921 154255370022562990618441)
                ·
                  refine ⟨115691527516922242963831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154255370022562990618441 115691527516922242963831)
                  ·
                    rfl

theorem cell20_253472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_253472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253472 prefixEnd_253472 := by exact prefixLift 253472
  have htrace : WordTrace (prefixWord ++ tailWord_253472) baseStart_253472 baseEnd_253472 := by
    simpa [prefixWord, tailWord_253472, baseEnd_253472] using wordTrace_append hprefix tailTrace_253472
  have hstable : (prefixWord ++ tailWord_253472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253472).length < 2 ^ (prefixWord ++ tailWord_253472).sum := by decide
  have hdescent : baseEnd_253472 < baseStart_253472 := by decide
  rcases family_descends (prefixWord ++ tailWord_253472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253497 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_253497 : Nat := 118140960795 + 253497 * 2 ^ 59
def prefixEnd_253497 : Nat := 4983230072969 + 3 ^ 40 * 253497 * 2
def baseEnd_253497 : Nat := 115702938198133267130395

theorem tailTrace_253497 : CollatzResearch.WordTrace tailWord_253497 prefixEnd_253497 115702938198133267130395 := by
  unfold tailWord_253497
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245795162631137685910745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6163863441754091790607163 9245795162631137685910745)
  ·
    refine ⟨6934346371973353264433059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9245795162631137685910745 6934346371973353264433059)
    ·
      refine ⟨10401519557960029896649589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934346371973353264433059 10401519557960029896649589)
      ·
        refine ⟨975142458558752802810899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10401519557960029896649589 975142458558752802810899)
        ·
          refine ⟨1462713687838129204216349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975142458558752802810899 1462713687838129204216349)
          ·
            refine ⟨548517632939298451581131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1462713687838129204216349 548517632939298451581131)
            ·
              refine ⟨822776449408947677371697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548517632939298451581131 822776449408947677371697)
              ·
                refine ⟨617082337056710758028773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822776449408947677371697 617082337056710758028773)
                ·
                  refine ⟨115702938198133267130395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617082337056710758028773 115702938198133267130395)
                  ·
                    rfl

theorem cell20_253497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_253497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253497 prefixEnd_253497 := by exact prefixLift 253497
  have htrace : WordTrace (prefixWord ++ tailWord_253497) baseStart_253497 baseEnd_253497 := by
    simpa [prefixWord, tailWord_253497, baseEnd_253497] using wordTrace_append hprefix tailTrace_253497
  have hstable : (prefixWord ++ tailWord_253497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253497).length < 2 ^ (prefixWord ++ tailWord_253497).sum := by decide
  have hdescent : baseEnd_253497 < baseStart_253497 := by decide
  rcases family_descends (prefixWord ++ tailWord_253497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253514 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_253514 : Nat := 118140960795 + 253514 * 2 ^ 59
def prefixEnd_253514 : Nat := 4983230072969 + 3 ^ 40 * 253514 * 2
def baseEnd_253514 : Nat := 115710697461356763563659

theorem tailTrace_253514 : CollatzResearch.WordTrace tailWord_253514 prefixEnd_253514 115710697461356763563659 := by
  unfold tailWord_253514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311603800892387397319899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6164276802379699726186397 2311603800892387397319899)
  ·
    refine ⟨3467405701338581095979849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311603800892387397319899 3467405701338581095979849)
    ·
      refine ⟨2600554276003935821984887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3467405701338581095979849 2600554276003935821984887)
      ·
        refine ⟨3900831414005903732977331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600554276003935821984887 3900831414005903732977331)
        ·
          refine ⟨5851247121008855599465997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900831414005903732977331 5851247121008855599465997)
          ·
            refine ⟨2194217670378320849799749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5851247121008855599465997 2194217670378320849799749)
            ·
              refine ⟨411415813195935159337453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2194217670378320849799749 411415813195935159337453)
              ·
                refine ⟨154280929948475684751545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411415813195935159337453 154280929948475684751545)
                ·
                  refine ⟨115710697461356763563659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154280929948475684751545 115710697461356763563659)
                  ·
                    rfl

theorem cell20_253514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_253514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253514 prefixEnd_253514 := by exact prefixLift 253514
  have htrace : WordTrace (prefixWord ++ tailWord_253514) baseStart_253514 baseEnd_253514 := by
    simpa [prefixWord, tailWord_253514, baseEnd_253514] using wordTrace_append hprefix tailTrace_253514
  have hstable : (prefixWord ++ tailWord_253514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253514).length < 2 ^ (prefixWord ++ tailWord_253514).sum := by decide
  have hdescent : baseEnd_253514 < baseStart_253514 := by decide
  rcases family_descends (prefixWord ++ tailWord_253514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253518 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_253518 : Nat := 118140960795 + 253518 * 2 ^ 59
def prefixEnd_253518 : Nat := 4983230072969 + 3 ^ 40 * 253518 * 2
def baseEnd_253518 : Nat := 115712523170350527430309

theorem tailTrace_253518 : CollatzResearch.WordTrace tailWord_253518 prefixEnd_253518 115712523170350527430309 := by
  unfold tailWord_253518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155820136944382284053151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6164374063703372181616805 1155820136944382284053151)
  ·
    refine ⟨1733730205416573426079727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155820136944382284053151 1733730205416573426079727)
    ·
      refine ⟨2600595308124860139119591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733730205416573426079727 2600595308124860139119591)
      ·
        refine ⟨3900892962187290208679387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600595308124860139119591 3900892962187290208679387)
        ·
          refine ⟨5851339443280935313019081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900892962187290208679387 5851339443280935313019081)
          ·
            refine ⟨4388504582460701484764311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5851339443280935313019081 4388504582460701484764311)
            ·
              refine ⟨6582756873691052227146467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388504582460701484764311 6582756873691052227146467)
              ·
                refine ⟨9874135310536578340719701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582756873691052227146467 9874135310536578340719701)
                ·
                  refine ⟨115712523170350527430309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9874135310536578340719701 115712523170350527430309)
                  ·
                    rfl

theorem cell20_253518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_253518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253518 prefixEnd_253518 := by exact prefixLift 253518
  have htrace : WordTrace (prefixWord ++ tailWord_253518) baseStart_253518 baseEnd_253518 := by
    simpa [prefixWord, tailWord_253518, baseEnd_253518] using wordTrace_append hprefix tailTrace_253518
  have hstable : (prefixWord ++ tailWord_253518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253518).length < 2 ^ (prefixWord ++ tailWord_253518).sum := by decide
  have hdescent : baseEnd_253518 < baseStart_253518 := by decide
  rcases family_descends (prefixWord ++ tailWord_253518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253563 : List Nat := [1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_253563 : Nat := 118140960795 + 253563 * 2 ^ 59
def prefixEnd_253563 : Nat := 4983230072969 + 3 ^ 40 * 253563 * 2
def baseEnd_253563 : Nat := 38577687465510123643375

theorem tailTrace_253563 : CollatzResearch.WordTrace tailWord_253563 prefixEnd_253563 38577687465510123643375 := by
  unfold tailWord_253563
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248202380392030957813343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6165468253594687305208895 9248202380392030957813343)
  ·
    refine ⟨13872303570588046436720015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9248202380392030957813343 13872303570588046436720015)
    ·
      refine ⟨20808455355882069655080023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13872303570588046436720015 20808455355882069655080023)
      ·
        refine ⟨31212683033823104482620035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20808455355882069655080023 31212683033823104482620035)
        ·
          refine ⟨46819024550734656723930053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31212683033823104482620035 46819024550734656723930053)
          ·
            refine ⟨8778567103262748135736885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46819024550734656723930053 8778567103262748135736885)
            ·
              refine ⟨822990665930882637725333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8778567103262748135736885 822990665930882637725333)
              ·
                refine ⟨38577687465510123643375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 822990665930882637725333 38577687465510123643375)
                ·
                  rfl

theorem cell20_253563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_253563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253563 prefixEnd_253563 := by exact prefixLift 253563
  have htrace : WordTrace (prefixWord ++ tailWord_253563) baseStart_253563 baseEnd_253563 := by
    simpa [prefixWord, tailWord_253563, baseEnd_253563] using wordTrace_append hprefix tailTrace_253563
  have hstable : (prefixWord ++ tailWord_253563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253563).length < 2 ^ (prefixWord ++ tailWord_253563).sum := by decide
  have hdescent : baseEnd_253563 < baseStart_253563 := by decide
  rcases family_descends (prefixWord ++ tailWord_253563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253569 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 2]
def baseStart_253569 : Nat := 118140960795 + 253569 * 2 ^ 59
def prefixEnd_253569 : Nat := 4983230072969 + 3 ^ 40 * 253569 * 2
def baseEnd_253569 : Nat := 115735800960021016730101

theorem tailTrace_253569 : CollatzResearch.WordTrace tailWord_253569 prefixEnd_253569 115735800960021016730101 := by
  unfold tailWord_253569
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248421218370293982531761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6165614145580195988354507 9248421218370293982531761)
  ·
    refine ⟨6936315913777720486898821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9248421218370293982531761 6936315913777720486898821)
    ·
      refine ⟨1300559233833322591293529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6936315913777720486898821 1300559233833322591293529)
      ·
        refine ⟨975419425374991943470147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300559233833322591293529 975419425374991943470147)
        ·
          refine ⟨1463129138062487915205221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975419425374991943470147 1463129138062487915205221)
          ·
            refine ⟨274336713386716484100979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1463129138062487915205221 274336713386716484100979)
            ·
              refine ⟨411505070080074726151469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274336713386716484100979 411505070080074726151469)
              ·
                refine ⟨154314401280028022306801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411505070080074726151469 154314401280028022306801)
                ·
                  refine ⟨115735800960021016730101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154314401280028022306801 115735800960021016730101)
                  ·
                    rfl

theorem cell20_253569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_253569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253569 prefixEnd_253569 := by exact prefixLift 253569
  have htrace : WordTrace (prefixWord ++ tailWord_253569) baseStart_253569 baseEnd_253569 := by
    simpa [prefixWord, tailWord_253569, baseEnd_253569] using wordTrace_append hprefix tailTrace_253569
  have hstable : (prefixWord ++ tailWord_253569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253569).length < 2 ^ (prefixWord ++ tailWord_253569).sum := by decide
  have hdescent : baseEnd_253569 < baseStart_253569 := by decide
  rcases family_descends (prefixWord ++ tailWord_253569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253576 : List Nat := [2, 1, 3, 5, 2, 1, 6]
def baseStart_253576 : Nat := 118140960795 + 253576 * 2 ^ 59
def prefixEnd_253576 : Nat := 4983230072969 + 3 ^ 40 * 253576 * 2
def baseEnd_253576 : Nat := 12859888438973344832971

theorem tailTrace_253576 : CollatzResearch.WordTrace tailWord_253576 prefixEnd_253576 12859888438973344832971 := by
  unfold tailWord_253576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624338264672467089018291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6165784352896622785357721 4624338264672467089018291)
  ·
    refine ⟨6936507397008700633527437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624338264672467089018291 6936507397008700633527437)
    ·
      refine ⟨2601190273878262737572789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6936507397008700633527437 2601190273878262737572789)
      ·
        refine ⟨243861588176087131647449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2601190273878262737572789 243861588176087131647449)
        ·
          refine ⟨182896191132065348735587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243861588176087131647449 182896191132065348735587)
          ·
            refine ⟨274344286698098023103381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182896191132065348735587 274344286698098023103381)
            ·
              refine ⟨12859888438973344832971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274344286698098023103381 12859888438973344832971)
              ·
                rfl

theorem cell20_253576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 6].length) (baseStart_253576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253576 prefixEnd_253576 := by exact prefixLift 253576
  have htrace : WordTrace (prefixWord ++ tailWord_253576) baseStart_253576 baseEnd_253576 := by
    simpa [prefixWord, tailWord_253576, baseEnd_253576] using wordTrace_append hprefix tailTrace_253576
  have hstable : (prefixWord ++ tailWord_253576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253576).length < 2 ^ (prefixWord ++ tailWord_253576).sum := by decide
  have hdescent : baseEnd_253576 < baseStart_253576 := by decide
  rcases family_descends (prefixWord ++ tailWord_253576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253586 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_253586 : Nat := 118140960795 + 253586 * 2 ^ 59
def prefixEnd_253586 : Nat := 4983230072969 + 3 ^ 40 * 253586 * 2
def baseEnd_253586 : Nat := 115743560223244513163365

theorem tailTrace_253586 : CollatzResearch.WordTrace tailWord_253586 prefixEnd_253586 115743560223244513163365 := by
  unfold tailWord_253586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312260314827176471475153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6166027506205803923933741 2312260314827176471475153)
  ·
    refine ⟨1734195236120382353606365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2312260314827176471475153 1734195236120382353606365)
    ·
      refine ⟨650323213545143382602387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1734195236120382353606365 650323213545143382602387)
      ·
        refine ⟨975484820317715073903581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650323213545143382602387 975484820317715073903581)
        ·
          refine ⟨365806807619143152713843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 975484820317715073903581 365806807619143152713843)
          ·
            refine ⟨548710211428714729070765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365806807619143152713843 548710211428714729070765)
            ·
              refine ⟨205766329285768023401537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548710211428714729070765 205766329285768023401537)
              ·
                refine ⟨154324746964326017551153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205766329285768023401537 154324746964326017551153)
                ·
                  refine ⟨115743560223244513163365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154324746964326017551153 115743560223244513163365)
                  ·
                    rfl

theorem cell20_253586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_253586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253586 prefixEnd_253586 := by exact prefixLift 253586
  have htrace : WordTrace (prefixWord ++ tailWord_253586) baseStart_253586 baseEnd_253586 := by
    simpa [prefixWord, tailWord_253586, baseEnd_253586] using wordTrace_append hprefix tailTrace_253586
  have hstable : (prefixWord ++ tailWord_253586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253586).length < 2 ^ (prefixWord ++ tailWord_253586).sum := by decide
  have hdescent : baseEnd_253586 < baseStart_253586 := by decide
  rcases family_descends (prefixWord ++ tailWord_253586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253604 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_253604 : Nat := 118140960795 + 253604 * 2 ^ 59
def prefixEnd_253604 : Nat := 4983230072969 + 3 ^ 40 * 253604 * 2
def baseEnd_253604 : Nat := 115751775913716450563291

theorem tailTrace_253604 : CollatzResearch.WordTrace tailWord_253604 prefixEnd_253604 115751775913716450563291 := by
  unfold tailWord_253604
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624848886621747480027933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6166465182162329973370577 4624848886621747480027933)
  ·
    refine ⟨1734318332483155305010475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4624848886621747480027933 1734318332483155305010475)
    ·
      refine ⟨2601477498724732957515713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734318332483155305010475 2601477498724732957515713)
      ·
        refine ⟨1951108124043549718136785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2601477498724732957515713 1951108124043549718136785)
        ·
          refine ⟨1463331093032662288602589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951108124043549718136785 1463331093032662288602589)
          ·
            refine ⟨548749159887248358225971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1463331093032662288602589 548749159887248358225971)
            ·
              refine ⟨823123739830872537338957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548749159887248358225971 823123739830872537338957)
              ·
                refine ⟨308671402436577201502109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823123739830872537338957 308671402436577201502109)
                ·
                  refine ⟨115751775913716450563291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308671402436577201502109 115751775913716450563291)
                  ·
                    rfl

theorem cell20_253604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_253604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253604 prefixEnd_253604 := by exact prefixLift 253604
  have htrace : WordTrace (prefixWord ++ tailWord_253604) baseStart_253604 baseEnd_253604 := by
    simpa [prefixWord, tailWord_253604, baseEnd_253604] using wordTrace_append hprefix tailTrace_253604
  have hstable : (prefixWord ++ tailWord_253604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253604).length < 2 ^ (prefixWord ++ tailWord_253604).sum := by decide
  have hdescent : baseEnd_253604 < baseStart_253604 := by decide
  rcases family_descends (prefixWord ++ tailWord_253604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253638 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_253638 : Nat := 118140960795 + 253638 * 2 ^ 59
def prefixEnd_253638 : Nat := 4983230072969 + 3 ^ 40 * 253638 * 2
def baseEnd_253638 : Nat := 115767294440163443429819

theorem tailTrace_253638 : CollatzResearch.WordTrace tailWord_253638 prefixEnd_253638 115767294440163443429819 := by
  unfold tailWord_253638
  simp only [CollatzResearch.WordTrace]
  refine ⟨289091807972509961462299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6167291903413545844529045 289091807972509961462299)
  ·
    refine ⟨433637711958764942193449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289091807972509961462299 433637711958764942193449)
    ·
      refine ⟨325228283969073706645087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433637711958764942193449 325228283969073706645087)
      ·
        refine ⟨487842425953610559967631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325228283969073706645087 487842425953610559967631)
        ·
          refine ⟨731763638930415839951447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487842425953610559967631 731763638930415839951447)
          ·
            refine ⟨1097645458395623759927171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731763638930415839951447 1097645458395623759927171)
            ·
              refine ⟨1646468187593435639890757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097645458395623759927171 1646468187593435639890757)
              ·
                refine ⟨308712785173769182479517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1646468187593435639890757 308712785173769182479517)
                ·
                  refine ⟨115767294440163443429819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308712785173769182479517 115767294440163443429819)
                  ·
                    rfl

theorem cell20_253638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_253638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253638 prefixEnd_253638 := by exact prefixLift 253638
  have htrace : WordTrace (prefixWord ++ tailWord_253638) baseStart_253638 baseEnd_253638 := by
    simpa [prefixWord, tailWord_253638, baseEnd_253638] using wordTrace_append hprefix tailTrace_253638
  have hstable : (prefixWord ++ tailWord_253638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253638).length < 2 ^ (prefixWord ++ tailWord_253638).sum := by decide
  have hdescent : baseEnd_253638 < baseStart_253638 := by decide
  rcases family_descends (prefixWord ++ tailWord_253638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253663 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_253663 : Nat := 118140960795 + 253663 * 2 ^ 59
def prefixEnd_253663 : Nat := 4983230072969 + 3 ^ 40 * 253663 * 2
def baseEnd_253663 : Nat := 115778705121374467596383

theorem tailTrace_253663 : CollatzResearch.WordTrace tailWord_253663 prefixEnd_253663 115778705121374467596383 := by
  unfold tailWord_253663
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251849680029748036453643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6167899786686498690969095 9251849680029748036453643)
  ·
    refine ⟨13877774520044622054680465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9251849680029748036453643 13877774520044622054680465)
    ·
      refine ⟨10408330890033466541010349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13877774520044622054680465 10408330890033466541010349)
      ·
        refine ⟨3903124083762549952878881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10408330890033466541010349 3903124083762549952878881)
        ·
          refine ⟨2927343062821912464659161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3903124083762549952878881 2927343062821912464659161)
          ·
            refine ⟨2195507297116434348494371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2927343062821912464659161 2195507297116434348494371)
            ·
              refine ⟨3293260945674651522741557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195507297116434348494371 3293260945674651522741557)
              ·
                refine ⟨308743213656998580257021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3293260945674651522741557 308743213656998580257021)
                ·
                  refine ⟨115778705121374467596383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308743213656998580257021 115778705121374467596383)
                  ·
                    rfl

theorem cell20_253663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_253663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253663 prefixEnd_253663 := by exact prefixLift 253663
  have htrace : WordTrace (prefixWord ++ tailWord_253663) baseStart_253663 baseEnd_253663 := by
    simpa [prefixWord, tailWord_253663, baseEnd_253663] using wordTrace_append hprefix tailTrace_253663
  have hstable : (prefixWord ++ tailWord_253663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253663).length < 2 ^ (prefixWord ++ tailWord_253663).sum := by decide
  have hdescent : baseEnd_253663 < baseStart_253663 := by decide
  rcases family_descends (prefixWord ++ tailWord_253663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253687 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 2]
def baseStart_253687 : Nat := 118140960795 + 253687 * 2 ^ 59
def prefixEnd_253687 : Nat := 4983230072969 + 3 ^ 40 * 253687 * 2
def baseEnd_253687 : Nat := 115789659375337050796285

theorem tailTrace_253687 : CollatzResearch.WordTrace tailWord_253687 prefixEnd_253687 115789659375337050796285 := by
  unfold tailWord_253687
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252725031942800135327315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168483354628533423551543 9252725031942800135327315)
  ·
    refine ⟨13879087547914200202990973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9252725031942800135327315 13879087547914200202990973)
    ·
      refine ⟨5204657830467825076121615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13879087547914200202990973 5204657830467825076121615)
      ·
        refine ⟨7806986745701737614182423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204657830467825076121615 7806986745701737614182423)
        ·
          refine ⟨11710480118552606421273635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7806986745701737614182423 11710480118552606421273635)
          ·
            refine ⟨17565720177828909631910453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11710480118552606421273635 17565720177828909631910453)
            ·
              refine ⟨1646786266671460277991605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17565720177828909631910453 1646786266671460277991605)
              ·
                refine ⟨154386212500449401061713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1646786266671460277991605 154386212500449401061713)
                ·
                  refine ⟨115789659375337050796285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154386212500449401061713 115789659375337050796285)
                  ·
                    rfl

theorem cell20_253687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2].length) (baseStart_253687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253687 prefixEnd_253687 := by exact prefixLift 253687
  have htrace : WordTrace (prefixWord ++ tailWord_253687) baseStart_253687 baseEnd_253687 := by
    simpa [prefixWord, tailWord_253687, baseEnd_253687] using wordTrace_append hprefix tailTrace_253687
  have hstable : (prefixWord ++ tailWord_253687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253687).length < 2 ^ (prefixWord ++ tailWord_253687).sum := by decide
  have hdescent : baseEnd_253687 < baseStart_253687 := by decide
  rcases family_descends (prefixWord ++ tailWord_253687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253708 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_253708 : Nat := 118140960795 + 253708 * 2 ^ 59
def prefixEnd_253708 : Nat := 4983230072969 + 3 ^ 40 * 253708 * 2
def baseEnd_253708 : Nat := 115799244347554311096199

theorem tailTrace_253708 : CollatzResearch.WordTrace tailWord_253708 prefixEnd_253708 115799244347554311096199 := by
  unfold tailWord_253708
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626745482433360360920889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6168993976577813814561185 4626745482433360360920889)
  ·
    refine ⟨3470059111825020270690667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4626745482433360360920889 3470059111825020270690667)
    ·
      refine ⟨5205088667737530406036001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470059111825020270690667 5205088667737530406036001)
      ·
        refine ⟨3903816500803147804527001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5205088667737530406036001 3903816500803147804527001)
        ·
          refine ⟨2927862375602360853395251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3903816500803147804527001 2927862375602360853395251)
          ·
            refine ⟨4391793563403541280092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927862375602360853395251 4391793563403541280092877)
            ·
              refine ⟨1646922586276327980034829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4391793563403541280092877 1646922586276327980034829)
              ·
                refine ⟨617595969853622992513061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646922586276327980034829 617595969853622992513061)
                ·
                  refine ⟨115799244347554311096199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617595969853622992513061 115799244347554311096199)
                  ·
                    rfl

theorem cell20_253708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_253708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253708 prefixEnd_253708 := by exact prefixLift 253708
  have htrace : WordTrace (prefixWord ++ tailWord_253708) baseStart_253708 baseEnd_253708 := by
    simpa [prefixWord, tailWord_253708, baseEnd_253708] using wordTrace_append hprefix tailTrace_253708
  have hstable : (prefixWord ++ tailWord_253708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253708).length < 2 ^ (prefixWord ++ tailWord_253708).sum := by decide
  have hdescent : baseEnd_253708 < baseStart_253708 := by decide
  rcases family_descends (prefixWord ++ tailWord_253708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253714 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_253714 : Nat := 118140960795 + 253714 * 2 ^ 59
def prefixEnd_253714 : Nat := 4983230072969 + 3 ^ 40 * 253714 * 2
def baseEnd_253714 : Nat := 115801982911044956896175

theorem tailTrace_253714 : CollatzResearch.WordTrace tailWord_253714 prefixEnd_253714 115801982911044956896175 := by
  unfold tailWord_253714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313427450711245936640049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6169139868563322497706797 2313427450711245936640049)
  ·
    refine ⟨1735070588033434452480037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2313427450711245936640049 1735070588033434452480037)
    ·
      refine ⟨325325735256268959840007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1735070588033434452480037 325325735256268959840007)
      ·
        refine ⟨487988602884403439760011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325325735256268959840007 487988602884403439760011)
        ·
          refine ⟨731982904326605159640017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487988602884403439760011 731982904326605159640017)
          ·
            refine ⟨548987178244953869730013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731982904326605159640017 548987178244953869730013)
            ·
              refine ⟨205870191841857701148755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548987178244953869730013 205870191841857701148755)
              ·
                refine ⟨308805287762786551723133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205870191841857701148755 308805287762786551723133)
                ·
                  refine ⟨115801982911044956896175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308805287762786551723133 115801982911044956896175)
                  ·
                    rfl

theorem cell20_253714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_253714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253714 prefixEnd_253714 := by exact prefixLift 253714
  have htrace : WordTrace (prefixWord ++ tailWord_253714) baseStart_253714 baseEnd_253714 := by
    simpa [prefixWord, tailWord_253714, baseEnd_253714] using wordTrace_append hprefix tailTrace_253714
  have hstable : (prefixWord ++ tailWord_253714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253714).length < 2 ^ (prefixWord ++ tailWord_253714).sum := by decide
  have hdescent : baseEnd_253714 < baseStart_253714 := by decide
  rcases family_descends (prefixWord ++ tailWord_253714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253732 : List Nat := [2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_253732 : Nat := 118140960795 + 253732 * 2 ^ 59
def prefixEnd_253732 : Nat := 4983230072969 + 3 ^ 40 * 253732 * 2
def baseEnd_253732 : Nat := 38603399533838964765367

theorem tailTrace_253732 : CollatzResearch.WordTrace tailWord_253732 prefixEnd_253732 38603399533838964765367 := by
  unfold tailWord_253732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627183158389886410357725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6169577544519848547143633 4627183158389886410357725)
  ·
    refine ⟨1735193684396207403884147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4627183158389886410357725 1735193684396207403884147)
    ·
      refine ⟨2602790526594311105826221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735193684396207403884147 2602790526594311105826221)
      ·
        refine ⟨976046447472866664684833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2602790526594311105826221 976046447472866664684833)
        ·
          refine ⟨732034835604649998513625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976046447472866664684833 732034835604649998513625)
          ·
            refine ⟨549026126703487498885219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732034835604649998513625 549026126703487498885219)
            ·
              refine ⟨823539190055231248327829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549026126703487498885219 823539190055231248327829)
              ·
                refine ⟨38603399533838964765367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 823539190055231248327829 38603399533838964765367)
                ·
                  rfl

theorem cell20_253732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_253732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253732 prefixEnd_253732 := by exact prefixLift 253732
  have htrace : WordTrace (prefixWord ++ tailWord_253732) baseStart_253732 baseEnd_253732 := by
    simpa [prefixWord, tailWord_253732, baseEnd_253732] using wordTrace_append hprefix tailTrace_253732
  have hstable : (prefixWord ++ tailWord_253732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253732).length < 2 ^ (prefixWord ++ tailWord_253732).sum := by decide
  have hdescent : baseEnd_253732 < baseStart_253732 := by decide
  rcases family_descends (prefixWord ++ tailWord_253732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253749 : List Nat := [1, 3, 3, 1, 5, 1, 6]
def baseStart_253749 : Nat := 118140960795 + 253749 * 2 ^ 59
def prefixEnd_253749 : Nat := 4983230072969 + 3 ^ 40 * 253749 * 2
def baseEnd_253749 : Nat := 12868661984971154525485

theorem tailTrace_253749 : CollatzResearch.WordTrace tailWord_253749 prefixEnd_253749 12868661984971154525485 := by
  unfold tailWord_253749
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254986357718184724084301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6169990905145456482722867 9254986357718184724084301)
  ·
    refine ⟨3470619884144319271531613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9254986357718184724084301 3470619884144319271531613)
    ·
      refine ⟨1301482456554119726824355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3470619884144319271531613 1301482456554119726824355)
      ·
        refine ⟨1952223684831179590236533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301482456554119726824355 1952223684831179590236533)
        ·
          refine ⟨183020970452923086584675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1952223684831179590236533 183020970452923086584675)
          ·
            refine ⟨274531455679384629877013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183020970452923086584675 274531455679384629877013)
            ·
              refine ⟨12868661984971154525485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274531455679384629877013 12868661984971154525485)
              ·
                rfl

theorem cell20_253749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 6].length) (baseStart_253749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253749 prefixEnd_253749 := by exact prefixLift 253749
  have htrace : WordTrace (prefixWord ++ tailWord_253749) baseStart_253749 baseEnd_253749 := by
    simpa [prefixWord, tailWord_253749, baseEnd_253749] using wordTrace_append hprefix tailTrace_253749
  have hstable : (prefixWord ++ tailWord_253749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253749).length < 2 ^ (prefixWord ++ tailWord_253749).sum := by decide
  have hdescent : baseEnd_253749 < baseStart_253749 := by decide
  rcases family_descends (prefixWord ++ tailWord_253749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253759 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 2]
def baseStart_253759 : Nat := 118140960795 + 253759 * 2 ^ 59
def prefixEnd_253759 : Nat := 4983230072969 + 3 ^ 40 * 253759 * 2
def baseEnd_253759 : Nat := 115822522137224800395991

theorem tailTrace_253759 : CollatzResearch.WordTrace tailWord_253759 prefixEnd_253759 115822522137224800395991 := by
  unfold tailWord_253759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255351087681956431948331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6170234058454637621298887 9255351087681956431948331)
  ·
    refine ⟨13883026631522934647922497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255351087681956431948331 13883026631522934647922497)
    ·
      refine ⟨10412269973642200985941873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13883026631522934647922497 10412269973642200985941873)
      ·
        refine ⟨7809202480231650739456405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10412269973642200985941873 7809202480231650739456405)
        ·
          refine ⟨366056366260858628412019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7809202480231650739456405 366056366260858628412019)
          ·
            refine ⟨549084549391287942618029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366056366260858628412019 549084549391287942618029)
            ·
              refine ⟨205906706021732978481761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549084549391287942618029 205906706021732978481761)
              ·
                refine ⟨154430029516299733861321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205906706021732978481761 154430029516299733861321)
                ·
                  refine ⟨115822522137224800395991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154430029516299733861321 115822522137224800395991)
                  ·
                    rfl

theorem cell20_253759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2].length) (baseStart_253759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253759 prefixEnd_253759 := by exact prefixLift 253759
  have htrace : WordTrace (prefixWord ++ tailWord_253759) baseStart_253759 baseEnd_253759 := by
    simpa [prefixWord, tailWord_253759, baseEnd_253759] using wordTrace_append hprefix tailTrace_253759
  have hstable : (prefixWord ++ tailWord_253759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253759).length < 2 ^ (prefixWord ++ tailWord_253759).sum := by decide
  have hdescent : baseEnd_253759 < baseStart_253759 := by decide
  rcases family_descends (prefixWord ++ tailWord_253759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253763 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_253763 : Nat := 118140960795 + 253763 * 2 ^ 59
def prefixEnd_253763 : Nat := 4983230072969 + 3 ^ 40 * 253763 * 2
def baseEnd_253763 : Nat := 115824347846218564262641

theorem tailTrace_253763 : CollatzResearch.WordTrace tailWord_253763 prefixEnd_253763 115824347846218564262641 := by
  unfold tailWord_253763
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255496979667465115093943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6170331319778310076729295 9255496979667465115093943)
  ·
    refine ⟨13883245469501197672640915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255496979667465115093943 13883245469501197672640915)
    ·
      refine ⟨20824868204251796508961373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13883245469501197672640915 20824868204251796508961373)
      ·
        refine ⟨7809325576594423690860515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20824868204251796508961373 7809325576594423690860515)
        ·
          refine ⟨11713988364891635536290773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809325576594423690860515 11713988364891635536290773)
          ·
            refine ⟨274546602302147707881815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11713988364891635536290773 274546602302147707881815)
            ·
              refine ⟨411819903453221561822723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274546602302147707881815 411819903453221561822723)
              ·
                refine ⟨617729855179832342734085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411819903453221561822723 617729855179832342734085)
                ·
                  refine ⟨115824347846218564262641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617729855179832342734085 115824347846218564262641)
                  ·
                    rfl

theorem cell20_253763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_253763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253763 prefixEnd_253763 := by exact prefixLift 253763
  have htrace : WordTrace (prefixWord ++ tailWord_253763) baseStart_253763 baseEnd_253763 := by
    simpa [prefixWord, tailWord_253763, baseEnd_253763] using wordTrace_append hprefix tailTrace_253763
  have hstable : (prefixWord ++ tailWord_253763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253763).length < 2 ^ (prefixWord ++ tailWord_253763).sum := by decide
  have hdescent : baseEnd_253763 < baseStart_253763 := by decide
  rcases family_descends (prefixWord ++ tailWord_253763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253766 : List Nat := [6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_253766 : Nat := 118140960795 + 253766 * 2 ^ 59
def prefixEnd_253766 : Nat := 4983230072969 + 3 ^ 40 * 253766 * 2
def baseEnd_253766 : Nat := 38608572375987962387543

theorem tailTrace_253766 : CollatzResearch.WordTrace tailWord_253766 prefixEnd_253766 38608572375987962387543 := by
  unfold tailWord_253766
  simp only [CollatzResearch.WordTrace]
  refine ⟨289237699958018644607911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6170404265771064418302101 289237699958018644607911)
  ·
    refine ⟨433856549937027966911867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289237699958018644607911 433856549937027966911867)
    ·
      refine ⟨650784824905541950367801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433856549937027966911867 650784824905541950367801)
      ·
        refine ⟨488088618679156462775851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650784824905541950367801 488088618679156462775851)
        ·
          refine ⟨732132928018734694163777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488088618679156462775851 732132928018734694163777)
          ·
            refine ⟨549099696014051020622833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732132928018734694163777 549099696014051020622833)
            ·
              refine ⟨411824772010538265467125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549099696014051020622833 411824772010538265467125)
              ·
                refine ⟨38608572375987962387543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411824772010538265467125 38608572375987962387543)
                ·
                  rfl

theorem cell20_253766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_253766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253766 prefixEnd_253766 := by exact prefixLift 253766
  have htrace : WordTrace (prefixWord ++ tailWord_253766) baseStart_253766 baseEnd_253766 := by
    simpa [prefixWord, tailWord_253766, baseEnd_253766] using wordTrace_append hprefix tailTrace_253766
  have hstable : (prefixWord ++ tailWord_253766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253766).length < 2 ^ (prefixWord ++ tailWord_253766).sum := by decide
  have hdescent : baseEnd_253766 < baseStart_253766 := by decide
  rcases family_descends (prefixWord ++ tailWord_253766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253773 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_253773 : Nat := 118140960795 + 253773 * 2 ^ 59
def prefixEnd_253773 : Nat := 4983230072969 + 3 ^ 40 * 253773 * 2
def baseEnd_253773 : Nat := 115828912118702973929267

theorem tailTrace_253773 : CollatzResearch.WordTrace tailWord_253773 prefixEnd_253773 115828912118702973929267 := by
  unfold tailWord_253773
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255861709631236822957973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6170574473087491215305315 9255861709631236822957973)
  ·
    refine ⟨433868517638964226076155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9255861709631236822957973 433868517638964226076155)
    ·
      refine ⟨650802776458446339114233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433868517638964226076155 650802776458446339114233)
      ·
        refine ⟨488102082343834754335675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650802776458446339114233 488102082343834754335675)
        ·
          refine ⟨732153123515752131503513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488102082343834754335675 732153123515752131503513)
          ·
            refine ⟨549114842636814098627635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732153123515752131503513 549114842636814098627635)
            ·
              refine ⟨823672263955221147941453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549114842636814098627635 823672263955221147941453)
              ·
                refine ⟨308877098983207930478045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823672263955221147941453 308877098983207930478045)
                ·
                  refine ⟨115828912118702973929267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308877098983207930478045 115828912118702973929267)
                  ·
                    rfl

theorem cell20_253773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_253773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253773 prefixEnd_253773 := by exact prefixLift 253773
  have htrace : WordTrace (prefixWord ++ tailWord_253773) baseStart_253773 baseEnd_253773 := by
    simpa [prefixWord, tailWord_253773, baseEnd_253773] using wordTrace_append hprefix tailTrace_253773
  have hstable : (prefixWord ++ tailWord_253773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253773).length < 2 ^ (prefixWord ++ tailWord_253773).sum := by decide
  have hdescent : baseEnd_253773 < baseStart_253773 := by decide
  rcases family_descends (prefixWord ++ tailWord_253773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253791 : List Nat := [1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_253791 : Nat := 118140960795 + 253791 * 2 ^ 59
def prefixEnd_253791 : Nat := 4983230072969 + 3 ^ 40 * 253791 * 2
def baseEnd_253791 : Nat := 38612375936391637109731

theorem tailTrace_253791 : CollatzResearch.WordTrace tailWord_253791 prefixEnd_253791 38612375936391637109731 := by
  unfold tailWord_253791
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256518223566025897113227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6171012149044017264742151 9256518223566025897113227)
  ·
    refine ⟨13884777335349038845669841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9256518223566025897113227 13884777335349038845669841)
    ·
      refine ⟨10413583001511779134252381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13884777335349038845669841 10413583001511779134252381)
      ·
        refine ⟨3905093625566917175344643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10413583001511779134252381 3905093625566917175344643)
        ·
          refine ⟨5857640438350375763016965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905093625566917175344643 5857640438350375763016965)
          ·
            refine ⟨1098307582190695455565681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5857640438350375763016965 1098307582190695455565681)
            ·
              refine ⟨823730686643021591674261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098307582190695455565681 823730686643021591674261)
              ·
                refine ⟨38612375936391637109731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 823730686643021591674261 38612375936391637109731)
                ·
                  rfl

theorem cell20_253791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_253791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253791 prefixEnd_253791 := by exact prefixLift 253791
  have htrace : WordTrace (prefixWord ++ tailWord_253791) baseStart_253791 baseEnd_253791 := by
    simpa [prefixWord, tailWord_253791, baseEnd_253791] using wordTrace_append hprefix tailTrace_253791
  have hstable : (prefixWord ++ tailWord_253791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253791).length < 2 ^ (prefixWord ++ tailWord_253791).sum := by decide
  have hdescent : baseEnd_253791 < baseStart_253791 := by decide
  rcases family_descends (prefixWord ++ tailWord_253791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253818 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_253818 : Nat := 118140960795 + 253818 * 2 ^ 59
def prefixEnd_253818 : Nat := 4983230072969 + 3 ^ 40 * 253818 * 2
def baseEnd_253818 : Nat := 115849451344882817429083

theorem tailTrace_253818 : CollatzResearch.WordTrace tailWord_253818 prefixEnd_253818 115849451344882817429083 := by
  unfold tailWord_253818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314375748617052377086527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6171668662978806338897405 2314375748617052377086527)
  ·
    refine ⟨3471563622925578565629791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314375748617052377086527 3471563622925578565629791)
    ·
      refine ⟨5207345434388367848444687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471563622925578565629791 5207345434388367848444687)
      ·
        refine ⟨7811018151582551772667031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5207345434388367848444687 7811018151582551772667031)
        ·
          refine ⟨11716527227373827659000547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811018151582551772667031 11716527227373827659000547)
          ·
            refine ⟨17574790841060741488500821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11716527227373827659000547 17574790841060741488500821)
            ·
              refine ⟨205954580168680564318369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 17574790841060741488500821 205954580168680564318369)
              ·
                refine ⟨154465935126510423238777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205954580168680564318369 154465935126510423238777)
                ·
                  refine ⟨115849451344882817429083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154465935126510423238777 115849451344882817429083)
                  ·
                    rfl

theorem cell20_253818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_253818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253818 prefixEnd_253818 := by exact prefixLift 253818
  have htrace : WordTrace (prefixWord ++ tailWord_253818) baseStart_253818 baseEnd_253818 := by
    simpa [prefixWord, tailWord_253818, baseEnd_253818] using wordTrace_append hprefix tailTrace_253818
  have hstable : (prefixWord ++ tailWord_253818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253818).length < 2 ^ (prefixWord ++ tailWord_253818).sum := by decide
  have hdescent : baseEnd_253818 < baseStart_253818 := by decide
  rcases family_descends (prefixWord ++ tailWord_253818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253836 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_253836 : Nat := 118140960795 + 253836 * 2 ^ 59
def prefixEnd_253836 : Nat := 4983230072969 + 3 ^ 40 * 253836 * 2
def baseEnd_253836 : Nat := 115857667035354754829009

theorem tailTrace_253836 : CollatzResearch.WordTrace tailWord_253836 prefixEnd_253836 115857667035354754829009 := by
  unfold tailWord_253836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629079754201499291250681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6172106338935332388334241 4629079754201499291250681)
  ·
    refine ⟨3471809815651124468438011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4629079754201499291250681 3471809815651124468438011)
    ·
      refine ⟨5207714723476686702657017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471809815651124468438011 5207714723476686702657017)
      ·
        refine ⟨3905786042607515026992763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5207714723476686702657017 3905786042607515026992763)
        ·
          refine ⟨5858679063911272540489145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905786042607515026992763 5858679063911272540489145)
          ·
            refine ⟨4394009297933454405366859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5858679063911272540489145 4394009297933454405366859)
            ·
              refine ⟨6591013946900181608050289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394009297933454405366859 6591013946900181608050289)
              ·
                refine ⟨4943260460175136206037717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591013946900181608050289 4943260460175136206037717)
                ·
                  refine ⟨115857667035354754829009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4943260460175136206037717 115857667035354754829009)
                  ·
                    rfl

theorem cell20_253836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_253836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253836 prefixEnd_253836 := by exact prefixLift 253836
  have htrace : WordTrace (prefixWord ++ tailWord_253836) baseStart_253836 baseEnd_253836 := by
    simpa [prefixWord, tailWord_253836, baseEnd_253836] using wordTrace_append hprefix tailTrace_253836
  have hstable : (prefixWord ++ tailWord_253836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253836).length < 2 ^ (prefixWord ++ tailWord_253836).sum := by decide
  have hdescent : baseEnd_253836 < baseStart_253836 := by decide
  rcases family_descends (prefixWord ++ tailWord_253836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253877 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_253877 : Nat := 118140960795 + 253877 * 2 ^ 59
def prefixEnd_253877 : Nat := 4983230072969 + 3 ^ 40 * 253877 * 2
def baseEnd_253877 : Nat := 115876380552540834462175

theorem tailTrace_253877 : CollatzResearch.WordTrace tailWord_253877 prefixEnd_253877 115876380552540834462175 := by
  unfold tailWord_253877
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259654901254462584743885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6173103267502975056495923 9259654901254462584743885)
  ·
    refine ⟨3472370587970423469278957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9259654901254462584743885 3472370587970423469278957)
    ·
      refine ⟨1302138970488908800979609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3472370587970423469278957 1302138970488908800979609)
      ·
        refine ⟨976604227866681600734707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302138970488908800979609 976604227866681600734707)
        ·
          refine ⟨1464906341800022401102061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976604227866681600734707 1464906341800022401102061)
          ·
            refine ⟨549339878175008400413273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1464906341800022401102061 549339878175008400413273)
            ·
              refine ⟨412004908631256300309955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549339878175008400413273 412004908631256300309955)
              ·
                refine ⟨618007362946884450464933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412004908631256300309955 618007362946884450464933)
                ·
                  refine ⟨115876380552540834462175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618007362946884450464933 115876380552540834462175)
                  ·
                    rfl

theorem cell20_253877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_253877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253877 prefixEnd_253877 := by exact prefixLift 253877
  have htrace : WordTrace (prefixWord ++ tailWord_253877) baseStart_253877 baseEnd_253877 := by
    simpa [prefixWord, tailWord_253877, baseEnd_253877] using wordTrace_append hprefix tailTrace_253877
  have hstable : (prefixWord ++ tailWord_253877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253877).length < 2 ^ (prefixWord ++ tailWord_253877).sum := by decide
  have hdescent : baseEnd_253877 < baseStart_253877 := by decide
  rcases family_descends (prefixWord ++ tailWord_253877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253898 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_253898 : Nat := 118140960795 + 253898 * 2 ^ 59
def prefixEnd_253898 : Nat := 4983230072969 + 3 ^ 40 * 253898 * 2
def baseEnd_253898 : Nat := 115885965524758094762089

theorem tailTrace_253898 : CollatzResearch.WordTrace tailWord_253898 prefixEnd_253898 115885965524758094762089 := by
  unfold tailWord_253898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315105208544595792814587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6173613889452255447505565 2315105208544595792814587)
  ·
    refine ⟨3472657812816893689221881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2315105208544595792814587 3472657812816893689221881)
    ·
      refine ⟨2604493359612670266916411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3472657812816893689221881 2604493359612670266916411)
      ·
        refine ⟨3906740039419005400374617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2604493359612670266916411 3906740039419005400374617)
        ·
          refine ⟨2930055029564254050280963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3906740039419005400374617 2930055029564254050280963)
          ·
            refine ⟨4395082544346381075421445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930055029564254050280963 4395082544346381075421445)
            ·
              refine ⟨824077977064946451641521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4395082544346381075421445 824077977064946451641521)
              ·
                refine ⟨618058482798709838731141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824077977064946451641521 618058482798709838731141)
                ·
                  refine ⟨115885965524758094762089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618058482798709838731141 115885965524758094762089)
                  ·
                    rfl

theorem cell20_253898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_253898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253898 prefixEnd_253898 := by exact prefixLift 253898
  have htrace : WordTrace (prefixWord ++ tailWord_253898) baseStart_253898 baseEnd_253898 := by
    simpa [prefixWord, tailWord_253898, baseEnd_253898] using wordTrace_append hprefix tailTrace_253898
  have hstable : (prefixWord ++ tailWord_253898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253898).length < 2 ^ (prefixWord ++ tailWord_253898).sum := by decide
  have hdescent : baseEnd_253898 < baseStart_253898 := by decide
  rcases family_descends (prefixWord ++ tailWord_253898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253912 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_253912 : Nat := 118140960795 + 253912 * 2 ^ 59
def prefixEnd_253912 : Nat := 4983230072969 + 3 ^ 40 * 253912 * 2
def baseEnd_253912 : Nat := 115892355506236268295365

theorem tailTrace_253912 : CollatzResearch.WordTrace tailWord_253912 prefixEnd_253912 115892355506236268295365 := by
  unfold tailWord_253912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4630465728063831781133995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6173954304085109041511993 4630465728063831781133995)
  ·
    refine ⟨6945698592095747671700993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4630465728063831781133995 6945698592095747671700993)
    ·
      refine ⟨5209273944071810753775745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6945698592095747671700993 5209273944071810753775745)
      ·
        refine ⟨3906955458053858065331809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5209273944071810753775745 3906955458053858065331809)
        ·
          refine ⟨2930216593540393548998857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3906955458053858065331809 2930216593540393548998857)
          ·
            refine ⟨2197662445155295161749143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2930216593540393548998857 2197662445155295161749143)
            ·
              refine ⟨3296493667732942742623715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197662445155295161749143 3296493667732942742623715)
              ·
                refine ⟨4944740501599414113935573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296493667732942742623715 4944740501599414113935573)
                ·
                  refine ⟨115892355506236268295365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4944740501599414113935573 115892355506236268295365)
                  ·
                    rfl

theorem cell20_253912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_253912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253912 prefixEnd_253912 := by exact prefixLift 253912
  have htrace : WordTrace (prefixWord ++ tailWord_253912) baseStart_253912 baseEnd_253912 := by
    simpa [prefixWord, tailWord_253912, baseEnd_253912] using wordTrace_append hprefix tailTrace_253912
  have hstable : (prefixWord ++ tailWord_253912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253912).length < 2 ^ (prefixWord ++ tailWord_253912).sum := by decide
  have hdescent : baseEnd_253912 < baseStart_253912 := by decide
  rcases family_descends (prefixWord ++ tailWord_253912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253936 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_253936 : Nat := 118140960795 + 253936 * 2 ^ 59
def prefixEnd_253936 : Nat := 4983230072969 + 3 ^ 40 * 253936 * 2
def baseEnd_253936 : Nat := 115903309760198851495267

theorem tailTrace_253936 : CollatzResearch.WordTrace tailWord_253936 prefixEnd_253936 115903309760198851495267 := by
  unfold tailWord_253936
  simp only [CollatzResearch.WordTrace]
  refine ⟨4630903404020357830570831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6174537872027143774094441 4630903404020357830570831)
  ·
    refine ⟨6946355106030536745856247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4630903404020357830570831 6946355106030536745856247)
    ·
      refine ⟨10419532659045805118784371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946355106030536745856247 10419532659045805118784371)
      ·
        refine ⟨15629298988568707678176557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419532659045805118784371 15629298988568707678176557)
        ·
          refine ⟨5860987120713265379316209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15629298988568707678176557 5860987120713265379316209)
          ·
            refine ⟨4395740340534949034487157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5860987120713265379316209 4395740340534949034487157)
            ·
              refine ⟨412100656925151471983171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4395740340534949034487157 412100656925151471983171)
              ·
                refine ⟨618150985387727207974757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412100656925151471983171 618150985387727207974757)
                ·
                  refine ⟨115903309760198851495267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618150985387727207974757 115903309760198851495267)
                  ·
                    rfl

theorem cell20_253936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_253936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253936 prefixEnd_253936 := by exact prefixLift 253936
  have htrace : WordTrace (prefixWord ++ tailWord_253936) baseStart_253936 baseEnd_253936 := by
    simpa [prefixWord, tailWord_253936, baseEnd_253936] using wordTrace_append hprefix tailTrace_253936
  have hstable : (prefixWord ++ tailWord_253936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253936).length < 2 ^ (prefixWord ++ tailWord_253936).sum := by decide
  have hdescent : baseEnd_253936 < baseStart_253936 := by decide
  rcases family_descends (prefixWord ++ tailWord_253936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253942 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_253942 : Nat := 118140960795 + 253942 * 2 ^ 59
def prefixEnd_253942 : Nat := 4983230072969 + 3 ^ 40 * 253942 * 2
def baseEnd_253942 : Nat := 115906048323689497295243

theorem tailTrace_253942 : CollatzResearch.WordTrace tailWord_253942 prefixEnd_253942 115906048323689497295243 := by
  unfold tailWord_253942
  simp only [CollatzResearch.WordTrace]
  refine ⟨578876602876186167866255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6174683764012652457240053 578876602876186167866255)
  ·
    refine ⟨868314904314279251799383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 578876602876186167866255 868314904314279251799383)
    ·
      refine ⟨1302472356471418877699075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868314904314279251799383 1302472356471418877699075)
      ·
        refine ⟨1953708534707128316548613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302472356471418877699075 1953708534707128316548613)
        ·
          refine ⟨366320350257586559352865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1953708534707128316548613 366320350257586559352865)
          ·
            refine ⟨274740262693189919514649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366320350257586559352865 274740262693189919514649)
            ·
              refine ⟨206055197019892439635987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274740262693189919514649 206055197019892439635987)
              ·
                refine ⟨309082795529838659453981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206055197019892439635987 309082795529838659453981)
                ·
                  refine ⟨115906048323689497295243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309082795529838659453981 115906048323689497295243)
                  ·
                    rfl

theorem cell20_253942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_253942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253942 prefixEnd_253942 := by exact prefixLift 253942
  have htrace : WordTrace (prefixWord ++ tailWord_253942) baseStart_253942 baseEnd_253942 := by
    simpa [prefixWord, tailWord_253942, baseEnd_253942] using wordTrace_append hprefix tailTrace_253942
  have hstable : (prefixWord ++ tailWord_253942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253942).length < 2 ^ (prefixWord ++ tailWord_253942).sum := by decide
  have hdescent : baseEnd_253942 < baseStart_253942 := by decide
  rcases family_descends (prefixWord ++ tailWord_253942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253981 : List Nat := [1, 4, 2, 2, 2, 9]
def baseStart_253981 : Nat := 118140960795 + 253981 * 2 ^ 59
def prefixEnd_253981 : Nat := 4983230072969 + 3 ^ 40 * 253981 * 2
def baseEnd_253981 : Nat := 4293475888384396110929

theorem tailTrace_253981 : CollatzResearch.WordTrace tailWord_253981 prefixEnd_253981 4293475888384396110929 := by
  unfold tailWord_253981
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263448092877688346529797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6175632061918458897686531 9263448092877688346529797)
  ·
    refine ⟨1736896517414566564974337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9263448092877688346529797 1736896517414566564974337)
    ·
      refine ⟨1302672388060924923730753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1736896517414566564974337 1302672388060924923730753)
      ·
        refine ⟨977004291045693692798065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302672388060924923730753 977004291045693692798065)
        ·
          refine ⟨732753218284270269598549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977004291045693692798065 732753218284270269598549)
          ·
            refine ⟨4293475888384396110929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 732753218284270269598549 4293475888384396110929)
            ·
              rfl

theorem cell20_253981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 9].length) (baseStart_253981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253981 prefixEnd_253981 := by exact prefixLift 253981
  have htrace : WordTrace (prefixWord ++ tailWord_253981) baseStart_253981 baseEnd_253981 := by
    simpa [prefixWord, tailWord_253981, baseEnd_253981] using wordTrace_append hprefix tailTrace_253981
  have hstable : (prefixWord ++ tailWord_253981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253981).length < 2 ^ (prefixWord ++ tailWord_253981).sum := by decide
  have hdescent : baseEnd_253981 < baseStart_253981 := by decide
  rcases family_descends (prefixWord ++ tailWord_253981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253998 : List Nat := [4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_253998 : Nat := 118140960795 + 253998 * 2 ^ 59
def prefixEnd_253998 : Nat := 4983230072969 + 3 ^ 40 * 253998 * 2
def baseEnd_253998 : Nat := 38643869416534063809449

theorem tailTrace_253998 : CollatzResearch.WordTrace tailWord_253998 prefixEnd_253998 38643869416534063809449 := by
  unfold tailWord_253998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158008516727012531237331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6176045422544066833265765 1158008516727012531237331)
  ·
    refine ⟨1737012775090518796855997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1158008516727012531237331 1737012775090518796855997)
    ·
      refine ⟨651379790658944548820999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1737012775090518796855997 651379790658944548820999)
      ·
        refine ⟨977069685988416823231499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651379790658944548820999 977069685988416823231499)
        ·
          refine ⟨1465604528982625234847249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977069685988416823231499 1465604528982625234847249)
          ·
            refine ⟨1099203396736968926135437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465604528982625234847249 1099203396736968926135437)
            ·
              refine ⟨412201273776363347300789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099203396736968926135437 412201273776363347300789)
              ·
                refine ⟨38643869416534063809449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 412201273776363347300789 38643869416534063809449)
                ·
                  rfl

theorem cell20_253998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_253998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_253998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_253998 prefixEnd_253998 := by exact prefixLift 253998
  have htrace : WordTrace (prefixWord ++ tailWord_253998) baseStart_253998 baseEnd_253998 := by
    simpa [prefixWord, tailWord_253998, baseEnd_253998] using wordTrace_append hprefix tailTrace_253998
  have hstable : (prefixWord ++ tailWord_253998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253998).length < 2 ^ (prefixWord ++ tailWord_253998).sum := by decide
  have hdescent : baseEnd_253998 < baseStart_253998 := by decide
  rcases family_descends (prefixWord ++ tailWord_253998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254005 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_254005 : Nat := 118140960795 + 254005 * 2 ^ 59
def prefixEnd_254005 : Nat := 4983230072969 + 3 ^ 40 * 254005 * 2
def baseEnd_254005 : Nat := 115934803240341278194985

theorem tailTrace_254005 : CollatzResearch.WordTrace tailWord_254005 prefixEnd_254005 115934803240341278194985 := by
  unfold tailWord_254005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264323444790740445403469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6176215629860493630268979 9264323444790740445403469)
  ·
    refine ⟨3474121291796527667026301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9264323444790740445403469 3474121291796527667026301)
    ·
      refine ⟨1302795484423697875134863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3474121291796527667026301 1302795484423697875134863)
      ·
        refine ⟨1954193226635546812702295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302795484423697875134863 1954193226635546812702295)
        ·
          refine ⟨2931289839953320219053443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954193226635546812702295 2931289839953320219053443)
          ·
            refine ⟨4396934759929980328580165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931289839953320219053443 4396934759929980328580165)
            ·
              refine ⟨824425267486871311608781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4396934759929980328580165 824425267486871311608781)
              ·
                refine ⟨309159475307576741853293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824425267486871311608781 309159475307576741853293)
                ·
                  refine ⟨115934803240341278194985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309159475307576741853293 115934803240341278194985)
                  ·
                    rfl

theorem cell20_254005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_254005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254005 prefixEnd_254005 := by exact prefixLift 254005
  have htrace : WordTrace (prefixWord ++ tailWord_254005) baseStart_254005 baseEnd_254005 := by
    simpa [prefixWord, tailWord_254005, baseEnd_254005] using wordTrace_append hprefix tailTrace_254005
  have hstable : (prefixWord ++ tailWord_254005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254005).length < 2 ^ (prefixWord ++ tailWord_254005).sum := by decide
  have hdescent : baseEnd_254005 < baseStart_254005 := by decide
  rcases family_descends (prefixWord ++ tailWord_254005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254012 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_254012 : Nat := 118140960795 + 254012 * 2 ^ 59
def prefixEnd_254012 : Nat := 4983230072969 + 3 ^ 40 * 254012 * 2
def baseEnd_254012 : Nat := 115937998231080364961623

theorem tailTrace_254012 : CollatzResearch.WordTrace tailWord_254012 prefixEnd_254012 115937998231080364961623 := by
  unfold tailWord_254012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632289377882690320454145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6176385837176920427272193 4632289377882690320454145)
  ·
    refine ⟨3474217033412017740340609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4632289377882690320454145 3474217033412017740340609)
    ·
      refine ⟨2605662775059013305255457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3474217033412017740340609 2605662775059013305255457)
      ·
        refine ⟨1954247081294259978941593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2605662775059013305255457 1954247081294259978941593)
        ·
          refine ⟨1465685310970694984206195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954247081294259978941593 1465685310970694984206195)
          ·
            refine ⟨2198527966456042476309293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465685310970694984206195 2198527966456042476309293)
            ·
              refine ⟨824447987421015928615985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2198527966456042476309293 824447987421015928615985)
              ·
                refine ⟨618335990565761946461989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824447987421015928615985 618335990565761946461989)
                ·
                  refine ⟨115937998231080364961623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618335990565761946461989 115937998231080364961623)
                  ·
                    rfl

theorem cell20_254012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_254012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254012 prefixEnd_254012 := by exact prefixLift 254012
  have htrace : WordTrace (prefixWord ++ tailWord_254012) baseStart_254012 baseEnd_254012 := by
    simpa [prefixWord, tailWord_254012, baseEnd_254012] using wordTrace_append hprefix tailTrace_254012
  have hstable : (prefixWord ++ tailWord_254012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254012).length < 2 ^ (prefixWord ++ tailWord_254012).sum := by decide
  have hdescent : baseEnd_254012 < baseStart_254012 := by decide
  rcases family_descends (prefixWord ++ tailWord_254012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254022 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_254022 : Nat := 118140960795 + 254022 * 2 ^ 59
def prefixEnd_254022 : Nat := 4983230072969 + 3 ^ 40 * 254022 * 2
def baseEnd_254022 : Nat := 115942562503564774628249

theorem tailTrace_254022 : CollatzResearch.WordTrace tailWord_254022 prefixEnd_254022 115942562503564774628249 := by
  unfold tailWord_254022
  simp only [CollatzResearch.WordTrace]
  refine ⟨289529483929036010899135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6176628990486101565848213 289529483929036010899135)
  ·
    refine ⟨434294225893554016348703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289529483929036010899135 434294225893554016348703)
    ·
      refine ⟨651441338840331024523055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434294225893554016348703 651441338840331024523055)
      ·
        refine ⟨977162008260496536784583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651441338840331024523055 977162008260496536784583)
        ·
          refine ⟨1465743012390744805176875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977162008260496536784583 1465743012390744805176875)
          ·
            refine ⟨2198614518586117207765313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465743012390744805176875 2198614518586117207765313)
            ·
              refine ⟨1648960888939587905823985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198614518586117207765313 1648960888939587905823985)
              ·
                refine ⟨1236720666704690929367989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648960888939587905823985 1236720666704690929367989)
                ·
                  refine ⟨115942562503564774628249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1236720666704690929367989 115942562503564774628249)
                  ·
                    rfl

theorem cell20_254022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_254022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254022 prefixEnd_254022 := by exact prefixLift 254022
  have htrace : WordTrace (prefixWord ++ tailWord_254022) baseStart_254022 baseEnd_254022 := by
    simpa [prefixWord, tailWord_254022, baseEnd_254022] using wordTrace_append hprefix tailTrace_254022
  have hstable : (prefixWord ++ tailWord_254022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254022).length < 2 ^ (prefixWord ++ tailWord_254022).sum := by decide
  have hdescent : baseEnd_254022 < baseStart_254022 := by decide
  rcases family_descends (prefixWord ++ tailWord_254022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254026 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_254026 : Nat := 118140960795 + 254026 * 2 ^ 59
def prefixEnd_254026 : Nat := 4983230072969 + 3 ^ 40 * 254026 * 2
def baseEnd_254026 : Nat := 115944388212558538494899

theorem tailTrace_254026 : CollatzResearch.WordTrace tailWord_254026 prefixEnd_254026 115944388212558538494899 := by
  unfold tailWord_254026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316272344428665257979483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6176726251809774021278621 2316272344428665257979483)
  ·
    refine ⟨3474408516642997886969225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316272344428665257979483 3474408516642997886969225)
    ·
      refine ⟨2605806387482248415226919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3474408516642997886969225 2605806387482248415226919)
      ·
        refine ⟨3908709581223372622840379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605806387482248415226919 3908709581223372622840379)
        ·
          refine ⟨5863064371835058934260569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908709581223372622840379 5863064371835058934260569)
          ·
            refine ⟨4397298278876294200695427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5863064371835058934260569 4397298278876294200695427)
            ·
              refine ⟨6595947418314441301043141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397298278876294200695427 6595947418314441301043141)
              ·
                refine ⟨1236740140933957743945589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6595947418314441301043141 1236740140933957743945589)
                ·
                  refine ⟨115944388212558538494899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1236740140933957743945589 115944388212558538494899)
                  ·
                    rfl

theorem cell20_254026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_254026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254026 prefixEnd_254026 := by exact prefixLift 254026
  have htrace : WordTrace (prefixWord ++ tailWord_254026) baseStart_254026 baseEnd_254026 := by
    simpa [prefixWord, tailWord_254026, baseEnd_254026] using wordTrace_append hprefix tailTrace_254026
  have hstable : (prefixWord ++ tailWord_254026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254026).length < 2 ^ (prefixWord ++ tailWord_254026).sum := by decide
  have hdescent : baseEnd_254026 < baseStart_254026 := by decide
  rcases family_descends (prefixWord ++ tailWord_254026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254033 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_254033 : Nat := 118140960795 + 254033 * 2 ^ 59
def prefixEnd_254033 : Nat := 4983230072969 + 3 ^ 40 * 254033 * 2
def baseEnd_254033 : Nat := 115947583203297625261537

theorem tailTrace_254033 : CollatzResearch.WordTrace tailWord_254033 prefixEnd_254033 115947583203297625261537 := by
  unfold tailWord_254033
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265344688689301227422753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6176896459126200818281835 9265344688689301227422753)
  ·
    refine ⟨6949008516516975920567065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9265344688689301227422753 6949008516516975920567065)
    ·
      refine ⟨5211756387387731940425299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6949008516516975920567065 5211756387387731940425299)
      ·
        refine ⟨7817634581081597910637949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211756387387731940425299 7817634581081597910637949)
        ·
          refine ⟨2931612967905599216489231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7817634581081597910637949 2931612967905599216489231)
          ·
            refine ⟨4397419451858398824733847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931612967905599216489231 4397419451858398824733847)
            ·
              refine ⟨6596129177787598237100771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397419451858398824733847 6596129177787598237100771)
              ·
                refine ⟨9894193766681397355651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596129177787598237100771 9894193766681397355651157)
                ·
                  refine ⟨115947583203297625261537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9894193766681397355651157 115947583203297625261537)
                  ·
                    rfl

theorem cell20_254033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_254033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254033 prefixEnd_254033 := by exact prefixLift 254033
  have htrace : WordTrace (prefixWord ++ tailWord_254033) baseStart_254033 baseEnd_254033 := by
    simpa [prefixWord, tailWord_254033, baseEnd_254033] using wordTrace_append hprefix tailTrace_254033
  have hstable : (prefixWord ++ tailWord_254033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254033).length < 2 ^ (prefixWord ++ tailWord_254033).sum := by decide
  have hdescent : baseEnd_254033 < baseStart_254033 := by decide
  rcases family_descends (prefixWord ++ tailWord_254033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254060 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_254060 : Nat := 118140960795 + 254060 * 2 ^ 59
def prefixEnd_254060 : Nat := 4983230072969 + 3 ^ 40 * 254060 * 2
def baseEnd_254060 : Nat := 115959906739005531361427

theorem tailTrace_254060 : CollatzResearch.WordTrace tailWord_254060 prefixEnd_254060 115959906739005531361427 := by
  unfold tailWord_254060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633164729795742419327817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6177552973060989892437089 4633164729795742419327817)
  ·
    refine ⟨3474873547346806814495863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4633164729795742419327817 3474873547346806814495863)
    ·
      refine ⟨5212310321020210221743795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474873547346806814495863 5212310321020210221743795)
      ·
        refine ⟨7818465481530315332615693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212310321020210221743795 7818465481530315332615693)
        ·
          refine ⟨2931924555573868249730885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7818465481530315332615693 2931924555573868249730885)
          ·
            refine ⟨549735854170100296824541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2931924555573868249730885 549735854170100296824541)
            ·
              refine ⟨206150945313787611309203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549735854170100296824541 206150945313787611309203)
              ·
                refine ⟨309226417970681416963805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206150945313787611309203 309226417970681416963805)
                ·
                  refine ⟨115959906739005531361427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309226417970681416963805 115959906739005531361427)
                  ·
                    rfl

theorem cell20_254060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_254060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254060 prefixEnd_254060 := by exact prefixLift 254060
  have htrace : WordTrace (prefixWord ++ tailWord_254060) baseStart_254060 baseEnd_254060 := by
    simpa [prefixWord, tailWord_254060, baseEnd_254060] using wordTrace_append hprefix tailTrace_254060
  have hstable : (prefixWord ++ tailWord_254060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254060).length < 2 ^ (prefixWord ++ tailWord_254060).sum := by decide
  have hdescent : baseEnd_254060 < baseStart_254060 := by decide
  rcases family_descends (prefixWord ++ tailWord_254060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254150 : List Nat := [6, 1, 2, 11]
def baseStart_254150 : Nat := 118140960795 + 254150 * 2 ^ 59
def prefixEnd_254150 : Nat := 4983230072969 + 3 ^ 40 * 254150 * 2
def baseEnd_254150 : Nat := 477370309429486495313

theorem tailTrace_254150 : CollatzResearch.WordTrace tailWord_254150 prefixEnd_254150 477370309429486495313 := by
  unfold tailWord_254150
  simp only [CollatzResearch.WordTrace]
  refine ⟨289675375914544694044747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6179741352843620139621269 289675375914544694044747)
  ·
    refine ⟨434513063871817041067121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289675375914544694044747 434513063871817041067121)
    ·
      refine ⟨325884797903862780800341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434513063871817041067121 325884797903862780800341)
      ·
        refine ⟨477370309429486495313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 325884797903862780800341 477370309429486495313)
        ·
          rfl

theorem cell20_254150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 11].length) (baseStart_254150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254150 prefixEnd_254150 := by exact prefixLift 254150
  have htrace : WordTrace (prefixWord ++ tailWord_254150) baseStart_254150 baseEnd_254150 := by
    simpa [prefixWord, tailWord_254150, baseEnd_254150] using wordTrace_append hprefix tailTrace_254150
  have hstable : (prefixWord ++ tailWord_254150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254150).length < 2 ^ (prefixWord ++ tailWord_254150).sum := by decide
  have hdescent : baseEnd_254150 < baseStart_254150 := by decide
  rcases family_descends (prefixWord ++ tailWord_254150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254156 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_254156 : Nat := 118140960795 + 254156 * 2 ^ 59
def prefixEnd_254156 : Nat := 4983230072969 + 3 ^ 40 * 254156 * 2
def baseEnd_254156 : Nat := 116003723754855864161035

theorem tailTrace_254156 : CollatzResearch.WordTrace tailWord_254156 prefixEnd_254156 116003723754855864161035 := by
  unfold tailWord_254156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4634915433621846617075161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6179887244829128822766881 4634915433621846617075161)
  ·
    refine ⟨3476186575216384962806371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4634915433621846617075161 3476186575216384962806371)
    ·
      refine ⟨5214279862824577444209557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476186575216384962806371 5214279862824577444209557)
      ·
        refine ⟨244419368569902067697323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5214279862824577444209557 244419368569902067697323)
        ·
          refine ⟨366629052854853101545985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244419368569902067697323 366629052854853101545985)
          ·
            refine ⟨274971789641139826159489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366629052854853101545985 274971789641139826159489)
            ·
              refine ⟨206228842230854869619617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274971789641139826159489 206228842230854869619617)
              ·
                refine ⟨154671631673141152214713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206228842230854869619617 154671631673141152214713)
                ·
                  refine ⟨116003723754855864161035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154671631673141152214713 116003723754855864161035)
                  ·
                    rfl

theorem cell20_254156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_254156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254156 prefixEnd_254156 := by exact prefixLift 254156
  have htrace : WordTrace (prefixWord ++ tailWord_254156) baseStart_254156 baseEnd_254156 := by
    simpa [prefixWord, tailWord_254156, baseEnd_254156] using wordTrace_append hprefix tailTrace_254156
  have hstable : (prefixWord ++ tailWord_254156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254156).length < 2 ^ (prefixWord ++ tailWord_254156).sum := by decide
  have hdescent : baseEnd_254156 < baseStart_254156 := by decide
  rcases family_descends (prefixWord ++ tailWord_254156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_254185 : Nat := 118140960795 + 254185 * 2 ^ 59
def prefixEnd_254185 : Nat := 4983230072969 + 3 ^ 40 * 254185 * 2
def baseEnd_254185 : Nat := 116016960145060652194249

theorem tailTrace_254185 : CollatzResearch.WordTrace tailWord_254185 prefixEnd_254185 116016960145060652194249 := by
  unfold tailWord_254185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270888584138631186956009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6180592389425754124637339 9270888584138631186956009)
  ·
    refine ⟨6953166438103973390217007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9270888584138631186956009 6953166438103973390217007)
    ·
      refine ⟨10429749657155960085325511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953166438103973390217007 10429749657155960085325511)
      ·
        refine ⟨15644624485733940127988267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10429749657155960085325511 15644624485733940127988267)
        ·
          refine ⟨23466936728600910191982401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15644624485733940127988267 23466936728600910191982401)
          ·
            refine ⟨17600202546450682643986801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23466936728600910191982401 17600202546450682643986801)
            ·
              refine ⟨13200151909838011982990101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17600202546450682643986801 13200151909838011982990101)
              ·
                refine ⟨618757120773656811702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13200151909838011982990101 618757120773656811702661)
                ·
                  refine ⟨116016960145060652194249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618757120773656811702661 116016960145060652194249)
                  ·
                    rfl

theorem cell20_254185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_254185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254185 prefixEnd_254185 := by exact prefixLift 254185
  have htrace : WordTrace (prefixWord ++ tailWord_254185) baseStart_254185 baseEnd_254185 := by
    simpa [prefixWord, tailWord_254185, baseEnd_254185] using wordTrace_append hprefix tailTrace_254185
  have hstable : (prefixWord ++ tailWord_254185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254185).length < 2 ^ (prefixWord ++ tailWord_254185).sum := by decide
  have hdescent : baseEnd_254185 < baseStart_254185 := by decide
  rcases family_descends (prefixWord ++ tailWord_254185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254192 : List Nat := [2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_254192 : Nat := 118140960795 + 254192 * 2 ^ 59
def prefixEnd_254192 : Nat := 4983230072969 + 3 ^ 40 * 254192 * 2
def baseEnd_254192 : Nat := 38673385045266579653629

theorem tailTrace_254192 : CollatzResearch.WordTrace tailWord_254192 prefixEnd_254192 38673385045266579653629 := by
  unfold tailWord_254192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635571947556635691230415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6180762596742180921640553 4635571947556635691230415)
  ·
    refine ⟨6953357921334953536845623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4635571947556635691230415 6953357921334953536845623)
    ·
      refine ⟨10430036882002430305268435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953357921334953536845623 10430036882002430305268435)
      ·
        refine ⟨15645055323003645457902653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430036882002430305268435 15645055323003645457902653)
        ·
          refine ⟨5866895746126367046713495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15645055323003645457902653 5866895746126367046713495)
          ·
            refine ⟨8800343619189550570070243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866895746126367046713495 8800343619189550570070243)
            ·
              refine ⟨13200515428784325855105365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800343619189550570070243 13200515428784325855105365)
              ·
                refine ⟨38673385045266579653629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13200515428784325855105365 38673385045266579653629)
                ·
                  rfl

theorem cell20_254192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_254192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254192 prefixEnd_254192 := by exact prefixLift 254192
  have htrace : WordTrace (prefixWord ++ tailWord_254192) baseStart_254192 baseEnd_254192 := by
    simpa [prefixWord, tailWord_254192, baseEnd_254192] using wordTrace_append hprefix tailTrace_254192
  have hstable : (prefixWord ++ tailWord_254192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254192).length < 2 ^ (prefixWord ++ tailWord_254192).sum := by decide
  have hdescent : baseEnd_254192 < baseStart_254192 := by decide
  rcases family_descends (prefixWord ++ tailWord_254192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254240 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_254240 : Nat := 118140960795 + 254240 * 2 ^ 59
def prefixEnd_254240 : Nat := 4983230072969 + 3 ^ 40 * 254240 * 2
def baseEnd_254240 : Nat := 116042063643724905360691

theorem tailTrace_254240 : CollatzResearch.WordTrace tailWord_254240 prefixEnd_254240 116042063643724905360691 := by
  unfold tailWord_254240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636447299469687790104087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6181929732626250386805449 4636447299469687790104087)
  ·
    refine ⟨6954670949204531685156131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4636447299469687790104087 6954670949204531685156131)
    ·
      refine ⟨10432006423806797527734197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954670949204531685156131 10432006423806797527734197)
      ·
        refine ⟨978000602231887268225081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10432006423806797527734197 978000602231887268225081)
        ·
          refine ⟨733500451673915451168811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978000602231887268225081 733500451673915451168811)
          ·
            refine ⟨1100250677510873176753217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733500451673915451168811 1100250677510873176753217)
            ·
              refine ⟨825188008133154882564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100250677510873176753217 825188008133154882564913)
              ·
                refine ⟨618891006099866161923685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825188008133154882564913 618891006099866161923685)
                ·
                  refine ⟨116042063643724905360691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618891006099866161923685 116042063643724905360691)
                  ·
                    rfl

theorem cell20_254240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_254240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254240 prefixEnd_254240 := by exact prefixLift 254240
  have htrace : WordTrace (prefixWord ++ tailWord_254240) baseStart_254240 baseEnd_254240 := by
    simpa [prefixWord, tailWord_254240, baseEnd_254240] using wordTrace_append hprefix tailTrace_254240
  have hstable : (prefixWord ++ tailWord_254240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254240).length < 2 ^ (prefixWord ++ tailWord_254240).sum := by decide
  have hdescent : baseEnd_254240 < baseStart_254240 := by decide
  rcases family_descends (prefixWord ++ tailWord_254240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254288 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_254288 : Nat := 118140960795 + 254288 * 2 ^ 59
def prefixEnd_254288 : Nat := 4983230072969 + 3 ^ 40 * 254288 * 2
def baseEnd_254288 : Nat := 116063972151650071760495

theorem tailTrace_254288 : CollatzResearch.WordTrace tailWord_254288 prefixEnd_254288 116063972151650071760495 := by
  unfold tailWord_254288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637322651382739888977759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6183096868510319851970345 4637322651382739888977759)
  ·
    refine ⟨6955983977074109833466639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637322651382739888977759 6955983977074109833466639)
    ·
      refine ⟨10433975965611164750199959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955983977074109833466639 10433975965611164750199959)
      ·
        refine ⟨15650963948416747125299939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433975965611164750199959 15650963948416747125299939)
        ·
          refine ⟨23476445922625120687949909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15650963948416747125299939 23476445922625120687949909)
          ·
            refine ⟨275114600655763133061913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 23476445922625120687949909 275114600655763133061913)
            ·
              refine ⟨206335950491822349796435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275114600655763133061913 206335950491822349796435)
              ·
                refine ⟨309503925737733524694653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206335950491822349796435 309503925737733524694653)
                ·
                  refine ⟨116063972151650071760495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309503925737733524694653 116063972151650071760495)
                  ·
                    rfl

theorem cell20_254288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_254288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254288 prefixEnd_254288 := by exact prefixLift 254288
  have htrace : WordTrace (prefixWord ++ tailWord_254288) baseStart_254288 baseEnd_254288 := by
    simpa [prefixWord, tailWord_254288, baseEnd_254288] using wordTrace_append hprefix tailTrace_254288
  have hstable : (prefixWord ++ tailWord_254288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254288).length < 2 ^ (prefixWord ++ tailWord_254288).sum := by decide
  have hdescent : baseEnd_254288 < baseStart_254288 := by decide
  rcases family_descends (prefixWord ++ tailWord_254288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254333 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 2]
def baseStart_254333 : Nat := 118140960795 + 254333 * 2 ^ 59
def prefixEnd_254333 : Nat := 4983230072969 + 3 ^ 40 * 254333 * 2
def baseEnd_254333 : Nat := 116084511377829915260311

theorem tailTrace_254333 : CollatzResearch.WordTrace tailWord_254333 prefixEnd_254333 116084511377829915260311 := by
  unfold tailWord_254333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276286587602452463343653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6184191058401634975562435 9276286587602452463343653)
  ·
    refine ⟨1739303735175459836876935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9276286587602452463343653 1739303735175459836876935)
    ·
      refine ⟨2608955602763189755315403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739303735175459836876935 2608955602763189755315403)
      ·
        refine ⟨3913433404144784632973105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2608955602763189755315403 3913433404144784632973105)
        ·
          refine ⟨2935075053108588474729829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3913433404144784632973105 2935075053108588474729829)
          ·
            refine ⟨550326572457860339011843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2935075053108588474729829 550326572457860339011843)
            ·
              refine ⟨825489858686790508517765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550326572457860339011843 825489858686790508517765)
              ·
                refine ⟨154779348503773220347081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825489858686790508517765 154779348503773220347081)
                ·
                  refine ⟨116084511377829915260311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154779348503773220347081 116084511377829915260311)
                  ·
                    rfl

theorem cell20_254333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_254333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254333 prefixEnd_254333 := by exact prefixLift 254333
  have htrace : WordTrace (prefixWord ++ tailWord_254333) baseStart_254333 baseEnd_254333 := by
    simpa [prefixWord, tailWord_254333, baseEnd_254333] using wordTrace_append hprefix tailTrace_254333
  have hstable : (prefixWord ++ tailWord_254333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254333).length < 2 ^ (prefixWord ++ tailWord_254333).sum := by decide
  have hdescent : baseEnd_254333 < baseStart_254333 := by decide
  rcases family_descends (prefixWord ++ tailWord_254333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254361 : List Nat := [1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_254361 : Nat := 118140960795 + 254361 * 2 ^ 59
def prefixEnd_254361 : Nat := 4983230072969 + 3 ^ 40 * 254361 * 2
def baseEnd_254361 : Nat := 38699097113595420775621

theorem tailTrace_254361 : CollatzResearch.WordTrace tailWord_254361 prefixEnd_254361 38699097113595420775621 := by
  unfold tailWord_254361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277307831501013245362937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6184871887667342163575291 9277307831501013245362937)
  ·
    refine ⟨6957980873625759934022203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9277307831501013245362937 6957980873625759934022203)
    ·
      refine ⟨10436971310438639901033305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6957980873625759934022203 10436971310438639901033305)
      ·
        refine ⟨7827728482828979925774979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10436971310438639901033305 7827728482828979925774979)
        ·
          refine ⟨11741592724243469888662469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827728482828979925774979 11741592724243469888662469)
          ·
            refine ⟨2201548635795650604124213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11741592724243469888662469 2201548635795650604124213)
            ·
              refine ⟨206395184605842244136645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2201548635795650604124213 206395184605842244136645)
              ·
                refine ⟨38699097113595420775621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206395184605842244136645 38699097113595420775621)
                ·
                  rfl

theorem cell20_254361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_254361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254361 prefixEnd_254361 := by exact prefixLift 254361
  have htrace : WordTrace (prefixWord ++ tailWord_254361) baseStart_254361 baseEnd_254361 := by
    simpa [prefixWord, tailWord_254361, baseEnd_254361] using wordTrace_append hprefix tailTrace_254361
  have hstable : (prefixWord ++ tailWord_254361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254361).length < 2 ^ (prefixWord ++ tailWord_254361).sum := by decide
  have hdescent : baseEnd_254361 < baseStart_254361 := by decide
  rcases family_descends (prefixWord ++ tailWord_254361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254371 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 2]
def baseStart_254371 : Nat := 118140960795 + 254371 * 2 ^ 59
def prefixEnd_254371 : Nat := 4983230072969 + 3 ^ 40 * 254371 * 2
def baseEnd_254371 : Nat := 116101855613270671993489

theorem tailTrace_254371 : CollatzResearch.WordTrace tailWord_254371 prefixEnd_254371 116101855613270671993489 := by
  unfold tailWord_254371
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277672561464784953226967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6185115040976523302151311 9277672561464784953226967)
  ·
    refine ⟨13916508842197177429840451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9277672561464784953226967 13916508842197177429840451)
    ·
      refine ⟨20874763263295766144760677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13916508842197177429840451 20874763263295766144760677)
      ·
        refine ⟨3914018111867956152142627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20874763263295766144760677 3914018111867956152142627)
        ·
          refine ⟨5871027167801934228213941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914018111867956152142627 5871027167801934228213941)
          ·
            refine ⟨550408796981431333895057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5871027167801934228213941 550408796981431333895057)
            ·
              refine ⟨412806597736073500421293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550408796981431333895057 412806597736073500421293)
              ·
                refine ⟨154802474151027562657985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412806597736073500421293 154802474151027562657985)
                ·
                  refine ⟨116101855613270671993489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154802474151027562657985 116101855613270671993489)
                  ·
                    rfl

theorem cell20_254371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2].length) (baseStart_254371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254371 prefixEnd_254371 := by exact prefixLift 254371
  have htrace : WordTrace (prefixWord ++ tailWord_254371) baseStart_254371 baseEnd_254371 := by
    simpa [prefixWord, tailWord_254371, baseEnd_254371] using wordTrace_append hprefix tailTrace_254371
  have hstable : (prefixWord ++ tailWord_254371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254371).length < 2 ^ (prefixWord ++ tailWord_254371).sum := by decide
  have hdescent : baseEnd_254371 < baseStart_254371 := by decide
  rcases family_descends (prefixWord ++ tailWord_254371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254381 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_254381 : Nat := 118140960795 + 254381 * 2 ^ 59
def prefixEnd_254381 : Nat := 4983230072969 + 3 ^ 40 * 254381 * 2
def baseEnd_254381 : Nat := 116106419885755081660115

theorem tailTrace_254381 : CollatzResearch.WordTrace tailWord_254381 prefixEnd_254381 116106419885755081660115 := by
  unfold tailWord_254381
  simp only [CollatzResearch.WordTrace]
  refine ⟨9278037291428556661090997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6185358194285704440727331 9278037291428556661090997)
  ·
    refine ⟨869815996071427186977281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9278037291428556661090997 869815996071427186977281)
    ·
      refine ⟨652361997053570390232961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 869815996071427186977281 652361997053570390232961)
      ·
        refine ⟨489271497790177792674721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652361997053570390232961 489271497790177792674721)
        ·
          refine ⟨366953623342633344506041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489271497790177792674721 366953623342633344506041)
          ·
            refine ⟨275215217506975008379531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366953623342633344506041 275215217506975008379531)
            ·
              refine ⟨412822826260462512569297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275215217506975008379531 412822826260462512569297)
              ·
                refine ⟨309617119695346884426973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412822826260462512569297 309617119695346884426973)
                ·
                  refine ⟨116106419885755081660115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309617119695346884426973 116106419885755081660115)
                  ·
                    rfl

theorem cell20_254381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_254381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254381 prefixEnd_254381 := by exact prefixLift 254381
  have htrace : WordTrace (prefixWord ++ tailWord_254381) baseStart_254381 baseEnd_254381 := by
    simpa [prefixWord, tailWord_254381, baseEnd_254381] using wordTrace_append hprefix tailTrace_254381
  have hstable : (prefixWord ++ tailWord_254381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254381).length < 2 ^ (prefixWord ++ tailWord_254381).sum := by decide
  have hdescent : baseEnd_254381 < baseStart_254381 := by decide
  rcases family_descends (prefixWord ++ tailWord_254381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254385 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_254385 : Nat := 118140960795 + 254385 * 2 ^ 59
def prefixEnd_254385 : Nat := 4983230072969 + 3 ^ 40 * 254385 * 2
def baseEnd_254385 : Nat := 116108245594748845526765

theorem tailTrace_254385 : CollatzResearch.WordTrace tailWord_254385 prefixEnd_254385 116108245594748845526765 := by
  unfold tailWord_254385
  simp only [CollatzResearch.WordTrace]
  refine ⟨9278183183414065344236609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6185455455609376896157739 9278183183414065344236609)
  ·
    refine ⟨6958637387560549008177457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9278183183414065344236609 6958637387560549008177457)
    ·
      refine ⟨5218978040670411756133093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6958637387560549008177457 5218978040670411756133093)
      ·
        refine ⟨978558382625702204274955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5218978040670411756133093 978558382625702204274955)
        ·
          refine ⟨1467837573938553306412433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978558382625702204274955 1467837573938553306412433)
          ·
            refine ⟨1100878180453914979809325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467837573938553306412433 1100878180453914979809325)
            ·
              refine ⟨412829317670218117428497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1100878180453914979809325 412829317670218117428497)
              ·
                refine ⟨309621988252663588071373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412829317670218117428497 309621988252663588071373)
                ·
                  refine ⟨116108245594748845526765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309621988252663588071373 116108245594748845526765)
                  ·
                    rfl

theorem cell20_254385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_254385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254385 prefixEnd_254385 := by exact prefixLift 254385
  have htrace : WordTrace (prefixWord ++ tailWord_254385) baseStart_254385 baseEnd_254385 := by
    simpa [prefixWord, tailWord_254385, baseEnd_254385] using wordTrace_append hprefix tailTrace_254385
  have hstable : (prefixWord ++ tailWord_254385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254385).length < 2 ^ (prefixWord ++ tailWord_254385).sum := by decide
  have hdescent : baseEnd_254385 < baseStart_254385 := by decide
  rcases family_descends (prefixWord ++ tailWord_254385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254444 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_254444 : Nat := 118140960795 + 254444 * 2 ^ 59
def prefixEnd_254444 : Nat := 4983230072969 + 3 ^ 40 * 254444 * 2
def baseEnd_254444 : Nat := 116135174802406862559857

theorem tailTrace_254444 : CollatzResearch.WordTrace tailWord_254444 prefixEnd_254444 116135174802406862559857 := by
  unfold tailWord_254444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640167545100159210317193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6186890060133545613756257 4640167545100159210317193)
  ·
    refine ⟨3480125658825119407737895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4640167545100159210317193 3480125658825119407737895)
    ·
      refine ⟨5220188488237679111606843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480125658825119407737895 5220188488237679111606843)
      ·
        refine ⟨7830282732356518667410265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220188488237679111606843 7830282732356518667410265)
        ·
          refine ⟨5872712049267389000557699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830282732356518667410265 5872712049267389000557699)
          ·
            refine ⟨8809068073901083500836549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872712049267389000557699 8809068073901083500836549)
            ·
              refine ⟨1651700263856453156406853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8809068073901083500836549 1651700263856453156406853)
              ·
                refine ⟨309693799473084966826285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1651700263856453156406853 309693799473084966826285)
                ·
                  refine ⟨116135174802406862559857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309693799473084966826285 116135174802406862559857)
                  ·
                    rfl

theorem cell20_254444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_254444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254444 prefixEnd_254444 := by exact prefixLift 254444
  have htrace : WordTrace (prefixWord ++ tailWord_254444) baseStart_254444 baseEnd_254444 := by
    simpa [prefixWord, tailWord_254444, baseEnd_254444] using wordTrace_append hprefix tailTrace_254444
  have hstable : (prefixWord ++ tailWord_254444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254444).length < 2 ^ (prefixWord ++ tailWord_254444).sum := by decide
  have hdescent : baseEnd_254444 < baseStart_254444 := by decide
  rcases family_descends (prefixWord ++ tailWord_254444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254496 : List Nat := [2, 1, 1, 6, 10]
def baseStart_254496 : Nat := 118140960795 + 254496 * 2 ^ 59
def prefixEnd_254496 : Nat := 4983230072969 + 3 ^ 40 * 254496 * 2
def baseEnd_254496 : Nat := 1434060605176861639831

theorem tailTrace_254496 : CollatzResearch.WordTrace tailWord_254496 prefixEnd_254496 1434060605176861639831 := by
  unfold tailWord_254496
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641115843005965650763671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6188154457341287534351561 4641115843005965650763671)
  ·
    refine ⟨6961673764508948476145507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641115843005965650763671 6961673764508948476145507)
    ·
      refine ⟨10442510646763422714218261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961673764508948476145507 10442510646763422714218261)
      ·
        refine ⟨489492686567035439728981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10442510646763422714218261 489492686567035439728981)
        ·
          refine ⟨1434060605176861639831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 489492686567035439728981 1434060605176861639831)
          ·
            rfl

theorem cell20_254496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 10].length) (baseStart_254496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254496 prefixEnd_254496 := by exact prefixLift 254496
  have htrace : WordTrace (prefixWord ++ tailWord_254496) baseStart_254496 baseEnd_254496 := by
    simpa [prefixWord, tailWord_254496, baseEnd_254496] using wordTrace_append hprefix tailTrace_254496
  have hstable : (prefixWord ++ tailWord_254496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254496).length < 2 ^ (prefixWord ++ tailWord_254496).sum := by decide
  have hdescent : baseEnd_254496 < baseStart_254496 := by decide
  rcases family_descends (prefixWord ++ tailWord_254496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254499 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_254499 : Nat := 118140960795 + 254499 * 2 ^ 59
def prefixEnd_254499 : Nat := 4983230072969 + 3 ^ 40 * 254499 * 2
def baseEnd_254499 : Nat := 116160278301071115726299

theorem tailTrace_254499 : CollatzResearch.WordTrace tailWord_254499 prefixEnd_254499 116160278301071115726299 := by
  unfold tailWord_254499
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282341105001062813886551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6188227403334041875924367 9282341105001062813886551)
  ·
    refine ⟨13923511657501594220829827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282341105001062813886551 13923511657501594220829827)
    ·
      refine ⟨20885267486252391331244741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923511657501594220829827 20885267486252391331244741)
      ·
        refine ⟨3915987653672323374608389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20885267486252391331244741 3915987653672323374608389)
        ·
          refine ⟨734247685063560632739073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3915987653672323374608389 734247685063560632739073)
          ·
            refine ⟨550685763797670474554305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734247685063560632739073 550685763797670474554305)
            ·
              refine ⟨413014322848252855915729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550685763797670474554305 413014322848252855915729)
              ·
                refine ⟨309760742136189641936797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413014322848252855915729 309760742136189641936797)
                ·
                  refine ⟨116160278301071115726299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309760742136189641936797 116160278301071115726299)
                  ·
                    rfl

theorem cell20_254499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_254499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254499 prefixEnd_254499 := by exact prefixLift 254499
  have htrace : WordTrace (prefixWord ++ tailWord_254499) baseStart_254499 baseEnd_254499 := by
    simpa [prefixWord, tailWord_254499, baseEnd_254499] using wordTrace_append hprefix tailTrace_254499
  have hstable : (prefixWord ++ tailWord_254499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254499).length < 2 ^ (prefixWord ++ tailWord_254499).sum := by decide
  have hdescent : baseEnd_254499 < baseStart_254499 := by decide
  rcases family_descends (prefixWord ++ tailWord_254499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254520 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_254520 : Nat := 118140960795 + 254520 * 2 ^ 59
def prefixEnd_254520 : Nat := 4983230072969 + 3 ^ 40 * 254520 * 2
def baseEnd_254520 : Nat := 116169863273288376026213

theorem tailTrace_254520 : CollatzResearch.WordTrace tailWord_254520 prefixEnd_254520 116169863273288376026213 := by
  unfold tailWord_254520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641553518962491700200507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6188738025283322266934009 4641553518962491700200507)
  ·
    refine ⟨6962330278443737550300761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641553518962491700200507 6962330278443737550300761)
    ·
      refine ⟨5221747708832803162725571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6962330278443737550300761 5221747708832803162725571)
      ·
        refine ⟨7832621563249204744088357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221747708832803162725571 7832621563249204744088357)
        ·
          refine ⟨1468616543109225889516567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7832621563249204744088357 1468616543109225889516567)
          ·
            refine ⟨2202924814663838834274851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468616543109225889516567 2202924814663838834274851)
            ·
              refine ⟨3304387221995758251412277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202924814663838834274851 3304387221995758251412277)
              ·
                refine ⟨309786302062102336069901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3304387221995758251412277 309786302062102336069901)
                ·
                  refine ⟨116169863273288376026213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309786302062102336069901 116169863273288376026213)
                  ·
                    rfl

theorem cell20_254520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_254520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254520 prefixEnd_254520 := by exact prefixLift 254520
  have htrace : WordTrace (prefixWord ++ tailWord_254520) baseStart_254520 baseEnd_254520 := by
    simpa [prefixWord, tailWord_254520, baseEnd_254520] using wordTrace_append hprefix tailTrace_254520
  have hstable : (prefixWord ++ tailWord_254520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254520).length < 2 ^ (prefixWord ++ tailWord_254520).sum := by decide
  have hdescent : baseEnd_254520 < baseStart_254520 := by decide
  rcases family_descends (prefixWord ++ tailWord_254520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254527 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_254527 : Nat := 118140960795 + 254527 * 2 ^ 59
def prefixEnd_254527 : Nat := 4983230072969 + 3 ^ 40 * 254527 * 2
def baseEnd_254527 : Nat := 116173058264027462792851

theorem tailTrace_254527 : CollatzResearch.WordTrace tailWord_254527 prefixEnd_254527 116173058264027462792851 := by
  unfold tailWord_254527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283362348899623595905835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6188908232599749063937223 9283362348899623595905835)
  ·
    refine ⟨13925043523349435393858753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9283362348899623595905835 13925043523349435393858753)
    ·
      refine ⟨10443782642512076545394065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13925043523349435393858753 10443782642512076545394065)
      ·
        refine ⟨7832836981884057409045549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10443782642512076545394065 7832836981884057409045549)
        ·
          refine ⟨2937313868206521528392081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7832836981884057409045549 2937313868206521528392081)
          ·
            refine ⟨2202985401154891146294061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937313868206521528392081 2202985401154891146294061)
            ·
              refine ⟨826119525433084179860273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202985401154891146294061 826119525433084179860273)
              ·
                refine ⟨619589644074813134895205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826119525433084179860273 619589644074813134895205)
                ·
                  refine ⟨116173058264027462792851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619589644074813134895205 116173058264027462792851)
                  ·
                    rfl

theorem cell20_254527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_254527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254527 prefixEnd_254527 := by exact prefixLift 254527
  have htrace : WordTrace (prefixWord ++ tailWord_254527) baseStart_254527 baseEnd_254527 := by
    simpa [prefixWord, tailWord_254527, baseEnd_254527] using wordTrace_append hprefix tailTrace_254527
  have hstable : (prefixWord ++ tailWord_254527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254527).length < 2 ^ (prefixWord ++ tailWord_254527).sum := by decide
  have hdescent : baseEnd_254527 < baseStart_254527 := by decide
  rcases family_descends (prefixWord ++ tailWord_254527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254589 : List Nat := [1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_254589 : Nat := 118140960795 + 254589 * 2 ^ 59
def prefixEnd_254589 : Nat := 4983230072969 + 3 ^ 40 * 254589 * 2
def baseEnd_254589 : Nat := 38733785584476934241977

theorem tailTrace_254589 : CollatzResearch.WordTrace tailWord_254589 prefixEnd_254589 38733785584476934241977 := by
  unfold tailWord_254589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285623674675008184662821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6190415783116672123108547 9285623674675008184662821)
  ·
    refine ⟨1741054439001564034624279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9285623674675008184662821 1741054439001564034624279)
    ·
      refine ⟨2611581658502346051936419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1741054439001564034624279 2611581658502346051936419)
      ·
        refine ⟨3917372487753519077904629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611581658502346051936419 3917372487753519077904629)
        ·
          refine ⟨367253670726892413553559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3917372487753519077904629 367253670726892413553559)
          ·
            refine ⟨550880506090338620330339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367253670726892413553559 550880506090338620330339)
            ·
              refine ⟨826320759135507930495509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550880506090338620330339 826320759135507930495509)
              ·
                refine ⟨38733785584476934241977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 826320759135507930495509 38733785584476934241977)
                ·
                  rfl

theorem cell20_254589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_254589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254589 prefixEnd_254589 := by exact prefixLift 254589
  have htrace : WordTrace (prefixWord ++ tailWord_254589) baseStart_254589 baseEnd_254589 := by
    simpa [prefixWord, tailWord_254589, baseEnd_254589] using wordTrace_append hprefix tailTrace_254589
  have hstable : (prefixWord ++ tailWord_254589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254589).length < 2 ^ (prefixWord ++ tailWord_254589).sum := by decide
  have hdescent : baseEnd_254589 < baseStart_254589 := by decide
  rcases family_descends (prefixWord ++ tailWord_254589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254596 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_254596 : Nat := 118140960795 + 254596 * 2 ^ 59
def prefixEnd_254596 : Nat := 4983230072969 + 3 ^ 40 * 254596 * 2
def baseEnd_254596 : Nat := 116204551744169889492569

theorem tailTrace_254596 : CollatzResearch.WordTrace tailWord_254596 prefixEnd_254596 116204551744169889492569 := by
  unfold tailWord_254596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642939492824824190083821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6190585990433098920111761 4642939492824824190083821)
  ·
    refine ⟨1741102309809309071281433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4642939492824824190083821 1741102309809309071281433)
    ·
      refine ⟨1305826732356981803461075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1741102309809309071281433 1305826732356981803461075)
      ·
        refine ⟨1958740098535472705191613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305826732356981803461075 1958740098535472705191613)
        ·
          refine ⟨734527536950802264446855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1958740098535472705191613 734527536950802264446855)
          ·
            refine ⟨1101791305426203396670283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734527536950802264446855 1101791305426203396670283)
            ·
              refine ⟨1652686958139305095005425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101791305426203396670283 1652686958139305095005425)
              ·
                refine ⟨1239515218604478821254069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652686958139305095005425 1239515218604478821254069)
                ·
                  refine ⟨116204551744169889492569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239515218604478821254069 116204551744169889492569)
                  ·
                    rfl

theorem cell20_254596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_254596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254596 prefixEnd_254596 := by exact prefixLift 254596
  have htrace : WordTrace (prefixWord ++ tailWord_254596) baseStart_254596 baseEnd_254596 := by
    simpa [prefixWord, tailWord_254596, baseEnd_254596] using wordTrace_append hprefix tailTrace_254596
  have hstable : (prefixWord ++ tailWord_254596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254596).length < 2 ^ (prefixWord ++ tailWord_254596).sum := by decide
  have hdescent : baseEnd_254596 < baseStart_254596 := by decide
  rcases family_descends (prefixWord ++ tailWord_254596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254617 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_254617 : Nat := 118140960795 + 254617 * 2 ^ 59
def prefixEnd_254617 : Nat := 4983230072969 + 3 ^ 40 * 254617 * 2
def baseEnd_254617 : Nat := 116214136716387149792483

theorem tailTrace_254617 : CollatzResearch.WordTrace tailWord_254617 prefixEnd_254617 116214136716387149792483 := by
  unfold tailWord_254617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9286644918573568966682105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6191096612382379311121403 9286644918573568966682105)
  ·
    refine ⟨6964983688930176725011579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9286644918573568966682105 6964983688930176725011579)
    ·
      refine ⟨10447475533395265087517369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964983688930176725011579 10447475533395265087517369)
      ·
        refine ⟨7835606650046448815638027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10447475533395265087517369 7835606650046448815638027)
        ·
          refine ⟨11753409975069673223457041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835606650046448815638027 11753409975069673223457041)
          ·
            refine ⟨8815057481302254917592781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753409975069673223457041 8815057481302254917592781)
            ·
              refine ⟨3305646555488345594097293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8815057481302254917592781 3305646555488345594097293)
              ·
                refine ⟨1239617458308129597786485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305646555488345594097293 1239617458308129597786485)
                ·
                  refine ⟨116214136716387149792483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239617458308129597786485 116214136716387149792483)
                  ·
                    rfl

theorem cell20_254617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_254617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254617 prefixEnd_254617 := by exact prefixLift 254617
  have htrace : WordTrace (prefixWord ++ tailWord_254617) baseStart_254617 baseEnd_254617 := by
    simpa [prefixWord, tailWord_254617, baseEnd_254617] using wordTrace_append hprefix tailTrace_254617
  have hstable : (prefixWord ++ tailWord_254617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254617).length < 2 ^ (prefixWord ++ tailWord_254617).sum := by decide
  have hdescent : baseEnd_254617 < baseStart_254617 := by decide
  rcases family_descends (prefixWord ++ tailWord_254617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254620 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_254620 : Nat := 118140960795 + 254620 * 2 ^ 59
def prefixEnd_254620 : Nat := 4983230072969 + 3 ^ 40 * 254620 * 2
def baseEnd_254620 : Nat := 116215505998132472692471

theorem tailTrace_254620 : CollatzResearch.WordTrace tailWord_254620 prefixEnd_254620 116215505998132472692471 := by
  unfold tailWord_254620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643377168781350239520657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6191169558375133652694209 4643377168781350239520657)
  ·
    refine ⟨3482532876586012679640493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4643377168781350239520657 3482532876586012679640493)
    ·
      refine ⟨1305949828719754754865185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3482532876586012679640493 1305949828719754754865185)
      ·
        refine ⟨979462371539816066148889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305949828719754754865185 979462371539816066148889)
        ·
          refine ⟨734596778654862049611667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979462371539816066148889 734596778654862049611667)
          ·
            refine ⟨1101895167982293074417501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734596778654862049611667 1101895167982293074417501)
            ·
              refine ⟨413210687993359902906563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1101895167982293074417501 413210687993359902906563)
              ·
                refine ⟨619816031990039854359845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413210687993359902906563 619816031990039854359845)
                ·
                  refine ⟨116215505998132472692471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619816031990039854359845 116215505998132472692471)
                  ·
                    rfl

theorem cell20_254620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_254620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254620 prefixEnd_254620 := by exact prefixLift 254620
  have htrace : WordTrace (prefixWord ++ tailWord_254620) baseStart_254620 baseEnd_254620 := by
    simpa [prefixWord, tailWord_254620, baseEnd_254620] using wordTrace_append hprefix tailTrace_254620
  have hstable : (prefixWord ++ tailWord_254620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254620).length < 2 ^ (prefixWord ++ tailWord_254620).sum := by decide
  have hdescent : baseEnd_254620 < baseStart_254620 := by decide
  rcases family_descends (prefixWord ++ tailWord_254620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254696 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_254696 : Nat := 118140960795 + 254696 * 2 ^ 59
def prefixEnd_254696 : Nat := 4983230072969 + 3 ^ 40 * 254696 * 2
def baseEnd_254696 : Nat := 116250194469013986158827

theorem tailTrace_254696 : CollatzResearch.WordTrace tailWord_254696 prefixEnd_254696 116250194469013986158827 := by
  unfold tailWord_254696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4644763142643682729403971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6193017523524910305871961 4644763142643682729403971)
  ·
    refine ⟨6967144713965524094105957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4644763142643682729403971 6967144713965524094105957)
    ·
      refine ⟨1306339633868535767644867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6967144713965524094105957 1306339633868535767644867)
      ·
        refine ⟨1959509450802803651467301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306339633868535767644867 1959509450802803651467301)
        ·
          refine ⟨367408022025525684650119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1959509450802803651467301 367408022025525684650119)
          ·
            refine ⟨551112033038288526975179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367408022025525684650119 551112033038288526975179)
            ·
              refine ⟨826668049557432790462769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551112033038288526975179 826668049557432790462769)
              ·
                refine ⟨620001037168074592847077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826668049557432790462769 620001037168074592847077)
                ·
                  refine ⟨116250194469013986158827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620001037168074592847077 116250194469013986158827)
                  ·
                    rfl

theorem cell20_254696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_254696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254696 prefixEnd_254696 := by exact prefixLift 254696
  have htrace : WordTrace (prefixWord ++ tailWord_254696) baseStart_254696 baseEnd_254696 := by
    simpa [prefixWord, tailWord_254696, baseEnd_254696] using wordTrace_append hprefix tailTrace_254696
  have hstable : (prefixWord ++ tailWord_254696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254696).length < 2 ^ (prefixWord ++ tailWord_254696).sum := by decide
  have hdescent : baseEnd_254696 < baseStart_254696 := by decide
  rcases family_descends (prefixWord ++ tailWord_254696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254703 : List Nat := [1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_254703 : Nat := 118140960795 + 254703 * 2 ^ 59
def prefixEnd_254703 : Nat := 4983230072969 + 3 ^ 40 * 254703 * 2
def baseEnd_254703 : Nat := 38751129819917690975155

theorem tailTrace_254703 : CollatzResearch.WordTrace tailWord_254703 prefixEnd_254703 38751129819917690975155 := by
  unfold tailWord_254703
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289781596262005654312763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6193187730841337102875175 9289781596262005654312763)
  ·
    refine ⟨13934672394393008481469145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9289781596262005654312763 13934672394393008481469145)
    ·
      refine ⟨10451004295794756361101859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13934672394393008481469145 10451004295794756361101859)
      ·
        refine ⟨15676506443692134541652789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451004295794756361101859 15676506443692134541652789)
        ·
          refine ⟨1469672479096137613279949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15676506443692134541652789 1469672479096137613279949)
          ·
            refine ⟨551127179661051604979981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1469672479096137613279949 551127179661051604979981)
            ·
              refine ⟨206672692372894351867493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551127179661051604979981 206672692372894351867493)
              ·
                refine ⟨38751129819917690975155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206672692372894351867493 38751129819917690975155)
                ·
                  rfl

theorem cell20_254703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_254703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254703 prefixEnd_254703 := by exact prefixLift 254703
  have htrace : WordTrace (prefixWord ++ tailWord_254703) baseStart_254703 baseEnd_254703 := by
    simpa [prefixWord, tailWord_254703, baseEnd_254703] using wordTrace_append hprefix tailTrace_254703
  have hstable : (prefixWord ++ tailWord_254703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254703).length < 2 ^ (prefixWord ++ tailWord_254703).sum := by decide
  have hdescent : baseEnd_254703 < baseStart_254703 := by decide
  rcases family_descends (prefixWord ++ tailWord_254703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254710 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_254710 : Nat := 118140960795 + 254710 * 2 ^ 59
def prefixEnd_254710 : Nat := 4983230072969 + 3 ^ 40 * 254710 * 2
def baseEnd_254710 : Nat := 116256584450492159692103

theorem tailTrace_254710 : CollatzResearch.WordTrace tailWord_254710 prefixEnd_254710 116256584450492159692103 := by
  unfold tailWord_254710
  simp only [CollatzResearch.WordTrace]
  refine ⟨580627306702290365613599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6193357938157763899878389 580627306702290365613599)
  ·
    refine ⟨870940960053435548420399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580627306702290365613599 870940960053435548420399)
    ·
      refine ⟨1306411440080153322630599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870940960053435548420399 1306411440080153322630599)
      ·
        refine ⟨1959617160120229983945899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306411440080153322630599 1959617160120229983945899)
        ·
          refine ⟨2939425740180344975918849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959617160120229983945899 2939425740180344975918849)
          ·
            refine ⟨2204569305135258731939137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939425740180344975918849 2204569305135258731939137)
            ·
              refine ⟨1653426978851444048954353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204569305135258731939137 1653426978851444048954353)
              ·
                refine ⟨1240070234138583036715765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653426978851444048954353 1240070234138583036715765)
                ·
                  refine ⟨116256584450492159692103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240070234138583036715765 116256584450492159692103)
                  ·
                    rfl

theorem cell20_254710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_254710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254710 prefixEnd_254710 := by exact prefixLift 254710
  have htrace : WordTrace (prefixWord ++ tailWord_254710) baseStart_254710 baseEnd_254710 := by
    simpa [prefixWord, tailWord_254710, baseEnd_254710] using wordTrace_append hprefix tailTrace_254710
  have hstable : (prefixWord ++ tailWord_254710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254710).length < 2 ^ (prefixWord ++ tailWord_254710).sum := by decide
  have hdescent : baseEnd_254710 < baseStart_254710 := by decide
  rcases family_descends (prefixWord ++ tailWord_254710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254724 : List Nat := [2, 3, 2, 2, 1, 1, 9]
def baseStart_254724 : Nat := 118140960795 + 254724 * 2 ^ 59
def prefixEnd_254724 : Nat := 4983230072969 + 3 ^ 40 * 254724 * 2
def baseEnd_254724 : Nat := 12918108270218925913931

theorem tailTrace_254724 : CollatzResearch.WordTrace tailWord_254724 prefixEnd_254724 12918108270218925913931 := by
  unfold tailWord_254724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4645273764592963120413613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6193698352790617493884817 4645273764592963120413613)
  ·
    refine ⟨1741977661722361170155105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4645273764592963120413613 1741977661722361170155105)
    ·
      refine ⟨1306483246291770877616329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1741977661722361170155105 1306483246291770877616329)
      ·
        refine ⟨979862434718828158212247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306483246291770877616329 979862434718828158212247)
        ·
          refine ⟨1469793652078242237318371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979862434718828158212247 1469793652078242237318371)
          ·
            refine ⟨2204690478117363355977557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469793652078242237318371 2204690478117363355977557)
            ·
              refine ⟨12918108270218925913931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2204690478117363355977557 12918108270218925913931)
              ·
                rfl

theorem cell20_254724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_254724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254724 prefixEnd_254724 := by exact prefixLift 254724
  have htrace : WordTrace (prefixWord ++ tailWord_254724) baseStart_254724 baseEnd_254724 := by
    simpa [prefixWord, tailWord_254724, baseEnd_254724] using wordTrace_append hprefix tailTrace_254724
  have hstable : (prefixWord ++ tailWord_254724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254724).length < 2 ^ (prefixWord ++ tailWord_254724).sum := by decide
  have hdescent : baseEnd_254724 < baseStart_254724 := by decide
  rcases family_descends (prefixWord ++ tailWord_254724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254727 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_254727 : Nat := 118140960795 + 254727 * 2 ^ 59
def prefixEnd_254727 : Nat := 4983230072969 + 3 ^ 40 * 254727 * 2
def baseEnd_254727 : Nat := 116264343713715656125367

theorem tailTrace_254727 : CollatzResearch.WordTrace tailWord_254727 prefixEnd_254727 116264343713715656125367 := by
  unfold tailWord_254727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290656948175057753186435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6193771298783371835457623 9290656948175057753186435)
  ·
    refine ⟨13935985422262586629779653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290656948175057753186435 13935985422262586629779653)
    ·
      refine ⟨2612997266674234993083685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13935985422262586629779653 2612997266674234993083685)
      ·
        refine ⟨489936987501419061203191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2612997266674234993083685 489936987501419061203191)
        ·
          refine ⟨734905481252128591804787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489936987501419061203191 734905481252128591804787)
          ·
            refine ⟨1102358221878192887707181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734905481252128591804787 1102358221878192887707181)
            ·
              refine ⟨413384333204322332890193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102358221878192887707181 413384333204322332890193)
              ·
                refine ⟨310038249903241749667645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413384333204322332890193 310038249903241749667645)
                ·
                  refine ⟨116264343713715656125367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310038249903241749667645 116264343713715656125367)
                  ·
                    rfl

theorem cell20_254727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_254727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254727 prefixEnd_254727 := by exact prefixLift 254727
  have htrace : WordTrace (prefixWord ++ tailWord_254727) baseStart_254727 baseEnd_254727 := by
    simpa [prefixWord, tailWord_254727, baseEnd_254727] using wordTrace_append hprefix tailTrace_254727
  have hstable : (prefixWord ++ tailWord_254727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254727).length < 2 ^ (prefixWord ++ tailWord_254727).sum := by decide
  have hdescent : baseEnd_254727 < baseStart_254727 := by decide
  rcases family_descends (prefixWord ++ tailWord_254727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254769 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_254769 : Nat := 118140960795 + 254769 * 2 ^ 59
def prefixEnd_254769 : Nat := 4983230072969 + 3 ^ 40 * 254769 * 2
def baseEnd_254769 : Nat := 116283513658150176725195

theorem tailTrace_254769 : CollatzResearch.WordTrace tailWord_254769 prefixEnd_254769 116283513658150176725195 := by
  unfold tailWord_254769
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292188814022898926215361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6194792542681932617476907 9292188814022898926215361)
  ·
    refine ⟨6969141610517174194661521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292188814022898926215361 6969141610517174194661521)
    ·
      refine ⟨5226856207887880645996141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6969141610517174194661521 5226856207887880645996141)
      ·
        refine ⟨1960071077957955242248553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5226856207887880645996141 1960071077957955242248553)
        ·
          refine ⟨1470053308468466431686415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960071077957955242248553 1470053308468466431686415)
          ·
            refine ⟨2205079962702699647529623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470053308468466431686415 2205079962702699647529623)
            ·
              refine ⟨3307619944054049471294435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205079962702699647529623 3307619944054049471294435)
              ·
                refine ⟨4961429916081074206941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307619944054049471294435 4961429916081074206941653)
                ·
                  refine ⟨116283513658150176725195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4961429916081074206941653 116283513658150176725195)
                  ·
                    rfl

theorem cell20_254769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_254769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254769 prefixEnd_254769 := by exact prefixLift 254769
  have htrace : WordTrace (prefixWord ++ tailWord_254769) baseStart_254769 baseEnd_254769 := by
    simpa [prefixWord, tailWord_254769, baseEnd_254769] using wordTrace_append hprefix tailTrace_254769
  have hstable : (prefixWord ++ tailWord_254769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254769).length < 2 ^ (prefixWord ++ tailWord_254769).sum := by decide
  have hdescent : baseEnd_254769 < baseStart_254769 := by decide
  rcases family_descends (prefixWord ++ tailWord_254769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254785 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 2]
def baseStart_254785 : Nat := 118140960795 + 254785 * 2 ^ 59
def prefixEnd_254785 : Nat := 4983230072969 + 3 ^ 40 * 254785 * 2
def baseEnd_254785 : Nat := 116290816494125232191797

theorem tailTrace_254785 : CollatzResearch.WordTrace tailWord_254785 prefixEnd_254785 116290816494125232191797 := by
  unfold tailWord_254785
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292772381964933658797809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6195181587976622439198539 9292772381964933658797809)
  ·
    refine ⟨6969579286473700244098357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292772381964933658797809 6969579286473700244098357)
    ·
      refine ⟨653398058106909397884221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6969579286473700244098357 653398058106909397884221)
      ·
        refine ⟨245024271790091024206583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653398058106909397884221 245024271790091024206583)
        ·
          refine ⟨367536407685136536309875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245024271790091024206583 367536407685136536309875)
          ·
            refine ⟨551304611527704804464813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367536407685136536309875 551304611527704804464813)
            ·
              refine ⟨206739229322889301674305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551304611527704804464813 206739229322889301674305)
              ·
                refine ⟨155054421992166976255729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206739229322889301674305 155054421992166976255729)
                ·
                  refine ⟨116290816494125232191797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155054421992166976255729 116290816494125232191797)
                  ·
                    rfl

theorem cell20_254785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_254785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254785 prefixEnd_254785 := by exact prefixLift 254785
  have htrace : WordTrace (prefixWord ++ tailWord_254785) baseStart_254785 baseEnd_254785 := by
    simpa [prefixWord, tailWord_254785, baseEnd_254785] using wordTrace_append hprefix tailTrace_254785
  have hstable : (prefixWord ++ tailWord_254785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254785).length < 2 ^ (prefixWord ++ tailWord_254785).sum := by decide
  have hdescent : baseEnd_254785 < baseStart_254785 := by decide
  rcases family_descends (prefixWord ++ tailWord_254785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254793 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_254793 : Nat := 118140960795 + 254793 * 2 ^ 59
def prefixEnd_254793 : Nat := 4983230072969 + 3 ^ 40 * 254793 * 2
def baseEnd_254793 : Nat := 116294467912112759925097

theorem tailTrace_254793 : CollatzResearch.WordTrace tailWord_254793 prefixEnd_254793 116294467912112759925097 := by
  unfold tailWord_254793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293064165935951025089033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6195376110623967350059355 9293064165935951025089033)
  ·
    refine ⟨6969798124451963268816775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9293064165935951025089033 6969798124451963268816775)
    ·
      refine ⟨10454697186677944903225163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969798124451963268816775 10454697186677944903225163)
      ·
        refine ⟨15682045780016917354837745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454697186677944903225163 15682045780016917354837745)
        ·
          refine ⟨11761534335012688016128309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682045780016917354837745 11761534335012688016128309)
          ·
            refine ⟨1102643843907439501512029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11761534335012688016128309 1102643843907439501512029)
            ·
              refine ⟨413491441465289813067011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102643843907439501512029 413491441465289813067011)
              ·
                refine ⟨620237162197934719600517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413491441465289813067011 620237162197934719600517)
                ·
                  refine ⟨116294467912112759925097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620237162197934719600517 116294467912112759925097)
                  ·
                    rfl

theorem cell20_254793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_254793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254793 prefixEnd_254793 := by exact prefixLift 254793
  have htrace : WordTrace (prefixWord ++ tailWord_254793) baseStart_254793 baseEnd_254793 := by
    simpa [prefixWord, tailWord_254793, baseEnd_254793] using wordTrace_append hprefix tailTrace_254793
  have hstable : (prefixWord ++ tailWord_254793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254793).length < 2 ^ (prefixWord ++ tailWord_254793).sum := by decide
  have hdescent : baseEnd_254793 < baseStart_254793 := by decide
  rcases family_descends (prefixWord ++ tailWord_254793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254845 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_254845 : Nat := 118140960795 + 254845 * 2 ^ 59
def prefixEnd_254845 : Nat := 4983230072969 + 3 ^ 40 * 254845 * 2
def baseEnd_254845 : Nat := 116318202129031690191551

theorem tailTrace_254845 : CollatzResearch.WordTrace tailWord_254845 prefixEnd_254845 116318202129031690191551 := by
  unfold tailWord_254845
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294960761747563905981989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196640507831709270654659 9294960761747563905981989)
  ·
    refine ⟨1742805142827668232371623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9294960761747563905981989 1742805142827668232371623)
    ·
      refine ⟨2614207714241502348557435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742805142827668232371623 2614207714241502348557435)
      ·
        refine ⟨3921311571362253522836153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614207714241502348557435 3921311571362253522836153)
        ·
          refine ⟨2940983678521690142127115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921311571362253522836153 2940983678521690142127115)
          ·
            refine ⟨4411475517782535213190673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940983678521690142127115 4411475517782535213190673)
            ·
              refine ⟨3308606638336901409893005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411475517782535213190673 3308606638336901409893005)
              ·
                refine ⟨1240727489376338028709877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3308606638336901409893005 1240727489376338028709877)
                ·
                  refine ⟨116318202129031690191551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240727489376338028709877 116318202129031690191551)
                  ·
                    rfl

theorem cell20_254845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_254845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254845 prefixEnd_254845 := by exact prefixLift 254845
  have htrace : WordTrace (prefixWord ++ tailWord_254845) baseStart_254845 baseEnd_254845 := by
    simpa [prefixWord, tailWord_254845, baseEnd_254845] using wordTrace_append hprefix tailTrace_254845
  have hstable : (prefixWord ++ tailWord_254845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254845).length < 2 ^ (prefixWord ++ tailWord_254845).sum := by decide
  have hdescent : baseEnd_254845 < baseStart_254845 := by decide
  rcases family_descends (prefixWord ++ tailWord_254845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
