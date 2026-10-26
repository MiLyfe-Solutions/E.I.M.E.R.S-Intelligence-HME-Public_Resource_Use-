import V185TrunkScan23Chunk0859

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5089324 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_5089324 : Nat := 118140960795 + 5089324 * 2 ^ 59
def prefixEnd_5089324 : Nat := 4983230072969 + 3 ^ 40 * 5089324 * 2
def baseEnd_5089324 : Nat := 2613269418462751230144631

theorem tailTrace_5089324 : CollatzResearch.WordTrace tailWord_5089324 prefixEnd_5089324 2613269418462751230144631 := by
  unfold tailWord_5089324
  simp only [CollatzResearch.WordTrace]
  refine ⟨92811447907127905092385513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123748597209503873456514017 92811447907127905092385513)
  ·
    refine ⟨69608585930345928819289135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92811447907127905092385513 69608585930345928819289135)
    ·
      refine ⟨104412878895518893228933703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69608585930345928819289135 104412878895518893228933703)
      ·
        refine ⟨156619318343278339843400555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104412878895518893228933703 156619318343278339843400555)
        ·
          refine ⟨234928977514917509765100833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156619318343278339843400555 234928977514917509765100833)
          ·
            refine ⟨176196733136188132323825625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234928977514917509765100833 176196733136188132323825625)
            ·
              refine ⟨132147549852141099242869219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176196733136188132323825625 132147549852141099242869219)
              ·
                refine ⟨198221324778211648864303829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132147549852141099242869219 198221324778211648864303829)
                ·
                  refine ⟨4645812299489335520257121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 198221324778211648864303829 4645812299489335520257121)
                  ·
                    refine ⟨3484359224617001640192841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4645812299489335520257121 3484359224617001640192841)
                    ·
                      refine ⟨2613269418462751230144631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484359224617001640192841 2613269418462751230144631)
                      ·
                        rfl

theorem cell23_5089324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_5089324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089324 prefixEnd_5089324 := by exact prefixLift 5089324
  have htrace : WordTrace (prefixWord ++ tailWord_5089324) baseStart_5089324 baseEnd_5089324 := by
    simpa [prefixWord, tailWord_5089324, baseEnd_5089324] using wordTrace_append hprefix tailTrace_5089324
  have hstable : (prefixWord ++ tailWord_5089324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089324).length < 2 ^ (prefixWord ++ tailWord_5089324).sum := by decide
  have hdescent : baseEnd_5089324 < baseStart_5089324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089330 : List Nat := [3, 2, 1, 1, 2, 14]
def baseStart_5089330 : Nat := 118140960795 + 5089330 * 2 ^ 59
def prefixEnd_5089330 : Nat := 4983230072969 + 3 ^ 40 * 5089330 * 2
def baseEnd_5089330 : Nat := 10754207816241474101521

theorem tailTrace_5089330 : CollatzResearch.WordTrace tailWord_5089330 prefixEnd_5089330 10754207816241474101521 := by
  unfold tailWord_5089330
  simp only [CollatzResearch.WordTrace]
  refine ⟨46405778663058518302372361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123748743101489382139659629 46405778663058518302372361)
  ·
    refine ⟨34804333997293888726779271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46405778663058518302372361 34804333997293888726779271)
    ·
      refine ⟨52206500995940833090168907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34804333997293888726779271 52206500995940833090168907)
      ·
        refine ⟨78309751493911249635253361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52206500995940833090168907 78309751493911249635253361)
        ·
          refine ⟨58732313620433437226440021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78309751493911249635253361 58732313620433437226440021)
          ·
            refine ⟨10754207816241474101521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 58732313620433437226440021 10754207816241474101521)
            ·
              rfl

theorem cell23_5089330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 14].length) (baseStart_5089330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089330 prefixEnd_5089330 := by exact prefixLift 5089330
  have htrace : WordTrace (prefixWord ++ tailWord_5089330) baseStart_5089330 baseEnd_5089330 := by
    simpa [prefixWord, tailWord_5089330, baseEnd_5089330] using wordTrace_append hprefix tailTrace_5089330
  have hstable : (prefixWord ++ tailWord_5089330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089330).length < 2 ^ (prefixWord ++ tailWord_5089330).sum := by decide
  have hdescent : baseEnd_5089330 < baseStart_5089330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089341 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_5089341 : Nat := 118140960795 + 5089341 * 2 ^ 59
def prefixEnd_5089341 : Nat := 4983230072969 + 3 ^ 40 * 5089341 * 2
def baseEnd_5089341 : Nat := 2613278147633877663632053

theorem tailTrace_5089341 : CollatzResearch.WordTrace tailWord_5089341 prefixEnd_5089341 2613278147633877663632053 := by
  unfold tailWord_5089341
  simp only [CollatzResearch.WordTrace]
  refine ⟨185623515855194222088139877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123749010570129481392093251 185623515855194222088139877)
  ·
    refine ⟨34804409222848916641526227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185623515855194222088139877 34804409222848916641526227)
    ·
      refine ⟨52206613834273374962289341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34804409222848916641526227 52206613834273374962289341)
      ·
        refine ⟨19577480187852515610858503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52206613834273374962289341 19577480187852515610858503)
        ·
          refine ⟨29366220281778773416287755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19577480187852515610858503 29366220281778773416287755)
          ·
            refine ⟨44049330422668160124431633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29366220281778773416287755 44049330422668160124431633)
            ·
              refine ⟨33036997817001120093323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44049330422668160124431633 33036997817001120093323725)
              ·
                refine ⟨12388874181375420034996397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33036997817001120093323725 12388874181375420034996397)
                ·
                  refine ⟨4645827818015782513123649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12388874181375420034996397 4645827818015782513123649)
                  ·
                    refine ⟨3484370863511836884842737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4645827818015782513123649 3484370863511836884842737)
                    ·
                      refine ⟨2613278147633877663632053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484370863511836884842737 2613278147633877663632053)
                      ·
                        rfl

theorem cell23_5089341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_5089341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089341 prefixEnd_5089341 := by exact prefixLift 5089341
  have htrace : WordTrace (prefixWord ++ tailWord_5089341) baseStart_5089341 baseEnd_5089341 := by
    simpa [prefixWord, tailWord_5089341, baseEnd_5089341] using wordTrace_append hprefix tailTrace_5089341
  have hstable : (prefixWord ++ tailWord_5089341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089341).length < 2 ^ (prefixWord ++ tailWord_5089341).sum := by decide
  have hdescent : baseEnd_5089341 < baseStart_5089341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089378 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5089378 : Nat := 118140960795 + 5089378 * 2 ^ 59
def prefixEnd_5089378 : Nat := 4983230072969 + 3 ^ 40 * 5089378 * 2
def baseEnd_5089378 : Nat := 2613297146418094018869383

theorem tailTrace_5089378 : CollatzResearch.WordTrace tailWord_5089378 prefixEnd_5089378 2613297146418094018869383 := by
  unfold tailWord_5089378
  simp only [CollatzResearch.WordTrace]
  refine ⟨46406216339015044351809197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123749910237373451604824525 46406216339015044351809197)
  ·
    refine ⟨17402331127130641631928449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46406216339015044351809197 17402331127130641631928449)
    ·
      refine ⟨13051748345347981223946337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17402331127130641631928449 13051748345347981223946337)
      ·
        refine ⟨9788811259010985917959753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13051748345347981223946337 9788811259010985917959753)
        ·
          refine ⟨7341608444258239438469815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9788811259010985917959753 7341608444258239438469815)
          ·
            refine ⟨11012412666387359157704723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341608444258239438469815 11012412666387359157704723)
            ·
              refine ⟨16518618999581038736557085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11012412666387359157704723 16518618999581038736557085)
              ·
                refine ⟨6194482124842889526208907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16518618999581038736557085 6194482124842889526208907)
                ·
                  refine ⟨9291723187264334289313361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194482124842889526208907 9291723187264334289313361)
                  ·
                    refine ⟨6968792390448250716985021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9291723187264334289313361 6968792390448250716985021)
                    ·
                      refine ⟨2613297146418094018869383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968792390448250716985021 2613297146418094018869383)
                      ·
                        rfl

theorem cell23_5089378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5089378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089378 prefixEnd_5089378 := by exact prefixLift 5089378
  have htrace : WordTrace (prefixWord ++ tailWord_5089378) baseStart_5089378 baseEnd_5089378 := by
    simpa [prefixWord, tailWord_5089378, baseEnd_5089378] using wordTrace_append hprefix tailTrace_5089378
  have hstable : (prefixWord ++ tailWord_5089378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089378).length < 2 ^ (prefixWord ++ tailWord_5089378).sum := by decide
  have hdescent : baseEnd_5089378 < baseStart_5089378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089391 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 3]
def baseStart_5089391 : Nat := 118140960795 + 5089391 * 2 ^ 59
def prefixEnd_5089391 : Nat := 4983230072969 + 3 ^ 40 * 5089391 * 2
def baseEnd_5089391 : Nat := 2613303821666602468006823

theorem tailTrace_5089391 : CollatzResearch.WordTrace tailWord_5089391 prefixEnd_5089391 2613303821666602468006823 := by
  unfold tailWord_5089391
  simp only [CollatzResearch.WordTrace]
  refine ⟨185625339505013080627460027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123750226336675387084973351 185625339505013080627460027)
  ·
    refine ⟨278438009257519620941190041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185625339505013080627460027 278438009257519620941190041)
    ·
      refine ⟨208828506943139715705892531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278438009257519620941190041 208828506943139715705892531)
      ·
        refine ⟨313242760414709573558838797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208828506943139715705892531 313242760414709573558838797)
        ·
          refine ⟨117466035155516090084564549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313242760414709573558838797 117466035155516090084564549)
          ·
            refine ⟨22024881591659266890855853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117466035155516090084564549 22024881591659266890855853)
            ·
              refine ⟨8259330596872225084070945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22024881591659266890855853 8259330596872225084070945)
              ·
                refine ⟨6194497947654168813053209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259330596872225084070945 6194497947654168813053209)
                ·
                  refine ⟨4645873460740626609789907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6194497947654168813053209 4645873460740626609789907)
                  ·
                    refine ⟨6968810191110939914684861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645873460740626609789907 6968810191110939914684861)
                    ·
                      refine ⟨2613303821666602468006823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968810191110939914684861 2613303821666602468006823)
                      ·
                        rfl

theorem cell23_5089391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_5089391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089391 prefixEnd_5089391 := by exact prefixLift 5089391
  have htrace : WordTrace (prefixWord ++ tailWord_5089391) baseStart_5089391 baseEnd_5089391 := by
    simpa [prefixWord, tailWord_5089391, baseEnd_5089391] using wordTrace_append hprefix tailTrace_5089391
  have hstable : (prefixWord ++ tailWord_5089391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089391).length < 2 ^ (prefixWord ++ tailWord_5089391).sum := by decide
  have hdescent : baseEnd_5089391 < baseStart_5089391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089417 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_5089417 : Nat := 118140960795 + 5089417 * 2 ^ 59
def prefixEnd_5089417 : Nat := 4983230072969 + 3 ^ 40 * 5089417 * 2
def baseEnd_5089417 : Nat := 2613317172163619366281703

theorem tailTrace_5089417 : CollatzResearch.WordTrace tailWord_5089417 prefixEnd_5089417 2613317172163619366281703 := by
  unfold tailWord_5089417
  simp only [CollatzResearch.WordTrace]
  refine ⟨185626287802918887067906505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123750858535279258045271003 185626287802918887067906505)
  ·
    refine ⟨139219715852189165300929879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185626287802918887067906505 139219715852189165300929879)
    ·
      refine ⟨208829573778283747951394819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139219715852189165300929879 208829573778283747951394819)
      ·
        refine ⟨313244360667425621927092229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208829573778283747951394819 313244360667425621927092229)
        ·
          refine ⟨58733317625142304111329793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313244360667425621927092229 58733317625142304111329793)
          ·
            refine ⟨44049988218856728083497345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58733317625142304111329793 44049988218856728083497345)
            ·
              refine ⟨33037491164142546062623009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44049988218856728083497345 33037491164142546062623009)
              ·
                refine ⟨24778118373106909546967257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33037491164142546062623009 24778118373106909546967257)
                ·
                  refine ⟨18583588779830182160225443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24778118373106909546967257 18583588779830182160225443)
                  ·
                    refine ⟨27875383169745273240338165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18583588779830182160225443 27875383169745273240338165)
                    ·
                      refine ⟨2613317172163619366281703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27875383169745273240338165 2613317172163619366281703)
                      ·
                        rfl

theorem cell23_5089417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_5089417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089417 prefixEnd_5089417 := by exact prefixLift 5089417
  have htrace : WordTrace (prefixWord ++ tailWord_5089417) baseStart_5089417 baseEnd_5089417 := by
    simpa [prefixWord, tailWord_5089417, baseEnd_5089417] using wordTrace_append hprefix tailTrace_5089417
  have hstable : (prefixWord ++ tailWord_5089417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089417).length < 2 ^ (prefixWord ++ tailWord_5089417).sum := by decide
  have hdescent : baseEnd_5089417 < baseStart_5089417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089418 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_5089418 : Nat := 118140960795 + 5089418 * 2 ^ 59
def prefixEnd_5089418 : Nat := 4983230072969 + 3 ^ 40 * 5089418 * 2
def baseEnd_5089418 : Nat := 2613317685644273862369199

theorem tailTrace_5089418 : CollatzResearch.WordTrace tailWord_5089418 prefixEnd_5089418 2613317685644273862369199 := by
  unfold tailWord_5089418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46406581068978816059673227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123750882850610176159128605 46406581068978816059673227)
  ·
    refine ⟨69609871603468224089509841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46406581068978816059673227 69609871603468224089509841)
    ·
      refine ⟨52207403702601168067132381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69609871603468224089509841 52207403702601168067132381)
      ·
        refine ⟨19577776388475438025174643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52207403702601168067132381 19577776388475438025174643)
        ·
          refine ⟨29366664582713157037761965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19577776388475438025174643 29366664582713157037761965)
          ·
            refine ⟨11012499218517433889160737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29366664582713157037761965 11012499218517433889160737)
            ·
              refine ⟨8259374413888075416870553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11012499218517433889160737 8259374413888075416870553)
              ·
                refine ⟨6194530810416056562652915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259374413888075416870553 6194530810416056562652915)
                ·
                  refine ⟨9291796215624084843979373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194530810416056562652915 9291796215624084843979373)
                  ·
                    refine ⟨3484423580859031816492265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9291796215624084843979373 3484423580859031816492265)
                    ·
                      refine ⟨2613317685644273862369199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484423580859031816492265 2613317685644273862369199)
                      ·
                        rfl

theorem cell23_5089418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_5089418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089418 prefixEnd_5089418 := by exact prefixLift 5089418
  have htrace : WordTrace (prefixWord ++ tailWord_5089418) baseStart_5089418 baseEnd_5089418 := by
    simpa [prefixWord, tailWord_5089418, baseEnd_5089418] using wordTrace_append hprefix tailTrace_5089418
  have hstable : (prefixWord ++ tailWord_5089418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089418).length < 2 ^ (prefixWord ++ tailWord_5089418).sum := by decide
  have hdescent : baseEnd_5089418 < baseStart_5089418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089467 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 4, 5]
def baseStart_5089467 : Nat := 118140960795 + 5089467 * 2 ^ 59
def prefixEnd_5089467 : Nat := 4983230072969 + 3 ^ 40 * 5089467 * 2
def baseEnd_5089467 : Nat := 871114282065448056885491

theorem tailTrace_5089467 : CollatzResearch.WordTrace tailWord_5089467 prefixEnd_5089467 871114282065448056885491 := by
  unfold tailWord_5089467
  simp only [CollatzResearch.WordTrace]
  refine ⟨185628111452737745607226655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123752074301825163738151103 185628111452737745607226655)
  ·
    refine ⟨278442167179106618410839983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185628111452737745607226655 278442167179106618410839983)
    ·
      refine ⟨417663250768659927616259975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278442167179106618410839983 417663250768659927616259975)
      ·
        refine ⟨626494876152989891424389963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417663250768659927616259975 626494876152989891424389963)
        ·
          refine ⟨939742314229484837136584945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626494876152989891424389963 939742314229484837136584945)
          ·
            refine ⟨704806735672113627852438709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939742314229484837136584945 704806735672113627852438709)
            ·
              refine ⟨66075631469260652611166129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 704806735672113627852438709 66075631469260652611166129)
              ·
                refine ⟨49556723601945489458374597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66075631469260652611166129 49556723601945489458374597)
                ·
                  refine ⟨9291885675364779273445237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49556723601945489458374597 9291885675364779273445237)
                  ·
                    refine ⟨871114282065448056885491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9291885675364779273445237 871114282065448056885491)
                    ·
                      rfl

theorem cell23_5089467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 5].length) (baseStart_5089467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089467 prefixEnd_5089467 := by exact prefixLift 5089467
  have htrace : WordTrace (prefixWord ++ tailWord_5089467) baseStart_5089467 baseEnd_5089467 := by
    simpa [prefixWord, tailWord_5089467, baseEnd_5089467] using wordTrace_append hprefix tailTrace_5089467
  have hstable : (prefixWord ++ tailWord_5089467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089467).length < 2 ^ (prefixWord ++ tailWord_5089467).sum := by decide
  have hdescent : baseEnd_5089467 < baseStart_5089467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089501 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5089501 : Nat := 118140960795 + 5089501 * 2 ^ 59
def prefixEnd_5089501 : Nat := 4983230072969 + 3 ^ 40 * 5089501 * 2
def baseEnd_5089501 : Nat := 871120101512865679210439

theorem tailTrace_5089501 : CollatzResearch.WordTrace tailWord_5089501 prefixEnd_5089501 871120101512865679210439 := by
  unfold tailWord_5089501
  simp only [CollatzResearch.WordTrace]
  refine ⟨185629351534614569413964357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123752901023076379609309571 185629351534614569413964357)
  ·
    refine ⟨34805503412740231765118317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185629351534614569413964357 34805503412740231765118317)
    ·
      refine ⟨13052063779777586911919369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34805503412740231765118317 13052063779777586911919369)
      ·
        refine ⟨9789047834833190183939527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13052063779777586911919369 9789047834833190183939527)
        ·
          refine ⟨14683571752249785275909291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9789047834833190183939527 14683571752249785275909291)
          ·
            refine ⟨22025357628374677913863937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683571752249785275909291 22025357628374677913863937)
            ·
              refine ⟨16519018221281008435397953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22025357628374677913863937 16519018221281008435397953)
              ·
                refine ⟨12389263665960756326548465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16519018221281008435397953 12389263665960756326548465)
                ·
                  refine ⟨9291947749470567244911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12389263665960756326548465 9291947749470567244911349)
                  ·
                    refine ⟨871120101512865679210439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9291947749470567244911349 871120101512865679210439)
                    ·
                      rfl

theorem cell23_5089501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5089501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089501 prefixEnd_5089501 := by exact prefixLift 5089501
  have htrace : WordTrace (prefixWord ++ tailWord_5089501) baseStart_5089501 baseEnd_5089501 := by
    simpa [prefixWord, tailWord_5089501, baseEnd_5089501] using wordTrace_append hprefix tailTrace_5089501
  have hstable : (prefixWord ++ tailWord_5089501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089501).length < 2 ^ (prefixWord ++ tailWord_5089501).sum := by decide
  have hdescent : baseEnd_5089501 < baseStart_5089501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089504 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_5089504 : Nat := 118140960795 + 5089504 * 2 ^ 59
def prefixEnd_5089504 : Nat := 4983230072969 + 3 ^ 40 * 5089504 * 2
def baseEnd_5089504 : Nat := 2613361844980560525893803

theorem tailTrace_5089504 : CollatzResearch.WordTrace tailWord_5089504 prefixEnd_5089504 2613361844980560525893803 := by
  unfold tailWord_5089504
  simp only [CollatzResearch.WordTrace]
  refine ⟨92814730476801850463161783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123752973969069133950882377 92814730476801850463161783)
  ·
    refine ⟨139222095715202775694742675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92814730476801850463161783 139222095715202775694742675)
    ·
      refine ⟨208833143572804163542114013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139222095715202775694742675 208833143572804163542114013)
      ·
        refine ⟨78312428839801561328292755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208833143572804163542114013 78312428839801561328292755)
        ·
          refine ⟨117468643259702341992439133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78312428839801561328292755 117468643259702341992439133)
          ·
            refine ⟨44050741222388378247164675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117468643259702341992439133 44050741222388378247164675)
            ·
              refine ⟨66076111833582567370747013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44050741222388378247164675 66076111833582567370747013)
              ·
                refine ⟨12389270968796731382015065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66076111833582567370747013 12389270968796731382015065)
                ·
                  refine ⟨9291953226597548536511299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12389270968796731382015065 9291953226597548536511299)
                  ·
                    refine ⟨13937929839896322804766949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291953226597548536511299 13937929839896322804766949)
                    ·
                      refine ⟨2613361844980560525893803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13937929839896322804766949 2613361844980560525893803)
                      ·
                        rfl

theorem cell23_5089504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_5089504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089504 prefixEnd_5089504 := by exact prefixLift 5089504
  have htrace : WordTrace (prefixWord ++ tailWord_5089504) baseStart_5089504 baseEnd_5089504 := by
    simpa [prefixWord, tailWord_5089504, baseEnd_5089504] using wordTrace_append hprefix tailTrace_5089504
  have hstable : (prefixWord ++ tailWord_5089504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089504).length < 2 ^ (prefixWord ++ tailWord_5089504).sum := by decide
  have hdescent : baseEnd_5089504 < baseStart_5089504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089538 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5089538 : Nat := 118140960795 + 5089538 * 2 ^ 59
def prefixEnd_5089538 : Nat := 4983230072969 + 3 ^ 40 * 5089538 * 2
def baseEnd_5089538 : Nat := 2613379303322813392868647

theorem tailTrace_5089538 : CollatzResearch.WordTrace tailWord_5089538 prefixEnd_5089538 2613379303322813392868647 := by
  unfold tailWord_5089538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46407675258870131183265317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123753800690320349822040845 46407675258870131183265317)
  ·
    refine ⟨8701439111038149596862247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46407675258870131183265317 8701439111038149596862247)
    ·
      refine ⟨13052158666557224395293371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8701439111038149596862247 13052158666557224395293371)
      ·
        refine ⟨19578237999835836592940057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13052158666557224395293371 19578237999835836592940057)
        ·
          refine ⟨14683678499876877444705043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19578237999835836592940057 14683678499876877444705043)
          ·
            refine ⟨22025517749815316167057565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683678499876877444705043 22025517749815316167057565)
            ·
              refine ⟨8259569156180743562646587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22025517749815316167057565 8259569156180743562646587)
              ·
                refine ⟨12389353734271115343969881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8259569156180743562646587 12389353734271115343969881)
                ·
                  refine ⟨9292015300703336507977411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12389353734271115343969881 9292015300703336507977411)
                  ·
                    refine ⟨13938022951055004761966117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9292015300703336507977411 13938022951055004761966117)
                    ·
                      refine ⟨2613379303322813392868647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13938022951055004761966117 2613379303322813392868647)
                      ·
                        rfl

theorem cell23_5089538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5089538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089538 prefixEnd_5089538 := by exact prefixLift 5089538
  have htrace : WordTrace (prefixWord ++ tailWord_5089538) baseStart_5089538 baseEnd_5089538 := by
    simpa [prefixWord, tailWord_5089538, baseEnd_5089538] using wordTrace_append hprefix tailTrace_5089538
  have hstable : (prefixWord ++ tailWord_5089538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089538).length < 2 ^ (prefixWord ++ tailWord_5089538).sum := by decide
  have hdescent : baseEnd_5089538 < baseStart_5089538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089548 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_5089548 : Nat := 118140960795 + 5089548 * 2 ^ 59
def prefixEnd_5089548 : Nat := 4983230072969 + 3 ^ 40 * 5089548 * 2
def baseEnd_5089548 : Nat := 871128146043119451247867

theorem tailTrace_5089548 : CollatzResearch.WordTrace tailWord_5089548 prefixEnd_5089548 871128146043119451247867 := by
  unfold tailWord_5089548
  simp only [CollatzResearch.WordTrace]
  refine ⟨92815532882722148220462649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123754043843629530960616865 92815532882722148220462649)
  ·
    refine ⟨69611649662041611165346987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92815532882722148220462649 69611649662041611165346987)
    ·
      refine ⟨104417474493062416748020481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69611649662041611165346987 104417474493062416748020481)
      ·
        refine ⟨78313105869796812561015361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104417474493062416748020481 78313105869796812561015361)
        ·
          refine ⟨58734829402347609420761521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78313105869796812561015361 58734829402347609420761521)
          ·
            refine ⟨44051122051760707065571141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58734829402347609420761521 44051122051760707065571141)
            ·
              refine ⟨8259585384705132574794589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44051122051760707065571141 8259585384705132574794589)
              ·
                refine ⟨3097344519264424715547971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8259585384705132574794589 3097344519264424715547971)
                ·
                  refine ⟨4646016778896637073321957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097344519264424715547971 4646016778896637073321957)
                  ·
                    refine ⟨871128146043119451247867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646016778896637073321957 871128146043119451247867)
                    ·
                      rfl

theorem cell23_5089548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_5089548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089548 prefixEnd_5089548 := by exact prefixLift 5089548
  have htrace : WordTrace (prefixWord ++ tailWord_5089548) baseStart_5089548 baseEnd_5089548 := by
    simpa [prefixWord, tailWord_5089548, baseEnd_5089548] using wordTrace_append hprefix tailTrace_5089548
  have hstable : (prefixWord ++ tailWord_5089548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089548).length < 2 ^ (prefixWord ++ tailWord_5089548).sum := by decide
  have hdescent : baseEnd_5089548 < baseStart_5089548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089598 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_5089598 : Nat := 118140960795 + 5089598 * 2 ^ 59
def prefixEnd_5089598 : Nat := 4983230072969 + 3 ^ 40 * 5089598 * 2
def baseEnd_5089598 : Nat := 2613410112162083158118371

theorem tailTrace_5089598 : CollatzResearch.WordTrace tailWord_5089598 prefixEnd_5089598 2613410112162083158118371 := by
  unfold tailWord_5089598
  simp only [CollatzResearch.WordTrace]
  refine ⟨23204111176907894372530681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123755259610175436653496965 23204111176907894372530681)
  ·
    refine ⟨17403083382680920779398011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23204111176907894372530681 17403083382680920779398011)
    ·
      refine ⟨26104625074021381169097017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17403083382680920779398011 26104625074021381169097017)
      ·
        refine ⟨19578468805516035876822763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26104625074021381169097017 19578468805516035876822763)
        ·
          refine ⟨29367703208274053815234145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19578468805516035876822763 29367703208274053815234145)
          ·
            refine ⟨22025777406205540361425609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29367703208274053815234145 22025777406205540361425609)
            ·
              refine ⟨16519333054654155271069207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22025777406205540361425609 16519333054654155271069207)
              ·
                refine ⟨24778999581981232906603811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16519333054654155271069207 24778999581981232906603811)
                ·
                  refine ⟨37168499372971849359905717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24778999581981232906603811 37168499372971849359905717)
                  ·
                    refine ⟨3484546816216110877491161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37168499372971849359905717 3484546816216110877491161)
                    ·
                      refine ⟨2613410112162083158118371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484546816216110877491161 2613410112162083158118371)
                      ·
                        rfl

theorem cell23_5089598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_5089598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089598 prefixEnd_5089598 := by exact prefixLift 5089598
  have htrace : WordTrace (prefixWord ++ tailWord_5089598) baseStart_5089598 baseEnd_5089598 := by
    simpa [prefixWord, tailWord_5089598, baseEnd_5089598] using wordTrace_append hprefix tailTrace_5089598
  have hstable : (prefixWord ++ tailWord_5089598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089598).length < 2 ^ (prefixWord ++ tailWord_5089598).sum := by decide
  have hdescent : baseEnd_5089598 < baseStart_5089598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089624 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5089624 : Nat := 118140960795 + 5089624 * 2 ^ 59
def prefixEnd_5089624 : Nat := 4983230072969 + 3 ^ 40 * 5089624 * 2
def baseEnd_5089624 : Nat := 2613423462659100056393251

theorem tailTrace_5089624 : CollatzResearch.WordTrace tailWord_5089624 prefixEnd_5089624 2613423462659100056393251 := by
  unfold tailWord_5089624
  simp only [CollatzResearch.WordTrace]
  refine ⟨92816918856584480710345963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123755891808779307613794617 92816918856584480710345963)
  ·
    refine ⟨139225378284876721065518945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92816918856584480710345963 139225378284876721065518945)
    ·
      refine ⟨104419033713657540799139209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139225378284876721065518945 104419033713657540799139209)
      ·
        refine ⟨78314275285243155599354407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104419033713657540799139209 78314275285243155599354407)
        ·
          refine ⟨117471412927864733399031611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78314275285243155599354407 117471412927864733399031611)
          ·
            refine ⟨176207119391797100098547417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117471412927864733399031611 176207119391797100098547417)
            ·
              refine ⟨132155339543847825073910563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176207119391797100098547417 132155339543847825073910563)
              ·
                refine ⟨198233009315771737610865845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132155339543847825073910563 198233009315771737610865845)
                ·
                  refine ⟨18584344623353600401018673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198233009315771737610865845 18584344623353600401018673)
                  ·
                    refine ⟨13938258467515200300764005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18584344623353600401018673 13938258467515200300764005)
                    ·
                      refine ⟨2613423462659100056393251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13938258467515200300764005 2613423462659100056393251)
                      ·
                        rfl

theorem cell23_5089624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5089624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089624 prefixEnd_5089624 := by exact prefixLift 5089624
  have htrace : WordTrace (prefixWord ++ tailWord_5089624) baseStart_5089624 baseEnd_5089624 := by
    simpa [prefixWord, tailWord_5089624, baseEnd_5089624] using wordTrace_append hprefix tailTrace_5089624
  have hstable : (prefixWord ++ tailWord_5089624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089624).length < 2 ^ (prefixWord ++ tailWord_5089624).sum := by decide
  have hdescent : baseEnd_5089624 < baseStart_5089624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089648 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_5089648 : Nat := 118140960795 + 5089648 * 2 ^ 59
def prefixEnd_5089648 : Nat := 4983230072969 + 3 ^ 40 * 5089648 * 2
def baseEnd_5089648 : Nat := 2613435786194807962493141

theorem tailTrace_5089648 : CollatzResearch.WordTrace tailWord_5089648 prefixEnd_5089648 2613435786194807962493141 := by
  unfold tailWord_5089648
  simp only [CollatzResearch.WordTrace]
  refine ⟨92817356532541006759782799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123756475376721342346377065 92817356532541006759782799)
  ·
    refine ⟨139226034798811510139674199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92817356532541006759782799 139226034798811510139674199)
    ·
      refine ⟨208839052198217265209511299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139226034798811510139674199 208839052198217265209511299)
      ·
        refine ⟨313258578297325897814266949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208839052198217265209511299 313258578297325897814266949)
        ·
          refine ⟨58735983430748605840175053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313258578297325897814266949 58735983430748605840175053)
          ·
            refine ⟨22025993786530727190065645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58735983430748605840175053 22025993786530727190065645)
            ·
              refine ⟨8259747669949022696274617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22025993786530727190065645 8259747669949022696274617)
              ·
                refine ⟨6194810752461767022205963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259747669949022696274617 6194810752461767022205963)
                ·
                  refine ⟨9292216128692650533308945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194810752461767022205963 9292216128692650533308945)
                  ·
                    refine ⟨6969162096519487899981709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9292216128692650533308945 6969162096519487899981709)
                    ·
                      refine ⟨2613435786194807962493141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969162096519487899981709 2613435786194807962493141)
                      ·
                        rfl

theorem cell23_5089648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_5089648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089648 prefixEnd_5089648 := by exact prefixLift 5089648
  have htrace : WordTrace (prefixWord ++ tailWord_5089648) baseStart_5089648 baseEnd_5089648 := by
    simpa [prefixWord, tailWord_5089648, baseEnd_5089648] using wordTrace_append hprefix tailTrace_5089648
  have hstable : (prefixWord ++ tailWord_5089648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089648).length < 2 ^ (prefixWord ++ tailWord_5089648).sum := by decide
  have hdescent : baseEnd_5089648 < baseStart_5089648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089661 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_5089661 : Nat := 118140960795 + 5089661 * 2 ^ 59
def prefixEnd_5089661 : Nat := 4983230072969 + 3 ^ 40 * 5089661 * 2
def baseEnd_5089661 : Nat := 2613442461443316411630581

theorem tailTrace_5089661 : CollatzResearch.WordTrace tailWord_5089661 prefixEnd_5089661 2613442461443316411630581 := by
  unfold tailWord_5089661
  simp only [CollatzResearch.WordTrace]
  refine ⟨185635187214034916739788837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123756791476023277826525891 185635187214034916739788837)
  ·
    refine ⟨34806597602631546888710407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185635187214034916739788837 34806597602631546888710407)
    ·
      refine ⟨52209896403947320333065611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34806597602631546888710407 52209896403947320333065611)
      ·
        refine ⟨78314844605920980499598417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52209896403947320333065611 78314844605920980499598417)
        ·
          refine ⟨58736133454440735374698813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78314844605920980499598417 58736133454440735374698813)
          ·
            refine ⟨22026050045415275765512055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58736133454440735374698813 22026050045415275765512055)
            ·
              refine ⟨33039075068122913648268083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22026050045415275765512055 33039075068122913648268083)
              ·
                refine ⟨49558612602184370472402125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33039075068122913648268083 49558612602184370472402125)
                ·
                  refine ⟨18584479725819138927150797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49558612602184370472402125 18584479725819138927150797)
                  ·
                    refine ⟨6969179897182177097681549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18584479725819138927150797 6969179897182177097681549)
                    ·
                      refine ⟨2613442461443316411630581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969179897182177097681549 2613442461443316411630581)
                      ·
                        rfl

theorem cell23_5089661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_5089661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089661 prefixEnd_5089661 := by exact prefixLift 5089661
  have htrace : WordTrace (prefixWord ++ tailWord_5089661) baseStart_5089661 baseEnd_5089661 := by
    simpa [prefixWord, tailWord_5089661, baseEnd_5089661] using wordTrace_append hprefix tailTrace_5089661
  have hstable : (prefixWord ++ tailWord_5089661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089661).length < 2 ^ (prefixWord ++ tailWord_5089661).sum := by decide
  have hdescent : baseEnd_5089661 < baseStart_5089661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089716 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5089716 : Nat := 118140960795 + 5089716 * 2 ^ 59
def prefixEnd_5089716 : Nat := 4983230072969 + 3 ^ 40 * 5089716 * 2
def baseEnd_5089716 : Nat := 2613470702879313696442829

theorem tailTrace_5089716 : CollatzResearch.WordTrace tailWord_5089716 prefixEnd_5089716 2613470702879313696442829 := by
  unfold tailWord_5089716
  simp only [CollatzResearch.WordTrace]
  refine ⟨92818596614417830566520501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123758128819223774088694001 92818596614417830566520501)
  ·
    refine ⟨8701743432601671615611297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92818596614417830566520501 8701743432601671615611297)
    ·
      refine ⟨6526307574451253711708473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8701743432601671615611297 6526307574451253711708473)
      ·
        refine ⟨4894730680838440283781355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6526307574451253711708473 4894730680838440283781355)
        ·
          refine ⟨7342096021257660425672033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894730680838440283781355 7342096021257660425672033)
          ·
            refine ⟨5506572015943245319254025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7342096021257660425672033 5506572015943245319254025)
            ·
              refine ⟨4129929011957433989440519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5506572015943245319254025 4129929011957433989440519)
              ·
                refine ⟨6194893517936150984160779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129929011957433989440519 6194893517936150984160779)
                ·
                  refine ⟨9292340276904226476241169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194893517936150984160779 9292340276904226476241169)
                  ·
                    refine ⟨6969255207678169857180877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9292340276904226476241169 6969255207678169857180877)
                    ·
                      refine ⟨2613470702879313696442829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969255207678169857180877 2613470702879313696442829)
                      ·
                        rfl

theorem cell23_5089716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5089716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089716 prefixEnd_5089716 := by exact prefixLift 5089716
  have htrace : WordTrace (prefixWord ++ tailWord_5089716) baseStart_5089716 baseEnd_5089716 := by
    simpa [prefixWord, tailWord_5089716, baseEnd_5089716] using wordTrace_append hprefix tailTrace_5089716
  have hstable : (prefixWord ++ tailWord_5089716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089716).length < 2 ^ (prefixWord ++ tailWord_5089716).sum := by decide
  have hdescent : baseEnd_5089716 < baseStart_5089716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089729 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5089729 : Nat := 118140960795 + 5089729 * 2 ^ 59
def prefixEnd_5089729 : Nat := 4983230072969 + 3 ^ 40 * 5089729 * 2
def baseEnd_5089729 : Nat := 2613477378127822145580269

theorem tailTrace_5089729 : CollatzResearch.WordTrace tailWord_5089729 prefixEnd_5089729 2613477378127822145580269 := by
  unfold tailWord_5089729
  simp only [CollatzResearch.WordTrace]
  refine ⟨185637667377788564353264241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123758444918525709568842827 185637667377788564353264241)
  ·
    refine ⟨139228250533341423264948181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185637667377788564353264241 139228250533341423264948181)
    ·
      refine ⟨3263162121875189607772223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 139228250533341423264948181 3263162121875189607772223)
      ·
        refine ⟨4894743182812784411658335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263162121875189607772223 4894743182812784411658335)
        ·
          refine ⟨7342114774219176617487503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894743182812784411658335 7342114774219176617487503)
          ·
            refine ⟨11013172161328764926231255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7342114774219176617487503 11013172161328764926231255)
            ·
              refine ⟨16519758241993147389346883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013172161328764926231255 16519758241993147389346883)
              ·
                refine ⟨24779637362989721084020325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16519758241993147389346883 24779637362989721084020325)
                ·
                  refine ⟨4646182005560572703253811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24779637362989721084020325 4646182005560572703253811)
                  ·
                    refine ⟨6969273008340859054880717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4646182005560572703253811 6969273008340859054880717)
                    ·
                      refine ⟨2613477378127822145580269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969273008340859054880717 2613477378127822145580269)
                      ·
                        rfl

theorem cell23_5089729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5089729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089729 prefixEnd_5089729 := by exact prefixLift 5089729
  have htrace : WordTrace (prefixWord ++ tailWord_5089729) baseStart_5089729 baseEnd_5089729 := by
    simpa [prefixWord, tailWord_5089729, baseEnd_5089729] using wordTrace_append hprefix tailTrace_5089729
  have hstable : (prefixWord ++ tailWord_5089729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089729).length < 2 ^ (prefixWord ++ tailWord_5089729).sum := by decide
  have hdescent : baseEnd_5089729 < baseStart_5089729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089735 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_5089735 : Nat := 118140960795 + 5089735 * 2 ^ 59
def prefixEnd_5089735 : Nat := 4983230072969 + 3 ^ 40 * 5089735 * 2
def baseEnd_5089735 : Nat := 2613480459011749122105241

theorem tailTrace_5089735 : CollatzResearch.WordTrace tailWord_5089735 prefixEnd_5089735 2613480459011749122105241 := by
  unfold tailWord_5089735
  simp only [CollatzResearch.WordTrace]
  refine ⟨185637886215766827377982659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123758590810511218251988439 185637886215766827377982659)
  ·
    refine ⟨278456829323650241066973989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185637886215766827377982659 278456829323650241066973989)
    ·
      refine ⟨52210655498184420200057623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278456829323650241066973989 52210655498184420200057623)
      ·
        refine ⟨78315983247276630300086435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52210655498184420200057623 78315983247276630300086435)
        ·
          refine ⟨117473974870914945450129653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78315983247276630300086435 117473974870914945450129653)
          ·
            refine ⟨11013185144148276135949655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117473974870914945450129653 11013185144148276135949655)
            ·
              refine ⟨16519777716222414203924483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013185144148276135949655 16519777716222414203924483)
              ·
                refine ⟨24779666574333621305886725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16519777716222414203924483 24779666574333621305886725)
                ·
                  refine ⟨4646187482687553994853761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24779666574333621305886725 4646187482687553994853761)
                  ·
                    refine ⟨3484640612015665496140321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4646187482687553994853761 3484640612015665496140321)
                    ·
                      refine ⟨2613480459011749122105241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484640612015665496140321 2613480459011749122105241)
                      ·
                        rfl

theorem cell23_5089735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_5089735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089735 prefixEnd_5089735 := by exact prefixLift 5089735
  have htrace : WordTrace (prefixWord ++ tailWord_5089735) baseStart_5089735 baseEnd_5089735 := by
    simpa [prefixWord, tailWord_5089735, baseEnd_5089735] using wordTrace_append hprefix tailTrace_5089735
  have hstable : (prefixWord ++ tailWord_5089735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089735).length < 2 ^ (prefixWord ++ tailWord_5089735).sum := by decide
  have hdescent : baseEnd_5089735 < baseStart_5089735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089744 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_5089744 : Nat := 118140960795 + 5089744 * 2 ^ 59
def prefixEnd_5089744 : Nat := 4983230072969 + 3 ^ 40 * 5089744 * 2
def baseEnd_5089744 : Nat := 2613485080337639586892699

theorem tailTrace_5089744 : CollatzResearch.WordTrace tailWord_5089744 prefixEnd_5089744 2613485080337639586892699 := by
  unfold tailWord_5089744
  simp only [CollatzResearch.WordTrace]
  refine ⟨92819107236367110957530143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123758809648489481276706857 92819107236367110957530143)
  ·
    refine ⟨139228660854550666436295215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92819107236367110957530143 139228660854550666436295215)
    ·
      refine ⟨208842991281825999654442823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139228660854550666436295215 208842991281825999654442823)
      ·
        refine ⟨313264486922738999481664235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208842991281825999654442823 313264486922738999481664235)
        ·
          refine ⟨469896730384108499222496353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313264486922738999481664235 469896730384108499222496353)
          ·
            refine ⟨352422547788081374416872265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469896730384108499222496353 352422547788081374416872265)
            ·
              refine ⟨264316910841061030812654199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352422547788081374416872265 264316910841061030812654199)
              ·
                refine ⟨396475366261591546218981299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264316910841061030812654199 396475366261591546218981299)
                ·
                  refine ⟨594713049392387319328471949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396475366261591546218981299 594713049392387319328471949)
                  ·
                    refine ⟨223017393522145244748176981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594713049392387319328471949 223017393522145244748176981)
                    ·
                      refine ⟨2613485080337639586892699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 223017393522145244748176981 2613485080337639586892699)
                      ·
                        rfl

theorem cell23_5089744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_5089744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089744 prefixEnd_5089744 := by exact prefixLift 5089744
  have htrace : WordTrace (prefixWord ++ tailWord_5089744) baseStart_5089744 baseEnd_5089744 := by
    simpa [prefixWord, tailWord_5089744, baseEnd_5089744] using wordTrace_append hprefix tailTrace_5089744
  have hstable : (prefixWord ++ tailWord_5089744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089744).length < 2 ^ (prefixWord ++ tailWord_5089744).sum := by decide
  have hdescent : baseEnd_5089744 < baseStart_5089744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089748 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5089748 : Nat := 118140960795 + 5089748 * 2 ^ 59
def prefixEnd_5089748 : Nat := 4983230072969 + 3 ^ 40 * 5089748 * 2
def baseEnd_5089748 : Nat := 2613487134260257571242681

theorem tailTrace_5089748 : CollatzResearch.WordTrace tailWord_5089748 prefixEnd_5089748 2613487134260257571242681 := by
  unfold tailWord_5089748
  simp only [CollatzResearch.WordTrace]
  refine ⟨92819180182359865299102949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123758906909813153732137265 92819180182359865299102949)
  ·
    refine ⟨17403596284192474743581803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92819180182359865299102949 17403596284192474743581803)
    ·
      refine ⟨26105394426288712115372705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17403596284192474743581803 26105394426288712115372705)
      ·
        refine ⟨19579045819716534086529529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26105394426288712115372705 19579045819716534086529529)
        ·
          refine ⟨14684284364787400564897147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19579045819716534086529529 14684284364787400564897147)
          ·
            refine ⟨22026426547181100847345721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14684284364787400564897147 22026426547181100847345721)
            ·
              refine ⟨16519819910385825635509291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22026426547181100847345721 16519819910385825635509291)
              ·
                refine ⟨24779729865578738453263937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16519819910385825635509291 24779729865578738453263937)
                ·
                  refine ⟨18584797399184053839947953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24779729865578738453263937 18584797399184053839947953)
                  ·
                    refine ⟨13938598049388040379960965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18584797399184053839947953 13938598049388040379960965)
                    ·
                      refine ⟨2613487134260257571242681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13938598049388040379960965 2613487134260257571242681)
                      ·
                        rfl

theorem cell23_5089748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5089748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089748 prefixEnd_5089748 := by exact prefixLift 5089748
  have htrace : WordTrace (prefixWord ++ tailWord_5089748) baseStart_5089748 baseEnd_5089748 := by
    simpa [prefixWord, tailWord_5089748, baseEnd_5089748] using wordTrace_append hprefix tailTrace_5089748
  have hstable : (prefixWord ++ tailWord_5089748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089748).length < 2 ^ (prefixWord ++ tailWord_5089748).sum := by decide
  have hdescent : baseEnd_5089748 < baseStart_5089748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089771 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 2, 5]
def baseStart_5089771 : Nat := 118140960795 + 5089771 * 2 ^ 59
def prefixEnd_5089771 : Nat := 4983230072969 + 3 ^ 40 * 5089771 * 2
def baseEnd_5089771 : Nat := 871166314771770327085025

theorem tailTrace_5089771 : CollatzResearch.WordTrace tailWord_5089771 prefixEnd_5089771 871166314771770327085025 := by
  unfold tailWord_5089771
  simp only [CollatzResearch.WordTrace]
  refine ⟨185639199243636405526293167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123759466162424270350862111 185639199243636405526293167)
  ·
    refine ⟨278458798865454608289439751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185639199243636405526293167 278458798865454608289439751)
    ·
      refine ⟨417688198298181912434159627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278458798865454608289439751 417688198298181912434159627)
      ·
        refine ⟨626532297447272868651239441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417688198298181912434159627 626532297447272868651239441)
        ·
          refine ⟨469899223085454651488429581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626532297447272868651239441 469899223085454651488429581)
          ·
            refine ⟨176212208657045494308161093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469899223085454651488429581 176212208657045494308161093)
            ·
              refine ⟨33039789123196030182780205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176212208657045494308161093 33039789123196030182780205)
              ·
                refine ⟨12389920921198511318542577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33039789123196030182780205 12389920921198511318542577)
                ·
                  refine ⟨9292440690898883488906933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12389920921198511318542577 9292440690898883488906933)
                  ·
                    refine ⟨871166314771770327085025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9292440690898883488906933 871166314771770327085025)
                    ·
                      rfl

theorem cell23_5089771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 5].length) (baseStart_5089771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089771 prefixEnd_5089771 := by exact prefixLift 5089771
  have htrace : WordTrace (prefixWord ++ tailWord_5089771) baseStart_5089771 baseEnd_5089771 := by
    simpa [prefixWord, tailWord_5089771, baseEnd_5089771] using wordTrace_append hprefix tailTrace_5089771
  have hstable : (prefixWord ++ tailWord_5089771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089771).length < 2 ^ (prefixWord ++ tailWord_5089771).sum := by decide
  have hdescent : baseEnd_5089771 < baseStart_5089771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089818 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_5089818 : Nat := 118140960795 + 5089818 * 2 ^ 59
def prefixEnd_5089818 : Nat := 4983230072969 + 3 ^ 40 * 5089818 * 2
def baseEnd_5089818 : Nat := 871174359302024099122453

theorem tailTrace_5089818 : CollatzResearch.WordTrace tailWord_5089818 prefixEnd_5089818 871174359302024099122453 := by
  unfold tailWord_5089818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46410228368616533138313527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123760608982977421702169405 46410228368616533138313527)
  ·
    refine ⟨69615342552924799707470291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46410228368616533138313527 69615342552924799707470291)
    ·
      refine ⟨104423013829387199561205437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69615342552924799707470291 104423013829387199561205437)
      ·
        refine ⟨39158630186020199835452039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104423013829387199561205437 39158630186020199835452039)
        ·
          refine ⟨58737945279030299753178059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39158630186020199835452039 58737945279030299753178059)
          ·
            refine ⟨88106917918545449629767089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58737945279030299753178059 88106917918545449629767089)
            ·
              refine ⟨66080188438909087222325317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88106917918545449629767089 66080188438909087222325317)
              ·
                refine ⟨12390035332295453854185997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66080188438909087222325317 12390035332295453854185997)
                ·
                  refine ⟨4646263249610795195319749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12390035332295453854185997 4646263249610795195319749)
                  ·
                    refine ⟨871174359302024099122453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646263249610795195319749 871174359302024099122453)
                    ·
                      rfl

theorem cell23_5089818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_5089818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089818 prefixEnd_5089818 := by exact prefixLift 5089818
  have htrace : WordTrace (prefixWord ++ tailWord_5089818) baseStart_5089818 baseEnd_5089818 := by
    simpa [prefixWord, tailWord_5089818, baseEnd_5089818] using wordTrace_append hprefix tailTrace_5089818
  have hstable : (prefixWord ++ tailWord_5089818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089818).length < 2 ^ (prefixWord ++ tailWord_5089818).sum := by decide
  have hdescent : baseEnd_5089818 < baseStart_5089818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089848 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 6]
def baseStart_5089848 : Nat := 118140960795 + 5089848 * 2 ^ 59
def prefixEnd_5089848 : Nat := 4983230072969 + 3 ^ 40 * 5089848 * 2
def baseEnd_5089848 : Nat := 290393164702856353332469

theorem tailTrace_5089848 : CollatzResearch.WordTrace tailWord_5089848 prefixEnd_5089848 290393164702856353332469 := by
  unfold tailWord_5089848
  simp only [CollatzResearch.WordTrace]
  refine ⟨92821003832178723838423099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123761338442904965117897465 92821003832178723838423099)
  ·
    refine ⟨139231505748268085757634649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92821003832178723838423099 139231505748268085757634649)
    ·
      refine ⟨104423629311201064318225987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139231505748268085757634649 104423629311201064318225987)
      ·
        refine ⟨156635443966801596477338981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104423629311201064318225987 156635443966801596477338981)
        ·
          refine ⟨29369145743775299339501059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156635443966801596477338981 29369145743775299339501059)
          ·
            refine ⟨44053718615662949009251589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29369145743775299339501059 44053718615662949009251589)
            ·
              refine ⟨8260072240436802939234673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44053718615662949009251589 8260072240436802939234673)
              ·
                refine ⟨6195054180327602204426005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8260072240436802939234673 6195054180327602204426005)
                ·
                  refine ⟨290393164702856353332469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6195054180327602204426005 290393164702856353332469)
                  ·
                    rfl

theorem cell23_5089848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_5089848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089848 prefixEnd_5089848 := by exact prefixLift 5089848
  have htrace : WordTrace (prefixWord ++ tailWord_5089848) baseStart_5089848 baseEnd_5089848 := by
    simpa [prefixWord, tailWord_5089848, baseEnd_5089848] using wordTrace_append hprefix tailTrace_5089848
  have hstable : (prefixWord ++ tailWord_5089848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089848).length < 2 ^ (prefixWord ++ tailWord_5089848).sum := by decide
  have hdescent : baseEnd_5089848 < baseStart_5089848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089852 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_5089852 : Nat := 118140960795 + 5089852 * 2 ^ 59
def prefixEnd_5089852 : Nat := 4983230072969 + 3 ^ 40 * 5089852 * 2
def baseEnd_5089852 : Nat := 871180178749441721447401

theorem tailTrace_5089852 : CollatzResearch.WordTrace tailWord_5089852 prefixEnd_5089852 871180178749441721447401 := by
  unfold tailWord_5089852
  simp only [CollatzResearch.WordTrace]
  refine ⟨92821076778171478179995905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123761435704228637573327873 92821076778171478179995905)
  ·
    refine ⟨69615807583628608634996929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92821076778171478179995905 69615807583628608634996929)
    ·
      refine ⟨52211855687721456476247697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69615807583628608634996929 52211855687721456476247697)
      ·
        refine ⟨39158891765791092357185773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52211855687721456476247697 39158891765791092357185773)
        ·
          refine ⟨14684584412171659633944665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39158891765791092357185773 14684584412171659633944665)
          ·
            refine ⟨11013438309128744725458499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14684584412171659633944665 11013438309128744725458499)
            ·
              refine ⟨16520157463693117088187749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013438309128744725458499 16520157463693117088187749)
              ·
                refine ⟨3097529524442459454035203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16520157463693117088187749 3097529524442459454035203)
                ·
                  refine ⟨4646294286663689181052805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097529524442459454035203 4646294286663689181052805)
                  ·
                    refine ⟨871180178749441721447401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646294286663689181052805 871180178749441721447401)
                    ·
                      rfl

theorem cell23_5089852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_5089852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089852 prefixEnd_5089852 := by exact prefixLift 5089852
  have htrace : WordTrace (prefixWord ++ tailWord_5089852) baseStart_5089852 baseEnd_5089852 := by
    simpa [prefixWord, tailWord_5089852, baseEnd_5089852] using wordTrace_append hprefix tailTrace_5089852
  have hstable : (prefixWord ++ tailWord_5089852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089852).length < 2 ^ (prefixWord ++ tailWord_5089852).sum := by decide
  have hdescent : baseEnd_5089852 < baseStart_5089852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089909 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5089909 : Nat := 118140960795 + 5089909 * 2 ^ 59
def prefixEnd_5089909 : Nat := 4983230072969 + 3 ^ 40 * 5089909 * 2
def baseEnd_5089909 : Nat := 2613569804645631441329441

theorem tailTrace_5089909 : CollatzResearch.WordTrace tailWord_5089909 prefixEnd_5089909 2613569804645631441329441 := by
  unfold tailWord_5089909
  simp only [CollatzResearch.WordTrace]
  refine ⟨185644232517136455094816781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123762821678090970063211187 185644232517136455094816781)
  ·
    refine ⟨69616587193926170660556293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185644232517136455094816781 69616587193926170660556293)
    ·
      refine ⟨13053110098861156998854305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69616587193926170660556293 13053110098861156998854305)
      ·
        refine ⟨9789832574145867749140729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13053110098861156998854305 9789832574145867749140729)
        ·
          refine ⟨7342374430609400811855547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9789832574145867749140729 7342374430609400811855547)
          ·
            refine ⟨11013561645914101217783321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7342374430609400811855547 11013561645914101217783321)
            ·
              refine ⟨8260171234435575913337491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11013561645914101217783321 8260171234435575913337491)
              ·
                refine ⟨12390256851653363870006237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260171234435575913337491 12390256851653363870006237)
                ·
                  refine ⟨4646346319370011451252339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12390256851653363870006237 4646346319370011451252339)
                  ·
                    refine ⟨6969519479055017176878509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4646346319370011451252339 6969519479055017176878509)
                    ·
                      refine ⟨2613569804645631441329441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969519479055017176878509 2613569804645631441329441)
                      ·
                        rfl

theorem cell23_5089909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5089909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089909 prefixEnd_5089909 := by exact prefixLift 5089909
  have htrace : WordTrace (prefixWord ++ tailWord_5089909) baseStart_5089909 baseEnd_5089909 := by
    simpa [prefixWord, tailWord_5089909, baseEnd_5089909] using wordTrace_append hprefix tailTrace_5089909
  have hstable : (prefixWord ++ tailWord_5089909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089909).length < 2 ^ (prefixWord ++ tailWord_5089909).sum := by decide
  have hdescent : baseEnd_5089909 < baseStart_5089909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089925 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_5089925 : Nat := 118140960795 + 5089925 * 2 ^ 59
def prefixEnd_5089925 : Nat := 4983230072969 + 3 ^ 40 * 5089925 * 2
def baseEnd_5089925 : Nat := 871192673445367792909789

theorem tailTrace_5089925 : CollatzResearch.WordTrace tailWord_5089925 prefixEnd_5089925 871192673445367792909789 := by
  unfold tailWord_5089925
  simp only [CollatzResearch.WordTrace]
  refine ⟨185644816085078489827399229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123763210723385659884932819 185644816085078489827399229)
  ·
    refine ⟨69616806031904433685274711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185644816085078489827399229 69616806031904433685274711)
    ·
      refine ⟨104425209047856650527912067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69616806031904433685274711 104425209047856650527912067)
      ·
        refine ⟨156637813571784975791868101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104425209047856650527912067 156637813571784975791868101)
        ·
          refine ⟨29369590044709682960975269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156637813571784975791868101 29369590044709682960975269)
          ·
            refine ⟨5506798133383065555182863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29369590044709682960975269 5506798133383065555182863)
            ·
              refine ⟨8260197200074598332774295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5506798133383065555182863 8260197200074598332774295)
              ·
                refine ⟨12390295800111897499161443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260197200074598332774295 12390295800111897499161443)
                ·
                  refine ⟨18585443700167846248742165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12390295800111897499161443 18585443700167846248742165)
                  ·
                    refine ⟨871192673445367792909789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18585443700167846248742165 871192673445367792909789)
                    ·
                      rfl

theorem cell23_5089925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_5089925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089925 prefixEnd_5089925 := by exact prefixLift 5089925
  have htrace : WordTrace (prefixWord ++ tailWord_5089925) baseStart_5089925 baseEnd_5089925 := by
    simpa [prefixWord, tailWord_5089925, baseEnd_5089925] using wordTrace_append hprefix tailTrace_5089925
  have hstable : (prefixWord ++ tailWord_5089925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089925).length < 2 ^ (prefixWord ++ tailWord_5089925).sum := by decide
  have hdescent : baseEnd_5089925 < baseStart_5089925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089966 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5089966 : Nat := 118140960795 + 5089966 * 2 ^ 59
def prefixEnd_5089966 : Nat := 4983230072969 + 3 ^ 40 * 5089966 * 2
def baseEnd_5089966 : Nat := 2613599073042937718316679

theorem tailTrace_5089966 : CollatzResearch.WordTrace tailWord_5089966 prefixEnd_5089966 2613599073042937718316679 := by
  unfold tailWord_5089966
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205788934741244228705219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123764207651953302553094501 23205788934741244228705219)
  ·
    refine ⟨34808683402111866343057829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23205788934741244228705219 34808683402111866343057829)
    ·
      refine ⟨6526628137895974939323343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34808683402111866343057829 6526628137895974939323343)
      ·
        refine ⟨9789942206843962408985015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6526628137895974939323343 9789942206843962408985015)
        ·
          refine ⟨14684913310265943613477523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9789942206843962408985015 14684913310265943613477523)
          ·
            refine ⟨22027369965398915420216285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14684913310265943613477523 22027369965398915420216285)
            ·
              refine ⟨8260263737024593282581107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22027369965398915420216285 8260263737024593282581107)
              ·
                refine ⟨12390395605536889923871661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260263737024593282581107 12390395605536889923871661)
                ·
                  refine ⟨4646398352076333721451873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12390395605536889923871661 4646398352076333721451873)
                  ·
                    refine ⟨3484798764057250291088905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4646398352076333721451873 3484798764057250291088905)
                    ·
                      refine ⟨2613599073042937718316679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484798764057250291088905 2613599073042937718316679)
                      ·
                        rfl

theorem cell23_5089966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5089966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089966 prefixEnd_5089966 := by exact prefixLift 5089966
  have htrace : WordTrace (prefixWord ++ tailWord_5089966) baseStart_5089966 baseEnd_5089966 := by
    simpa [prefixWord, tailWord_5089966, baseEnd_5089966] using wordTrace_append hprefix tailTrace_5089966
  have hstable : (prefixWord ++ tailWord_5089966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089966).length < 2 ^ (prefixWord ++ tailWord_5089966).sum := by decide
  have hdescent : baseEnd_5089966 < baseStart_5089966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089992 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_5089992 : Nat := 118140960795 + 5089992 * 2 ^ 59
def prefixEnd_5089992 : Nat := 4983230072969 + 3 ^ 40 * 5089992 * 2
def baseEnd_5089992 : Nat := 2613612423539954616591559

theorem tailTrace_5089992 : CollatzResearch.WordTrace tailWord_5089992 prefixEnd_5089992 2613612423539954616591559 := by
  unfold tailWord_5089992
  simp only [CollatzResearch.WordTrace]
  refine ⟨92823629887917880135044115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123764839850557173513392153 92823629887917880135044115)
  ·
    refine ⟨139235444831876820202566173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92823629887917880135044115 139235444831876820202566173)
    ·
      refine ⟨52213291811953807575962315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139235444831876820202566173 52213291811953807575962315)
      ·
        refine ⟨78319937717930711363943473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52213291811953807575962315 78319937717930711363943473)
        ·
          refine ⟨58739953288448033522957605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78319937717930711363943473 58739953288448033522957605)
          ·
            refine ⟨11013741241584006285554551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58739953288448033522957605 11013741241584006285554551)
            ·
              refine ⟨16520611862376009428331827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013741241584006285554551 16520611862376009428331827)
              ·
                refine ⟨24780917793564014142497741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16520611862376009428331827 24780917793564014142497741)
                ·
                  refine ⟨9292844172586505303436653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24780917793564014142497741 9292844172586505303436653)
                  ·
                    refine ⟨3484816564719939488788745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9292844172586505303436653 3484816564719939488788745)
                    ·
                      refine ⟨2613612423539954616591559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484816564719939488788745 2613612423539954616591559)
                      ·
                        rfl

theorem cell23_5089992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_5089992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089992 prefixEnd_5089992 := by exact prefixLift 5089992
  have htrace : WordTrace (prefixWord ++ tailWord_5089992) baseStart_5089992 baseEnd_5089992 := by
    simpa [prefixWord, tailWord_5089992, baseEnd_5089992] using wordTrace_append hprefix tailTrace_5089992
  have hstable : (prefixWord ++ tailWord_5089992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089992).length < 2 ^ (prefixWord ++ tailWord_5089992).sum := by decide
  have hdescent : baseEnd_5089992 < baseStart_5089992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090009 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 1, 3, 2]
def baseStart_5090009 : Nat := 118140960795 + 5090009 * 2 ^ 59
def prefixEnd_5090009 : Nat := 4983230072969 + 3 ^ 40 * 5090009 * 2
def baseEnd_5090009 : Nat := 2613621152711081050078981

theorem tailTrace_5090009 : CollatzResearch.WordTrace tailWord_5090009 prefixEnd_5090009 2613621152711081050078981 := by
  unfold tailWord_5090009
  simp only [CollatzResearch.WordTrace]
  refine ⟨185647879816774172173457081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123765253211182781448971387 185647879816774172173457081)
  ·
    refine ⟨139235909862580629130092811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185647879816774172173457081 139235909862580629130092811)
    ·
      refine ⟨208853864793870943695139217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139235909862580629130092811 208853864793870943695139217)
      ·
        refine ⟨156640398595403207771354413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208853864793870943695139217 156640398595403207771354413)
        ·
          refine ⟨58740149473276202914257905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156640398595403207771354413 58740149473276202914257905)
          ·
            refine ⟨44055112104957152185693429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58740149473276202914257905 44055112104957152185693429)
            ·
              refine ⟨4130166759839733017408759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44055112104957152185693429 4130166759839733017408759)
              ·
                refine ⟨6195250139759599526113139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130166759839733017408759 6195250139759599526113139)
                ·
                  refine ⟨9292875209639399289169709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6195250139759599526113139 9292875209639399289169709)
                  ·
                    refine ⟨3484828203614774733438641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9292875209639399289169709 3484828203614774733438641)
                    ·
                      refine ⟨2613621152711081050078981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484828203614774733438641 2613621152711081050078981)
                      ·
                        rfl

theorem cell23_5090009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_5090009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090009 prefixEnd_5090009 := by exact prefixLift 5090009
  have htrace : WordTrace (prefixWord ++ tailWord_5090009) baseStart_5090009 baseEnd_5090009 := by
    simpa [prefixWord, tailWord_5090009, baseEnd_5090009] using wordTrace_append hprefix tailTrace_5090009
  have hstable : (prefixWord ++ tailWord_5090009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090009).length < 2 ^ (prefixWord ++ tailWord_5090009).sum := by decide
  have hdescent : baseEnd_5090009 < baseStart_5090009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090028 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 7]
def baseStart_5090028 : Nat := 118140960795 + 5090028 * 2 ^ 59
def prefixEnd_5090028 : Nat := 4983230072969 + 3 ^ 40 * 5090028 * 2
def baseEnd_5090028 : Nat := 290403434315946275082377

theorem tailTrace_5090028 : CollatzResearch.WordTrace tailWord_5090028 prefixEnd_5090028 290403434315946275082377 := by
  unfold tailWord_5090028
  simp only [CollatzResearch.WordTrace]
  refine ⟨92824286401852669209199369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123765715202470225612265825 92824286401852669209199369)
  ·
    refine ⟨69618214801389501906899527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92824286401852669209199369 69618214801389501906899527)
    ·
      refine ⟨104427322202084252860349291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69618214801389501906899527 104427322202084252860349291)
      ·
        refine ⟨156640983303126379290523937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104427322202084252860349291 156640983303126379290523937)
        ·
          refine ⟨117480737477344784467892953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156640983303126379290523937 117480737477344784467892953)
          ·
            refine ⟨88110553108008588350919715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117480737477344784467892953 88110553108008588350919715)
            ·
              refine ⟨132165829662012882526379573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88110553108008588350919715 132165829662012882526379573)
              ·
                refine ⟨12390546530813707736848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132165829662012882526379573 12390546530813707736848085)
                ·
                  refine ⟨290403434315946275082377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12390546530813707736848085 290403434315946275082377)
                  ·
                    rfl

theorem cell23_5090028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_5090028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090028 prefixEnd_5090028 := by exact prefixLift 5090028
  have htrace : WordTrace (prefixWord ++ tailWord_5090028) baseStart_5090028 baseEnd_5090028 := by
    simpa [prefixWord, tailWord_5090028, baseEnd_5090028] using wordTrace_append hprefix tailTrace_5090028
  have hstable : (prefixWord ++ tailWord_5090028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090028).length < 2 ^ (prefixWord ++ tailWord_5090028).sum := by decide
  have hdescent : baseEnd_5090028 < baseStart_5090028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090090 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5090090 : Nat := 118140960795 + 5090090 * 2 ^ 59
def prefixEnd_5090090 : Nat := 4983230072969 + 3 ^ 40 * 5090090 * 2
def baseEnd_5090090 : Nat := 2613662744644095233166109

theorem tailTrace_5090090 : CollatzResearch.WordTrace tailWord_5090090 prefixEnd_5090090 2613662744644095233166109 := by
  unfold tailWord_5090090
  simp only [CollatzResearch.WordTrace]
  refine ⟨46412708532370180751788931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123767222752987148671437149 46412708532370180751788931)
  ·
    refine ⟨69619062798555271127683397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46412708532370180751788931 69619062798555271127683397)
    ·
      refine ⟨13053574274729113336440637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69619062798555271127683397 13053574274729113336440637)
      ·
        refine ⟨4895090353023417501165239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13053574274729113336440637 4895090353023417501165239)
        ·
          refine ⟨7342635529535126251747859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4895090353023417501165239 7342635529535126251747859)
          ·
            refine ⟨11013953294302689377621789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7342635529535126251747859 11013953294302689377621789)
            ·
              refine ⟨4130232485363508516608171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11013953294302689377621789 4130232485363508516608171)
              ·
                refine ⟨6195348728045262774912257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130232485363508516608171 6195348728045262774912257)
                ·
                  refine ⟨4646511546033947081184193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6195348728045262774912257 4646511546033947081184193)
                  ·
                    refine ⟨3484883659525460310888145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4646511546033947081184193 3484883659525460310888145)
                    ·
                      refine ⟨2613662744644095233166109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484883659525460310888145 2613662744644095233166109)
                      ·
                        rfl

theorem cell23_5090090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5090090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090090 prefixEnd_5090090 := by exact prefixLift 5090090
  have htrace : WordTrace (prefixWord ++ tailWord_5090090) baseStart_5090090 baseEnd_5090090 := by
    simpa [prefixWord, tailWord_5090090, baseEnd_5090090] using wordTrace_append hprefix tailTrace_5090090
  have hstable : (prefixWord ++ tailWord_5090090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090090).length < 2 ^ (prefixWord ++ tailWord_5090090).sum := by decide
  have hdescent : baseEnd_5090090 < baseStart_5090090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090113 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 5]
def baseStart_5090113 : Nat := 118140960795 + 5090113 * 2 ^ 59
def prefixEnd_5090113 : Nat := 4983230072969 + 3 ^ 40 * 5090113 * 2
def baseEnd_5090113 : Nat := 290408283855460960353167

theorem tailTrace_5090113 : CollatzResearch.WordTrace tailWord_5090113 prefixEnd_5090113 290408283855460960353167 := by
  unfold tailWord_5090113
  simp only [CollatzResearch.WordTrace]
  refine ⟨185651673008397397935242993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123767782005598265290161995 185651673008397397935242993)
  ·
    refine ⟨139238754756298048451432245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185651673008397397935242993 139238754756298048451432245)
    ·
      refine ⟨13053633258402942042321773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139238754756298048451432245 13053633258402942042321773)
      ·
        refine ⟨4895112471901103265870665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13053633258402942042321773 4895112471901103265870665)
        ·
          refine ⟨3671334353925827449402999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4895112471901103265870665 3671334353925827449402999)
          ·
            refine ⟨5507001530888741174104499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671334353925827449402999 5507001530888741174104499)
            ·
              refine ⟨8260502296333111761156749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507001530888741174104499 8260502296333111761156749)
              ·
                refine ⟨3097688361124916910433781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8260502296333111761156749 3097688361124916910433781)
                ·
                  refine ⟨290408283855460960353167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097688361124916910433781 290408283855460960353167)
                  ·
                    rfl

theorem cell23_5090113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 5].length) (baseStart_5090113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090113 prefixEnd_5090113 := by exact prefixLift 5090113
  have htrace : WordTrace (prefixWord ++ tailWord_5090113) baseStart_5090113 baseEnd_5090113 := by
    simpa [prefixWord, tailWord_5090113, baseEnd_5090113] using wordTrace_append hprefix tailTrace_5090113
  have hstable : (prefixWord ++ tailWord_5090113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090113).length < 2 ^ (prefixWord ++ tailWord_5090113).sum := by decide
  have hdescent : baseEnd_5090113 < baseStart_5090113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090115 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3]
def baseStart_5090115 : Nat := 118140960795 + 5090115 * 2 ^ 59
def prefixEnd_5090115 : Nat := 4983230072969 + 3 ^ 40 * 5090115 * 2
def baseEnd_5090115 : Nat := 2613675581660457635353493

theorem tailTrace_5090115 : CollatzResearch.WordTrace tailWord_5090115 prefixEnd_5090115 2613675581660457635353493 := by
  unfold tailWord_5090115
  simp only [CollatzResearch.WordTrace]
  refine ⟨185651745954390152276815799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123767830636260101517877199 185651745954390152276815799)
  ·
    refine ⟨278477618931585228415223699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185651745954390152276815799 278477618931585228415223699)
    ·
      refine ⟨417716428397377842622835549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278477618931585228415223699 417716428397377842622835549)
      ·
        refine ⟨156643660649016690983563331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417716428397377842622835549 156643660649016690983563331)
        ·
          refine ⟨234965490973525036475344997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156643660649016690983563331 234965490973525036475344997)
          ·
            refine ⟨44056029557535944339127187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234965490973525036475344997 44056029557535944339127187)
            ·
              refine ⟨66084044336303916508690781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44056029557535944339127187 66084044336303916508690781)
              ·
                refine ⟨24781516626113968690759043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66084044336303916508690781 24781516626113968690759043)
                ·
                  refine ⟨37172274939170953036138565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24781516626113968690759043 37172274939170953036138565)
                  ·
                    refine ⟨6969801551094553694275981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37172274939170953036138565 6969801551094553694275981)
                    ·
                      refine ⟨2613675581660457635353493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969801551094553694275981 2613675581660457635353493)
                      ·
                        rfl

theorem cell23_5090115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_5090115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090115 prefixEnd_5090115 := by exact prefixLift 5090115
  have htrace : WordTrace (prefixWord ++ tailWord_5090115) baseStart_5090115 baseEnd_5090115 := by
    simpa [prefixWord, tailWord_5090115, baseEnd_5090115] using wordTrace_append hprefix tailTrace_5090115
  have hstable : (prefixWord ++ tailWord_5090115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090115).length < 2 ^ (prefixWord ++ tailWord_5090115).sum := by decide
  have hdescent : baseEnd_5090115 < baseStart_5090115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090135 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 8]
def baseStart_5090135 : Nat := 118140960795 + 5090135 * 2 ^ 59
def prefixEnd_5090135 : Nat := 4983230072969 + 3 ^ 40 * 5090135 * 2
def baseEnd_5090135 : Nat := 290409539030394173011489

theorem tailTrace_5090135 : CollatzResearch.WordTrace tailWord_5090135 prefixEnd_5090135 290409539030394173011489 := by
  unfold tailWord_5090135
  simp only [CollatzResearch.WordTrace]
  refine ⟨185652475414317695692543859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123768316942878463795029239 185652475414317695692543859)
  ·
    refine ⟨278478713121476543538815789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185652475414317695692543859 278478713121476543538815789)
    ·
      refine ⟨104429517420553703827055921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278478713121476543538815789 104429517420553703827055921)
      ·
        refine ⟨78322138065415277870291941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104429517420553703827055921 78322138065415277870291941)
        ·
          refine ⟨14685400887265364600679739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78322138065415277870291941 14685400887265364600679739)
          ·
            refine ⟨22028101330898046901019609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14685400887265364600679739 22028101330898046901019609)
            ·
              refine ⟨16521075998173535175764707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22028101330898046901019609 16521075998173535175764707)
              ·
                refine ⟨24781613997260302763647061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16521075998173535175764707 24781613997260302763647061)
                ·
                  refine ⟨290409539030394173011489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24781613997260302763647061 290409539030394173011489)
                  ·
                    rfl

theorem cell23_5090135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 8].length) (baseStart_5090135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090135 prefixEnd_5090135 := by exact prefixLift 5090135
  have htrace : WordTrace (prefixWord ++ tailWord_5090135) baseStart_5090135 baseEnd_5090135 := by
    simpa [prefixWord, tailWord_5090135, baseEnd_5090135] using wordTrace_append hprefix tailTrace_5090135
  have hstable : (prefixWord ++ tailWord_5090135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090135).length < 2 ^ (prefixWord ++ tailWord_5090135).sum := by decide
  have hdescent : baseEnd_5090135 < baseStart_5090135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090145 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_5090145 : Nat := 118140960795 + 5090145 * 2 ^ 59
def prefixEnd_5090145 : Nat := 4983230072969 + 3 ^ 40 * 5090145 * 2
def baseEnd_5090145 : Nat := 2613690986080092517978355

theorem tailTrace_5090145 : CollatzResearch.WordTrace tailWord_5090145 prefixEnd_5090145 2613690986080092517978355 := by
  unfold tailWord_5090145
  simp only [CollatzResearch.WordTrace]
  refine ⟨185652840144281467400407889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123768560096187644933605259 185652840144281467400407889)
  ·
    refine ⟨139239630108211100550305917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185652840144281467400407889 139239630108211100550305917)
    ·
      refine ⟨52214861290579162706364719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139239630108211100550305917 52214861290579162706364719)
      ·
        refine ⟨78322291935868744059547079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52214861290579162706364719 78322291935868744059547079)
        ·
          refine ⟨117483437903803116089320619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78322291935868744059547079 117483437903803116089320619)
          ·
            refine ⟨176225156855704674133980929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117483437903803116089320619 176225156855704674133980929)
            ·
              refine ⟨132168867641778505600485697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176225156855704674133980929 132168867641778505600485697)
              ·
                refine ⟨99126650731333879200364273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132168867641778505600485697 99126650731333879200364273)
                ·
                  refine ⟨74344988048500409400273205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99126650731333879200364273 74344988048500409400273205)
                  ·
                    refine ⟨6969842629546913381275613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74344988048500409400273205 6969842629546913381275613)
                    ·
                      refine ⟨2613690986080092517978355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969842629546913381275613 2613690986080092517978355)
                      ·
                        rfl

theorem cell23_5090145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_5090145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090145 prefixEnd_5090145 := by exact prefixLift 5090145
  have htrace : WordTrace (prefixWord ++ tailWord_5090145) baseStart_5090145 baseEnd_5090145 := by
    simpa [prefixWord, tailWord_5090145, baseEnd_5090145] using wordTrace_append hprefix tailTrace_5090145
  have hstable : (prefixWord ++ tailWord_5090145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090145).length < 2 ^ (prefixWord ++ tailWord_5090145).sum := by decide
  have hdescent : baseEnd_5090145 < baseStart_5090145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090152 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 6]
def baseStart_5090152 : Nat := 118140960795 + 5090152 * 2 ^ 59
def prefixEnd_5090152 : Nat := 4983230072969 + 3 ^ 40 * 5090152 * 2
def baseEnd_5090152 : Nat := 290410508938297110065647

theorem tailTrace_5090152 : CollatzResearch.WordTrace tailWord_5090152 prefixEnd_5090152 290410508938297110065647 := by
  unfold tailWord_5090152
  simp only [CollatzResearch.WordTrace]
  refine ⟨92826547727628053797956355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123768730303504071730608473 92826547727628053797956355)
  ·
    refine ⟨139239821591442080696934533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92826547727628053797956355 139239821591442080696934533)
    ·
      refine ⟨26107466548395390130675225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139239821591442080696934533 26107466548395390130675225)
      ·
        refine ⟨19580599911296542598006419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26107466548395390130675225 19580599911296542598006419)
        ·
          refine ⟨29370899866944813897009629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19580599911296542598006419 29370899866944813897009629)
          ·
            refine ⟨11014087450104305211378611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29370899866944813897009629 11014087450104305211378611)
            ·
              refine ⟨16521131175156457817067917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11014087450104305211378611 16521131175156457817067917)
              ·
                refine ⟨6195424190683671681400469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16521131175156457817067917 6195424190683671681400469)
                ·
                  refine ⟨290410508938297110065647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6195424190683671681400469 290410508938297110065647)
                  ·
                    rfl

theorem cell23_5090152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_5090152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090152 prefixEnd_5090152 := by exact prefixLift 5090152
  have htrace : WordTrace (prefixWord ++ tailWord_5090152) baseStart_5090152 baseEnd_5090152 := by
    simpa [prefixWord, tailWord_5090152, baseEnd_5090152] using wordTrace_append hprefix tailTrace_5090152
  have hstable : (prefixWord ++ tailWord_5090152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090152).length < 2 ^ (prefixWord ++ tailWord_5090152).sum := by decide
  have hdescent : baseEnd_5090152 < baseStart_5090152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090166 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5090166 : Nat := 118140960795 + 5090166 * 2 ^ 59
def prefixEnd_5090166 : Nat := 4983230072969 + 3 ^ 40 * 5090166 * 2
def baseEnd_5090166 : Nat := 2613701769173836935815759

theorem tailTrace_5090166 : CollatzResearch.WordTrace tailWord_5090166 prefixEnd_5090166 2613701769173836935815759 := by
  unfold tailWord_5090166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603350379825336749182647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123769070718136925324614901 11603350379825336749182647)
  ·
    refine ⟨17405025569738005123773971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11603350379825336749182647 17405025569738005123773971)
    ·
      refine ⟨26107538354607007685660957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17405025569738005123773971 26107538354607007685660957)
      ·
        refine ⟨9790326882977627882122859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26107538354607007685660957 9790326882977627882122859)
        ·
          refine ⟨14685490324466441823184289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9790326882977627882122859 14685490324466441823184289)
          ·
            refine ⟨11014117743349831367388217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14685490324466441823184289 11014117743349831367388217)
            ·
              refine ⟨8260588307512373525541163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11014117743349831367388217 8260588307512373525541163)
              ·
                refine ⟨12390882461268560288311745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260588307512373525541163 12390882461268560288311745)
                ·
                  refine ⟨9293161845951420216233809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12390882461268560288311745 9293161845951420216233809)
                  ·
                    refine ⟨6969871384463565162175357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9293161845951420216233809 6969871384463565162175357)
                    ·
                      refine ⟨2613701769173836935815759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6969871384463565162175357 2613701769173836935815759)
                      ·
                        rfl

theorem cell23_5090166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5090166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090166 prefixEnd_5090166 := by exact prefixLift 5090166
  have htrace : WordTrace (prefixWord ++ tailWord_5090166) baseStart_5090166 baseEnd_5090166 := by
    simpa [prefixWord, tailWord_5090166, baseEnd_5090166] using wordTrace_append hprefix tailTrace_5090166
  have hstable : (prefixWord ++ tailWord_5090166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090166).length < 2 ^ (prefixWord ++ tailWord_5090166).sum := by decide
  have hdescent : baseEnd_5090166 < baseStart_5090166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090172 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_5090172 : Nat := 118140960795 + 5090172 * 2 ^ 59
def prefixEnd_5090172 : Nat := 4983230072969 + 3 ^ 40 * 5090172 * 2
def baseEnd_5090172 : Nat := 2613704850057763912340731

theorem tailTrace_5090172 : CollatzResearch.WordTrace tailWord_5090172 prefixEnd_5090172 2613704850057763912340731 := by
  unfold tailWord_5090172
  simp only [CollatzResearch.WordTrace]
  refine ⟨92826912457591825505820385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123769216610122434007760513 92826912457591825505820385)
  ·
    refine ⟨69620184343193869129365289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92826912457591825505820385 69620184343193869129365289)
    ·
      refine ⟨52215138257395401847023967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69620184343193869129365289 52215138257395401847023967)
      ·
        refine ⟨78322707386093102770535951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52215138257395401847023967 78322707386093102770535951)
        ·
          refine ⟨117484061079139654155803927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78322707386093102770535951 117484061079139654155803927)
          ·
            refine ⟨176226091618709481233705891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117484061079139654155803927 176226091618709481233705891)
            ·
              refine ⟨264339137428064221850558837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176226091618709481233705891 264339137428064221850558837)
              ·
                refine ⟨24781794133881020798489891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264339137428064221850558837 24781794133881020798489891)
                ·
                  refine ⟨37172691200821531197734837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24781794133881020798489891 37172691200821531197734837)
                  ·
                    refine ⟨3484939800077018549787641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37172691200821531197734837 3484939800077018549787641)
                    ·
                      refine ⟨2613704850057763912340731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484939800077018549787641 2613704850057763912340731)
                      ·
                        rfl

theorem cell23_5090172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_5090172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090172 prefixEnd_5090172 := by exact prefixLift 5090172
  have htrace : WordTrace (prefixWord ++ tailWord_5090172) baseStart_5090172 baseEnd_5090172 := by
    simpa [prefixWord, tailWord_5090172, baseEnd_5090172] using wordTrace_append hprefix tailTrace_5090172
  have hstable : (prefixWord ++ tailWord_5090172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090172).length < 2 ^ (prefixWord ++ tailWord_5090172).sum := by decide
  have hdescent : baseEnd_5090172 < baseStart_5090172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090212 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_5090212 : Nat := 118140960795 + 5090212 * 2 ^ 59
def prefixEnd_5090212 : Nat := 4983230072969 + 3 ^ 40 * 5090212 * 2
def baseEnd_5090212 : Nat := 871241796427981251946849

theorem tailTrace_5090212 : CollatzResearch.WordTrace tailWord_5090212 prefixEnd_5090212 871241796427981251946849 := by
  unfold tailWord_5090212
  simp only [CollatzResearch.WordTrace]
  refine ⟨92827641917519368921548445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123770189223359158562064593 92827641917519368921548445)
  ·
    refine ⟨34810365719069763345580667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92827641917519368921548445 34810365719069763345580667)
    ·
      refine ⟨52215548578604645018371001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34810365719069763345580667 52215548578604645018371001)
      ·
        refine ⟨39161661433953483763778251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52215548578604645018371001 39161661433953483763778251)
        ·
          refine ⟨58742492150930225645667377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39161661433953483763778251 58742492150930225645667377)
          ·
            refine ⟨44056869113197669234250533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58742492150930225645667377 44056869113197669234250533)
            ·
              refine ⟨8260662958724562981421975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44056869113197669234250533 8260662958724562981421975)
              ·
                refine ⟨12390994438086844472132963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260662958724562981421975 12390994438086844472132963)
                ·
                  refine ⟨18586491657130266708199445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12390994438086844472132963 18586491657130266708199445)
                  ·
                    refine ⟨871241796427981251946849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18586491657130266708199445 871241796427981251946849)
                    ·
                      rfl

theorem cell23_5090212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_5090212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090212 prefixEnd_5090212 := by exact prefixLift 5090212
  have htrace : WordTrace (prefixWord ++ tailWord_5090212) baseStart_5090212 baseEnd_5090212 := by
    simpa [prefixWord, tailWord_5090212, baseEnd_5090212] using wordTrace_append hprefix tailTrace_5090212
  have hstable : (prefixWord ++ tailWord_5090212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090212).length < 2 ^ (prefixWord ++ tailWord_5090212).sum := by decide
  have hdescent : baseEnd_5090212 < baseStart_5090212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 3, 2, 2]
def baseStart_5090219 : Nat := 118140960795 + 5090219 * 2 ^ 59
def prefixEnd_5090219 : Nat := 4983230072969 + 3 ^ 40 * 5090219 * 2
def baseEnd_5090219 : Nat := 2613728983648525228453015

theorem tailTrace_5090219 : CollatzResearch.WordTrace tailWord_5090219 prefixEnd_5090219 2613728983648525228453015 := by
  unfold tailWord_5090219
  simp only [CollatzResearch.WordTrace]
  refine ⟨185655539146013378038601711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123770359430675585359067807 185655539146013378038601711)
  ·
    refine ⟨278483308719020067057902567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185655539146013378038601711 278483308719020067057902567)
    ·
      refine ⟨417724963078530100586853851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278483308719020067057902567 417724963078530100586853851)
      ·
        refine ⟨626587444617795150880280777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417724963078530100586853851 626587444617795150880280777)
        ·
          refine ⟨469940583463346363160210583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626587444617795150880280777 469940583463346363160210583)
          ·
            refine ⟨704910875195019544740315875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469940583463346363160210583 704910875195019544740315875)
            ·
              refine ⟨1057366312792529317110473813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704910875195019544740315875 1057366312792529317110473813)
              ·
                refine ⟨12391011478037452934888365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1057366312792529317110473813 12391011478037452934888365)
                ·
                  refine ⟨4646629304264044850583137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12391011478037452934888365 4646629304264044850583137)
                  ·
                    refine ⟨3484971978198033637937353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4646629304264044850583137 3484971978198033637937353)
                    ·
                      refine ⟨2613728983648525228453015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484971978198033637937353 2613728983648525228453015)
                      ·
                        rfl

theorem cell23_5090219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2, 2].length) (baseStart_5090219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090219 prefixEnd_5090219 := by exact prefixLift 5090219
  have htrace : WordTrace (prefixWord ++ tailWord_5090219) baseStart_5090219 baseEnd_5090219 := by
    simpa [prefixWord, tailWord_5090219, baseEnd_5090219] using wordTrace_append hprefix tailTrace_5090219
  have hstable : (prefixWord ++ tailWord_5090219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090219).length < 2 ^ (prefixWord ++ tailWord_5090219).sum := by decide
  have hdescent : baseEnd_5090219 < baseStart_5090219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090232 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_5090232 : Nat := 118140960795 + 5090232 * 2 ^ 59
def prefixEnd_5090232 : Nat := 4983230072969 + 3 ^ 40 * 5090232 * 2
def baseEnd_5090232 : Nat := 2613735658897033677590455

theorem tailTrace_5090232 : CollatzResearch.WordTrace tailWord_5090232 prefixEnd_5090232 2613735658897033677590455 := by
  unfold tailWord_5090232
  simp only [CollatzResearch.WordTrace]
  refine ⟨92828006647483140629412475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123770675529977520839216633 92828006647483140629412475)
  ·
    refine ⟨139242009971224710944118713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92828006647483140629412475 139242009971224710944118713)
    ·
      refine ⟨104431507478418533208089035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139242009971224710944118713 104431507478418533208089035)
      ·
        refine ⟨156647261217627799812133553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104431507478418533208089035 156647261217627799812133553)
        ·
          refine ⟨117485445913220849859100165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156647261217627799812133553 117485445913220849859100165)
          ·
            refine ⟨22028521108728909348581281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117485445913220849859100165 22028521108728909348581281)
            ·
              refine ⟨16521390831546682011435961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22028521108728909348581281 16521390831546682011435961)
              ·
                refine ⟨12391043123660011508576971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16521390831546682011435961 12391043123660011508576971)
                ·
                  refine ⟨18586564685490017262865457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12391043123660011508576971 18586564685490017262865457)
                  ·
                    refine ⟨13939923514117512947149093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18586564685490017262865457 13939923514117512947149093)
                    ·
                      refine ⟨2613735658897033677590455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13939923514117512947149093 2613735658897033677590455)
                      ·
                        rfl

theorem cell23_5090232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_5090232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090232 prefixEnd_5090232 := by exact prefixLift 5090232
  have htrace : WordTrace (prefixWord ++ tailWord_5090232) baseStart_5090232 baseEnd_5090232 := by
    simpa [prefixWord, tailWord_5090232, baseEnd_5090232] using wordTrace_append hprefix tailTrace_5090232
  have hstable : (prefixWord ++ tailWord_5090232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090232).length < 2 ^ (prefixWord ++ tailWord_5090232).sum := by decide
  have hdescent : baseEnd_5090232 < baseStart_5090232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090282 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5090282 : Nat := 118140960795 + 5090282 * 2 ^ 59
def prefixEnd_5090282 : Nat := 4983230072969 + 3 ^ 40 * 5090282 * 2
def baseEnd_5090282 : Nat := 2613761332929758481965225

theorem tailTrace_5090282 : CollatzResearch.WordTrace tailWord_5090282 prefixEnd_5090282 2613761332929758481965225 := by
  unfold tailWord_5090282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46414459236196284949536275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123771891296523426532096733 46414459236196284949536275)
  ·
    refine ⟨69621688854294427424304413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46414459236196284949536275 69621688854294427424304413)
    ·
      refine ⟨26108133320360410284114155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69621688854294427424304413 26108133320360410284114155)
      ·
        refine ⟨39162199980540615426171233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26108133320360410284114155 39162199980540615426171233)
        ·
          refine ⟨29371649985405461569628425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39162199980540615426171233 29371649985405461569628425)
          ·
            refine ⟨22028737489054096177221319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29371649985405461569628425 22028737489054096177221319)
            ·
              refine ⟨33043106233581144265831979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22028737489054096177221319 33043106233581144265831979)
              ·
                refine ⟨49564659350371716398747969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33043106233581144265831979 49564659350371716398747969)
                ·
                  refine ⟨37173494512778787299060977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49564659350371716398747969 37173494512778787299060977)
                  ·
                    refine ⟨27880120884584090474295733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37173494512778787299060977 27880120884584090474295733)
                    ·
                      refine ⟨2613761332929758481965225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27880120884584090474295733 2613761332929758481965225)
                      ·
                        rfl

theorem cell23_5090282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5090282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090282 prefixEnd_5090282 := by exact prefixLift 5090282
  have htrace : WordTrace (prefixWord ++ tailWord_5090282) baseStart_5090282 baseEnd_5090282 := by
    simpa [prefixWord, tailWord_5090282, baseEnd_5090282] using wordTrace_append hprefix tailTrace_5090282
  have hstable : (prefixWord ++ tailWord_5090282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090282).length < 2 ^ (prefixWord ++ tailWord_5090282).sum := by decide
  have hdescent : baseEnd_5090282 < baseStart_5090282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090343 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5090343 : Nat := 118140960795 + 5090343 * 2 ^ 59
def prefixEnd_5090343 : Nat := 4983230072969 + 3 ^ 40 * 5090343 * 2
def baseEnd_5090343 : Nat := 2613792655249682743302445

theorem tailTrace_5090343 : CollatzResearch.WordTrace tailWord_5090343 prefixEnd_5090343 2613792655249682743302445 := by
  unfold tailWord_5090343
  simp only [CollatzResearch.WordTrace]
  refine ⟨185660061797564147216115683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123773374531709431477410455 185660061797564147216115683)
  ·
    refine ⟨278490092696346220824173525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185660061797564147216115683 278490092696346220824173525)
    ·
      refine ⟨6527111547570614550566567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 278490092696346220824173525 6527111547570614550566567)
      ·
        refine ⟨9790667321355921825849851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527111547570614550566567 9790667321355921825849851)
        ·
          refine ⟨14686000982033882738774777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9790667321355921825849851 14686000982033882738774777)
          ·
            refine ⟨11014500736525412054081083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14686000982033882738774777 11014500736525412054081083)
            ·
              refine ⟨16521751104788118081121625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11014500736525412054081083 16521751104788118081121625)
              ·
                refine ⟨12391313328591088560841219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16521751104788118081121625 12391313328591088560841219)
                ·
                  refine ⟨18586969992886632841261829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12391313328591088560841219 18586969992886632841261829)
                  ·
                    refine ⟨3485056873666243657736593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18586969992886632841261829 3485056873666243657736593)
                    ·
                      refine ⟨2613792655249682743302445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485056873666243657736593 2613792655249682743302445)
                      ·
                        rfl

theorem cell23_5090343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5090343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090343 prefixEnd_5090343 := by exact prefixLift 5090343
  have htrace : WordTrace (prefixWord ++ tailWord_5090343) baseStart_5090343 baseEnd_5090343 := by
    simpa [prefixWord, tailWord_5090343, baseEnd_5090343] using wordTrace_append hprefix tailTrace_5090343
  have hstable : (prefixWord ++ tailWord_5090343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090343).length < 2 ^ (prefixWord ++ tailWord_5090343).sum := by decide
  have hdescent : baseEnd_5090343 < baseStart_5090343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090399 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 6, 2]
def baseStart_5090399 : Nat := 118140960795 + 5090399 * 2 ^ 59
def prefixEnd_5090399 : Nat := 4983230072969 + 3 ^ 40 * 5090399 * 2
def baseEnd_5090399 : Nat := 2613821410166334524202187

theorem tailTrace_5090399 : CollatzResearch.WordTrace tailWord_5090399 prefixEnd_5090399 2613821410166334524202187 := by
  unfold tailWord_5090399
  simp only [CollatzResearch.WordTrace]
  refine ⟨185662104285361268780154251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123774736190240845853436167 185662104285361268780154251)
  ·
    refine ⟨278493156428041903170231377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185662104285361268780154251 278493156428041903170231377)
    ·
      refine ⟨208869867321031427377673533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278493156428041903170231377 208869867321031427377673533)
      ·
        refine ⟨78326200245386785266627575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208869867321031427377673533 78326200245386785266627575)
        ·
          refine ⟨117489300368080177899941363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78326200245386785266627575 117489300368080177899941363)
          ·
            refine ⟨176233950552120266849912045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117489300368080177899941363 176233950552120266849912045)
            ·
              refine ⟨66087731457045100068717017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176233950552120266849912045 66087731457045100068717017)
              ·
                refine ⟨49565798592783825051537763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66087731457045100068717017 49565798592783825051537763)
                ·
                  refine ⟨74348697889175737577306645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49565798592783825051537763 74348697889175737577306645)
                  ·
                    refine ⟨3485095213555112698936249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74348697889175737577306645 3485095213555112698936249)
                    ·
                      refine ⟨2613821410166334524202187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485095213555112698936249 2613821410166334524202187)
                      ·
                        rfl

theorem cell23_5090399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_5090399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090399 prefixEnd_5090399 := by exact prefixLift 5090399
  have htrace : WordTrace (prefixWord ++ tailWord_5090399) baseStart_5090399 baseEnd_5090399 := by
    simpa [prefixWord, tailWord_5090399, baseEnd_5090399] using wordTrace_append hprefix tailTrace_5090399
  have hstable : (prefixWord ++ tailWord_5090399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090399).length < 2 ^ (prefixWord ++ tailWord_5090399).sum := by decide
  have hdescent : baseEnd_5090399 < baseStart_5090399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090412 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_5090412 : Nat := 118140960795 + 5090412 * 2 ^ 59
def prefixEnd_5090412 : Nat := 4983230072969 + 3 ^ 40 * 5090412 * 2
def baseEnd_5090412 : Nat := 2613828085414842973339627

theorem tailTrace_5090412 : CollatzResearch.WordTrace tailWord_5090412 prefixEnd_5090412 2613828085414842973339627 := by
  unfold tailWord_5090412
  simp only [CollatzResearch.WordTrace]
  refine ⟨92831289217157086000188745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123775052289542781333584993 92831289217157086000188745)
  ·
    refine ⟨69623466912867814500141559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92831289217157086000188745 69623466912867814500141559)
    ·
      refine ⟨104435200369301721750212339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69623466912867814500141559 104435200369301721750212339)
      ·
        refine ⟨156652800553952582625318509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104435200369301721750212339 156652800553952582625318509)
        ·
          refine ⟨58744800207732218484494441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156652800553952582625318509 58744800207732218484494441)
          ·
            refine ⟨44058600155799163863370831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58744800207732218484494441 44058600155799163863370831)
            ·
              refine ⟨66087900233698745795056247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44058600155799163863370831 66087900233698745795056247)
              ·
                refine ⟨99131850350548118692584371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66087900233698745795056247 99131850350548118692584371)
                ·
                  refine ⟨148697775525822178038876557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99131850350548118692584371 148697775525822178038876557)
                  ·
                    refine ⟨55761665822183316764578709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148697775525822178038876557 55761665822183316764578709)
                    ·
                      refine ⟨2613828085414842973339627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55761665822183316764578709 2613828085414842973339627)
                      ·
                        rfl

theorem cell23_5090412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_5090412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090412 prefixEnd_5090412 := by exact prefixLift 5090412
  have htrace : WordTrace (prefixWord ++ tailWord_5090412) baseStart_5090412 baseEnd_5090412 := by
    simpa [prefixWord, tailWord_5090412, baseEnd_5090412] using wordTrace_append hprefix tailTrace_5090412
  have hstable : (prefixWord ++ tailWord_5090412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090412).length < 2 ^ (prefixWord ++ tailWord_5090412).sum := by decide
  have hdescent : baseEnd_5090412 < baseStart_5090412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090460 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5090460 : Nat := 118140960795 + 5090460 * 2 ^ 59
def prefixEnd_5090460 : Nat := 4983230072969 + 3 ^ 40 * 5090460 * 2
def baseEnd_5090460 : Nat := 871284244162086261846469

theorem tailTrace_5090460 : CollatzResearch.WordTrace tailWord_5090460 prefixEnd_5090460 871284244162086261846469 := by
  unfold tailWord_5090460
  simp only [CollatzResearch.WordTrace]
  refine ⟨92832164569070138099062417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123776219425426850798749889 92832164569070138099062417)
  ·
    refine ⟨69624123426802603574296813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92832164569070138099062417 69624123426802603574296813)
    ·
      refine ⟨26109046285050976340361305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69624123426802603574296813 26109046285050976340361305)
      ·
        refine ⟨19581784713788232255270979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26109046285050976340361305 19581784713788232255270979)
        ·
          refine ⟨29372677070682348382906469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19581784713788232255270979 29372677070682348382906469)
          ·
            refine ⟨5507376950752940321794963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29372677070682348382906469 5507376950752940321794963)
            ·
              refine ⟨8261065426129410482692445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507376950752940321794963 8261065426129410482692445)
              ·
                refine ⟨3097899534798528931009667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8261065426129410482692445 3097899534798528931009667)
                ·
                  refine ⟨4646849302197793396514501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097899534798528931009667 4646849302197793396514501)
                  ·
                    refine ⟨871284244162086261846469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646849302197793396514501 871284244162086261846469)
                    ·
                      rfl

theorem cell23_5090460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5090460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090460 prefixEnd_5090460 := by exact prefixLift 5090460
  have htrace : WordTrace (prefixWord ++ tailWord_5090460) baseStart_5090460 baseEnd_5090460 := by
    simpa [prefixWord, tailWord_5090460, baseEnd_5090460] using wordTrace_append hprefix tailTrace_5090460
  have hstable : (prefixWord ++ tailWord_5090460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090460).length < 2 ^ (prefixWord ++ tailWord_5090460).sum := by decide
  have hdescent : baseEnd_5090460 < baseStart_5090460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090477 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_5090477 : Nat := 118140960795 + 5090477 * 2 ^ 59
def prefixEnd_5090477 : Nat := 4983230072969 + 3 ^ 40 * 5090477 * 2
def baseEnd_5090477 : Nat := 871287153885795073008943

theorem tailTrace_5090477 : CollatzResearch.WordTrace tailWord_5090477 prefixEnd_5090477 871287153885795073008943 := by
  unfold tailWord_5090477
  simp only [CollatzResearch.WordTrace]
  refine ⟨185664949179078688101493685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123776632786052458734329123 185664949179078688101493685)
  ·
    refine ⟨17406088985538627009515033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185664949179078688101493685 17406088985538627009515033)
    ·
      refine ⟨13054566739153970257136275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17406088985538627009515033 13054566739153970257136275)
      ·
        refine ⟨19581850108730955385704413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13054566739153970257136275 19581850108730955385704413)
        ·
          refine ⟨7343193790774108269639155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19581850108730955385704413 7343193790774108269639155)
          ·
            refine ⟨11014790686161162404458733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343193790774108269639155 11014790686161162404458733)
            ·
              refine ⟨4130546507310435901672025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11014790686161162404458733 4130546507310435901672025)
              ·
                refine ⟨3097909880482826926254019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130546507310435901672025 3097909880482826926254019)
                ·
                  refine ⟨4646864820724240389381029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097909880482826926254019 4646864820724240389381029)
                  ·
                    refine ⟨871287153885795073008943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646864820724240389381029 871287153885795073008943)
                    ·
                      rfl

theorem cell23_5090477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_5090477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090477 prefixEnd_5090477 := by exact prefixLift 5090477
  have htrace : WordTrace (prefixWord ++ tailWord_5090477) baseStart_5090477 baseEnd_5090477 := by
    simpa [prefixWord, tailWord_5090477, baseEnd_5090477] using wordTrace_append hprefix tailTrace_5090477
  have hstable : (prefixWord ++ tailWord_5090477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090477).length < 2 ^ (prefixWord ++ tailWord_5090477).sum := by decide
  have hdescent : baseEnd_5090477 < baseStart_5090477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090483 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 1, 1, 3]
def baseStart_5090483 : Nat := 118140960795 + 5090483 * 2 ^ 59
def prefixEnd_5090483 : Nat := 4983230072969 + 3 ^ 40 * 5090483 * 2
def baseEnd_5090483 : Nat := 2613864542541312195551801

theorem tailTrace_5090483 : CollatzResearch.WordTrace tailWord_5090483 prefixEnd_5090483 2613864542541312195551801 := by
  unfold tailWord_5090483
  simp only [CollatzResearch.WordTrace]
  refine ⟨185665168017056951126212103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123776778678037967417474735 185665168017056951126212103)
  ·
    refine ⟨278497752025585426689318155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185665168017056951126212103 278497752025585426689318155)
    ·
      refine ⟨417746628038378140033977233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278497752025585426689318155 417746628038378140033977233)
      ·
        refine ⟨313309971028783605025482925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417746628038378140033977233 313309971028783605025482925)
        ·
          refine ⟨117491239135793851884556097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313309971028783605025482925 117491239135793851884556097)
          ·
            refine ⟨88118429351845388913417073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117491239135793851884556097 88118429351845388913417073)
            ·
              refine ⟨66088822013884041685062805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88118429351845388913417073 66088822013884041685062805)
              ·
                refine ⟨3097913531900814453987319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66088822013884041685062805 3097913531900814453987319)
                ·
                  refine ⟨4646870297851221680980979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097913531900814453987319 4646870297851221680980979)
                  ·
                    refine ⟨6970305446776832521471469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4646870297851221680980979 6970305446776832521471469)
                    ·
                      refine ⟨2613864542541312195551801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6970305446776832521471469 2613864542541312195551801)
                      ·
                        rfl

theorem cell23_5090483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 1, 3].length) (baseStart_5090483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090483 prefixEnd_5090483 := by exact prefixLift 5090483
  have htrace : WordTrace (prefixWord ++ tailWord_5090483) baseStart_5090483 baseEnd_5090483 := by
    simpa [prefixWord, tailWord_5090483, baseEnd_5090483] using wordTrace_append hprefix tailTrace_5090483
  have hstable : (prefixWord ++ tailWord_5090483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090483).length < 2 ^ (prefixWord ++ tailWord_5090483).sum := by decide
  have hdescent : baseEnd_5090483 < baseStart_5090483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090499 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 6, 4]
def baseStart_5090499 : Nat := 118140960795 + 5090499 * 2 ^ 59
def prefixEnd_5090499 : Nat := 4983230072969 + 3 ^ 40 * 5090499 * 2
def baseEnd_5090499 : Nat := 871290919410594710983909

theorem tailTrace_5090499 : CollatzResearch.WordTrace tailWord_5090499 prefixEnd_5090499 871290919410594710983909 := by
  unfold tailWord_5090499
  simp only [CollatzResearch.WordTrace]
  refine ⟨185665751584998985858794551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123777167723332657239196367 185665751584998985858794551)
  ·
    refine ⟨278498627377498478788191827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185665751584998985858794551 278498627377498478788191827)
    ·
      refine ⟨417747941066247718182287741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278498627377498478788191827 417747941066247718182287741)
      ·
        refine ⟨156655477899842894318357903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417747941066247718182287741 156655477899842894318357903)
        ·
          refine ⟨234983216849764341477536855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156655477899842894318357903 234983216849764341477536855)
          ·
            refine ⟨352474825274646512216305283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234983216849764341477536855 352474825274646512216305283)
            ·
              refine ⟨528712237911969768324457925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352474825274646512216305283 528712237911969768324457925)
              ·
                refine ⟨99133544608494331560835861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528712237911969768324457925 99133544608494331560835861)
                ·
                  refine ⟨4646884903523171791914181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99133544608494331560835861 4646884903523171791914181)
                  ·
                    refine ⟨871290919410594710983909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646884903523171791914181 871290919410594710983909)
                    ·
                      rfl

theorem cell23_5090499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 4].length) (baseStart_5090499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090499 prefixEnd_5090499 := by exact prefixLift 5090499
  have htrace : WordTrace (prefixWord ++ tailWord_5090499) baseStart_5090499 baseEnd_5090499 := by
    simpa [prefixWord, tailWord_5090499, baseEnd_5090499] using wordTrace_append hprefix tailTrace_5090499
  have hstable : (prefixWord ++ tailWord_5090499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090499).length < 2 ^ (prefixWord ++ tailWord_5090499).sum := by decide
  have hdescent : baseEnd_5090499 < baseStart_5090499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090506 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5090506 : Nat := 118140960795 + 5090506 * 2 ^ 59
def prefixEnd_5090506 : Nat := 4983230072969 + 3 ^ 40 * 5090506 * 2
def baseEnd_5090506 : Nat := 2613876352596365605564195

theorem tailTrace_5090506 : CollatzResearch.WordTrace tailWord_5090506 prefixEnd_5090506 2613876352596365605564195 := by
  unfold tailWord_5090506
  simp only [CollatzResearch.WordTrace]
  refine ⟨46416501723993406513574843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123777337930649084036199581 46416501723993406513574843)
  ·
    refine ⟨69624752585990109770362265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46416501723993406513574843 69624752585990109770362265)
    ·
      refine ⟨52218564439492582327771699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69624752585990109770362265 52218564439492582327771699)
      ·
        refine ⟨78327846659238873491657549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52218564439492582327771699 78327846659238873491657549)
        ·
          refine ⟨29372942497214577559371581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78327846659238873491657549 29372942497214577559371581)
          ·
            refine ⟨11014853436455466584764343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29372942497214577559371581 11014853436455466584764343)
            ·
              refine ⟨16522280154683199877146515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11014853436455466584764343 16522280154683199877146515)
              ·
                refine ⟨24783420232024799815719773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16522280154683199877146515 24783420232024799815719773)
                ·
                  refine ⟨9293782587009299930894915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24783420232024799815719773 9293782587009299930894915)
                  ·
                    refine ⟨13940673880513949896342373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9293782587009299930894915 13940673880513949896342373)
                    ·
                      refine ⟨2613876352596365605564195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13940673880513949896342373 2613876352596365605564195)
                      ·
                        rfl

theorem cell23_5090506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5090506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090506 prefixEnd_5090506 := by exact prefixLift 5090506
  have htrace : WordTrace (prefixWord ++ tailWord_5090506) baseStart_5090506 baseEnd_5090506 := by
    simpa [prefixWord, tailWord_5090506, baseEnd_5090506] using wordTrace_append hprefix tailTrace_5090506
  have hstable : (prefixWord ++ tailWord_5090506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090506).length < 2 ^ (prefixWord ++ tailWord_5090506).sum := by decide
  have hdescent : baseEnd_5090506 < baseStart_5090506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090510 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_5090510 : Nat := 118140960795 + 5090510 * 2 ^ 59
def prefixEnd_5090510 : Nat := 4983230072969 + 3 ^ 40 * 5090510 * 2
def baseEnd_5090510 : Nat := 2613878406518983589914177

theorem tailTrace_5090510 : CollatzResearch.WordTrace tailWord_5090510 prefixEnd_5090510 2613878406518983589914177 := by
  unfold tailWord_5090510
  simp only [CollatzResearch.WordTrace]
  refine ⟨23208269098494891842180623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123777435191972756491629989 23208269098494891842180623)
  ·
    refine ⟨34812403647742337763270935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23208269098494891842180623 34812403647742337763270935)
    ·
      refine ⟨52218605471613506644906403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34812403647742337763270935 52218605471613506644906403)
      ·
        refine ⟨78327908207420259967359605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52218605471613506644906403 78327908207420259967359605)
        ·
          refine ⟨7343241394445649371939963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78327908207420259967359605 7343241394445649371939963)
          ·
            refine ⟨11014862091668474057909945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343241394445649371939963 11014862091668474057909945)
            ·
              refine ⟨8261146568751355543432459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11014862091668474057909945 8261146568751355543432459)
              ·
                refine ⟨12391719853127033315148689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8261146568751355543432459 12391719853127033315148689)
                ·
                  refine ⟨9293789889845274986361517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12391719853127033315148689 9293789889845274986361517)
                  ·
                    refine ⟨3485171208691978119885569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9293789889845274986361517 3485171208691978119885569)
                    ·
                      refine ⟨2613878406518983589914177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485171208691978119885569 2613878406518983589914177)
                      ·
                        rfl

theorem cell23_5090510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_5090510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090510 prefixEnd_5090510 := by exact prefixLift 5090510
  have htrace : WordTrace (prefixWord ++ tailWord_5090510) baseStart_5090510 baseEnd_5090510 := by
    simpa [prefixWord, tailWord_5090510, baseEnd_5090510] using wordTrace_append hprefix tailTrace_5090510
  have hstable : (prefixWord ++ tailWord_5090510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090510).length < 2 ^ (prefixWord ++ tailWord_5090510).sum := by decide
  have hdescent : baseEnd_5090510 < baseStart_5090510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090519 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_5090519 : Nat := 118140960795 + 5090519 * 2 ^ 59
def prefixEnd_5090519 : Nat := 4983230072969 + 3 ^ 40 * 5090519 * 2
def baseEnd_5090519 : Nat := 2613883027844874054701635

theorem tailTrace_5090519 : CollatzResearch.WordTrace tailWord_5090519 prefixEnd_5090519 2613883027844874054701635 := by
  unfold tailWord_5090519
  simp only [CollatzResearch.WordTrace]
  refine ⟨185666481044926529274522611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123777654029951019516348407 185666481044926529274522611)
  ·
    refine ⟨278499721567389793911783917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185666481044926529274522611 278499721567389793911783917)
    ·
      refine ⟨104437395587771172716918969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278499721567389793911783917 104437395587771172716918969)
      ·
        refine ⟨78328046690828379537689227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104437395587771172716918969 78328046690828379537689227)
        ·
          refine ⟨117492070036242569306533841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78328046690828379537689227 117492070036242569306533841)
          ·
            refine ⟨88119052527181926979900381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117492070036242569306533841 88119052527181926979900381)
            ·
              refine ⟨33044644697693222617462643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88119052527181926979900381 33044644697693222617462643)
              ·
                refine ⟨49566967046539833926193965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33044644697693222617462643 49566967046539833926193965)
                ·
                  refine ⟨18587612642452437722322737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49566967046539833926193965 18587612642452437722322737)
                  ·
                    refine ⟨13940709481839328291742053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18587612642452437722322737 13940709481839328291742053)
                    ·
                      refine ⟨2613883027844874054701635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13940709481839328291742053 2613883027844874054701635)
                      ·
                        rfl

theorem cell23_5090519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_5090519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090519 prefixEnd_5090519 := by exact prefixLift 5090519
  have htrace : WordTrace (prefixWord ++ tailWord_5090519) baseStart_5090519 baseEnd_5090519 := by
    simpa [prefixWord, tailWord_5090519, baseEnd_5090519] using wordTrace_append hprefix tailTrace_5090519
  have hstable : (prefixWord ++ tailWord_5090519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090519).length < 2 ^ (prefixWord ++ tailWord_5090519).sum := by decide
  have hdescent : baseEnd_5090519 < baseStart_5090519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090569 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_5090569 : Nat := 118140960795 + 5090569 * 2 ^ 59
def prefixEnd_5090569 : Nat := 4983230072969 + 3 ^ 40 * 5090569 * 2
def baseEnd_5090569 : Nat := 2613908701877598859076405

theorem tailTrace_5090569 : CollatzResearch.WordTrace tailWord_5090569 prefixEnd_5090569 2613908701877598859076405 := by
  unfold tailWord_5090569
  simp only [CollatzResearch.WordTrace]
  refine ⟨185668304694745387813842761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123778869796496925209228507 185668304694745387813842761)
  ·
    refine ⟨139251228521059040860382071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185668304694745387813842761 139251228521059040860382071)
    ·
      refine ⟨208876842781588561290573107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139251228521059040860382071 208876842781588561290573107)
      ·
        refine ⟨313315264172382841935859661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208876842781588561290573107 313315264172382841935859661)
        ·
          refine ⟨117493224064643565725947373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313315264172382841935859661 117493224064643565725947373)
          ·
            refine ⟨44059959024241337147230265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117493224064643565725947373 44059959024241337147230265)
            ·
              refine ⟨33044969268181002860422699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44059959024241337147230265 33044969268181002860422699)
              ·
                refine ⟨49567453902271504290634049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33044969268181002860422699 49567453902271504290634049)
                ·
                  refine ⟨37175590426703628217975537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49567453902271504290634049 37175590426703628217975537)
                  ·
                    refine ⟨27881692820027721163481653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37175590426703628217975537 27881692820027721163481653)
                    ·
                      refine ⟨2613908701877598859076405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27881692820027721163481653 2613908701877598859076405)
                      ·
                        rfl

theorem cell23_5090569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_5090569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090569 prefixEnd_5090569 := by exact prefixLift 5090569
  have htrace : WordTrace (prefixWord ++ tailWord_5090569) baseStart_5090569 baseEnd_5090569 := by
    simpa [prefixWord, tailWord_5090569, baseEnd_5090569] using wordTrace_append hprefix tailTrace_5090569
  have hstable : (prefixWord ++ tailWord_5090569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090569).length < 2 ^ (prefixWord ++ tailWord_5090569).sum := by decide
  have hdescent : baseEnd_5090569 < baseStart_5090569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090617 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5090617 : Nat := 118140960795 + 5090617 * 2 ^ 59
def prefixEnd_5090617 : Nat := 4983230072969 + 3 ^ 40 * 5090617 * 2
def baseEnd_5090617 : Nat := 2613933348949014671276185

theorem tailTrace_5090617 : CollatzResearch.WordTrace tailWord_5090617 prefixEnd_5090617 2613933348949014671276185 := by
  unfold tailWord_5090617
  simp only [CollatzResearch.WordTrace]
  refine ⟨185670055398571492011590105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123780036932380994674393403 185670055398571492011590105)
  ·
    refine ⟨139252541548928619008692579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185670055398571492011590105 139252541548928619008692579)
    ·
      refine ⟨208878812323392928513038869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139252541548928619008692579 208878812323392928513038869)
      ·
        refine ⟨9791194327659043524048697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208878812323392928513038869 9791194327659043524048697)
        ·
          refine ⟨7343395745744282643036523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791194327659043524048697 7343395745744282643036523)
          ·
            refine ⟨11015093618616423964554785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343395745744282643036523 11015093618616423964554785)
            ·
              refine ⟨8261320213962317973416089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11015093618616423964554785 8261320213962317973416089)
              ·
                refine ⟨6195990160471738480062067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8261320213962317973416089 6195990160471738480062067)
                ·
                  refine ⟨9293985240707607720093101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6195990160471738480062067 9293985240707607720093101)
                  ·
                    refine ⟨3485244465265352895034913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9293985240707607720093101 3485244465265352895034913)
                    ·
                      refine ⟨2613933348949014671276185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485244465265352895034913 2613933348949014671276185)
                      ·
                        rfl

theorem cell23_5090617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5090617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090617 prefixEnd_5090617 := by exact prefixLift 5090617
  have htrace : WordTrace (prefixWord ++ tailWord_5090617) baseStart_5090617 baseEnd_5090617 := by
    simpa [prefixWord, tailWord_5090617, baseEnd_5090617] using wordTrace_append hprefix tailTrace_5090617
  have hstable : (prefixWord ++ tailWord_5090617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090617).length < 2 ^ (prefixWord ++ tailWord_5090617).sum := by decide
  have hdescent : baseEnd_5090617 < baseStart_5090617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090736 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_5090736 : Nat := 118140960795 + 5090736 * 2 ^ 59
def prefixEnd_5090736 : Nat := 4983230072969 + 3 ^ 40 * 5090736 * 2
def baseEnd_5090736 : Nat := 2613994453146899705688137

theorem tailTrace_5090736 : CollatzResearch.WordTrace tailWord_5090736 prefixEnd_5090736 2613994453146899705688137 := by
  unfold tailWord_5090736
  simp only [CollatzResearch.WordTrace]
  refine ⟨92837197842570187667586031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123782930456760250223448041 92837197842570187667586031)
  ·
    refine ⟨139255796763855281501379047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92837197842570187667586031 139255796763855281501379047)
    ·
      refine ⟨208883695145782922252068571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139255796763855281501379047 208883695145782922252068571)
      ·
        refine ⟨313325542718674383378102857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208883695145782922252068571 313325542718674383378102857)
        ·
          refine ⟨234994157039005787533577143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313325542718674383378102857 234994157039005787533577143)
          ·
            refine ⟨352491235558508681300365715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234994157039005787533577143 352491235558508681300365715)
            ·
              refine ⟨528736853337763021950548573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352491235558508681300365715 528736853337763021950548573)
              ·
                refine ⟨198276320001661133231455715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528736853337763021950548573 198276320001661133231455715)
                ·
                  refine ⟨297414480002491699847183573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198276320001661133231455715 297414480002491699847183573)
                  ·
                    refine ⟨6970651875058399215168365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 297414480002491699847183573 6970651875058399215168365)
                    ·
                      refine ⟨2613994453146899705688137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6970651875058399215168365 2613994453146899705688137)
                      ·
                        rfl

theorem cell23_5090736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_5090736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090736 prefixEnd_5090736 := by exact prefixLift 5090736
  have htrace : WordTrace (prefixWord ++ tailWord_5090736) baseStart_5090736 baseEnd_5090736 := by
    simpa [prefixWord, tailWord_5090736, baseEnd_5090736] using wordTrace_append hprefix tailTrace_5090736
  have hstable : (prefixWord ++ tailWord_5090736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090736).length < 2 ^ (prefixWord ++ tailWord_5090736).sum := by decide
  have hdescent : baseEnd_5090736 < baseStart_5090736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090813 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_5090813 : Nat := 118140960795 + 5090813 * 2 ^ 59
def prefixEnd_5090813 : Nat := 4983230072969 + 3 ^ 40 * 5090813 * 2
def baseEnd_5090813 : Nat := 2614033991157295904425283

theorem tailTrace_5090813 : CollatzResearch.WordTrace tailWord_5090813 prefixEnd_5090813 2614033991157295904425283 := by
  unfold tailWord_5090813
  simp only [CollatzResearch.WordTrace]
  refine ⟨185677204105861417485725093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123784802737240944990483395 185677204105861417485725093)
  ·
    refine ⟨34814475769849015778573455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185677204105861417485725093 34814475769849015778573455)
    ·
      refine ⟨52221713654773523667860183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34814475769849015778573455 52221713654773523667860183)
      ·
        refine ⟨78332570482160285501790275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52221713654773523667860183 78332570482160285501790275)
        ·
          refine ⟨117498855723240428252685413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78332570482160285501790275 117498855723240428252685413)
          ·
            refine ⟨22031035448107580297378515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117498855723240428252685413 22031035448107580297378515)
            ·
              refine ⟨33046553172161370446067773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22031035448107580297378515 33046553172161370446067773)
              ·
                refine ⟨12392457439560513917275415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33046553172161370446067773 12392457439560513917275415)
                ·
                  refine ⟨18588686159340770875913123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12392457439560513917275415 18588686159340770875913123)
                  ·
                    refine ⟨27883029239011156313869685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18588686159340770875913123 27883029239011156313869685)
                    ·
                      refine ⟨2614033991157295904425283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27883029239011156313869685 2614033991157295904425283)
                      ·
                        rfl

theorem cell23_5090813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_5090813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090813 prefixEnd_5090813 := by exact prefixLift 5090813
  have htrace : WordTrace (prefixWord ++ tailWord_5090813) baseStart_5090813 baseEnd_5090813 := by
    simpa [prefixWord, tailWord_5090813, baseEnd_5090813] using wordTrace_append hprefix tailTrace_5090813
  have hstable : (prefixWord ++ tailWord_5090813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090813).length < 2 ^ (prefixWord ++ tailWord_5090813).sum := by decide
  have hdescent : baseEnd_5090813 < baseStart_5090813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090823 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5090823 : Nat := 118140960795 + 5090823 * 2 ^ 59
def prefixEnd_5090823 : Nat := 4983230072969 + 3 ^ 40 * 5090823 * 2
def baseEnd_5090823 : Nat := 2614039125963840865300237

theorem tailTrace_5090823 : CollatzResearch.WordTrace tailWord_5090823 prefixEnd_5090823 2614039125963840865300237 := by
  unfold tailWord_5090823
  simp only [CollatzResearch.WordTrace]
  refine ⟨185677568835825189193589123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123785045890550126129059415 185677568835825189193589123)
  ·
    refine ⟨278516353253737783790383685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185677568835825189193589123 278516353253737783790383685)
    ·
      refine ⟨52221816235075834460696941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278516353253737783790383685 52221816235075834460696941)
      ·
        refine ⟨19583181088153437922761353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52221816235075834460696941 19583181088153437922761353)
        ·
          refine ⟨14687385816115078442071015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19583181088153437922761353 14687385816115078442071015)
          ·
            refine ⟨22031078724172617663106523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14687385816115078442071015 22031078724172617663106523)
            ·
              refine ⟨33046618086258926494659785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22031078724172617663106523 33046618086258926494659785)
              ·
                refine ⟨24784963564694194870994839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33046618086258926494659785 24784963564694194870994839)
                ·
                  refine ⟨37177445347041292306492259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24784963564694194870994839 37177445347041292306492259)
                  ·
                    refine ⟨55766168020561938459738389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37177445347041292306492259 55766168020561938459738389)
                    ·
                      refine ⟨2614039125963840865300237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55766168020561938459738389 2614039125963840865300237)
                      ·
                        rfl

theorem cell23_5090823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5090823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090823 prefixEnd_5090823 := by exact prefixLift 5090823
  have htrace : WordTrace (prefixWord ++ tailWord_5090823) baseStart_5090823 baseEnd_5090823 := by
    simpa [prefixWord, tailWord_5090823, baseEnd_5090823] using wordTrace_append hprefix tailTrace_5090823
  have hstable : (prefixWord ++ tailWord_5090823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090823).length < 2 ^ (prefixWord ++ tailWord_5090823).sum := by decide
  have hdescent : baseEnd_5090823 < baseStart_5090823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090837 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_5090837 : Nat := 118140960795 + 5090837 * 2 ^ 59
def prefixEnd_5090837 : Nat := 4983230072969 + 3 ^ 40 * 5090837 * 2
def baseEnd_5090837 : Nat := 871348771564334603508391

theorem tailTrace_5090837 : CollatzResearch.WordTrace tailWord_5090837 prefixEnd_5090837 871348771564334603508391 := by
  unfold tailWord_5090837
  simp only [CollatzResearch.WordTrace]
  refine ⟨185678079457774469584598765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123785386305182979723065843 185678079457774469584598765)
  ·
    refine ⟨69629279796665426094224537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185678079457774469584598765 69629279796665426094224537)
    ·
      refine ⟨52221959847499069570668403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69629279796665426094224537 52221959847499069570668403)
      ·
        refine ⟨78332939771248604356002605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52221959847499069570668403 78332939771248604356002605)
        ·
          refine ⟨29374852414218226633500977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78332939771248604356002605 29374852414218226633500977)
          ·
            refine ⟨22031139310663669975125733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29374852414218226633500977 22031139310663669975125733)
            ·
              refine ⟨4130838620749438120336075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22031139310663669975125733 4130838620749438120336075)
              ·
                refine ⟨6196257931124157180504113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130838620749438120336075 6196257931124157180504113)
                ·
                  refine ⟨4647193448343117885378085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196257931124157180504113 4647193448343117885378085)
                  ·
                    refine ⟨871348771564334603508391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647193448343117885378085 871348771564334603508391)
                    ·
                      rfl

theorem cell23_5090837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_5090837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090837 prefixEnd_5090837 := by exact prefixLift 5090837
  have htrace : WordTrace (prefixWord ++ tailWord_5090837) baseStart_5090837 baseEnd_5090837 := by
    simpa [prefixWord, tailWord_5090837, baseEnd_5090837] using wordTrace_append hprefix tailTrace_5090837
  have hstable : (prefixWord ++ tailWord_5090837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090837).length < 2 ^ (prefixWord ++ tailWord_5090837).sum := by decide
  have hdescent : baseEnd_5090837 < baseStart_5090837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090913 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_5090913 : Nat := 118140960795 + 5090913 * 2 ^ 59
def prefixEnd_5090913 : Nat := 4983230072969 + 3 ^ 40 * 5090913 * 2
def baseEnd_5090913 : Nat := 2614085339222745513174823

theorem tailTrace_5090913 : CollatzResearch.WordTrace tailWord_5090913 prefixEnd_5090913 2614085339222745513174823 := by
  unfold tailWord_5090913
  simp only [CollatzResearch.WordTrace]
  refine ⟨185680851405499134564365393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123787234270332756376243595 185680851405499134564365393)
  ·
    refine ⟨139260638554124350923274045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185680851405499134564365393 139260638554124350923274045)
    ·
      refine ⟨52222739457796631596227767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139260638554124350923274045 52222739457796631596227767)
      ·
        refine ⟨78334109186694947394341651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52222739457796631596227767 78334109186694947394341651)
        ·
          refine ⟨117501163780042421091512477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78334109186694947394341651 117501163780042421091512477)
          ·
            refine ⟨44062936417515907909317179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117501163780042421091512477 44062936417515907909317179)
            ·
              refine ⟨66094404626273861863975769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44062936417515907909317179 66094404626273861863975769)
              ·
                refine ⟨49570803469705396397981827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66094404626273861863975769 49570803469705396397981827)
                ·
                  refine ⟨74356205204558094596972741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49570803469705396397981827 74356205204558094596972741)
                  ·
                    refine ⟨13941788475854642736932389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74356205204558094596972741 13941788475854642736932389)
                    ·
                      refine ⟨2614085339222745513174823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13941788475854642736932389 2614085339222745513174823)
                      ·
                        rfl

theorem cell23_5090913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_5090913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090913 prefixEnd_5090913 := by exact prefixLift 5090913
  have htrace : WordTrace (prefixWord ++ tailWord_5090913) baseStart_5090913 baseEnd_5090913 := by
    simpa [prefixWord, tailWord_5090913, baseEnd_5090913] using wordTrace_append hprefix tailTrace_5090913
  have hstable : (prefixWord ++ tailWord_5090913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090913).length < 2 ^ (prefixWord ++ tailWord_5090913).sum := by decide
  have hdescent : baseEnd_5090913 < baseStart_5090913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090917 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_5090917 : Nat := 118140960795 + 5090917 * 2 ^ 59
def prefixEnd_5090917 : Nat := 4983230072969 + 3 ^ 40 * 5090917 * 2
def baseEnd_5090917 : Nat := 2614087393145363497524805

theorem tailTrace_5090917 : CollatzResearch.WordTrace tailWord_5090917 prefixEnd_5090917 2614087393145363497524805 := by
  unfold tailWord_5090917
  simp only [CollatzResearch.WordTrace]
  refine ⟨185680997297484643247511005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123787331531656428831674003 185680997297484643247511005)
  ·
    refine ⟨69630373986556741217816627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185680997297484643247511005 69630373986556741217816627)
    ·
      refine ⟨104445560979835111826724941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69630373986556741217816627 104445560979835111826724941)
      ·
        refine ⟨39167085367438166935021853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104445560979835111826724941 39167085367438166935021853)
        ·
          refine ⟨14687657012789312600633195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39167085367438166935021853 14687657012789312600633195)
          ·
            refine ⟨22031485519183968900949793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14687657012789312600633195 22031485519183968900949793)
            ·
              refine ⟨16523614139387976675712345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22031485519183968900949793 16523614139387976675712345)
              ·
                refine ⟨12392710604540982506784259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16523614139387976675712345 12392710604540982506784259)
                ·
                  refine ⟨18589065906811473760176389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12392710604540982506784259 18589065906811473760176389)
                  ·
                    refine ⟨3485449857527151330033073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18589065906811473760176389 3485449857527151330033073)
                    ·
                      refine ⟨2614087393145363497524805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485449857527151330033073 2614087393145363497524805)
                      ·
                        rfl

theorem cell23_5090917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_5090917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090917 prefixEnd_5090917 := by exact prefixLift 5090917
  have htrace : WordTrace (prefixWord ++ tailWord_5090917) baseStart_5090917 baseEnd_5090917 := by
    simpa [prefixWord, tailWord_5090917, baseEnd_5090917] using wordTrace_append hprefix tailTrace_5090917
  have hstable : (prefixWord ++ tailWord_5090917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090917).length < 2 ^ (prefixWord ++ tailWord_5090917).sum := by decide
  have hdescent : baseEnd_5090917 < baseStart_5090917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090930 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5090930 : Nat := 118140960795 + 5090930 * 2 ^ 59
def prefixEnd_5090930 : Nat := 4983230072969 + 3 ^ 40 * 5090930 * 2
def baseEnd_5090930 : Nat := 2614094068393871946662245

theorem tailTrace_5090930 : CollatzResearch.WordTrace tailWord_5090930 prefixEnd_5090930 2614094068393871946662245 := by
  unfold tailWord_5090930
  simp only [CollatzResearch.WordTrace]
  refine ⟨46420367861609386616933561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123787647630958364311822829 46420367861609386616933561)
  ·
    refine ⟨34815275896207039962700171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46420367861609386616933561 34815275896207039962700171)
    ·
      refine ⟨52222913844310559944050257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34815275896207039962700171 52222913844310559944050257)
      ·
        refine ⟨39167185383232919958037693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52222913844310559944050257 39167185383232919958037693)
        ·
          refine ⟨14687694518712344984264135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39167185383232919958037693 14687694518712344984264135)
          ·
            refine ⟨22031541778068517476396203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14687694518712344984264135 22031541778068517476396203)
            ·
              refine ⟨33047312667102776214594305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22031541778068517476396203 33047312667102776214594305)
              ·
                refine ⟨24785484500327082160945729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33047312667102776214594305 24785484500327082160945729)
                ·
                  refine ⟨18589113375245311620709297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24785484500327082160945729 18589113375245311620709297)
                  ·
                    refine ⟨13941835031433983715531973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18589113375245311620709297 13941835031433983715531973)
                    ·
                      refine ⟨2614094068393871946662245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13941835031433983715531973 2614094068393871946662245)
                      ·
                        rfl

theorem cell23_5090930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5090930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090930 prefixEnd_5090930 := by exact prefixLift 5090930
  have htrace : WordTrace (prefixWord ++ tailWord_5090930) baseStart_5090930 baseEnd_5090930 := by
    simpa [prefixWord, tailWord_5090930, baseEnd_5090930] using wordTrace_append hprefix tailTrace_5090930
  have hstable : (prefixWord ++ tailWord_5090930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090930).length < 2 ^ (prefixWord ++ tailWord_5090930).sum := by decide
  have hdescent : baseEnd_5090930 < baseStart_5090930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090951 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_5090951 : Nat := 118140960795 + 5090951 * 2 ^ 59
def prefixEnd_5090951 : Nat := 4983230072969 + 3 ^ 40 * 5090951 * 2
def baseEnd_5090951 : Nat := 2614104851487616364499649

theorem tailTrace_5090951 : CollatzResearch.WordTrace tailWord_5090951 prefixEnd_5090951 2614104851487616364499649 := by
  unfold tailWord_5090951
  simp only [CollatzResearch.WordTrace]
  refine ⟨185682237379361467054248707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123788158252907644702832471 185682237379361467054248707)
  ·
    refine ⟨278523356069042200581373061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185682237379361467054248707 278523356069042200581373061)
    ·
      refine ⟨52223129262945412609007449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278523356069042200581373061 52223129262945412609007449)
      ·
        refine ⟨39167346947209059456755587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52223129262945412609007449 39167346947209059456755587)
        ·
          refine ⟨58751020420813589185133381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39167346947209059456755587 58751020420813589185133381)
          ·
            refine ⟨11015816328902547972212509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58751020420813589185133381 11015816328902547972212509)
            ·
              refine ⟨4130931123338455489579691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11015816328902547972212509 4130931123338455489579691)
              ·
                refine ⟨6196396685007683234369537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130931123338455489579691 6196396685007683234369537)
                ·
                  refine ⟨4647297513755762425777153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196396685007683234369537 4647297513755762425777153)
                  ·
                    refine ⟨3485473135316821819332865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647297513755762425777153 3485473135316821819332865)
                    ·
                      refine ⟨2614104851487616364499649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485473135316821819332865 2614104851487616364499649)
                      ·
                        rfl

theorem cell23_5090951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_5090951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090951 prefixEnd_5090951 := by exact prefixLift 5090951
  have htrace : WordTrace (prefixWord ++ tailWord_5090951) baseStart_5090951 baseEnd_5090951 := by
    simpa [prefixWord, tailWord_5090951, baseEnd_5090951] using wordTrace_append hprefix tailTrace_5090951
  have hstable : (prefixWord ++ tailWord_5090951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090951).length < 2 ^ (prefixWord ++ tailWord_5090951).sum := by decide
  have hdescent : baseEnd_5090951 < baseStart_5090951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090953 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_5090953 : Nat := 118140960795 + 5090953 * 2 ^ 59
def prefixEnd_5090953 : Nat := 4983230072969 + 3 ^ 40 * 5090953 * 2
def baseEnd_5090953 : Nat := 871368626149641785558213

theorem tailTrace_5090953 : CollatzResearch.WordTrace tailWord_5090953 prefixEnd_5090953 871368626149641785558213 := by
  unfold tailWord_5090953
  simp only [CollatzResearch.WordTrace]
  refine ⟨185682310325354221395821513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123788206883569480930547675 185682310325354221395821513)
  ·
    refine ⟨139261732744015666046866135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185682310325354221395821513 139261732744015666046866135)
    ·
      refine ⟨208892599116023499070299203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139261732744015666046866135 208892599116023499070299203)
      ·
        refine ⟨313338898674035248605448805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208892599116023499070299203 313338898674035248605448805)
        ·
          refine ⟨58751043501381609113521651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313338898674035248605448805 58751043501381609113521651)
          ·
            refine ⟨88126565252072413670282477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58751043501381609113521651 88126565252072413670282477)
            ·
              refine ⟨33047461969527155126355929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88126565252072413670282477 33047461969527155126355929)
              ·
                refine ⟨24785596477145366344766947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33047461969527155126355929 24785596477145366344766947)
                ·
                  refine ⟨37178394715718049517150421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24785596477145366344766947 37178394715718049517150421)
                  ·
                    refine ⟨871368626149641785558213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37178394715718049517150421 871368626149641785558213)
                    ·
                      rfl

theorem cell23_5090953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_5090953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090953 prefixEnd_5090953 := by exact prefixLift 5090953
  have htrace : WordTrace (prefixWord ++ tailWord_5090953) baseStart_5090953 baseEnd_5090953 := by
    simpa [prefixWord, tailWord_5090953, baseEnd_5090953] using wordTrace_append hprefix tailTrace_5090953
  have hstable : (prefixWord ++ tailWord_5090953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090953).length < 2 ^ (prefixWord ++ tailWord_5090953).sum := by decide
  have hdescent : baseEnd_5090953 < baseStart_5090953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090960 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2]
def baseStart_5090960 : Nat := 118140960795 + 5090960 * 2 ^ 59
def prefixEnd_5090960 : Nat := 4983230072969 + 3 ^ 40 * 5090960 * 2
def baseEnd_5090960 : Nat := 2614109472813506829287107

theorem tailTrace_5090960 : CollatzResearch.WordTrace tailWord_5090960 prefixEnd_5090960 2614109472813506829287107 := by
  unfold tailWord_5090960
  simp only [CollatzResearch.WordTrace]
  refine ⟨92841282818164430795663167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123788377090885907727550889 92841282818164430795663167)
  ·
    refine ⟨139261924227246646193494751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92841282818164430795663167 139261924227246646193494751)
    ·
      refine ⟨208892886340869969290242127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139261924227246646193494751 208892886340869969290242127)
      ·
        refine ⟨313339329511304953935363191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208892886340869969290242127 313339329511304953935363191)
        ·
          refine ⟨470008994266957430903044787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313339329511304953935363191 470008994266957430903044787)
          ·
            refine ⟨705013491400436146354567181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470008994266957430903044787 705013491400436146354567181)
            ·
              refine ⟨264380059275163554882962693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705013491400436146354567181 264380059275163554882962693)
              ·
                refine ⟨49571261114093166540555505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264380059275163554882962693 49571261114093166540555505)
                ·
                  refine ⟨37178445835569874905416629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49571261114093166540555505 37178445835569874905416629)
                  ·
                    refine ⟨3485479297084675772382809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37178445835569874905416629 3485479297084675772382809)
                    ·
                      refine ⟨2614109472813506829287107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485479297084675772382809 2614109472813506829287107)
                      ·
                        rfl

theorem cell23_5090960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2].length) (baseStart_5090960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090960 prefixEnd_5090960 := by exact prefixLift 5090960
  have htrace : WordTrace (prefixWord ++ tailWord_5090960) baseStart_5090960 baseEnd_5090960 := by
    simpa [prefixWord, tailWord_5090960, baseEnd_5090960] using wordTrace_append hprefix tailTrace_5090960
  have hstable : (prefixWord ++ tailWord_5090960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090960).length < 2 ^ (prefixWord ++ tailWord_5090960).sum := by decide
  have hdescent : baseEnd_5090960 < baseStart_5090960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090974 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_5090974 : Nat := 118140960795 + 5090974 * 2 ^ 59
def prefixEnd_5090974 : Nat := 4983230072969 + 3 ^ 40 * 5090974 * 2
def baseEnd_5090974 : Nat := 290457406838074419390227

theorem tailTrace_5090974 : CollatzResearch.WordTrace tailWord_5090974 prefixEnd_5090974 290457406838074419390227 := by
  unfold tailWord_5090974
  simp only [CollatzResearch.WordTrace]
  refine ⟨23210384532284767747791997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123788717505518761321557317 23210384532284767747791997)
  ·
    refine ⟨8703894199606787905421999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23210384532284767747791997 8703894199606787905421999)
    ·
      refine ⟨13055841299410181858132999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703894199606787905421999 13055841299410181858132999)
      ·
        refine ⟨19583761949115272787199499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13055841299410181858132999 19583761949115272787199499)
        ·
          refine ⟨29375642923672909180799249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19583761949115272787199499 29375642923672909180799249)
          ·
            refine ⟨22031732192754681885599437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29375642923672909180799249 22031732192754681885599437)
            ·
              refine ⟨8261899572283005707099789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22031732192754681885599437 8261899572283005707099789)
              ·
                refine ⟨3098212339606127140162421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8261899572283005707099789 3098212339606127140162421)
                ·
                  refine ⟨290457406838074419390227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098212339606127140162421 290457406838074419390227)
                  ·
                    rfl

theorem cell23_5090974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_5090974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090974 prefixEnd_5090974 := by exact prefixLift 5090974
  have htrace : WordTrace (prefixWord ++ tailWord_5090974) baseStart_5090974 baseEnd_5090974 := by
    simpa [prefixWord, tailWord_5090974, baseEnd_5090974] using wordTrace_append hprefix tailTrace_5090974
  have hstable : (prefixWord ++ tailWord_5090974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090974).length < 2 ^ (prefixWord ++ tailWord_5090974).sum := by decide
  have hdescent : baseEnd_5090974 < baseStart_5090974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5090997 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5090997 : Nat := 118140960795 + 5090997 * 2 ^ 59
def prefixEnd_5090997 : Nat := 4983230072969 + 3 ^ 40 * 5090997 * 2
def baseEnd_5090997 : Nat := 2614128471597723184524437

theorem tailTrace_5090997 : CollatzResearch.WordTrace tailWord_5090997 prefixEnd_5090997 2614128471597723184524437 := by
  unfold tailWord_5090997
  simp only [CollatzResearch.WordTrace]
  refine ⟨185683915137194816910423245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123789276758129877940282163 185683915137194816910423245)
  ·
    refine ⟨69631468176448056341408717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185683915137194816910423245 69631468176448056341408717)
    ·
      refine ⟨26111800566168021128028269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69631468176448056341408717 26111800566168021128028269)
      ·
        refine ⟨9791925212313007923010601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26111800566168021128028269 9791925212313007923010601)
        ·
          refine ⟨7343943909234755942257951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791925212313007923010601 7343943909234755942257951)
          ·
            refine ⟨11015915863852133913386927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343943909234755942257951 11015915863852133913386927)
            ·
              refine ⟨16523873795778200870080391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11015915863852133913386927 16523873795778200870080391)
              ·
                refine ⟨24785810693667301305120587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16523873795778200870080391 24785810693667301305120587)
                ·
                  refine ⟨37178716040500951957680881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24785810693667301305120587 37178716040500951957680881)
                  ·
                    refine ⟨27884037030375713968260661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37178716040500951957680881 27884037030375713968260661)
                    ·
                      refine ⟨2614128471597723184524437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27884037030375713968260661 2614128471597723184524437)
                      ·
                        rfl

theorem cell23_5090997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5090997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5090997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5090997 prefixEnd_5090997 := by exact prefixLift 5090997
  have htrace : WordTrace (prefixWord ++ tailWord_5090997) baseStart_5090997 baseEnd_5090997 := by
    simpa [prefixWord, tailWord_5090997, baseEnd_5090997] using wordTrace_append hprefix tailTrace_5090997
  have hstable : (prefixWord ++ tailWord_5090997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5090997).length < 2 ^ (prefixWord ++ tailWord_5090997).sum := by decide
  have hdescent : baseEnd_5090997 < baseStart_5090997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5090997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091003 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_5091003 : Nat := 118140960795 + 5091003 * 2 ^ 59
def prefixEnd_5091003 : Nat := 4983230072969 + 3 ^ 40 * 5091003 * 2
def baseEnd_5091003 : Nat := 2614131552481650161049409

theorem tailTrace_5091003 : CollatzResearch.WordTrace tailWord_5091003 prefixEnd_5091003 2614131552481650161049409 := by
  unfold tailWord_5091003
  simp only [CollatzResearch.WordTrace]
  refine ⟨185684133975173079935141663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123789422650115386623427775 185684133975173079935141663)
  ·
    refine ⟨278526200962759619902712495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185684133975173079935141663 278526200962759619902712495)
    ·
      refine ⟨417789301444139429854068743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278526200962759619902712495 417789301444139429854068743)
      ·
        refine ⟨626683952166209144781103115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417789301444139429854068743 626683952166209144781103115)
        ·
          refine ⟨940025928249313717171654673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626683952166209144781103115 940025928249313717171654673)
          ·
            refine ⟨705019446186985287878741005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940025928249313717171654673 705019446186985287878741005)
            ·
              refine ⟨264382292320119482954527877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705019446186985287878741005 264382292320119482954527877)
              ·
                refine ⟨49571679810022403053973977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264382292320119482954527877 49571679810022403053973977)
                ·
                  refine ⟨37178759857516802290480483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49571679810022403053973977 37178759857516802290480483)
                  ·
                    refine ⟨55768139786275203435720725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37178759857516802290480483 55768139786275203435720725)
                    ·
                      refine ⟨2614131552481650161049409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55768139786275203435720725 2614131552481650161049409)
                      ·
                        rfl

theorem cell23_5091003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_5091003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091003 prefixEnd_5091003 := by exact prefixLift 5091003
  have htrace : WordTrace (prefixWord ++ tailWord_5091003) baseStart_5091003 baseEnd_5091003 := by
    simpa [prefixWord, tailWord_5091003, baseEnd_5091003] using wordTrace_append hprefix tailTrace_5091003
  have hstable : (prefixWord ++ tailWord_5091003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091003).length < 2 ^ (prefixWord ++ tailWord_5091003).sum := by decide
  have hdescent : baseEnd_5091003 < baseStart_5091003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091084 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_5091084 : Nat := 118140960795 + 5091084 * 2 ^ 59
def prefixEnd_5091084 : Nat := 4983230072969 + 3 ^ 40 * 5091084 * 2
def baseEnd_5091084 : Nat := 2614173144414664344136537

theorem tailTrace_5091084 : CollatzResearch.WordTrace tailWord_5091084 prefixEnd_5091084 2614173144414664344136537 := by
  unfold tailWord_5091084
  simp only [CollatzResearch.WordTrace]
  refine ⟨92843544143939815384420153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123791392191919753845893537 92843544143939815384420153)
  ·
    refine ⟨69632658107954861538315115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92843544143939815384420153 69632658107954861538315115)
    ·
      refine ⟨104448987161932292307472673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69632658107954861538315115 104448987161932292307472673)
      ·
        refine ⟨78336740371449219230604505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104448987161932292307472673 78336740371449219230604505)
        ·
          refine ⟨58752555278586914422953379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78336740371449219230604505 58752555278586914422953379)
          ·
            refine ⟨88128832917880371634430069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58752555278586914422953379 88128832917880371634430069)
            ·
              refine ⟨8262078086051284840727819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88128832917880371634430069 8262078086051284840727819)
              ·
                refine ⟨12393117129076927261091729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8262078086051284840727819 12393117129076927261091729)
                ·
                  refine ⟨9294837846807695445818797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12393117129076927261091729 9294837846807695445818797)
                  ·
                    refine ⟨3485564192552885792182049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9294837846807695445818797 3485564192552885792182049)
                    ·
                      refine ⟨2614173144414664344136537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485564192552885792182049 2614173144414664344136537)
                      ·
                        rfl

theorem cell23_5091084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_5091084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091084 prefixEnd_5091084 := by exact prefixLift 5091084
  have htrace : WordTrace (prefixWord ++ tailWord_5091084) baseStart_5091084 baseEnd_5091084 := by
    simpa [prefixWord, tailWord_5091084, baseEnd_5091084] using wordTrace_append hprefix tailTrace_5091084
  have hstable : (prefixWord ++ tailWord_5091084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091084).length < 2 ^ (prefixWord ++ tailWord_5091084).sum := by decide
  have hdescent : baseEnd_5091084 < baseStart_5091084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091124 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_5091124 : Nat := 118140960795 + 5091124 * 2 ^ 59
def prefixEnd_5091124 : Nat := 4983230072969 + 3 ^ 40 * 5091124 * 2
def baseEnd_5091124 : Nat := 871397894546948062545451

theorem tailTrace_5091124 : CollatzResearch.WordTrace tailWord_5091124 prefixEnd_5091124 871397894546948062545451 := by
  unfold tailWord_5091124
  simp only [CollatzResearch.WordTrace]
  refine ⟨92844273603867358800148213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123792364805156478400197617 92844273603867358800148213)
  ·
    refine ⟨8704150650362564887513895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92844273603867358800148213 8704150650362564887513895)
    ·
      refine ⟨13056225975543847331270843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8704150650362564887513895 13056225975543847331270843)
      ·
        refine ⟨19584338963315770996906265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13056225975543847331270843 19584338963315770996906265)
        ·
          refine ⟨14688254222486828247679699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19584338963315770996906265 14688254222486828247679699)
          ·
            refine ⟨22032381333730242371519549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14688254222486828247679699 22032381333730242371519549)
            ·
              refine ⟨8262143000148840889319831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22032381333730242371519549 8262143000148840889319831)
              ·
                refine ⟨12393214500223261333979747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8262143000148840889319831 12393214500223261333979747)
                ·
                  refine ⟨18589821750334892000969621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12393214500223261333979747 18589821750334892000969621)
                  ·
                    refine ⟨871397894546948062545451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18589821750334892000969621 871397894546948062545451)
                    ·
                      rfl

theorem cell23_5091124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_5091124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091124 prefixEnd_5091124 := by exact prefixLift 5091124
  have htrace : WordTrace (prefixWord ++ tailWord_5091124) baseStart_5091124 baseEnd_5091124 := by
    simpa [prefixWord, tailWord_5091124, baseEnd_5091124] using wordTrace_append hprefix tailTrace_5091124
  have hstable : (prefixWord ++ tailWord_5091124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091124).length < 2 ^ (prefixWord ++ tailWord_5091124).sum := by decide
  have hdescent : baseEnd_5091124 < baseStart_5091124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091142 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5091142 : Nat := 118140960795 + 5091142 * 2 ^ 59
def prefixEnd_5091142 : Nat := 4983230072969 + 3 ^ 40 * 5091142 * 2
def baseEnd_5091142 : Nat := 2614202926292625117211271

theorem tailTrace_5091142 : CollatzResearch.WordTrace tailWord_5091142 prefixEnd_5091142 2614202926292625117211271 := by
  unfold tailWord_5091142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802787616302172083576615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123792802481113004449634453 5802787616302172083576615)
  ·
    refine ⟨8704181424453258125364923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802787616302172083576615 8704181424453258125364923)
    ·
      refine ⟨13056272136679887188047385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8704181424453258125364923 13056272136679887188047385)
      ·
        refine ⟨9792204102509915391035539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13056272136679887188047385 9792204102509915391035539)
        ·
          refine ⟨14688306153764873086553309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9792204102509915391035539 14688306153764873086553309)
          ·
            refine ⟨5508114807661827407457491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14688306153764873086553309 5508114807661827407457491)
            ·
              refine ⟨8262172211492741111186237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508114807661827407457491 8262172211492741111186237)
              ·
                refine ⟨3098314579309777916694839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8262172211492741111186237 3098314579309777916694839)
                ·
                  refine ⟨4647471868964666875042259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098314579309777916694839 4647471868964666875042259)
                  ·
                    refine ⟨6971207803447000312563389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4647471868964666875042259 6971207803447000312563389)
                    ·
                      refine ⟨2614202926292625117211271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6971207803447000312563389 2614202926292625117211271)
                      ·
                        rfl

theorem cell23_5091142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5091142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091142 prefixEnd_5091142 := by exact prefixLift 5091142
  have htrace : WordTrace (prefixWord ++ tailWord_5091142) baseStart_5091142 baseEnd_5091142 := by
    simpa [prefixWord, tailWord_5091142, baseEnd_5091142] using wordTrace_append hprefix tailTrace_5091142
  have hstable : (prefixWord ++ tailWord_5091142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091142).length < 2 ^ (prefixWord ++ tailWord_5091142).sum := by decide
  have hdescent : baseEnd_5091142 < baseStart_5091142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091150 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_5091150 : Nat := 118140960795 + 5091150 * 2 ^ 59
def prefixEnd_5091150 : Nat := 4983230072969 + 3 ^ 40 * 5091150 * 2
def baseEnd_5091150 : Nat := 871402344712620361970411

theorem tailTrace_5091150 : CollatzResearch.WordTrace tailWord_5091150 prefixEnd_5091150 871402344712620361970411 := by
  unfold tailWord_5091150
  simp only [CollatzResearch.WordTrace]
  refine ⟨23211186938205065505092863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123792997003760349360495269 23211186938205065505092863)
  ·
    refine ⟨34816780407307598257639295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23211186938205065505092863 34816780407307598257639295)
    ·
      refine ⟨52225170610961397386458943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34816780407307598257639295 52225170610961397386458943)
      ·
        refine ⟨78337755916442096079688415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52225170610961397386458943 78337755916442096079688415)
        ·
          refine ⟨117506633874663144119532623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78337755916442096079688415 117506633874663144119532623)
          ·
            refine ⟨176259950811994716179298935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117506633874663144119532623 176259950811994716179298935)
            ·
              refine ⟨264389926217992074268948403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176259950811994716179298935 264389926217992074268948403)
              ·
                refine ⟨396584889326988111403422605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264389926217992074268948403 396584889326988111403422605)
                ·
                  refine ⟨148719333497620541776283477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396584889326988111403422605 148719333497620541776283477)
                  ·
                    refine ⟨871402344712620361970411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 148719333497620541776283477 871402344712620361970411)
                    ·
                      rfl

theorem cell23_5091150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_5091150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091150 prefixEnd_5091150 := by exact prefixLift 5091150
  have htrace : WordTrace (prefixWord ++ tailWord_5091150) baseStart_5091150 baseEnd_5091150 := by
    simpa [prefixWord, tailWord_5091150, baseEnd_5091150] using wordTrace_append hprefix tailTrace_5091150
  have hstable : (prefixWord ++ tailWord_5091150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091150).length < 2 ^ (prefixWord ++ tailWord_5091150).sum := by decide
  have hdescent : baseEnd_5091150 < baseStart_5091150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091204 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_5091204 : Nat := 118140960795 + 5091204 * 2 ^ 59
def prefixEnd_5091204 : Nat := 4983230072969 + 3 ^ 40 * 5091204 * 2
def baseEnd_5091204 : Nat := 2614234762093203874635985

theorem tailTrace_5091204 : CollatzResearch.WordTrace tailWord_5091204 prefixEnd_5091204 2614234762093203874635985 := by
  unfold tailWord_5091204
  simp only [CollatzResearch.WordTrace]
  refine ⟨92845732523722445631604333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123794310031629927508805777 92845732523722445631604333)
  ·
    refine ⟨34817149696395917111851625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92845732523722445631604333 34817149696395917111851625)
    ·
      refine ⟨26112862272296937833888719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34817149696395917111851625 26112862272296937833888719)
      ·
        refine ⟨39169293408445406750833079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26112862272296937833888719 39169293408445406750833079)
        ·
          refine ⟨58753940112668110126249619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39169293408445406750833079 58753940112668110126249619)
          ·
            refine ⟨88130910169002165189374429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58753940112668110126249619 88130910169002165189374429)
            ·
              refine ⟨33049091313375811946015411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88130910169002165189374429 33049091313375811946015411)
              ·
                refine ⟨49573636970063717919023117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33049091313375811946015411 49573636970063717919023117)
                ·
                  refine ⟨18590113863773894219633669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49573636970063717919023117 18590113863773894219633669)
                  ·
                    refine ⟨3485646349457605166181313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18590113863773894219633669 3485646349457605166181313)
                    ·
                      refine ⟨2614234762093203874635985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485646349457605166181313 2614234762093203874635985)
                      ·
                        rfl

theorem cell23_5091204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_5091204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091204 prefixEnd_5091204 := by exact prefixLift 5091204
  have htrace : WordTrace (prefixWord ++ tailWord_5091204) baseStart_5091204 baseEnd_5091204 := by
    simpa [prefixWord, tailWord_5091204, baseEnd_5091204] using wordTrace_append hprefix tailTrace_5091204
  have hstable : (prefixWord ++ tailWord_5091204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091204).length < 2 ^ (prefixWord ++ tailWord_5091204).sum := by decide
  have hdescent : baseEnd_5091204 < baseStart_5091204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091257 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_5091257 : Nat := 118140960795 + 5091257 * 2 ^ 59
def prefixEnd_5091257 : Nat := 4983230072969 + 3 ^ 40 * 5091257 * 2
def baseEnd_5091257 : Nat := 871420658855964055757747

theorem tailTrace_5091257 : CollatzResearch.WordTrace tailWord_5091257 prefixEnd_5091257 871420658855964055757747 := by
  unfold tailWord_5091257
  simp only [CollatzResearch.WordTrace]
  refine ⟨185693398116252881314888025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123795598744168587543258683 185693398116252881314888025)
  ·
    refine ⟨139270048587189660986166019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185693398116252881314888025 139270048587189660986166019)
    ·
      refine ⟨208905072880784491479249029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139270048587189660986166019 208905072880784491479249029)
      ·
        refine ⟨39169701165147092152359193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208905072880784491479249029 39169701165147092152359193)
        ·
          refine ⟨29377275873860319114269395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39169701165147092152359193 29377275873860319114269395)
          ·
            refine ⟨44065913810790478671404093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29377275873860319114269395 44065913810790478671404093)
            ·
              refine ⟨16524717679046429501776535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44065913810790478671404093 16524717679046429501776535)
              ·
                refine ⟨24787076518569644252664803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16524717679046429501776535 24787076518569644252664803)
                ·
                  refine ⟨37180614777854466378997205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24787076518569644252664803 37180614777854466378997205)
                  ·
                    refine ⟨871420658855964055757747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37180614777854466378997205 871420658855964055757747)
                    ·
                      rfl

theorem cell23_5091257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_5091257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091257 prefixEnd_5091257 := by exact prefixLift 5091257
  have htrace : WordTrace (prefixWord ++ tailWord_5091257) baseStart_5091257 baseEnd_5091257 := by
    simpa [prefixWord, tailWord_5091257, baseEnd_5091257] using wordTrace_append hprefix tailTrace_5091257
  have hstable : (prefixWord ++ tailWord_5091257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091257).length < 2 ^ (prefixWord ++ tailWord_5091257).sum := by decide
  have hdescent : baseEnd_5091257 < baseStart_5091257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091261 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 5]
def baseStart_5091261 : Nat := 118140960795 + 5091261 * 2 ^ 59
def prefixEnd_5091261 : Nat := 4983230072969 + 3 ^ 40 * 5091261 * 2
def baseEnd_5091261 : Nat := 290473781165612239069247

theorem tailTrace_5091261 : CollatzResearch.WordTrace tailWord_5091261 prefixEnd_5091261 290473781165612239069247 := by
  unfold tailWord_5091261
  simp only [CollatzResearch.WordTrace]
  refine ⟨185693544008238389998033637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123795696005492259998689091 185693544008238389998033637)
  ·
    refine ⟨34817539501544698124631307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185693544008238389998033637 34817539501544698124631307)
    ·
      refine ⟨52226309252317047186946961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34817539501544698124631307 52226309252317047186946961)
      ·
        refine ⟨39169731939237785390210221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52226309252317047186946961 39169731939237785390210221)
        ·
          refine ⟨14688649477214169521328833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39169731939237785390210221 14688649477214169521328833)
          ·
            refine ⟨11016487107910627140996625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14688649477214169521328833 11016487107910627140996625)
            ·
              refine ⟨8262365330932970355747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11016487107910627140996625 8262365330932970355747469)
              ·
                refine ⟨3098386999099863883405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8262365330932970355747469 3098386999099863883405301)
                ·
                  refine ⟨290473781165612239069247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098386999099863883405301 290473781165612239069247)
                  ·
                    rfl

theorem cell23_5091261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_5091261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091261 prefixEnd_5091261 := by exact prefixLift 5091261
  have htrace : WordTrace (prefixWord ++ tailWord_5091261) baseStart_5091261 baseEnd_5091261 := by
    simpa [prefixWord, tailWord_5091261, baseEnd_5091261] using wordTrace_append hprefix tailTrace_5091261
  have hstable : (prefixWord ++ tailWord_5091261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091261).length < 2 ^ (prefixWord ++ tailWord_5091261).sum := by decide
  have hdescent : baseEnd_5091261 < baseStart_5091261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091338 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_5091338 : Nat := 118140960795 + 5091338 * 2 ^ 59
def prefixEnd_5091338 : Nat := 4983230072969 + 3 ^ 40 * 5091338 * 2
def baseEnd_5091338 : Nat := 871434522833635450120123

theorem tailTrace_5091338 : CollatzResearch.WordTrace tailWord_5091338 prefixEnd_5091338 871434522833635450120123 := by
  unfold tailWord_5091338
  simp only [CollatzResearch.WordTrace]
  refine ⟨46424088107239858037146667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123797568285972954765724445 46424088107239858037146667)
  ·
    refine ⟨69636132160859787055720001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46424088107239858037146667 69636132160859787055720001)
    ·
      refine ⟨52227099120644840291790001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69636132160859787055720001 52227099120644840291790001)
      ·
        refine ⟨39170324340483630218842501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52227099120644840291790001 39170324340483630218842501)
        ·
          refine ⟨7344435813840680666032969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39170324340483630218842501 7344435813840680666032969)
          ·
            refine ⟨5508326860380510499524727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7344435813840680666032969 5508326860380510499524727)
            ·
              refine ⟨8262490290570765749287091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508326860380510499524727 8262490290570765749287091)
              ·
                refine ⟨12393735435856148623930637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8262490290570765749287091 12393735435856148623930637)
                ·
                  refine ⟨4647650788446055733973989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12393735435856148623930637 4647650788446055733973989)
                  ·
                    refine ⟨871434522833635450120123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647650788446055733973989 871434522833635450120123)
                    ·
                      rfl

theorem cell23_5091338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_5091338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091338 prefixEnd_5091338 := by exact prefixLift 5091338
  have htrace : WordTrace (prefixWord ++ tailWord_5091338) baseStart_5091338 baseEnd_5091338 := by
    simpa [prefixWord, tailWord_5091338, baseEnd_5091338] using wordTrace_append hprefix tailTrace_5091338
  have hstable : (prefixWord ++ tailWord_5091338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091338).length < 2 ^ (prefixWord ++ tailWord_5091338).sum := by decide
  have hdescent : baseEnd_5091338 < baseStart_5091338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091351 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 6]
def baseStart_5091351 : Nat := 118140960795 + 5091351 * 2 ^ 59
def prefixEnd_5091351 : Nat := 4983230072969 + 3 ^ 40 * 5091351 * 2
def baseEnd_5091351 : Nat := 290478915972157199944201

theorem tailTrace_5091351 : CollatzResearch.WordTrace tailWord_5091351 prefixEnd_5091351 290478915972157199944201 := by
  unfold tailWord_5091351
  simp only [CollatzResearch.WordTrace]
  refine ⟨185696826577912335368809907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123797884385274890245873271 185696826577912335368809907)
  ·
    refine ⟨278545239866868503053214861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185696826577912335368809907 278545239866868503053214861)
    ·
      refine ⟨104454464950075688644955573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278545239866868503053214861 104454464950075688644955573)
      ·
        refine ⟨9792606089069595810464585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104454464950075688644955573 9792606089069595810464585)
        ·
          refine ⟨7344454566802196857848439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9792606089069595810464585 7344454566802196857848439)
          ·
            refine ⟨11016681850203295286772659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344454566802196857848439 11016681850203295286772659)
            ·
              refine ⟨16525022775304942930158989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11016681850203295286772659 16525022775304942930158989)
              ·
                refine ⟨6196883540739353598809621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16525022775304942930158989 6196883540739353598809621)
                ·
                  refine ⟨290478915972157199944201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6196883540739353598809621 290478915972157199944201)
                  ·
                    rfl

theorem cell23_5091351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 6].length) (baseStart_5091351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091351 prefixEnd_5091351 := by exact prefixLift 5091351
  have htrace : WordTrace (prefixWord ++ tailWord_5091351) baseStart_5091351 baseEnd_5091351 := by
    simpa [prefixWord, tailWord_5091351, baseEnd_5091351] using wordTrace_append hprefix tailTrace_5091351
  have hstable : (prefixWord ++ tailWord_5091351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091351).length < 2 ^ (prefixWord ++ tailWord_5091351).sum := by decide
  have hdescent : baseEnd_5091351 < baseStart_5091351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091404 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5091404 : Nat := 118140960795 + 5091404 * 2 ^ 59
def prefixEnd_5091404 : Nat := 4983230072969 + 3 ^ 40 * 5091404 * 2
def baseEnd_5091404 : Nat := 2614337458224103092135065

theorem tailTrace_5091404 : CollatzResearch.WordTrace tailWord_5091404 prefixEnd_5091404 2614337458224103092135065 := by
  unfold tailWord_5091404
  simp only [CollatzResearch.WordTrace]
  refine ⟨92849379823360162710244633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123799173097813550280326177 92849379823360162710244633)
  ·
    refine ⟨69637034867520122032683475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92849379823360162710244633 69637034867520122032683475)
    ·
      refine ⟨104455552301280183049025213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69637034867520122032683475 104455552301280183049025213)
      ·
        refine ⟨39170832112980068643384455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104455552301280183049025213 39170832112980068643384455)
        ·
          refine ⟨58756248169470102965076683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39170832112980068643384455 58756248169470102965076683)
          ·
            refine ⟨88134372254205154447615025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58756248169470102965076683 88134372254205154447615025)
            ·
              refine ⟨66100779190653865835711269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88134372254205154447615025 66100779190653865835711269)
              ·
                refine ⟨12393896098247599844195863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66100779190653865835711269 12393896098247599844195863)
                ·
                  refine ⟨18590844147371399766293795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12393896098247599844195863 18590844147371399766293795)
                  ·
                    refine ⟨27886266221057099649440693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18590844147371399766293795 27886266221057099649440693)
                    ·
                      refine ⟨2614337458224103092135065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27886266221057099649440693 2614337458224103092135065)
                      ·
                        rfl

theorem cell23_5091404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5091404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091404 prefixEnd_5091404 := by exact prefixLift 5091404
  have htrace : WordTrace (prefixWord ++ tailWord_5091404) baseStart_5091404 baseEnd_5091404 := by
    simpa [prefixWord, tailWord_5091404, baseEnd_5091404] using wordTrace_append hprefix tailTrace_5091404
  have hstable : (prefixWord ++ tailWord_5091404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091404).length < 2 ^ (prefixWord ++ tailWord_5091404).sum := by decide
  have hdescent : baseEnd_5091404 < baseStart_5091404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091418 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_5091418 : Nat := 118140960795 + 5091418 * 2 ^ 59
def prefixEnd_5091418 : Nat := 4983230072969 + 3 ^ 40 * 5091418 * 2
def baseEnd_5091418 : Nat := 2614344646953266037360001

theorem tailTrace_5091418 : CollatzResearch.WordTrace tailWord_5091418 prefixEnd_5091418 2614344646953266037360001 := by
  unfold tailWord_5091418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46424817567167401452874727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123799513512446403874332605 46424817567167401452874727)
  ·
    refine ⟨69637226350751102179312091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46424817567167401452874727 69637226350751102179312091)
    ·
      refine ⟨104455839526126653268968137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69637226350751102179312091 104455839526126653268968137)
      ·
        refine ⟨78341879644594989951726103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104455839526126653268968137 78341879644594989951726103)
        ·
          refine ⟨117512819466892484927589155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78341879644594989951726103 117512819466892484927589155)
          ·
            refine ⟨176269229200338727391383733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117512819466892484927589155 176269229200338727391383733)
            ·
              refine ⟨16525240237531755692942225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176269229200338727391383733 16525240237531755692942225)
              ·
                refine ⟨12393930178148816769706669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16525240237531755692942225 12393930178148816769706669)
                ·
                  refine ⟨4647723816805806288640001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12393930178148816769706669 4647723816805806288640001)
                  ·
                    refine ⟨3485792862604354716480001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647723816805806288640001 3485792862604354716480001)
                    ·
                      refine ⟨2614344646953266037360001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485792862604354716480001 2614344646953266037360001)
                      ·
                        rfl

theorem cell23_5091418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_5091418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091418 prefixEnd_5091418 := by exact prefixLift 5091418
  have htrace : WordTrace (prefixWord ++ tailWord_5091418) baseStart_5091418 baseEnd_5091418 := by
    simpa [prefixWord, tailWord_5091418, baseEnd_5091418] using wordTrace_append hprefix tailTrace_5091418
  have hstable : (prefixWord ++ tailWord_5091418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091418).length < 2 ^ (prefixWord ++ tailWord_5091418).sum := by decide
  have hdescent : baseEnd_5091418 < baseStart_5091418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091422 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5091422 : Nat := 118140960795 + 5091422 * 2 ^ 59
def prefixEnd_5091422 : Nat := 4983230072969 + 3 ^ 40 * 5091422 * 2
def baseEnd_5091422 : Nat := 2614346700875884021709983

theorem tailTrace_5091422 : CollatzResearch.WordTrace tailWord_5091422 prefixEnd_5091422 2614346700875884021709983 := by
  unfold tailWord_5091422
  simp only [CollatzResearch.WordTrace]
  refine ⟨23212427020081889311830565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123799610773770076329763013 23212427020081889311830565)
  ·
    refine ⟨4352330066265354245968231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23212427020081889311830565 4352330066265354245968231)
    ·
      refine ⟨6528495099398031368952347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4352330066265354245968231 6528495099398031368952347)
      ·
        refine ⟨9792742649097047053428521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6528495099398031368952347 9792742649097047053428521)
        ·
          refine ⟨7344556986822785290071391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9792742649097047053428521 7344556986822785290071391)
          ·
            refine ⟨11016835480234177935107087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344556986822785290071391 11016835480234177935107087)
            ·
              refine ⟨16525253220351266902660631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11016835480234177935107087 16525253220351266902660631)
              ·
                refine ⟨24787879830526900353990947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16525253220351266902660631 24787879830526900353990947)
                ·
                  refine ⟨37181819745790350530986421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24787879830526900353990947 37181819745790350530986421)
                  ·
                    refine ⟨3485795601167845362279977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37181819745790350530986421 3485795601167845362279977)
                    ·
                      refine ⟨2614346700875884021709983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485795601167845362279977 2614346700875884021709983)
                      ·
                        rfl

theorem cell23_5091422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5091422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091422 prefixEnd_5091422 := by exact prefixLift 5091422
  have htrace : WordTrace (prefixWord ++ tailWord_5091422) baseStart_5091422 baseEnd_5091422 := by
    simpa [prefixWord, tailWord_5091422, baseEnd_5091422] using wordTrace_append hprefix tailTrace_5091422
  have hstable : (prefixWord ++ tailWord_5091422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091422).length < 2 ^ (prefixWord ++ tailWord_5091422).sum := by decide
  have hdescent : baseEnd_5091422 < baseStart_5091422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091438 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5091438 : Nat := 118140960795 + 5091438 * 2 ^ 59
def prefixEnd_5091438 : Nat := 4983230072969 + 3 ^ 40 * 5091438 * 2
def baseEnd_5091438 : Nat := 2614354916566355959109909

theorem tailTrace_5091438 : CollatzResearch.WordTrace tailWord_5091438 prefixEnd_5091438 2614354916566355959109909 := by
  unfold tailWord_5091438
  simp only [CollatzResearch.WordTrace]
  refine ⟨23212499966074643653403371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123799999819064766151484645 23212499966074643653403371)
  ·
    refine ⟨34818749949111965480105057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23212499966074643653403371 34818749949111965480105057)
    ·
      refine ⟨26114062461833974110078793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34818749949111965480105057 26114062461833974110078793)
      ·
        refine ⟨19585546846375480582559095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26114062461833974110078793 19585546846375480582559095)
        ·
          refine ⟨29378320269563220873838643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19585546846375480582559095 29378320269563220873838643)
          ·
            refine ⟨44067480404344831310757965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29378320269563220873838643 44067480404344831310757965)
            ·
              refine ⟨16525305151629311741534237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44067480404344831310757965 16525305151629311741534237)
              ·
                refine ⟨6196989431860991903075339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16525305151629311741534237 6196989431860991903075339)
                ·
                  refine ⟨9295484147791487854613009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6196989431860991903075339 9295484147791487854613009)
                  ·
                    refine ⟨6971613110843615890959757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9295484147791487854613009 6971613110843615890959757)
                    ·
                      refine ⟨2614354916566355959109909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6971613110843615890959757 2614354916566355959109909)
                      ·
                        rfl

theorem cell23_5091438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5091438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091438 prefixEnd_5091438 := by exact prefixLift 5091438
  have htrace : WordTrace (prefixWord ++ tailWord_5091438) baseStart_5091438 baseEnd_5091438 := by
    simpa [prefixWord, tailWord_5091438, baseEnd_5091438] using wordTrace_append hprefix tailTrace_5091438
  have hstable : (prefixWord ++ tailWord_5091438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091438).length < 2 ^ (prefixWord ++ tailWord_5091438).sum := by decide
  have hdescent : baseEnd_5091438 < baseStart_5091438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091486 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_5091486 : Nat := 118140960795 + 5091486 * 2 ^ 59
def prefixEnd_5091486 : Nat := 4983230072969 + 3 ^ 40 * 5091486 * 2
def baseEnd_5091486 : Nat := 2614379563637771771309689

theorem tailTrace_5091486 : CollatzResearch.WordTrace tailWord_5091486 prefixEnd_5091486 2614379563637771771309689 := by
  unfold tailWord_5091486
  simp only [CollatzResearch.WordTrace]
  refine ⟨23212718804052906678121789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123801166954948835616649541 23212718804052906678121789)
  ·
    refine ⟨8704769551519840004295671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23212718804052906678121789 8704769551519840004295671)
    ·
      refine ⟨13057154327279760006443507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8704769551519840004295671 13057154327279760006443507)
      ·
        refine ⟨19585731490919640009665261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13057154327279760006443507 19585731490919640009665261)
        ·
          refine ⟨7344649309094865003624473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19585731490919640009665261 7344649309094865003624473)
          ·
            refine ⟨5508486981821148752718355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7344649309094865003624473 5508486981821148752718355)
            ·
              refine ⟨8262730472731723129077533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508486981821148752718355 8262730472731723129077533)
              ·
                refine ⟨3098523927274396173404075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8262730472731723129077533 3098523927274396173404075)
                ·
                  refine ⟨4647785890911594260106113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098523927274396173404075 4647785890911594260106113)
                  ·
                    refine ⟨3485839418183695695079585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647785890911594260106113 3485839418183695695079585)
                    ·
                      refine ⟨2614379563637771771309689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485839418183695695079585 2614379563637771771309689)
                      ·
                        rfl

theorem cell23_5091486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_5091486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091486 prefixEnd_5091486 := by exact prefixLift 5091486
  have htrace : WordTrace (prefixWord ++ tailWord_5091486) baseStart_5091486 baseEnd_5091486 := by
    simpa [prefixWord, tailWord_5091486, baseEnd_5091486] using wordTrace_append hprefix tailTrace_5091486
  have hstable : (prefixWord ++ tailWord_5091486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091486).length < 2 ^ (prefixWord ++ tailWord_5091486).sum := by decide
  have hdescent : baseEnd_5091486 < baseStart_5091486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091542 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5091542 : Nat := 118140960795 + 5091542 * 2 ^ 59
def prefixEnd_5091542 : Nat := 4983230072969 + 3 ^ 40 * 5091542 * 2
def baseEnd_5091542 : Nat := 2614408318554423552209431

theorem tailTrace_5091542 : CollatzResearch.WordTrace tailWord_5091542 prefixEnd_5091542 2614408318554423552209431 := by
  unfold tailWord_5091542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606487057513773436813305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123802528613480249992675253 11606487057513773436813305)
  ·
    refine ⟨8704865293135330077609979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11606487057513773436813305 8704865293135330077609979)
    ·
      refine ⟨13057297939702995116414969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8704865293135330077609979 13057297939702995116414969)
      ·
        refine ⟨9792973454777246337311227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13057297939702995116414969 9792973454777246337311227)
        ·
          refine ⟨14689460182165869505966841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9792973454777246337311227 14689460182165869505966841)
          ·
            refine ⟨11017095136624402129475131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14689460182165869505966841 11017095136624402129475131)
            ·
              refine ⟨16525642704936603194212697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11017095136624402129475131 16525642704936603194212697)
              ·
                refine ⟨12394232028702452395659523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16525642704936603194212697 12394232028702452395659523)
                ·
                  refine ⟨18591348043053678593489285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12394232028702452395659523 18591348043053678593489285)
                  ·
                    refine ⟨3485877758072564736279241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18591348043053678593489285 3485877758072564736279241)
                    ·
                      refine ⟨2614408318554423552209431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485877758072564736279241 2614408318554423552209431)
                      ·
                        rfl

theorem cell23_5091542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5091542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091542 prefixEnd_5091542 := by exact prefixLift 5091542
  have htrace : WordTrace (prefixWord ++ tailWord_5091542) baseStart_5091542 baseEnd_5091542 := by
    simpa [prefixWord, tailWord_5091542, baseEnd_5091542] using wordTrace_append hprefix tailTrace_5091542
  have hstable : (prefixWord ++ tailWord_5091542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091542).length < 2 ^ (prefixWord ++ tailWord_5091542).sum := by decide
  have hdescent : baseEnd_5091542 < baseStart_5091542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091565 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 5]
def baseStart_5091565 : Nat := 118140960795 + 5091565 * 2 ^ 59
def prefixEnd_5091565 : Nat := 4983230072969 + 3 ^ 40 * 5091565 * 2
def baseEnd_5091565 : Nat := 290491125401052995802425

theorem tailTrace_5091565 : CollatzResearch.WordTrace tailWord_5091565 prefixEnd_5091565 290491125401052995802425 := by
  unfold tailWord_5091565
  simp only [CollatzResearch.WordTrace]
  refine ⟨185704631799137049917100149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123803087866091366611400099 185704631799137049917100149)
  ·
    refine ⟨17409809231169098429728139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185704631799137049917100149 17409809231169098429728139)
    ·
      refine ⟨26114713846753647644592209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17409809231169098429728139 26114713846753647644592209)
      ·
        refine ⟨19586035385065235733444157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26114713846753647644592209 19586035385065235733444157)
        ·
          refine ⟨7344763269399463400041559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19586035385065235733444157 7344763269399463400041559)
          ·
            refine ⟨11017144904099195100062339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344763269399463400041559 11017144904099195100062339)
            ·
              refine ⟨16525717356148792650093509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11017144904099195100062339 16525717356148792650093509)
              ·
                refine ⟨3098572004277898621892533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16525717356148792650093509 3098572004277898621892533)
                ·
                  refine ⟨290491125401052995802425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098572004277898621892533 290491125401052995802425)
                  ·
                    rfl

theorem cell23_5091565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_5091565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091565 prefixEnd_5091565 := by exact prefixLift 5091565
  have htrace : WordTrace (prefixWord ++ tailWord_5091565) baseStart_5091565 baseEnd_5091565 := by
    simpa [prefixWord, tailWord_5091565, baseEnd_5091565] using wordTrace_append hprefix tailTrace_5091565
  have hstable : (prefixWord ++ tailWord_5091565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091565).length < 2 ^ (prefixWord ++ tailWord_5091565).sum := by decide
  have hdescent : baseEnd_5091565 < baseStart_5091565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091581 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_5091581 : Nat := 118140960795 + 5091581 * 2 ^ 59
def prefixEnd_5091581 : Nat := 4983230072969 + 3 ^ 40 * 5091581 * 2
def baseEnd_5091581 : Nat := 2614428344299948899621751

theorem tailTrace_5091581 : CollatzResearch.WordTrace tailWord_5091581 prefixEnd_5091581 2614428344299948899621751 := by
  unfold tailWord_5091581
  simp only [CollatzResearch.WordTrace]
  refine ⟨185705215367079084649682597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123803476911386056433121731 185705215367079084649682597)
  ·
    refine ⟨34819727881327328371815487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185705215367079084649682597 34819727881327328371815487)
    ·
      refine ⟨52229591821990992557723231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34819727881327328371815487 52229591821990992557723231)
      ·
        refine ⟨78344387732986488836584847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52229591821990992557723231 78344387732986488836584847)
        ·
          refine ⟨117516581599479733254877271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78344387732986488836584847 117516581599479733254877271)
          ·
            refine ⟨176274872399219599882315907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117516581599479733254877271 176274872399219599882315907)
            ·
              refine ⟨264412308598829399823473861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176274872399219599882315907 264412308598829399823473861)
              ·
                refine ⟨49577307862280512466901349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264412308598829399823473861 49577307862280512466901349)
                ·
                  refine ⟨9295745224177596087544003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49577307862280512466901349 9295745224177596087544003)
                  ·
                    refine ⟨13943617836266394131316005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9295745224177596087544003 13943617836266394131316005)
                    ·
                      refine ⟨2614428344299948899621751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13943617836266394131316005 2614428344299948899621751)
                      ·
                        rfl

theorem cell23_5091581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_5091581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091581 prefixEnd_5091581 := by exact prefixLift 5091581
  have htrace : WordTrace (prefixWord ++ tailWord_5091581) baseStart_5091581 baseEnd_5091581 := by
    simpa [prefixWord, tailWord_5091581, baseEnd_5091581] using wordTrace_append hprefix tailTrace_5091581
  have hstable : (prefixWord ++ tailWord_5091581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091581).length < 2 ^ (prefixWord ++ tailWord_5091581).sum := by decide
  have hdescent : baseEnd_5091581 < baseStart_5091581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091598 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_5091598 : Nat := 118140960795 + 5091598 * 2 ^ 59
def prefixEnd_5091598 : Nat := 4983230072969 + 3 ^ 40 * 5091598 * 2
def baseEnd_5091598 : Nat := 2614437073471075333109173

theorem tailTrace_5091598 : CollatzResearch.WordTrace tailWord_5091598 prefixEnd_5091598 2614437073471075333109173 := by
  unfold tailWord_5091598
  simp only [CollatzResearch.WordTrace]
  refine ⟨23213229426002187069131431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123803890272011664368700965 23213229426002187069131431)
  ·
    refine ⟨34819844139003280603697147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23213229426002187069131431 34819844139003280603697147)
    ·
      refine ⟨52229766208504920905545721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34819844139003280603697147 52229766208504920905545721)
      ·
        refine ⟨39172324656378690679159291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52229766208504920905545721 39172324656378690679159291)
        ·
          refine ⟨58758486984568036018738937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39172324656378690679159291 58758486984568036018738937)
          ·
            refine ⟨44068865238426027014054203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58758486984568036018738937 44068865238426027014054203)
            ·
              refine ⟨66103297857639040521081305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44068865238426027014054203 66103297857639040521081305)
              ·
                refine ⟨49577473393229280390810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66103297857639040521081305 49577473393229280390810979)
                ·
                  refine ⟨74366210089843920586216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49577473393229280390810979 74366210089843920586216469)
                  ·
                    refine ⟨3485916097961433777478897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74366210089843920586216469 3485916097961433777478897)
                    ·
                      refine ⟨2614437073471075333109173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485916097961433777478897 2614437073471075333109173)
                      ·
                        rfl

theorem cell23_5091598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_5091598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091598 prefixEnd_5091598 := by exact prefixLift 5091598
  have htrace : WordTrace (prefixWord ++ tailWord_5091598) baseStart_5091598 baseEnd_5091598 := by
    simpa [prefixWord, tailWord_5091598, baseEnd_5091598] using wordTrace_append hprefix tailTrace_5091598
  have hstable : (prefixWord ++ tailWord_5091598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091598).length < 2 ^ (prefixWord ++ tailWord_5091598).sum := by decide
  have hdescent : baseEnd_5091598 < baseStart_5091598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091648 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3]
def baseStart_5091648 : Nat := 118140960795 + 5091648 * 2 ^ 59
def prefixEnd_5091648 : Nat := 4983230072969 + 3 ^ 40 * 5091648 * 2
def baseEnd_5091648 : Nat := 2614462747503800137483943

theorem tailTrace_5091648 : CollatzResearch.WordTrace tailWord_5091648 prefixEnd_5091648 2614462747503800137483943 := by
  unfold tailWord_5091648
  simp only [CollatzResearch.WordTrace]
  refine ⟨92853829528918177546185799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123805106038557570061581065 92853829528918177546185799)
  ·
    refine ⟨139280744293377266319278699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92853829528918177546185799 139280744293377266319278699)
    ·
      refine ⟨208921116440065899478918049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139280744293377266319278699 208921116440065899478918049)
      ·
        refine ⟨156690837330049424609188537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208921116440065899478918049 156690837330049424609188537)
        ·
          refine ⟨117518127997537068456891403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156690837330049424609188537 117518127997537068456891403)
          ·
            refine ⟨176277191996305602685337105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117518127997537068456891403 176277191996305602685337105)
            ·
              refine ⟨132207893997229202014002829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176277191996305602685337105 132207893997229202014002829)
              ·
                refine ⟨49577960248960950755251061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132207893997229202014002829 49577960248960950755251061)
                ·
                  refine ⟨4647933773340089133304787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49577960248960950755251061 4647933773340089133304787)
                  ·
                    refine ⟨6971900660010133699957181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4647933773340089133304787 6971900660010133699957181)
                    ·
                      refine ⟨2614462747503800137483943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6971900660010133699957181 2614462747503800137483943)
                      ·
                        rfl

theorem cell23_5091648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_5091648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091648 prefixEnd_5091648 := by exact prefixLift 5091648
  have htrace : WordTrace (prefixWord ++ tailWord_5091648) baseStart_5091648 baseEnd_5091648 := by
    simpa [prefixWord, tailWord_5091648, baseEnd_5091648] using wordTrace_append hprefix tailTrace_5091648
  have hstable : (prefixWord ++ tailWord_5091648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091648).length < 2 ^ (prefixWord ++ tailWord_5091648).sum := by decide
  have hdescent : baseEnd_5091648 < baseStart_5091648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091651 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 3, 5]
def baseStart_5091651 : Nat := 118140960795 + 5091651 * 2 ^ 59
def prefixEnd_5091651 : Nat := 4983230072969 + 3 ^ 40 * 5091651 * 2
def baseEnd_5091651 : Nat := 871488095981921208582143

theorem tailTrace_5091651 : CollatzResearch.WordTrace tailWord_5091651 prefixEnd_5091651 871488095981921208582143 := by
  unfold tailWord_5091651
  simp only [CollatzResearch.WordTrace]
  refine ⟨185707768476825486604730807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123805178984550324403153871 185707768476825486604730807)
  ·
    refine ⟨278561652715238229907096211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185707768476825486604730807 278561652715238229907096211)
    ·
      refine ⟨417842479072857344860644317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278561652715238229907096211 417842479072857344860644317)
      ·
        refine ⟨156690929652321504322741619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417842479072857344860644317 156690929652321504322741619)
        ·
          refine ⟨235036394478482256484112429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156690929652321504322741619 235036394478482256484112429)
          ·
            refine ⟨88138647929430846181542161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235036394478482256484112429 88138647929430846181542161)
            ·
              refine ⟨66103985947073134636156621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88138647929430846181542161 66103985947073134636156621)
              ·
                refine ⟨24788994730152425488558733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66103985947073134636156621 24788994730152425488558733)
                ·
                  refine ⟨9295873023807159558209525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24788994730152425488558733 9295873023807159558209525)
                  ·
                    refine ⟨871488095981921208582143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9295873023807159558209525 871488095981921208582143)
                    ·
                      rfl

theorem cell23_5091651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5].length) (baseStart_5091651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091651 prefixEnd_5091651 := by exact prefixLift 5091651
  have htrace : WordTrace (prefixWord ++ tailWord_5091651) baseStart_5091651 baseEnd_5091651 := by
    simpa [prefixWord, tailWord_5091651, baseEnd_5091651] using wordTrace_append hprefix tailTrace_5091651
  have hstable : (prefixWord ++ tailWord_5091651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091651).length < 2 ^ (prefixWord ++ tailWord_5091651).sum := by decide
  have hdescent : baseEnd_5091651 < baseStart_5091651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091676 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_5091676 : Nat := 118140960795 + 5091676 * 2 ^ 59
def prefixEnd_5091676 : Nat := 4983230072969 + 3 ^ 40 * 5091676 * 2
def baseEnd_5091676 : Nat := 871492374987375342644605

theorem tailTrace_5091676 : CollatzResearch.WordTrace tailWord_5091676 prefixEnd_5091676 871492374987375342644605 := by
  unfold tailWord_5091676
  simp only [CollatzResearch.WordTrace]
  refine ⟨92854340150867457937195441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123805786867823277249593921 92854340150867457937195441)
  ·
    refine ⟨69640755113150593452896581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92854340150867457937195441 69640755113150593452896581)
    ·
      refine ⟨13057641583715736272418109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69640755113150593452896581 13057641583715736272418109)
      ·
        refine ⟨4896615593893401102156791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13057641583715736272418109 4896615593893401102156791)
        ·
          refine ⟨7344923390840101653235187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896615593893401102156791 7344923390840101653235187)
          ·
            refine ⟨11017385086260152479852781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344923390840101653235187 11017385086260152479852781)
            ·
              refine ⟨4131519407347557179944793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11017385086260152479852781 4131519407347557179944793)
              ·
                refine ⟨3098639555510667884958595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4131519407347557179944793 3098639555510667884958595)
                ·
                  refine ⟨4647959333266001827437893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098639555510667884958595 4647959333266001827437893)
                  ·
                    refine ⟨871492374987375342644605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647959333266001827437893 871492374987375342644605)
                    ·
                      rfl

theorem cell23_5091676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_5091676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091676 prefixEnd_5091676 := by exact prefixLift 5091676
  have htrace : WordTrace (prefixWord ++ tailWord_5091676) baseStart_5091676 baseEnd_5091676 := by
    simpa [prefixWord, tailWord_5091676, baseEnd_5091676] using wordTrace_append hprefix tailTrace_5091676
  have hstable : (prefixWord ++ tailWord_5091676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091676).length < 2 ^ (prefixWord ++ tailWord_5091676).sum := by decide
  have hdescent : baseEnd_5091676 < baseStart_5091676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091682 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5091682 : Nat := 118140960795 + 5091682 * 2 ^ 59
def prefixEnd_5091682 : Nat := 4983230072969 + 3 ^ 40 * 5091682 * 2
def baseEnd_5091682 : Nat := 2614480205846053004458787

theorem tailTrace_5091682 : CollatzResearch.WordTrace tailWord_5091682 prefixEnd_5091682 2614480205846053004458787 := by
  unfold tailWord_5091682
  simp only [CollatzResearch.WordTrace]
  refine ⟨46427224784928294724777325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123805932759808785932739533 46427224784928294724777325)
  ·
    refine ⟨17410209294348110521791497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46427224784928294724777325 17410209294348110521791497)
    ·
      refine ⟨13057656970761082891343623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17410209294348110521791497 13057656970761082891343623)
      ·
        refine ⟨19586485456141624337015435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13057656970761082891343623 19586485456141624337015435)
        ·
          refine ⟨29379728184212436505523153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19586485456141624337015435 29379728184212436505523153)
          ·
            refine ⟨22034796138159327379142365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29379728184212436505523153 22034796138159327379142365)
            ·
              refine ⟨8263048551809747767178387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22034796138159327379142365 8263048551809747767178387)
              ·
                refine ⟨12394572827714621650767581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263048551809747767178387 12394572827714621650767581)
                ·
                  refine ⟨4647964810392983119037843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12394572827714621650767581 4647964810392983119037843)
                  ·
                    refine ⟨6971947215589474678556765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4647964810392983119037843 6971947215589474678556765)
                    ·
                      refine ⟨2614480205846053004458787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6971947215589474678556765 2614480205846053004458787)
                      ·
                        rfl

theorem cell23_5091682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5091682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091682 prefixEnd_5091682 := by exact prefixLift 5091682
  have htrace : WordTrace (prefixWord ++ tailWord_5091682) baseStart_5091682 baseEnd_5091682 := by
    simpa [prefixWord, tailWord_5091682, baseEnd_5091682] using wordTrace_append hprefix tailTrace_5091682
  have hstable : (prefixWord ++ tailWord_5091682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091682).length < 2 ^ (prefixWord ++ tailWord_5091682).sum := by decide
  have hdescent : baseEnd_5091682 < baseStart_5091682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091702 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_5091702 : Nat := 118140960795 + 5091702 * 2 ^ 59
def prefixEnd_5091702 : Nat := 4983230072969 + 3 ^ 40 * 5091702 * 2
def baseEnd_5091702 : Nat := 871496825153047642069565

theorem tailTrace_5091702 : CollatzResearch.WordTrace tailWord_5091702 prefixEnd_5091702 871496825153047642069565 := by
  unfold tailWord_5091702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606851787477545144677335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123806419066427148209891573 11606851787477545144677335)
  ·
    refine ⟨17410277681216317717016003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11606851787477545144677335 17410277681216317717016003)
    ·
      refine ⟨26115416521824476575524005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17410277681216317717016003 26115416521824476575524005)
      ·
        refine ⟨4896640597842089357910751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26115416521824476575524005 4896640597842089357910751)
        ·
          refine ⟨7344960896763134036866127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896640597842089357910751 7344960896763134036866127)
          ·
            refine ⟨11017441345144701055299191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344960896763134036866127 11017441345144701055299191)
            ·
              refine ⟨16526162017717051582948787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11017441345144701055299191 16526162017717051582948787)
              ·
                refine ⟨24789243026575577374423181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16526162017717051582948787 24789243026575577374423181)
                ·
                  refine ⟨9295966134965841515408693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24789243026575577374423181 9295966134965841515408693)
                  ·
                    refine ⟨871496825153047642069565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9295966134965841515408693 871496825153047642069565)
                    ·
                      rfl

theorem cell23_5091702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_5091702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091702 prefixEnd_5091702 := by exact prefixLift 5091702
  have htrace : WordTrace (prefixWord ++ tailWord_5091702) baseStart_5091702 baseEnd_5091702 := by
    simpa [prefixWord, tailWord_5091702, baseEnd_5091702] using wordTrace_append hprefix tailTrace_5091702
  have hstable : (prefixWord ++ tailWord_5091702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091702).length < 2 ^ (prefixWord ++ tailWord_5091702).sum := by decide
  have hdescent : baseEnd_5091702 < baseStart_5091702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091705 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 5, 2, 2]
def baseStart_5091705 : Nat := 118140960795 + 5091705 * 2 ^ 59
def prefixEnd_5091705 : Nat := 4983230072969 + 3 ^ 40 * 5091705 * 2
def baseEnd_5091705 : Nat := 2614492015901106414471181

theorem tailTrace_5091705 : CollatzResearch.WordTrace tailWord_5091705 prefixEnd_5091705 2614492015901106414471181 := by
  unfold tailWord_5091705
  simp only [CollatzResearch.WordTrace]
  refine ⟨185709738018629853827196569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123806492012419902551464379 185709738018629853827196569)
  ·
    refine ⟨139282303513972390370397427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185709738018629853827196569 139282303513972390370397427)
    ·
      refine ⟨208923455270958585555596141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139282303513972390370397427 208923455270958585555596141)
      ·
        refine ⟨78346295726609469583348553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208923455270958585555596141 78346295726609469583348553)
        ·
          refine ⟨58759721794957102187511415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78346295726609469583348553 58759721794957102187511415)
          ·
            refine ⟨88139582692435653281267123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58759721794957102187511415 88139582692435653281267123)
            ·
              refine ⟨132209374038653479921900685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88139582692435653281267123 132209374038653479921900685)
              ·
                refine ⟨49578515264495054970712757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132209374038653479921900685 49578515264495054970712757)
                ·
                  refine ⟨4647985806046411403504321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49578515264495054970712757 4647985806046411403504321)
                  ·
                    refine ⟨3485989354534808552628241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647985806046411403504321 3485989354534808552628241)
                    ·
                      refine ⟨2614492015901106414471181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3485989354534808552628241 2614492015901106414471181)
                      ·
                        rfl

theorem cell23_5091705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_5091705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091705 prefixEnd_5091705 := by exact prefixLift 5091705
  have htrace : WordTrace (prefixWord ++ tailWord_5091705) baseStart_5091705 baseEnd_5091705 := by
    simpa [prefixWord, tailWord_5091705, baseEnd_5091705] using wordTrace_append hprefix tailTrace_5091705
  have hstable : (prefixWord ++ tailWord_5091705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091705).length < 2 ^ (prefixWord ++ tailWord_5091705).sum := by decide
  have hdescent : baseEnd_5091705 < baseStart_5091705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091742 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5091742 : Nat := 118140960795 + 5091742 * 2 ^ 59
def prefixEnd_5091742 : Nat := 4983230072969 + 3 ^ 40 * 5091742 * 2
def baseEnd_5091742 : Nat := 2614511014685322769708511

theorem tailTrace_5091742 : CollatzResearch.WordTrace tailWord_5091742 prefixEnd_5091742 2614511014685322769708511 := by
  unfold tailWord_5091742
  simp only [CollatzResearch.WordTrace]
  refine ⟨23213885939936976143286685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123807391679663872764195653 23213885939936976143286685)
  ·
    refine ⟨8705207227476366053732507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23213885939936976143286685 8705207227476366053732507)
    ·
      refine ⟨13057810841214549080598761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8705207227476366053732507 13057810841214549080598761)
      ·
        refine ⟨9793358130910911810449071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13057810841214549080598761 9793358130910911810449071)
        ·
          refine ⟨14690037196366367715673607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793358130910911810449071 14690037196366367715673607)
          ·
            refine ⟨22035055794549551573510411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14690037196366367715673607 22035055794549551573510411)
            ·
              refine ⟨33052583691824327360265617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22035055794549551573510411 33052583691824327360265617)
              ·
                refine ⟨24789437768868245520199213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33052583691824327360265617 24789437768868245520199213)
                ·
                  refine ⟨9296039163325592070074705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24789437768868245520199213 9296039163325592070074705)
                  ·
                    refine ⟨6972029372494194052556029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9296039163325592070074705 6972029372494194052556029)
                    ·
                      refine ⟨2614511014685322769708511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972029372494194052556029 2614511014685322769708511)
                      ·
                        rfl

theorem cell23_5091742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5091742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091742 prefixEnd_5091742 := by exact prefixLift 5091742
  have htrace : WordTrace (prefixWord ++ tailWord_5091742) baseStart_5091742 baseEnd_5091742 := by
    simpa [prefixWord, tailWord_5091742, baseEnd_5091742] using wordTrace_append hprefix tailTrace_5091742
  have hstable : (prefixWord ++ tailWord_5091742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091742).length < 2 ^ (prefixWord ++ tailWord_5091742).sum := by decide
  have hdescent : baseEnd_5091742 < baseStart_5091742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091752 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5091752 : Nat := 118140960795 + 5091752 * 2 ^ 59
def prefixEnd_5091752 : Nat := 4983230072969 + 3 ^ 40 * 5091752 * 2
def baseEnd_5091752 : Nat := 2614516149491867730583465

theorem tailTrace_5091752 : CollatzResearch.WordTrace tailWord_5091752 prefixEnd_5091752 2614516149491867730583465 := by
  unfold tailWord_5091752
  simp only [CollatzResearch.WordTrace]
  refine ⟨92855726124729790427078755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123807634832973053902771673 92855726124729790427078755)
  ·
    refine ⟨139283589187094685640618133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92855726124729790427078755 139283589187094685640618133)
    ·
      refine ⟨6528918243145063389403975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139283589187094685640618133 6528918243145063389403975)
      ·
        refine ⟨9793377364717595084105963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6528918243145063389403975 9793377364717595084105963)
        ·
          refine ⟨14690066047076392626158945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793377364717595084105963 14690066047076392626158945)
          ·
            refine ⟨11017549535307294469619209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14690066047076392626158945 11017549535307294469619209)
            ·
              refine ⟨8263162151480470852214407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11017549535307294469619209 8263162151480470852214407)
              ·
                refine ⟨12394743227220706278321611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263162151480470852214407 12394743227220706278321611)
                ·
                  refine ⟨18592114840831059417482417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12394743227220706278321611 18592114840831059417482417)
                  ·
                    refine ⟨13944086130623294563111813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18592114840831059417482417 13944086130623294563111813)
                    ·
                      refine ⟨2614516149491867730583465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13944086130623294563111813 2614516149491867730583465)
                      ·
                        rfl

theorem cell23_5091752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5091752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091752 prefixEnd_5091752 := by exact prefixLift 5091752
  have htrace : WordTrace (prefixWord ++ tailWord_5091752) baseStart_5091752 baseEnd_5091752 := by
    simpa [prefixWord, tailWord_5091752, baseEnd_5091752] using wordTrace_append hprefix tailTrace_5091752
  have hstable : (prefixWord ++ tailWord_5091752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091752).length < 2 ^ (prefixWord ++ tailWord_5091752).sum := by decide
  have hdescent : baseEnd_5091752 < baseStart_5091752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091808 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_5091808 : Nat := 118140960795 + 5091808 * 2 ^ 59
def prefixEnd_5091808 : Nat := 4983230072969 + 3 ^ 40 * 5091808 * 2
def baseEnd_5091808 : Nat := 2614544904408519511483207

theorem tailTrace_5091808 : CollatzResearch.WordTrace tailWord_5091808 prefixEnd_5091808 2614544904408519511483207 := by
  unfold tailWord_5091808
  simp only [CollatzResearch.WordTrace]
  refine ⟨92856747368628351209098039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123808996491504468278797385 92856747368628351209098039)
  ·
    refine ⟨139285121052942526813647059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92856747368628351209098039 139285121052942526813647059)
    ·
      refine ⟨208927681579413790220470589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139285121052942526813647059 208927681579413790220470589)
      ·
        refine ⟨78347880592280171332676471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208927681579413790220470589 78347880592280171332676471)
        ·
          refine ⟨117521820888420256999014707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78347880592280171332676471 117521820888420256999014707)
          ·
            refine ⟨176282731332630385498522061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117521820888420256999014707 176282731332630385498522061)
            ·
              refine ⟨66106024249736394561945773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176282731332630385498522061 66106024249736394561945773)
              ·
                refine ⟨24789759093651147960729665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66106024249736394561945773 24789759093651147960729665)
                ·
                  refine ⟨18592319320238360970547249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24789759093651147960729665 18592319320238360970547249)
                  ·
                    refine ⟨13944239490178770727910437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18592319320238360970547249 13944239490178770727910437)
                    ·
                      refine ⟨2614544904408519511483207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13944239490178770727910437 2614544904408519511483207)
                      ·
                        rfl

theorem cell23_5091808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_5091808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091808 prefixEnd_5091808 := by exact prefixLift 5091808
  have htrace : WordTrace (prefixWord ++ tailWord_5091808) baseStart_5091808 baseEnd_5091808 := by
    simpa [prefixWord, tailWord_5091808, baseEnd_5091808] using wordTrace_append hprefix tailTrace_5091808
  have hstable : (prefixWord ++ tailWord_5091808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091808).length < 2 ^ (prefixWord ++ tailWord_5091808).sum := by decide
  have hdescent : baseEnd_5091808 < baseStart_5091808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091882 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_5091882 : Nat := 118140960795 + 5091882 * 2 ^ 59
def prefixEnd_5091882 : Nat := 4983230072969 + 3 ^ 40 * 5091882 * 2
def baseEnd_5091882 : Nat := 871527633992317407319289

theorem tailTrace_5091882 : CollatzResearch.WordTrace tailWord_5091882 prefixEnd_5091882 871527633992317407319289 := by
  unfold tailWord_5091882
  simp only [CollatzResearch.WordTrace]
  refine ⟨46429048434747153264097475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123810795825992408704259933 46429048434747153264097475)
  ·
    refine ⟨69643572652120729896146213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46429048434747153264097475 69643572652120729896146213)
    ·
      refine ⟨13058169872272636855527415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69643572652120729896146213 13058169872272636855527415)
      ·
        refine ⟨19587254808408955283291123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13058169872272636855527415 19587254808408955283291123)
        ·
          refine ⟨29380882212613432924936685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19587254808408955283291123 29380882212613432924936685)
          ·
            refine ⟨11017830829730037346851257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29380882212613432924936685 11017830829730037346851257)
            ·
              refine ⟨8263373122297528010138443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11017830829730037346851257 8263373122297528010138443)
              ·
                refine ⟨12395059683446292015207665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263373122297528010138443 12395059683446292015207665)
                ·
                  refine ⟨9296294762584719011405749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12395059683446292015207665 9296294762584719011405749)
                  ·
                    refine ⟨871527633992317407319289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9296294762584719011405749 871527633992317407319289)
                    ·
                      rfl

theorem cell23_5091882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_5091882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091882 prefixEnd_5091882 := by exact prefixLift 5091882
  have htrace : WordTrace (prefixWord ++ tailWord_5091882) baseStart_5091882 baseEnd_5091882 := by
    simpa [prefixWord, tailWord_5091882, baseEnd_5091882] using wordTrace_append hprefix tailTrace_5091882
  have hstable : (prefixWord ++ tailWord_5091882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091882).length < 2 ^ (prefixWord ++ tailWord_5091882).sum := by decide
  have hdescent : baseEnd_5091882 < baseStart_5091882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091925 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 6]
def baseStart_5091925 : Nat := 118140960795 + 5091925 * 2 ^ 59
def prefixEnd_5091925 : Nat := 4983230072969 + 3 ^ 40 * 5091925 * 2
def baseEnd_5091925 : Nat := 290511664627232839302241

theorem tailTrace_5091925 : CollatzResearch.WordTrace tailWord_5091925 prefixEnd_5091925 290511664627232839302241 := by
  unfold tailWord_5091925
  simp only [CollatzResearch.WordTrace]
  refine ⟨185717762077832831400205229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123811841385221887600136819 185717762077832831400205229)
  ·
    refine ⟨69644160779187311775076961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185717762077832831400205229 69644160779187311775076961)
    ·
      refine ⟨52233120584390483831307721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69644160779187311775076961 52233120584390483831307721)
      ·
        refine ⟨39174840438292862873480791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52233120584390483831307721 39174840438292862873480791)
        ·
          refine ⟨58762260657439294310221187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39174840438292862873480791 58762260657439294310221187)
          ·
            refine ⟨88143390986158941465331781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58762260657439294310221187 88143390986158941465331781)
            ·
              refine ⟨16526885809904801524749709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88143390986158941465331781 16526885809904801524749709)
              ·
                refine ⟨6197582178714300571781141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16526885809904801524749709 6197582178714300571781141)
                ·
                  refine ⟨290511664627232839302241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6197582178714300571781141 290511664627232839302241)
                  ·
                    rfl

theorem cell23_5091925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_5091925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091925 prefixEnd_5091925 := by exact prefixLift 5091925
  have htrace : WordTrace (prefixWord ++ tailWord_5091925) baseStart_5091925 baseEnd_5091925 := by
    simpa [prefixWord, tailWord_5091925, baseEnd_5091925] using wordTrace_append hprefix tailTrace_5091925
  have hstable : (prefixWord ++ tailWord_5091925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091925).length < 2 ^ (prefixWord ++ tailWord_5091925).sum := by decide
  have hdescent : baseEnd_5091925 < baseStart_5091925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091969 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_5091969 : Nat := 118140960795 + 5091969 * 2 ^ 59
def prefixEnd_5091969 : Nat := 4983230072969 + 3 ^ 40 * 5091969 * 2
def baseEnd_5091969 : Nat := 2614627574793893381569967

theorem tailTrace_5091969 : CollatzResearch.WordTrace tailWord_5091969 prefixEnd_5091969 2614627574793893381569967 := by
  unfold tailWord_5091969
  simp only [CollatzResearch.WordTrace]
  refine ⟨185719366889673426914806961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123812911259782284609871307 185719366889673426914806961)
  ·
    refine ⟨139289525167255070186105221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185719366889673426914806961 139289525167255070186105221)
    ·
      refine ⟨26116785968860325659894729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139289525167255070186105221 26116785968860325659894729)
      ·
        refine ⟨19587589476645244244921047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26116785968860325659894729 19587589476645244244921047)
        ·
          refine ⟨29381384214967866367381571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19587589476645244244921047 29381384214967866367381571)
          ·
            refine ⟨44072076322451799551072357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29381384214967866367381571 44072076322451799551072357)
            ·
              refine ⟨8263514310459712415826067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44072076322451799551072357 8263514310459712415826067)
              ·
                refine ⟨12395271465689568623739101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263514310459712415826067 12395271465689568623739101)
                ·
                  refine ⟨4648226799633588233902163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12395271465689568623739101 4648226799633588233902163)
                  ·
                    refine ⟨6972340199450382350853245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648226799633588233902163 6972340199450382350853245)
                    ·
                      refine ⟨2614627574793893381569967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972340199450382350853245 2614627574793893381569967)
                      ·
                        rfl

theorem cell23_5091969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_5091969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091969 prefixEnd_5091969 := by exact prefixLift 5091969
  have htrace : WordTrace (prefixWord ++ tailWord_5091969) baseStart_5091969 baseEnd_5091969 := by
    simpa [prefixWord, tailWord_5091969, baseEnd_5091969] using wordTrace_append hprefix tailTrace_5091969
  have hstable : (prefixWord ++ tailWord_5091969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091969).length < 2 ^ (prefixWord ++ tailWord_5091969).sum := by decide
  have hdescent : baseEnd_5091969 < baseStart_5091969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091992 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5091992 : Nat := 118140960795 + 5091992 * 2 ^ 59
def prefixEnd_5091992 : Nat := 4983230072969 + 3 ^ 40 * 5091992 * 2
def baseEnd_5091992 : Nat := 2614639384848946791582361

theorem tailTrace_5091992 : CollatzResearch.WordTrace tailWord_5091992 prefixEnd_5091992 2614639384848946791582361 := by
  unfold tailWord_5091992
  simp only [CollatzResearch.WordTrace]
  refine ⟨92860102884295050921447115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123813470512393401228596153 92860102884295050921447115)
  ·
    refine ⟨139290154326442576382170673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92860102884295050921447115 139290154326442576382170673)
    ·
      refine ⟨104467615744831932286628005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139290154326442576382170673 104467615744831932286628005)
      ·
        refine ⟨19587677952155987303742751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104467615744831932286628005 19587677952155987303742751)
        ·
          refine ⟨29381516928233980955614127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19587677952155987303742751 29381516928233980955614127)
          ·
            refine ⟨44072275392350971433421191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29381516928233980955614127 44072275392350971433421191)
            ·
              refine ⟨66108413088526457150131787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44072275392350971433421191 66108413088526457150131787)
              ·
                refine ⟨99162619632789685725197681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66108413088526457150131787 99162619632789685725197681)
                ·
                  refine ⟨74371964724592264293898261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99162619632789685725197681 74371964724592264293898261)
                  ·
                    refine ⟨3486185846465262388776481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74371964724592264293898261 3486185846465262388776481)
                    ·
                      refine ⟨2614639384848946791582361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486185846465262388776481 2614639384848946791582361)
                      ·
                        rfl

theorem cell23_5091992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5091992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091992 prefixEnd_5091992 := by exact prefixLift 5091992
  have htrace : WordTrace (prefixWord ++ tailWord_5091992) baseStart_5091992 baseEnd_5091992 := by
    simpa [prefixWord, tailWord_5091992, baseEnd_5091992] using wordTrace_append hprefix tailTrace_5091992
  have hstable : (prefixWord ++ tailWord_5091992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091992).length < 2 ^ (prefixWord ++ tailWord_5091992).sum := by decide
  have hdescent : baseEnd_5091992 < baseStart_5091992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092005 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_5092005 : Nat := 118140960795 + 5092005 * 2 ^ 59
def prefixEnd_5092005 : Nat := 4983230072969 + 3 ^ 40 * 5092005 * 2
def baseEnd_5092005 : Nat := 2614646060097455240719801

theorem tailTrace_5092005 : CollatzResearch.WordTrace tailWord_5092005 prefixEnd_5092005 2614646060097455240719801 := by
  unfold tailWord_5092005
  simp only [CollatzResearch.WordTrace]
  refine ⟨185720679917543005063117469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123813786611695336708744979 185720679917543005063117469)
  ·
    refine ⟨69645254969078626898669051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185720679917543005063117469 69645254969078626898669051)
    ·
      refine ⟨104467882453617940348003577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69645254969078626898669051 104467882453617940348003577)
      ·
        refine ⟨78350911840213455261002683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104467882453617940348003577 78350911840213455261002683)
        ·
          refine ⟨117526367760320182891504025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78350911840213455261002683 117526367760320182891504025)
          ·
            refine ⟨88144775820240137168628019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117526367760320182891504025 88144775820240137168628019)
            ·
              refine ⟨132217163730360205752942029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88144775820240137168628019 132217163730360205752942029)
              ·
                refine ⟨49581436398885077157353261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132217163730360205752942029 49581436398885077157353261)
                ·
                  refine ⟨18593038649581903934007473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49581436398885077157353261 18593038649581903934007473)
                  ·
                    refine ⟨13944778987186427950505605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18593038649581903934007473 13944778987186427950505605)
                    ·
                      refine ⟨2614646060097455240719801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13944778987186427950505605 2614646060097455240719801)
                      ·
                        rfl

theorem cell23_5092005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_5092005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092005 prefixEnd_5092005 := by exact prefixLift 5092005
  have htrace : WordTrace (prefixWord ++ tailWord_5092005) baseStart_5092005 baseEnd_5092005 := by
    simpa [prefixWord, tailWord_5092005, baseEnd_5092005] using wordTrace_append hprefix tailTrace_5092005
  have hstable : (prefixWord ++ tailWord_5092005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092005).length < 2 ^ (prefixWord ++ tailWord_5092005).sum := by decide
  have hdescent : baseEnd_5092005 < baseStart_5092005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092015 : List Nat := [1, 1, 2, 1, 2, 7, 9]
def baseStart_5092015 : Nat := 118140960795 + 5092015 * 2 ^ 59
def prefixEnd_5092015 : Nat := 4983230072969 + 3 ^ 40 * 5092015 * 2
def baseEnd_5092015 : Nat := 32279644381530866686355

theorem tailTrace_5092015 : CollatzResearch.WordTrace tailWord_5092015 prefixEnd_5092015 32279644381530866686355 := by
  unfold tailWord_5092015
  simp only [CollatzResearch.WordTrace]
  refine ⟨185721044647506776770981499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123814029765004517847320999 185721044647506776770981499)
  ·
    refine ⟨278581566971260165156472249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185721044647506776770981499 278581566971260165156472249)
    ·
      refine ⟨208936175228445123867354187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278581566971260165156472249 208936175228445123867354187)
      ·
        refine ⟨313404262842667685801031281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208936175228445123867354187 313404262842667685801031281)
        ·
          refine ⟨235053197132000764350773461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313404262842667685801031281 235053197132000764350773461)
          ·
            refine ⟨5509059307781267914471253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 235053197132000764350773461 5509059307781267914471253)
            ·
              refine ⟨32279644381530866686355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5509059307781267914471253 32279644381530866686355)
              ·
                rfl

theorem cell23_5092015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 9].length) (baseStart_5092015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092015 prefixEnd_5092015 := by exact prefixLift 5092015
  have htrace : WordTrace (prefixWord ++ tailWord_5092015) baseStart_5092015 baseEnd_5092015 := by
    simpa [prefixWord, tailWord_5092015, baseEnd_5092015] using wordTrace_append hprefix tailTrace_5092015
  have hstable : (prefixWord ++ tailWord_5092015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092015).length < 2 ^ (prefixWord ++ tailWord_5092015).sum := by decide
  have hdescent : baseEnd_5092015 < baseStart_5092015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092036 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5092036 : Nat := 118140960795 + 5092036 * 2 ^ 59
def prefixEnd_5092036 : Nat := 4983230072969 + 3 ^ 40 * 5092036 * 2
def baseEnd_5092036 : Nat := 871553992665914873144053

theorem tailTrace_5092036 : CollatzResearch.WordTrace tailWord_5092036 prefixEnd_5092036 871553992665914873144053 := by
  unfold tailWord_5092036
  simp only [CollatzResearch.WordTrace]
  refine ⟨92860905290215348678747981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123814540386953798238330641 92860905290215348678747981)
  ·
    refine ⟨34822839483830755754530493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92860905290215348678747981 34822839483830755754530493)
    ·
      refine ⟨13058564806436533407948935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34822839483830755754530493 13058564806436533407948935)
      ·
        refine ⟨19587847209654800111923403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13058564806436533407948935 19587847209654800111923403)
        ·
          refine ⟨29381770814482200167885105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19587847209654800111923403 29381770814482200167885105)
          ·
            refine ⟨22036328110861650125913829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29381770814482200167885105 22036328110861650125913829)
            ·
              refine ⟨4131811520786559398608843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22036328110861650125913829 4131811520786559398608843)
              ·
                refine ⟨6197717281179839097913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131811520786559398608843 6197717281179839097913265)
                ·
                  refine ⟨4648287960884879323434949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197717281179839097913265 4648287960884879323434949)
                  ·
                    refine ⟨871553992665914873144053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648287960884879323434949 871553992665914873144053)
                    ·
                      rfl

theorem cell23_5092036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5092036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092036 prefixEnd_5092036 := by exact prefixLift 5092036
  have htrace : WordTrace (prefixWord ++ tailWord_5092036) baseStart_5092036 baseEnd_5092036 := by
    simpa [prefixWord, tailWord_5092036, baseEnd_5092036] using wordTrace_append hprefix tailTrace_5092036
  have hstable : (prefixWord ++ tailWord_5092036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092036).length < 2 ^ (prefixWord ++ tailWord_5092036).sum := by decide
  have hdescent : baseEnd_5092036 < baseStart_5092036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092046 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_5092046 : Nat := 118140960795 + 5092046 * 2 ^ 59
def prefixEnd_5092046 : Nat := 4983230072969 + 3 ^ 40 * 5092046 * 2
def baseEnd_5092046 : Nat := 2614667112804289580307113

theorem tailTrace_5092046 : CollatzResearch.WordTrace tailWord_5092046 prefixEnd_5092046 2614667112804289580307113 := by
  unfold tailWord_5092046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215271913799308633169999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123814783540262979376906661 23215271913799308633169999)
  ·
    refine ⟨34822907870698962949754999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23215271913799308633169999 34822907870698962949754999)
    ·
      refine ⟨52234361806048444424632499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34822907870698962949754999 52234361806048444424632499)
      ·
        refine ⟨78351542709072666636948749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52234361806048444424632499 78351542709072666636948749)
        ·
          refine ⟨29381828515902249988855781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78351542709072666636948749 29381828515902249988855781)
          ·
            refine ⟨5509092846731671872910459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29381828515902249988855781 5509092846731671872910459)
            ·
              refine ⟨8263639270097507809365689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509092846731671872910459 8263639270097507809365689)
              ·
                refine ⟨6197729452573130857024267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8263639270097507809365689 6197729452573130857024267)
                ·
                  refine ⟨9296594178859696285536401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197729452573130857024267 9296594178859696285536401)
                  ·
                    refine ⟨6972445634144772214152301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9296594178859696285536401 6972445634144772214152301)
                    ·
                      refine ⟨2614667112804289580307113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972445634144772214152301 2614667112804289580307113)
                      ·
                        rfl

theorem cell23_5092046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_5092046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092046 prefixEnd_5092046 := by exact prefixLift 5092046
  have htrace : WordTrace (prefixWord ++ tailWord_5092046) baseStart_5092046 baseEnd_5092046 := by
    simpa [prefixWord, tailWord_5092046, baseEnd_5092046] using wordTrace_append hprefix tailTrace_5092046
  have hstable : (prefixWord ++ tailWord_5092046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092046).length < 2 ^ (prefixWord ++ tailWord_5092046).sum := by decide
  have hdescent : baseEnd_5092046 < baseStart_5092046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092075 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 2, 6]
def baseStart_5092075 : Nat := 118140960795 + 5092075 * 2 ^ 59
def prefixEnd_5092075 : Nat := 4983230072969 + 3 ^ 40 * 5092075 * 2
def baseEnd_5092075 : Nat := 871560667914423322281493

theorem tailTrace_5092075 : CollatzResearch.WordTrace tailWord_5092075 prefixEnd_5092075 871560667914423322281493 := by
  unfold tailWord_5092075
  simp only [CollatzResearch.WordTrace]
  refine ⟨185723233027289407018165679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123815488684859604678777119 185723233027289407018165679)
  ·
    refine ⟨278584849540934110527248519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185723233027289407018165679 278584849540934110527248519)
    ·
      refine ⟨417877274311401165790872779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278584849540934110527248519 417877274311401165790872779)
      ·
        refine ⟨626815911467101748686309169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417877274311401165790872779 626815911467101748686309169)
        ·
          refine ⟨470111933600326311514731877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626815911467101748686309169 470111933600326311514731877)
          ·
            refine ⟨88145987550061183409012227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 470111933600326311514731877 88145987550061183409012227)
            ·
              refine ⟨132218981325091775113518341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88145987550061183409012227 132218981325091775113518341)
              ·
                refine ⟨24791058998454707833784689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132218981325091775113518341 24791058998454707833784689)
                ·
                  refine ⟨18593294248841030875338517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24791058998454707833784689 18593294248841030875338517)
                  ·
                    refine ⟨871560667914423322281493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18593294248841030875338517 871560667914423322281493)
                    ·
                      rfl

theorem cell23_5092075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_5092075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092075 prefixEnd_5092075 := by exact prefixLift 5092075
  have htrace : WordTrace (prefixWord ++ tailWord_5092075) baseStart_5092075 baseEnd_5092075 := by
    simpa [prefixWord, tailWord_5092075, baseEnd_5092075] using wordTrace_append hprefix tailTrace_5092075
  have hstable : (prefixWord ++ tailWord_5092075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092075).length < 2 ^ (prefixWord ++ tailWord_5092075).sum := by decide
  have hdescent : baseEnd_5092075 < baseStart_5092075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092082 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5092082 : Nat := 118140960795 + 5092082 * 2 ^ 59
def prefixEnd_5092082 : Nat := 4983230072969 + 3 ^ 40 * 5092082 * 2
def baseEnd_5092082 : Nat := 2614685598107851439456947

theorem tailTrace_5092082 : CollatzResearch.WordTrace tailWord_5092082 prefixEnd_5092082 2614685598107851439456947 := by
  unfold tailWord_5092082
  simp only [CollatzResearch.WordTrace]
  refine ⟨46430872084566011803417625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123815658892176031475780333 46430872084566011803417625)
  ·
    refine ⟨34823154063424508852563219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46430872084566011803417625 34823154063424508852563219)
    ·
      refine ⟨52234731095136763278844829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34823154063424508852563219 52234731095136763278844829)
      ·
        refine ⟨19588024160676286229566811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52234731095136763278844829 19588024160676286229566811)
        ·
          refine ⟨29382036241014429344350217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19588024160676286229566811 29382036241014429344350217)
          ·
            refine ⟨22036527180760822008262663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29382036241014429344350217 22036527180760822008262663)
            ·
              refine ⟨33054790771141233012393995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22036527180760822008262663 33054790771141233012393995)
              ·
                refine ⟨49582186156711849518590993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33054790771141233012393995 49582186156711849518590993)
                ·
                  refine ⟨37186639617533887138943245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49582186156711849518590993 37186639617533887138943245)
                  ·
                    refine ⟨13944989856575207677103717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37186639617533887138943245 13944989856575207677103717)
                    ·
                      refine ⟨2614685598107851439456947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13944989856575207677103717 2614685598107851439456947)
                      ·
                        rfl

theorem cell23_5092082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5092082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092082 prefixEnd_5092082 := by exact prefixLift 5092082
  have htrace : WordTrace (prefixWord ++ tailWord_5092082) baseStart_5092082 baseEnd_5092082 := by
    simpa [prefixWord, tailWord_5092082, baseEnd_5092082] using wordTrace_append hprefix tailTrace_5092082
  have hstable : (prefixWord ++ tailWord_5092082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092082).length < 2 ^ (prefixWord ++ tailWord_5092082).sum := by decide
  have hdescent : baseEnd_5092082 < baseStart_5092082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092092 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_5092092 : Nat := 118140960795 + 5092092 * 2 ^ 59
def prefixEnd_5092092 : Nat := 4983230072969 + 3 ^ 40 * 5092092 * 2
def baseEnd_5092092 : Nat := 871563577638132133443967

theorem tailTrace_5092092 : CollatzResearch.WordTrace tailWord_5092092 prefixEnd_5092092 871563577638132133443967 := by
  unfold tailWord_5092092
  simp only [CollatzResearch.WordTrace]
  refine ⟨92861926534113909460767265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123815902045485212614356353 92861926534113909460767265)
  ·
    refine ⟨69646444900585432095575449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92861926534113909460767265 69646444900585432095575449)
    ·
      refine ⟨52234833675439074071681587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69646444900585432095575449 52234833675439074071681587)
      ·
        refine ⟨78352250513158611107522381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52234833675439074071681587 78352250513158611107522381)
        ·
          refine ⟨29382093942434479165320893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78352250513158611107522381 29382093942434479165320893)
          ·
            refine ⟨11018285228412929686995335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29382093942434479165320893 11018285228412929686995335)
            ·
              refine ⟨16527427842619394530493003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018285228412929686995335 16527427842619394530493003)
              ·
                refine ⟨24791141763929091795739505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16527427842619394530493003 24791141763929091795739505)
                ·
                  refine ⟨18593356322946818846804629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24791141763929091795739505 18593356322946818846804629)
                  ·
                    refine ⟨871563577638132133443967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18593356322946818846804629 871563577638132133443967)
                    ·
                      rfl

theorem cell23_5092092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_5092092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092092 prefixEnd_5092092 := by exact prefixLift 5092092
  have htrace : WordTrace (prefixWord ++ tailWord_5092092) baseStart_5092092 baseEnd_5092092 := by
    simpa [prefixWord, tailWord_5092092, baseEnd_5092092] using wordTrace_append hprefix tailTrace_5092092
  have hstable : (prefixWord ++ tailWord_5092092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092092).length < 2 ^ (prefixWord ++ tailWord_5092092).sum := by decide
  have hdescent : baseEnd_5092092 < baseStart_5092092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092099 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 6, 2, 2]
def baseStart_5092099 : Nat := 118140960795 + 5092099 * 2 ^ 59
def prefixEnd_5092099 : Nat := 4983230072969 + 3 ^ 40 * 5092099 * 2
def baseEnd_5092099 : Nat := 2614694327278977872944369

theorem tailTrace_5092099 : CollatzResearch.WordTrace tailWord_5092099 prefixEnd_5092099 2614694327278977872944369 := by
  unfold tailWord_5092099
  simp only [CollatzResearch.WordTrace]
  refine ⟨185724108379202459117039351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123816072252801639411359567 185724108379202459117039351)
  ·
    refine ⟨278586162568803688675559027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185724108379202459117039351 278586162568803688675559027)
    ·
      refine ⟨417879243853205533013338541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278586162568803688675559027 417879243853205533013338541)
      ·
        refine ⟨156704716444952074880001953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417879243853205533013338541 156704716444952074880001953)
        ·
          refine ⟨117528537333714056160001465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156704716444952074880001953 117528537333714056160001465)
          ·
            refine ⟨88146403000285542120001099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117528537333714056160001465 88146403000285542120001099)
            ·
              refine ⟨132219604500428313180001649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88146403000285542120001099 132219604500428313180001649)
              ·
                refine ⟨99164703375321234885001237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132219604500428313180001649 99164703375321234885001237)
                ·
                  refine ⟨4648345470718182885234433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99164703375321234885001237 4648345470718182885234433)
                  ·
                    refine ⟨3486259103038637163925825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648345470718182885234433 3486259103038637163925825)
                    ·
                      refine ⟨2614694327278977872944369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486259103038637163925825 2614694327278977872944369)
                      ·
                        rfl

theorem cell23_5092099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_5092099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092099 prefixEnd_5092099 := by exact prefixLift 5092099
  have htrace : WordTrace (prefixWord ++ tailWord_5092099) baseStart_5092099 baseEnd_5092099 := by
    simpa [prefixWord, tailWord_5092099, baseEnd_5092099] using wordTrace_append hprefix tailTrace_5092099
  have hstable : (prefixWord ++ tailWord_5092099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092099).length < 2 ^ (prefixWord ++ tailWord_5092099).sum := by decide
  have hdescent : baseEnd_5092099 < baseStart_5092099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092105 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 9]
def baseStart_5092105 : Nat := 118140960795 + 5092105 * 2 ^ 59
def prefixEnd_5092105 : Nat := 4983230072969 + 3 ^ 40 * 5092105 * 2
def baseEnd_5092105 : Nat := 290521934240322761052149

theorem tailTrace_5092105 : CollatzResearch.WordTrace tailWord_5092105 prefixEnd_5092105 290521934240322761052149 := by
  unfold tailWord_5092105
  simp only [CollatzResearch.WordTrace]
  refine ⟨185724327217180722141757769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123816218144787148094505179 185724327217180722141757769)
  ·
    refine ⟨139293245412885541606318327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185724327217180722141757769 139293245412885541606318327)
    ·
      refine ⟨208939868119328312409477491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139293245412885541606318327 208939868119328312409477491)
      ·
        refine ⟨313409802178992468614216237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208939868119328312409477491 313409802178992468614216237)
        ·
          refine ⟨117528675817122175730331089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313409802178992468614216237 117528675817122175730331089)
          ·
            refine ⟨88146506862841631797748317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117528675817122175730331089 88146506862841631797748317)
            ·
              refine ⟨33054940073565611924155619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88146506862841631797748317 33054940073565611924155619)
              ·
                refine ⟨49582410110348417886233429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33054940073565611924155619 49582410110348417886233429)
                ·
                  refine ⟨290521934240322761052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49582410110348417886233429 290521934240322761052149)
                  ·
                    rfl

theorem cell23_5092105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_5092105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092105 prefixEnd_5092105 := by exact prefixLift 5092105
  have htrace : WordTrace (prefixWord ++ tailWord_5092105) baseStart_5092105 baseEnd_5092105 := by
    simpa [prefixWord, tailWord_5092105, baseEnd_5092105] using wordTrace_append hprefix tailTrace_5092105
  have hstable : (prefixWord ++ tailWord_5092105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092105).length < 2 ^ (prefixWord ++ tailWord_5092105).sum := by decide
  have hdescent : baseEnd_5092105 < baseStart_5092105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092149 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_5092149 : Nat := 118140960795 + 5092149 * 2 ^ 59
def prefixEnd_5092149 : Nat := 4983230072969 + 3 ^ 40 * 5092149 * 2
def baseEnd_5092149 : Nat := 2614720001311702677319139

theorem tailTrace_5092149 : CollatzResearch.WordTrace tailWord_5092149 prefixEnd_5092149 2614720001311702677319139 := by
  unfold tailWord_5092149
  simp only [CollatzResearch.WordTrace]
  refine ⟨185725932029021317656359501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123817288019347545104239667 185725932029021317656359501)
  ·
    refine ⟨69647224510882994121134813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185725932029021317656359501 69647224510882994121134813)
    ·
      refine ⟨26117709191581122795425555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69647224510882994121134813 26117709191581122795425555)
      ·
        refine ⟨39176563787371684193138333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26117709191581122795425555 39176563787371684193138333)
        ·
          refine ⟨14691211420264381572426875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39176563787371684193138333 14691211420264381572426875)
          ·
            refine ⟨22036817130396572358640313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14691211420264381572426875 22036817130396572358640313)
            ·
              refine ⟨16527612847797429268980235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22036817130396572358640313 16527612847797429268980235)
              ·
                refine ⟨24791419271696143903470353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16527612847797429268980235 24791419271696143903470353)
                ·
                  refine ⟨18593564453772107927602765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24791419271696143903470353 18593564453772107927602765)
                  ·
                    refine ⟨6972586670164540472851037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18593564453772107927602765 6972586670164540472851037)
                    ·
                      refine ⟨2614720001311702677319139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972586670164540472851037 2614720001311702677319139)
                      ·
                        rfl

theorem cell23_5092149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_5092149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092149 prefixEnd_5092149 := by exact prefixLift 5092149
  have htrace : WordTrace (prefixWord ++ tailWord_5092149) baseStart_5092149 baseEnd_5092149 := by
    simpa [prefixWord, tailWord_5092149, baseEnd_5092149] using wordTrace_append hprefix tailTrace_5092149
  have hstable : (prefixWord ++ tailWord_5092149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092149).length < 2 ^ (prefixWord ++ tailWord_5092149).sum := by decide
  have hdescent : baseEnd_5092149 < baseStart_5092149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092150 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5092150 : Nat := 118140960795 + 5092150 * 2 ^ 59
def prefixEnd_5092150 : Nat := 4983230072969 + 3 ^ 40 * 5092150 * 2
def baseEnd_5092150 : Nat := 2614720514792357173406635

theorem tailTrace_5092150 : CollatzResearch.WordTrace tailWord_5092150 prefixEnd_5092150 2614720514792357173406635 := by
  unfold tailWord_5092150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11607873031376105926696619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123817312334678463218097269 11607873031376105926696619)
  ·
    refine ⟨17411809547064158890044929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11607873031376105926696619 17411809547064158890044929)
    ·
      refine ⟨13058857160298119167533697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17411809547064158890044929 13058857160298119167533697)
      ·
        refine ⟨9794142870223589375650273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13058857160298119167533697 9794142870223589375650273)
        ·
          refine ⟨7345607152667692031737705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9794142870223589375650273 7345607152667692031737705)
          ·
            refine ⟨5509205364500769023803279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7345607152667692031737705 5509205364500769023803279)
            ·
              refine ⟨8263808046751153535704919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509205364500769023803279 8263808046751153535704919)
              ·
                refine ⟨12395712070126730303557379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263808046751153535704919 12395712070126730303557379)
                ·
                  refine ⟨18593568105190095455336069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12395712070126730303557379 18593568105190095455336069)
                  ·
                    refine ⟨3486294019723142897875513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18593568105190095455336069 3486294019723142897875513)
                    ·
                      refine ⟨2614720514792357173406635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486294019723142897875513 2614720514792357173406635)
                      ·
                        rfl

theorem cell23_5092150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5092150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092150 prefixEnd_5092150 := by exact prefixLift 5092150
  have htrace : WordTrace (prefixWord ++ tailWord_5092150) baseStart_5092150 baseEnd_5092150 := by
    simpa [prefixWord, tailWord_5092150, baseEnd_5092150] using wordTrace_append hprefix tailTrace_5092150
  have hstable : (prefixWord ++ tailWord_5092150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092150).length < 2 ^ (prefixWord ++ tailWord_5092150).sum := by decide
  have hdescent : baseEnd_5092150 < baseStart_5092150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092249 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 5, 2]
def baseStart_5092249 : Nat := 118140960795 + 5092249 * 2 ^ 59
def prefixEnd_5092249 : Nat := 4983230072969 + 3 ^ 40 * 5092249 * 2
def baseEnd_5092249 : Nat := 2614771349377152286068679

theorem tailTrace_5092249 : CollatzResearch.WordTrace tailWord_5092249 prefixEnd_5092249 2614771349377152286068679 := by
  unfold tailWord_5092249
  simp only [CollatzResearch.WordTrace]
  refine ⟨185729579328659034734999801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123819719552439356489999867 185729579328659034734999801)
  ·
    refine ⟨139297184496494276051249851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185729579328659034734999801 139297184496494276051249851)
    ·
      refine ⟨208945776744741414076874777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139297184496494276051249851 208945776744741414076874777)
      ·
        refine ⟨156709332558556060557656083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208945776744741414076874777 156709332558556060557656083)
        ·
          refine ⟨235063998837834090836484125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156709332558556060557656083 235063998837834090836484125)
          ·
            refine ⟨88148999564187784063681547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235063998837834090836484125 88148999564187784063681547)
            ·
              refine ⟨132223499346281676095522321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88148999564187784063681547 132223499346281676095522321)
              ·
                refine ⟨99167624509711257071641741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132223499346281676095522321 99167624509711257071641741)
                ·
                  refine ⟨37187859191141721401865653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99167624509711257071641741 37187859191141721401865653)
                  ·
                    refine ⟨3486361799169536381424905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37187859191141721401865653 3486361799169536381424905)
                    ·
                      refine ⟨2614771349377152286068679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486361799169536381424905 2614771349377152286068679)
                      ·
                        rfl

theorem cell23_5092249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_5092249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092249 prefixEnd_5092249 := by exact prefixLift 5092249
  have htrace : WordTrace (prefixWord ++ tailWord_5092249) baseStart_5092249 baseEnd_5092249 := by
    simpa [prefixWord, tailWord_5092249, baseEnd_5092249] using wordTrace_append hprefix tailTrace_5092249
  have hstable : (prefixWord ++ tailWord_5092249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092249).length < 2 ^ (prefixWord ++ tailWord_5092249).sum := by decide
  have hdescent : baseEnd_5092249 < baseStart_5092249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092273 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5092273 : Nat := 118140960795 + 5092273 * 2 ^ 59
def prefixEnd_5092273 : Nat := 4983230072969 + 3 ^ 40 * 5092273 * 2
def baseEnd_5092273 : Nat := 2614783672912860192168569

theorem tailTrace_5092273 : CollatzResearch.WordTrace tailWord_5092273 prefixEnd_5092273 2614783672912860192168569 := by
  unfold tailWord_5092273
  simp only [CollatzResearch.WordTrace]
  refine ⟨185730454680572086833873473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123820303120381391222582315 185730454680572086833873473)
  ·
    refine ⟨139297841010429065125405105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185730454680572086833873473 139297841010429065125405105)
    ·
      refine ⟨104473380757821798844053829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139297841010429065125405105 104473380757821798844053829)
      ·
        refine ⟨19588758892091587283260093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104473380757821798844053829 19588758892091587283260093)
        ·
          refine ⟨7345784584534345231222535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19588758892091587283260093 7345784584534345231222535)
          ·
            refine ⟨11018676876801517846833803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345784584534345231222535 11018676876801517846833803)
            ·
              refine ⟨16528015315202276770250705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018676876801517846833803 16528015315202276770250705)
              ·
                refine ⟨12396011486401707577688029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16528015315202276770250705 12396011486401707577688029)
                ·
                  refine ⟨4648504307400640341633011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12396011486401707577688029 4648504307400640341633011)
                  ·
                    refine ⟨6972756461100960512449517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648504307400640341633011 6972756461100960512449517)
                    ·
                      refine ⟨2614783672912860192168569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972756461100960512449517 2614783672912860192168569)
                      ·
                        rfl

theorem cell23_5092273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5092273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092273 prefixEnd_5092273 := by exact prefixLift 5092273
  have htrace : WordTrace (prefixWord ++ tailWord_5092273) baseStart_5092273 baseEnd_5092273 := by
    simpa [prefixWord, tailWord_5092273, baseEnd_5092273] using wordTrace_append hprefix tailTrace_5092273
  have hstable : (prefixWord ++ tailWord_5092273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092273).length < 2 ^ (prefixWord ++ tailWord_5092273).sum := by decide
  have hdescent : baseEnd_5092273 < baseStart_5092273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092279 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_5092279 : Nat := 118140960795 + 5092279 * 2 ^ 59
def prefixEnd_5092279 : Nat := 4983230072969 + 3 ^ 40 * 5092279 * 2
def baseEnd_5092279 : Nat := 2614786753796787168693541

theorem tailTrace_5092279 : CollatzResearch.WordTrace tailWord_5092279 prefixEnd_5092279 2614786753796787168693541 := by
  unfold tailWord_5092279
  simp only [CollatzResearch.WordTrace]
  refine ⟨185730673518550349858591891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123820449012366899905727927 185730673518550349858591891)
  ·
    refine ⟨278596010277825524787887837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185730673518550349858591891 278596010277825524787887837)
    ·
      refine ⟨104473503854184571795457939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278596010277825524787887837 104473503854184571795457939)
      ·
        refine ⟨156710255781276857693186909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104473503854184571795457939 156710255781276857693186909)
        ·
          refine ⟨58766345917978821634945091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156710255781276857693186909 58766345917978821634945091)
          ·
            refine ⟨88149518876968232452417637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58766345917978821634945091 88149518876968232452417637)
            ·
              refine ⟨16528034789431543584828307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88149518876968232452417637 16528034789431543584828307)
              ·
                refine ⟨24792052184147315377242461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16528034789431543584828307 24792052184147315377242461)
                ·
                  refine ⟨9297019569055243266465923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24792052184147315377242461 9297019569055243266465923)
                  ·
                    refine ⟨13945529353582864899698885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9297019569055243266465923 13945529353582864899698885)
                    ·
                      refine ⟨2614786753796787168693541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13945529353582864899698885 2614786753796787168693541)
                      ·
                        rfl

theorem cell23_5092279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_5092279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092279 prefixEnd_5092279 := by exact prefixLift 5092279
  have htrace : WordTrace (prefixWord ++ tailWord_5092279) baseStart_5092279 baseEnd_5092279 := by
    simpa [prefixWord, tailWord_5092279, baseEnd_5092279] using wordTrace_append hprefix tailTrace_5092279
  have hstable : (prefixWord ++ tailWord_5092279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092279).length < 2 ^ (prefixWord ++ tailWord_5092279).sum := by decide
  have hdescent : baseEnd_5092279 < baseStart_5092279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092313 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 3, 2, 2]
def baseStart_5092313 : Nat := 118140960795 + 5092313 * 2 ^ 59
def prefixEnd_5092313 : Nat := 4983230072969 + 3 ^ 40 * 5092313 * 2
def baseEnd_5092313 : Nat := 2614804212139040035668385

theorem tailTrace_5092313 : CollatzResearch.WordTrace tailWord_5092313 prefixEnd_5092313 2614804212139040035668385 := by
  unfold tailWord_5092313
  simp only [CollatzResearch.WordTrace]
  refine ⟨185731913600427173665329593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123821275733618115776886395 185731913600427173665329593)
  ·
    refine ⟨139298935200320380248997195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185731913600427173665329593 139298935200320380248997195)
    ·
      refine ⟨208948402800480570373495793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139298935200320380248997195 208948402800480570373495793)
      ·
        refine ⟨156711302100360427780121845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208948402800480570373495793 156711302100360427780121845)
        ·
          refine ⟨14691684571908790104386423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156711302100360427780121845 14691684571908790104386423)
          ·
            refine ⟨22037526857863185156579635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14691684571908790104386423 22037526857863185156579635)
            ·
              refine ⟨33056290286794777734869453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22037526857863185156579635 33056290286794777734869453)
              ·
                refine ⟨12396108857548041650576045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33056290286794777734869453 12396108857548041650576045)
                ·
                  refine ⟨4648540821580515618966017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12396108857548041650576045 4648540821580515618966017)
                  ·
                    refine ⟨3486405616185386714224513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648540821580515618966017 3486405616185386714224513)
                    ·
                      refine ⟨2614804212139040035668385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486405616185386714224513 2614804212139040035668385)
                      ·
                        rfl

theorem cell23_5092313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_5092313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092313 prefixEnd_5092313 := by exact prefixLift 5092313
  have htrace : WordTrace (prefixWord ++ tailWord_5092313) baseStart_5092313 baseEnd_5092313 := by
    simpa [prefixWord, tailWord_5092313, baseEnd_5092313] using wordTrace_append hprefix tailTrace_5092313
  have hstable : (prefixWord ++ tailWord_5092313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092313).length < 2 ^ (prefixWord ++ tailWord_5092313).sum := by decide
  have hdescent : baseEnd_5092313 < baseStart_5092313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092323 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 2, 4]
def baseStart_5092323 : Nat := 118140960795 + 5092323 * 2 ^ 59
def prefixEnd_5092323 : Nat := 4983230072969 + 3 ^ 40 * 5092323 * 2
def baseEnd_5092323 : Nat := 871603115648528332181113

theorem tailTrace_5092323 : CollatzResearch.WordTrace tailWord_5092323 prefixEnd_5092323 871603115648528332181113 := by
  unfold tailWord_5092323
  simp only [CollatzResearch.WordTrace]
  refine ⟨185732278330390945373193623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123821518886927296915462415 185732278330390945373193623)
  ·
    refine ⟨278598417495586418059790435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185732278330390945373193623 278598417495586418059790435)
    ·
      refine ⟨417897626243379627089685653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278598417495586418059790435 417897626243379627089685653)
      ·
        refine ⟨19588951230158420019829015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 417897626243379627089685653 19588951230158420019829015)
        ·
          refine ⟨29383426845237630029743523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19588951230158420019829015 29383426845237630029743523)
          ·
            refine ⟨44075140267856445044615285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29383426845237630029743523 44075140267856445044615285)
            ·
              refine ⟨4132044400111541722932683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44075140267856445044615285 4132044400111541722932683)
              ·
                refine ⟨6198066600167312584399025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132044400111541722932683 6198066600167312584399025)
                ·
                  refine ⟨4648549950125484438299269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6198066600167312584399025 4648549950125484438299269)
                  ·
                    refine ⟨871603115648528332181113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648549950125484438299269 871603115648528332181113)
                    ·
                      rfl

theorem cell23_5092323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 4].length) (baseStart_5092323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092323 prefixEnd_5092323 := by exact prefixLift 5092323
  have htrace : WordTrace (prefixWord ++ tailWord_5092323) baseStart_5092323 baseEnd_5092323 := by
    simpa [prefixWord, tailWord_5092323, baseEnd_5092323] using wordTrace_append hprefix tailTrace_5092323
  have hstable : (prefixWord ++ tailWord_5092323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092323).length < 2 ^ (prefixWord ++ tailWord_5092323).sum := by decide
  have hdescent : baseEnd_5092323 < baseStart_5092323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092341 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5092341 : Nat := 118140960795 + 5092341 * 2 ^ 59
def prefixEnd_5092341 : Nat := 4983230072969 + 3 ^ 40 * 5092341 * 2
def baseEnd_5092341 : Nat := 2614818589597365926118257

theorem tailTrace_5092341 : CollatzResearch.WordTrace tailWord_5092341 prefixEnd_5092341 2614818589597365926118257 := by
  unfold tailWord_5092341
  simp only [CollatzResearch.WordTrace]
  refine ⟨185732934844325734447348877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123821956562883822964899251 185732934844325734447348877)
  ·
    refine ⟨69649850566622150417755829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185732934844325734447348877 69649850566622150417755829)
    ·
      refine ⟨6529673490620826601664609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69649850566622150417755829 6529673490620826601664609)
      ·
        refine ⟨4897255117965619951248457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6529673490620826601664609 4897255117965619951248457)
        ·
          refine ⟨3672941338474214963436343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4897255117965619951248457 3672941338474214963436343)
          ·
            refine ⟨5509412007711322445154515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672941338474214963436343 5509412007711322445154515)
            ·
              refine ⟨8264118011566983667731773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509412007711322445154515 8264118011566983667731773)
              ·
                refine ⟨3099044254337618875399415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8264118011566983667731773 3099044254337618875399415)
                ·
                  refine ⟨4648566381506428313099123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099044254337618875399415 4648566381506428313099123)
                  ·
                    refine ⟨6972849572259642469648685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648566381506428313099123 6972849572259642469648685)
                    ·
                      refine ⟨2614818589597365926118257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972849572259642469648685 2614818589597365926118257)
                      ·
                        rfl

theorem cell23_5092341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5092341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092341 prefixEnd_5092341 := by exact prefixLift 5092341
  have htrace : WordTrace (prefixWord ++ tailWord_5092341) baseStart_5092341 baseEnd_5092341 := by
    simpa [prefixWord, tailWord_5092341, baseEnd_5092341] using wordTrace_append hprefix tailTrace_5092341
  have hstable : (prefixWord ++ tailWord_5092341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092341).length < 2 ^ (prefixWord ++ tailWord_5092341).sum := by decide
  have hdescent : baseEnd_5092341 < baseStart_5092341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092359 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5092359 : Nat := 118140960795 + 5092359 * 2 ^ 59
def prefixEnd_5092359 : Nat := 4983230072969 + 3 ^ 40 * 5092359 * 2
def baseEnd_5092359 : Nat := 2614827832249146855693173

theorem tailTrace_5092359 : CollatzResearch.WordTrace tailWord_5092359 prefixEnd_5092359 2614827832249146855693173 := by
  unfold tailWord_5092359
  simp only [CollatzResearch.WordTrace]
  refine ⟨185733591358260523521504131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123822394238840349014336087 185733591358260523521504131)
  ·
    refine ⟨278600387037390785282256197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185733591358260523521504131 278600387037390785282256197)
    ·
      refine ⟨52237572569510772240423037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278600387037390785282256197 52237572569510772240423037)
      ·
        refine ⟨19589089713566539590158639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52237572569510772240423037 19589089713566539590158639)
        ·
          refine ⟨29383634570349809385237959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19589089713566539590158639 29383634570349809385237959)
          ·
            refine ⟨44075451855524714077856939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29383634570349809385237959 44075451855524714077856939)
            ·
              refine ⟨66113177783287071116785409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44075451855524714077856939 66113177783287071116785409)
              ·
                refine ⟨49584883337465303337589057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66113177783287071116785409 49584883337465303337589057)
                ·
                  refine ⟨37188662503098977503191793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49584883337465303337589057 37188662503098977503191793)
                  ·
                    refine ⟨27891496877324233127393845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37188662503098977503191793 27891496877324233127393845)
                    ·
                      refine ⟨2614827832249146855693173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27891496877324233127393845 2614827832249146855693173)
                      ·
                        rfl

theorem cell23_5092359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5092359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092359 prefixEnd_5092359 := by exact prefixLift 5092359
  have htrace : WordTrace (prefixWord ++ tailWord_5092359) baseStart_5092359 baseEnd_5092359 := by
    simpa [prefixWord, tailWord_5092359, baseEnd_5092359] using wordTrace_append hprefix tailTrace_5092359
  have hstable : (prefixWord ++ tailWord_5092359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092359).length < 2 ^ (prefixWord ++ tailWord_5092359).sum := by decide
  have hdescent : baseEnd_5092359 < baseStart_5092359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092370 : List Nat := [3, 2, 5, 1, 1, 1, 2, 8]
def baseStart_5092370 : Nat := 118140960795 + 5092370 * 2 ^ 59
def prefixEnd_5092370 : Nat := 4983230072969 + 3 ^ 40 * 5092370 * 2
def baseEnd_5092370 : Nat := 96845684464309122690949

theorem tailTrace_5092370 : CollatzResearch.WordTrace tailWord_5092370 prefixEnd_5092370 96845684464309122690949 := by
  unfold tailWord_5092370
  simp only [CollatzResearch.WordTrace]
  refine ⟨46433498140305168100038641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123822661707480448266769709 46433498140305168100038641)
  ·
    refine ⟨34825123605228876075028981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46433498140305168100038641 34825123605228876075028981)
    ·
      refine ⟨3264855337990207132033967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34825123605228876075028981 3264855337990207132033967)
      ·
        refine ⟨4897283006985310698050951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264855337990207132033967 4897283006985310698050951)
        ·
          refine ⟨7345924510477966047076427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897283006985310698050951 7345924510477966047076427)
          ·
            refine ⟨11018886765716949070614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345924510477966047076427 11018886765716949070614641)
            ·
              refine ⟨8264165074287711802960981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11018886765716949070614641 8264165074287711802960981)
              ·
                refine ⟨96845684464309122690949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8264165074287711802960981 96845684464309122690949)
                ·
                  rfl

theorem cell23_5092370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_5092370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092370 prefixEnd_5092370 := by exact prefixLift 5092370
  have htrace : WordTrace (prefixWord ++ tailWord_5092370) baseStart_5092370 baseEnd_5092370 := by
    simpa [prefixWord, tailWord_5092370, baseEnd_5092370] using wordTrace_append hprefix tailTrace_5092370
  have hstable : (prefixWord ++ tailWord_5092370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092370).length < 2 ^ (prefixWord ++ tailWord_5092370).sum := by decide
  have hdescent : baseEnd_5092370 < baseStart_5092370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092380 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_5092380 : Nat := 118140960795 + 5092380 * 2 ^ 59
def prefixEnd_5092380 : Nat := 4983230072969 + 3 ^ 40 * 5092380 * 2
def baseEnd_5092380 : Nat := 2614838615342891273530577

theorem tailTrace_5092380 : CollatzResearch.WordTrace tailWord_5092380 prefixEnd_5092380 2614838615342891273530577 := by
  unfold tailWord_5092380
  simp only [CollatzResearch.WordTrace]
  refine ⟨92867178645592222054009297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123822904860789629405345729 92867178645592222054009297)
  ·
    refine ⟨69650383984194166540506973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92867178645592222054009297 69650383984194166540506973)
    ·
      refine ⟨26118893994072812452690115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69650383984194166540506973 26118893994072812452690115)
      ·
        refine ⟨39178340991109218679035173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26118893994072812452690115 39178340991109218679035173)
        ·
          refine ⟨7345938935832978502319095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39178340991109218679035173 7345938935832978502319095)
          ·
            refine ⟨11018908403749467753478643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345938935832978502319095 11018908403749467753478643)
            ·
              refine ⟨16528362605624201630217965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018908403749467753478643 16528362605624201630217965)
              ·
                refine ⟨6198135977109075611331737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16528362605624201630217965 6198135977109075611331737)
                ·
                  refine ⟨4648601982831806708498803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6198135977109075611331737 4648601982831806708498803)
                  ·
                    refine ⟨6972902974247710062748205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648601982831806708498803 6972902974247710062748205)
                    ·
                      refine ⟨2614838615342891273530577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972902974247710062748205 2614838615342891273530577)
                      ·
                        rfl

theorem cell23_5092380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_5092380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092380 prefixEnd_5092380 := by exact prefixLift 5092380
  have htrace : WordTrace (prefixWord ++ tailWord_5092380) baseStart_5092380 baseEnd_5092380 := by
    simpa [prefixWord, tailWord_5092380, baseEnd_5092380] using wordTrace_append hprefix tailTrace_5092380
  have hstable : (prefixWord ++ tailWord_5092380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092380).length < 2 ^ (prefixWord ++ tailWord_5092380).sum := by decide
  have hdescent : baseEnd_5092380 < baseStart_5092380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092389 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_5092389 : Nat := 118140960795 + 5092389 * 2 ^ 59
def prefixEnd_5092389 : Nat := 4983230072969 + 3 ^ 40 * 5092389 * 2
def baseEnd_5092389 : Nat := 2614843236668781738318035

theorem tailTrace_5092389 : CollatzResearch.WordTrace tailWord_5092389 prefixEnd_5092389 2614843236668781738318035 := by
  unfold tailWord_5092389
  simp only [CollatzResearch.WordTrace]
  refine ⟨185734685548151838645096221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123823123698767892430064147 185734685548151838645096221)
  ·
    refine ⟨69650507080556939491911083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185734685548151838645096221 69650507080556939491911083)
    ·
      refine ⟨104475760620835409237866625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69650507080556939491911083 104475760620835409237866625)
      ·
        refine ⟨78356820465626556928399969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104475760620835409237866625 78356820465626556928399969)
        ·
          refine ⟨58767615349219917696299977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78356820465626556928399969 58767615349219917696299977)
          ·
            refine ⟨44075711511914938272224983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58767615349219917696299977 44075711511914938272224983)
            ·
              refine ⟨66113567267872407408337475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44075711511914938272224983 66113567267872407408337475)
              ·
                refine ⟨99170350901808611112506213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66113567267872407408337475 99170350901808611112506213)
                ·
                  refine ⟨18594440794089114583594915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99170350901808611112506213 18594440794089114583594915)
                  ·
                    refine ⟨27891661191133671875392373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18594440794089114583594915 27891661191133671875392373)
                    ·
                      refine ⟨2614843236668781738318035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27891661191133671875392373 2614843236668781738318035)
                      ·
                        rfl

theorem cell23_5092389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_5092389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092389 prefixEnd_5092389 := by exact prefixLift 5092389
  have htrace : WordTrace (prefixWord ++ tailWord_5092389) baseStart_5092389 baseEnd_5092389 := by
    simpa [prefixWord, tailWord_5092389, baseEnd_5092389] using wordTrace_append hprefix tailTrace_5092389
  have hstable : (prefixWord ++ tailWord_5092389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092389).length < 2 ^ (prefixWord ++ tailWord_5092389).sum := by decide
  have hdescent : baseEnd_5092389 < baseStart_5092389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092436 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_5092436 : Nat := 118140960795 + 5092436 * 2 ^ 59
def prefixEnd_5092436 : Nat := 4983230072969 + 3 ^ 40 * 5092436 * 2
def baseEnd_5092436 : Nat := 2614867370259543054430319

theorem tailTrace_5092436 : CollatzResearch.WordTrace tailWord_5092436 prefixEnd_5092436 2614867370259543054430319 := by
  unfold tailWord_5092436
  simp only [CollatzResearch.WordTrace]
  refine ⟨92868199889490782836028581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123824266519321043781371441 92868199889490782836028581)
  ·
    refine ⟨17412787479279521781755359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92868199889490782836028581 17412787479279521781755359)
    ·
      refine ⟨26119181218919282672633039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17412787479279521781755359 26119181218919282672633039)
      ·
        refine ⟨39178771828378924008949559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26119181218919282672633039 39178771828378924008949559)
        ·
          refine ⟨58768157742568386013424339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39178771828378924008949559 58768157742568386013424339)
          ·
            refine ⟨88152236613852579020136509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58768157742568386013424339 88152236613852579020136509)
            ·
              refine ⟨33057088730194717132551191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88152236613852579020136509 33057088730194717132551191)
              ·
                refine ⟨49585633095292075698826787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33057088730194717132551191 49585633095292075698826787)
                ·
                  refine ⟨74378449642938113548240181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49585633095292075698826787 74378449642938113548240181)
                  ·
                    refine ⟨6972979654025448145147517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74378449642938113548240181 6972979654025448145147517)
                    ·
                      refine ⟨2614867370259543054430319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6972979654025448145147517 2614867370259543054430319)
                      ·
                        rfl

theorem cell23_5092436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_5092436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092436 prefixEnd_5092436 := by exact prefixLift 5092436
  have htrace : WordTrace (prefixWord ++ tailWord_5092436) baseStart_5092436 baseEnd_5092436 := by
    simpa [prefixWord, tailWord_5092436, baseEnd_5092436] using wordTrace_append hprefix tailTrace_5092436
  have hstable : (prefixWord ++ tailWord_5092436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092436).length < 2 ^ (prefixWord ++ tailWord_5092436).sum := by decide
  have hdescent : baseEnd_5092436 < baseStart_5092436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092439 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 7]
def baseStart_5092439 : Nat := 118140960795 + 5092439 * 2 ^ 59
def prefixEnd_5092439 : Nat := 4983230072969 + 3 ^ 40 * 5092439 * 2
def baseEnd_5092439 : Nat := 871622970233835514230935

theorem tailTrace_5092439 : CollatzResearch.WordTrace tailWord_5092439 prefixEnd_5092439 871622970233835514230935 := by
  unfold tailWord_5092439
  simp only [CollatzResearch.WordTrace]
  refine ⟨185736509197970697184416371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123824339465313798122944247 185736509197970697184416371)
  ·
    refine ⟨278604763796956045776624557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185736509197970697184416371 278604763796956045776624557)
    ·
      refine ⟨104476786423858517166234209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278604763796956045776624557 104476786423858517166234209)
      ·
        refine ⟨78357589817893887874675657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104476786423858517166234209 78357589817893887874675657)
        ·
          refine ⟨58768192363420415906006743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78357589817893887874675657 58768192363420415906006743)
          ·
            refine ⟨88152288545130623859010115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58768192363420415906006743 88152288545130623859010115)
            ·
              refine ⟨132228432817695935788515173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88152288545130623859010115 132228432817695935788515173)
              ·
                refine ⟨24792831153317987960346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132228432817695935788515173 24792831153317987960346595)
                ·
                  refine ⟨37189246729976981940519893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24792831153317987960346595 37189246729976981940519893)
                  ·
                    refine ⟨871622970233835514230935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37189246729976981940519893 871622970233835514230935)
                    ·
                      rfl

theorem cell23_5092439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_5092439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092439 prefixEnd_5092439 := by exact prefixLift 5092439
  have htrace : WordTrace (prefixWord ++ tailWord_5092439) baseStart_5092439 baseEnd_5092439 := by
    simpa [prefixWord, tailWord_5092439, baseEnd_5092439] using wordTrace_append hprefix tailTrace_5092439
  have hstable : (prefixWord ++ tailWord_5092439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092439).length < 2 ^ (prefixWord ++ tailWord_5092439).sum := by decide
  have hdescent : baseEnd_5092439 < baseStart_5092439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092449 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_5092449 : Nat := 118140960795 + 5092449 * 2 ^ 59
def prefixEnd_5092449 : Nat := 4983230072969 + 3 ^ 40 * 5092449 * 2
def baseEnd_5092449 : Nat := 2614874045508051503567759

theorem tailTrace_5092449 : CollatzResearch.WordTrace tailWord_5092449 prefixEnd_5092449 2614874045508051503567759 := by
  unfold tailWord_5092449
  simp only [CollatzResearch.WordTrace]
  refine ⟨185736873927934468892280401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123824582618622979261520267 185736873927934468892280401)
  ·
    refine ⟨139302655445950851669210301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185736873927934468892280401 139302655445950851669210301)
    ·
      refine ⟨52238495792231569375953863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139302655445950851669210301 52238495792231569375953863)
      ·
        refine ⟨78357743688347354063930795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52238495792231569375953863 78357743688347354063930795)
        ·
          refine ⟨117536615532521031095896193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78357743688347354063930795 117536615532521031095896193)
          ·
            refine ⟨88152461649390773321922145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117536615532521031095896193 88152461649390773321922145)
            ·
              refine ⟨66114346237043079991441609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88152461649390773321922145 66114346237043079991441609)
              ·
                refine ⟨49585759677782309993581207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66114346237043079991441609 49585759677782309993581207)
                ·
                  refine ⟨74378639516673464990371811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49585759677782309993581207 74378639516673464990371811)
                  ·
                    refine ⟨111567959275010197485557717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74378639516673464990371811 111567959275010197485557717)
                    ·
                      refine ⟨2614874045508051503567759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111567959275010197485557717 2614874045508051503567759)
                      ·
                        rfl

theorem cell23_5092449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_5092449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092449 prefixEnd_5092449 := by exact prefixLift 5092449
  have htrace : WordTrace (prefixWord ++ tailWord_5092449) baseStart_5092449 baseEnd_5092449 := by
    simpa [prefixWord, tailWord_5092449, baseEnd_5092449] using wordTrace_append hprefix tailTrace_5092449
  have hstable : (prefixWord ++ tailWord_5092449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092449).length < 2 ^ (prefixWord ++ tailWord_5092449).sum := by decide
  have hdescent : baseEnd_5092449 < baseStart_5092449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092476 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_5092476 : Nat := 118140960795 + 5092476 * 2 ^ 59
def prefixEnd_5092476 : Nat := 4983230072969 + 3 ^ 40 * 5092476 * 2
def baseEnd_5092476 : Nat := 2614887909485722897930135

theorem tailTrace_5092476 : CollatzResearch.WordTrace tailWord_5092476 prefixEnd_5092476 2614887909485722897930135 := by
  unfold tailWord_5092476
  simp only [CollatzResearch.WordTrace]
  refine ⟨92868929349418326251756641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123825239132557768335675521 92868929349418326251756641)
  ·
    refine ⟨69651697012063744688817481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92868929349418326251756641 69651697012063744688817481)
    ·
      refine ⟨52238772759047808516613111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69651697012063744688817481 52238772759047808516613111)
      ·
        refine ⟨78358159138571712774919667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52238772759047808516613111 78358159138571712774919667)
        ·
          refine ⟨117537238707857569162379501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78358159138571712774919667 117537238707857569162379501)
          ·
            refine ⟨44076464515446588435892313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117537238707857569162379501 44076464515446588435892313)
            ·
              refine ⟨33057348386584941326919235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44076464515446588435892313 33057348386584941326919235)
              ·
                refine ⟨49586022579877411990378853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33057348386584941326919235 49586022579877411990378853)
                ·
                  refine ⟨9297379233727014748196035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49586022579877411990378853 9297379233727014748196035)
                  ·
                    refine ⟨13946068850590522122294053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9297379233727014748196035 13946068850590522122294053)
                    ·
                      refine ⟨2614887909485722897930135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13946068850590522122294053 2614887909485722897930135)
                      ·
                        rfl

theorem cell23_5092476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_5092476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092476 prefixEnd_5092476 := by exact prefixLift 5092476
  have htrace : WordTrace (prefixWord ++ tailWord_5092476) baseStart_5092476 baseEnd_5092476 := by
    simpa [prefixWord, tailWord_5092476, baseEnd_5092476] using wordTrace_append hprefix tailTrace_5092476
  have hstable : (prefixWord ++ tailWord_5092476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092476).length < 2 ^ (prefixWord ++ tailWord_5092476).sum := by decide
  have hdescent : baseEnd_5092476 < baseStart_5092476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092496 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_5092496 : Nat := 118140960795 + 5092496 * 2 ^ 59
def prefixEnd_5092496 : Nat := 4983230072969 + 3 ^ 40 * 5092496 * 2
def baseEnd_5092496 : Nat := 2614898179098812819680043

theorem tailTrace_5092496 : CollatzResearch.WordTrace tailWord_5092496 prefixEnd_5092496 2614898179098812819680043 := by
  unfold tailWord_5092496
  simp only [CollatzResearch.WordTrace]
  refine ⟨92869294079382097959620671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123825725439176130612827561 92869294079382097959620671)
  ·
    refine ⟨139303941119073146939431007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92869294079382097959620671 139303941119073146939431007)
    ·
      refine ⟨208955911678609720409146511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139303941119073146939431007 208955911678609720409146511)
      ·
        refine ⟨313433867517914580613719767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208955911678609720409146511 313433867517914580613719767)
        ·
          refine ⟨470150801276871870920579651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313433867517914580613719767 470150801276871870920579651)
          ·
            refine ⟨705226201915307806380869477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470150801276871870920579651 705226201915307806380869477)
            ·
              refine ⟨132229912859120213696413027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 705226201915307806380869477 132229912859120213696413027)
              ·
                refine ⟨198344869288680320544619541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132229912859120213696413027 198344869288680320544619541)
                ·
                  refine ⟨9297415747906890025529041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 198344869288680320544619541 9297415747906890025529041)
                  ·
                    refine ⟨6973061810930167519146781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9297415747906890025529041 6973061810930167519146781)
                    ·
                      refine ⟨2614898179098812819680043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973061810930167519146781 2614898179098812819680043)
                      ·
                        rfl

theorem cell23_5092496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_5092496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092496 prefixEnd_5092496 := by exact prefixLift 5092496
  have htrace : WordTrace (prefixWord ++ tailWord_5092496) baseStart_5092496 baseEnd_5092496 := by
    simpa [prefixWord, tailWord_5092496, baseEnd_5092496] using wordTrace_append hprefix tailTrace_5092496
  have hstable : (prefixWord ++ tailWord_5092496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092496).length < 2 ^ (prefixWord ++ tailWord_5092496).sum := by decide
  have hdescent : baseEnd_5092496 < baseStart_5092496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092503 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 3, 4]
def baseStart_5092503 : Nat := 118140960795 + 5092503 * 2 ^ 59
def prefixEnd_5092503 : Nat := 4983230072969 + 3 ^ 40 * 5092503 * 2
def baseEnd_5092503 : Nat := 871633924487798097430837

theorem tailTrace_5092503 : CollatzResearch.WordTrace tailWord_5092503 prefixEnd_5092503 871633924487798097430837 := by
  unfold tailWord_5092503
  simp only [CollatzResearch.WordTrace]
  refine ⟨185738843469738836114746163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123825895646492557409830775 185738843469738836114746163)
  ·
    refine ⟨278608265204608254172119245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185738843469738836114746163 278608265204608254172119245)
    ·
      refine ⟨104478099451728095314544717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278608265204608254172119245 104478099451728095314544717)
      ·
        refine ⟨39179287294398035742954269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104478099451728095314544717 39179287294398035742954269)
        ·
          refine ⟨14692232735399263403607851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39179287294398035742954269 14692232735399263403607851)
          ·
            refine ⟨22038349103098895105411777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14692232735399263403607851 22038349103098895105411777)
            ·
              refine ⟨16528761827324171329058833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22038349103098895105411777 16528761827324171329058833)
              ·
                refine ⟨12396571370493128496794125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16528761827324171329058833 12396571370493128496794125)
                ·
                  refine ⟨4648714263934923186297797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12396571370493128496794125 4648714263934923186297797)
                  ·
                    refine ⟨871633924487798097430837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648714263934923186297797 871633924487798097430837)
                    ·
                      rfl

theorem cell23_5092503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_5092503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092503 prefixEnd_5092503 := by exact prefixLift 5092503
  have htrace : WordTrace (prefixWord ++ tailWord_5092503) baseStart_5092503 baseEnd_5092503 := by
    simpa [prefixWord, tailWord_5092503, baseEnd_5092503] using wordTrace_append hprefix tailTrace_5092503
  have hstable : (prefixWord ++ tailWord_5092503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092503).length < 2 ^ (prefixWord ++ tailWord_5092503).sum := by decide
  have hdescent : baseEnd_5092503 < baseStart_5092503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092513 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5092513 : Nat := 118140960795 + 5092513 * 2 ^ 59
def prefixEnd_5092513 : Nat := 4983230072969 + 3 ^ 40 * 5092513 * 2
def baseEnd_5092513 : Nat := 2614906908269939253167465

theorem tailTrace_5092513 : CollatzResearch.WordTrace tailWord_5092513 prefixEnd_5092513 2614906908269939253167465 := by
  unfold tailWord_5092513
  simp only [CollatzResearch.WordTrace]
  refine ⟨185739208199702607822610193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123826138799801738548406795 185739208199702607822610193)
  ·
    refine ⟨139304406149776955866957645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185739208199702607822610193 139304406149776955866957645)
    ·
      refine ⟨52239152306166358450109117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139304406149776955866957645 52239152306166358450109117)
      ·
        refine ⟨19589682114812384418790919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52239152306166358450109117 19589682114812384418790919)
        ·
          refine ⟨29384523172218576628186379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19589682114812384418790919 29384523172218576628186379)
          ·
            refine ⟨44076784758327864942279569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29384523172218576628186379 44076784758327864942279569)
            ·
              refine ⟨33057588568745898706709677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44076784758327864942279569 33057588568745898706709677)
              ·
                refine ⟨12396595713279712015016129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33057588568745898706709677 12396595713279712015016129)
                ·
                  refine ⟨9297446784959784011262097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12396595713279712015016129 9297446784959784011262097)
                  ·
                    refine ⟨6973085088719838008446573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9297446784959784011262097 6973085088719838008446573)
                    ·
                      refine ⟨2614906908269939253167465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973085088719838008446573 2614906908269939253167465)
                      ·
                        rfl

theorem cell23_5092513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5092513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092513 prefixEnd_5092513 := by exact prefixLift 5092513
  have htrace : WordTrace (prefixWord ++ tailWord_5092513) baseStart_5092513 baseEnd_5092513 := by
    simpa [prefixWord, tailWord_5092513, baseEnd_5092513] using wordTrace_append hprefix tailTrace_5092513
  have hstable : (prefixWord ++ tailWord_5092513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092513).length < 2 ^ (prefixWord ++ tailWord_5092513).sum := by decide
  have hdescent : baseEnd_5092513 < baseStart_5092513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092516 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 8]
def baseStart_5092516 : Nat := 118140960795 + 5092516 * 2 ^ 59
def prefixEnd_5092516 : Nat := 4983230072969 + 3 ^ 40 * 5092516 * 2
def baseEnd_5092516 : Nat := 290545383190211415714439

theorem tailTrace_5092516 : CollatzResearch.WordTrace tailWord_5092516 prefixEnd_5092516 290545383190211415714439 := by
  unfold tailWord_5092516
  simp only [CollatzResearch.WordTrace]
  refine ⟨92869658809345869667484701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123826211745794492889979601 92869658809345869667484701)
  ·
    refine ⟨34826122053504701125306763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92869658809345869667484701 34826122053504701125306763)
    ·
      refine ⟨52239183080257051687960145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34826122053504701125306763 52239183080257051687960145)
      ·
        refine ⟨39179387310192788765970109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52239183080257051687960145 39179387310192788765970109)
        ·
          refine ⟨14692270241322295787238791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39179387310192788765970109 14692270241322295787238791)
          ·
            refine ⟨22038405361983443680858187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14692270241322295787238791 22038405361983443680858187)
            ·
              refine ⟨33057608042975165521287281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22038405361983443680858187 33057608042975165521287281)
              ·
                refine ⟨24793206032231374140965461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33057608042975165521287281 24793206032231374140965461)
                ·
                  refine ⟨290545383190211415714439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24793206032231374140965461 290545383190211415714439)
                  ·
                    rfl

theorem cell23_5092516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_5092516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092516 prefixEnd_5092516 := by exact prefixLift 5092516
  have htrace : WordTrace (prefixWord ++ tailWord_5092516) baseStart_5092516 baseEnd_5092516 := by
    simpa [prefixWord, tailWord_5092516, baseEnd_5092516] using wordTrace_append hprefix tailTrace_5092516
  have hstable : (prefixWord ++ tailWord_5092516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092516).length < 2 ^ (prefixWord ++ tailWord_5092516).sum := by decide
  have hdescent : baseEnd_5092516 < baseStart_5092516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092537 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 1, 4]
def baseStart_5092537 : Nat := 118140960795 + 5092537 * 2 ^ 59
def prefixEnd_5092537 : Nat := 4983230072969 + 3 ^ 40 * 5092537 * 2
def baseEnd_5092537 : Nat := 871639743935215719755785

theorem tailTrace_5092537 : CollatzResearch.WordTrace tailWord_5092537 prefixEnd_5092537 871639743935215719755785 := by
  unfold tailWord_5092537
  simp only [CollatzResearch.WordTrace]
  refine ⟨185740083551615659921483865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123826722367743773280989243 185740083551615659921483865)
  ·
    refine ⟨139305062663711744941112899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185740083551615659921483865 139305062663711744941112899)
    ·
      refine ⟨208957593995567617411669349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139305062663711744941112899 208957593995567617411669349)
      ·
        refine ⟨39179548874168928264688003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208957593995567617411669349 39179548874168928264688003)
        ·
          refine ⟨58769323311253392397032005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39179548874168928264688003 58769323311253392397032005)
          ·
            refine ⟨11019248120860011074443501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58769323311253392397032005 11019248120860011074443501)
            ·
              refine ⟨4132218045322504152916313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11019248120860011074443501 4132218045322504152916313)
              ·
                refine ⟨3099163533991878114687235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132218045322504152916313 3099163533991878114687235)
                ·
                  refine ⟨4648745300987817172030853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099163533991878114687235 4648745300987817172030853)
                  ·
                    refine ⟨871639743935215719755785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648745300987817172030853 871639743935215719755785)
                    ·
                      rfl

theorem cell23_5092537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 4].length) (baseStart_5092537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092537 prefixEnd_5092537 := by exact prefixLift 5092537
  have htrace : WordTrace (prefixWord ++ tailWord_5092537) baseStart_5092537 baseEnd_5092537 := by
    simpa [prefixWord, tailWord_5092537, baseEnd_5092537] using wordTrace_append hprefix tailTrace_5092537
  have hstable : (prefixWord ++ tailWord_5092537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092537).length < 2 ^ (prefixWord ++ tailWord_5092537).sum := by decide
  have hdescent : baseEnd_5092537 < baseStart_5092537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092576 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_5092576 : Nat := 118140960795 + 5092576 * 2 ^ 59
def prefixEnd_5092576 : Nat := 4983230072969 + 3 ^ 40 * 5092576 * 2
def baseEnd_5092576 : Nat := 871646419183724168893225

theorem tailTrace_5092576 : CollatzResearch.WordTrace tailWord_5092576 prefixEnd_5092576 871646419183724168893225 := by
  unfold tailWord_5092576
  simp only [CollatzResearch.WordTrace]
  refine ⟨92870752999237184791076791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123827670665649579721435721 92870752999237184791076791)
  ·
    refine ⟨139306129498855777186615187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92870752999237184791076791 139306129498855777186615187)
    ·
      refine ⟨208959194248283665779922781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139306129498855777186615187 208959194248283665779922781)
      ·
        refine ⟨78359697843106374667471043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208959194248283665779922781 78359697843106374667471043)
        ·
          refine ⟨117539546764659562001206565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78359697843106374667471043 117539546764659562001206565)
          ·
            refine ⟨22038665018373667875226231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117539546764659562001206565 22038665018373667875226231)
            ·
              refine ⟨33057997527560501812839347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22038665018373667875226231 33057997527560501812839347)
              ·
                refine ⟨49586996291340752719259021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33057997527560501812839347 49586996291340752719259021)
                ·
                  refine ⟨18595123609252782269722133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49586996291340752719259021 18595123609252782269722133)
                  ·
                    refine ⟨871646419183724168893225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18595123609252782269722133 871646419183724168893225)
                    ·
                      rfl

theorem cell23_5092576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_5092576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092576 prefixEnd_5092576 := by exact prefixLift 5092576
  have htrace : WordTrace (prefixWord ++ tailWord_5092576) baseStart_5092576 baseEnd_5092576 := by
    simpa [prefixWord, tailWord_5092576, baseEnd_5092576] using wordTrace_append hprefix tailTrace_5092576
  have hstable : (prefixWord ++ tailWord_5092576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092576).length < 2 ^ (prefixWord ++ tailWord_5092576).sum := by decide
  have hdescent : baseEnd_5092576 < baseStart_5092576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092594 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5092594 : Nat := 118140960795 + 5092594 * 2 ^ 59
def prefixEnd_5092594 : Nat := 4983230072969 + 3 ^ 40 * 5092594 * 2
def baseEnd_5092594 : Nat := 2614948500202953436254593

theorem tailTrace_5092594 : CollatzResearch.WordTrace tailWord_5092594 prefixEnd_5092594 2614948500202953436254593 := by
  unfold tailWord_5092594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435540628102289664077209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123828108341606105770872557 46435540628102289664077209)
  ·
    refine ⟨34826655471076717248057907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46435540628102289664077209 34826655471076717248057907)
    ·
      refine ⟨52239983206615075872086861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34826655471076717248057907 52239983206615075872086861)
      ·
        refine ⟨19589993702480653452032573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52239983206615075872086861 19589993702480653452032573)
        ·
          refine ⟨7346247638430245044512215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19589993702480653452032573 7346247638430245044512215)
          ·
            refine ⟨11019371457645367566768323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346247638430245044512215 11019371457645367566768323)
            ·
              refine ⟨16529057186468051350152485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019371457645367566768323 16529057186468051350152485)
              ·
                refine ⟨3099198222462759628153591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16529057186468051350152485 3099198222462759628153591)
                ·
                  refine ⟨4648797333694139442230387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099198222462759628153591 4648797333694139442230387)
                  ·
                    refine ⟨6973196000541209163345581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648797333694139442230387 6973196000541209163345581)
                    ·
                      refine ⟨2614948500202953436254593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973196000541209163345581 2614948500202953436254593)
                      ·
                        rfl

theorem cell23_5092594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5092594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092594 prefixEnd_5092594 := by exact prefixLift 5092594
  have htrace : WordTrace (prefixWord ++ tailWord_5092594) baseStart_5092594 baseEnd_5092594 := by
    simpa [prefixWord, tailWord_5092594, baseEnd_5092594] using wordTrace_append hprefix tailTrace_5092594
  have hstable : (prefixWord ++ tailWord_5092594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092594).length < 2 ^ (prefixWord ++ tailWord_5092594).sum := by decide
  have hdescent : baseEnd_5092594 < baseStart_5092594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092613 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_5092613 : Nat := 118140960795 + 5092613 * 2 ^ 59
def prefixEnd_5092613 : Nat := 4983230072969 + 3 ^ 40 * 5092613 * 2
def baseEnd_5092613 : Nat := 2614958256335388861917005

theorem tailTrace_5092613 : CollatzResearch.WordTrace tailWord_5092613 prefixEnd_5092613 2614958256335388861917005 := by
  unfold tailWord_5092613
  simp only [CollatzResearch.WordTrace]
  refine ⟨185742855499340324901250493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123828570332893549934166995 185742855499340324901250493)
  ·
    refine ⟨69653570812252621837968935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185742855499340324901250493 69653570812252621837968935)
    ·
      refine ⟨104480356218378932756953403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69653570812252621837968935 104480356218378932756953403)
      ·
        refine ⟨156720534327568399135430105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104480356218378932756953403 156720534327568399135430105)
        ·
          refine ⟨117540400745676299351572579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156720534327568399135430105 117540400745676299351572579)
          ·
            refine ⟨176310601118514449027358869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117540400745676299351572579 176310601118514449027358869)
            ·
              refine ⟨8264559427430364798157447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 176310601118514449027358869 8264559427430364798157447)
              ·
                refine ⟨12396839141145547197236171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8264559427430364798157447 12396839141145547197236171)
                ·
                  refine ⟨18595258711718320795854257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12396839141145547197236171 18595258711718320795854257)
                  ·
                    refine ⟨13946444033788740596890693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18595258711718320795854257 13946444033788740596890693)
                    ·
                      refine ⟨2614958256335388861917005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13946444033788740596890693 2614958256335388861917005)
                      ·
                        rfl

theorem cell23_5092613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_5092613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092613 prefixEnd_5092613 := by exact prefixLift 5092613
  have htrace : WordTrace (prefixWord ++ tailWord_5092613) baseStart_5092613 baseEnd_5092613 := by
    simpa [prefixWord, tailWord_5092613, baseEnd_5092613] using wordTrace_append hprefix tailTrace_5092613
  have hstable : (prefixWord ++ tailWord_5092613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092613).length < 2 ^ (prefixWord ++ tailWord_5092613).sum := by decide
  have hdescent : baseEnd_5092613 < baseStart_5092613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092634 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2]
def baseStart_5092634 : Nat := 118140960795 + 5092634 * 2 ^ 59
def prefixEnd_5092634 : Nat := 4983230072969 + 3 ^ 40 * 5092634 * 2
def baseEnd_5092634 : Nat := 2614969039429133279754409

theorem tailTrace_5092634 : CollatzResearch.WordTrace tailWord_5092634 prefixEnd_5092634 2614969039429133279754409 := by
  unfold tailWord_5092634
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435905358066061371941239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123829080954842830325176637 46435905358066061371941239)
  ·
    refine ⟨69653858037099092057911859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46435905358066061371941239 69653858037099092057911859)
    ·
      refine ⟨104480787055648638086867789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69653858037099092057911859 104480787055648638086867789)
      ·
        refine ⟨39180295145868239282575421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104480787055648638086867789 39180295145868239282575421)
        ·
          refine ⟨14692610679700589730965783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39180295145868239282575421 14692610679700589730965783)
          ·
            refine ⟨22038916019550884596448675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14692610679700589730965783 22038916019550884596448675)
            ·
              refine ⟨33058374029326326894673013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22038916019550884596448675 33058374029326326894673013)
              ·
                refine ⟨3099222565249343146375595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33058374029326326894673013 3099222565249343146375595)
                ·
                  refine ⟨4648833847874014719563393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099222565249343146375595 4648833847874014719563393)
                  ·
                    refine ⟨3486625385905511039672545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648833847874014719563393 3486625385905511039672545)
                    ·
                      refine ⟨2614969039429133279754409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486625385905511039672545 2614969039429133279754409)
                      ·
                        rfl

theorem cell23_5092634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_5092634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092634 prefixEnd_5092634 := by exact prefixLift 5092634
  have htrace : WordTrace (prefixWord ++ tailWord_5092634) baseStart_5092634 baseEnd_5092634 := by
    simpa [prefixWord, tailWord_5092634, baseEnd_5092634] using wordTrace_append hprefix tailTrace_5092634
  have hstable : (prefixWord ++ tailWord_5092634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092634).length < 2 ^ (prefixWord ++ tailWord_5092634).sum := by decide
  have hdescent : baseEnd_5092634 < baseStart_5092634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092637 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5092637 : Nat := 118140960795 + 5092637 * 2 ^ 59
def prefixEnd_5092637 : Nat := 4983230072969 + 3 ^ 40 * 5092637 * 2
def baseEnd_5092637 : Nat := 2614970579871096768016895

theorem tailTrace_5092637 : CollatzResearch.WordTrace tailWord_5092637 prefixEnd_5092637 2614970579871096768016895 := by
  unfold tailWord_5092637
  simp only [CollatzResearch.WordTrace]
  refine ⟨185743730851253377000124165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123829153900835584666749443 185743730851253377000124165)
  ·
    refine ⟨34826949534610008187523281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185743730851253377000124165 34826949534610008187523281)
    ·
      refine ⟨26120212150957506140642461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34826949534610008187523281 26120212150957506140642461)
      ·
        refine ⟨9795079556609064802740923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26120212150957506140642461 9795079556609064802740923)
        ·
          refine ⟨14692619334913597204111385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795079556609064802740923 14692619334913597204111385)
          ·
            refine ⟨11019464501185197903083539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14692619334913597204111385 11019464501185197903083539)
            ·
              refine ⟨16529196751777796854625309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019464501185197903083539 16529196751777796854625309)
              ·
                refine ⟨6198448781916673820484491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16529196751777796854625309 6198448781916673820484491)
                ·
                  refine ⟨9297673172875010730726737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6198448781916673820484491 9297673172875010730726737)
                  ·
                    refine ⟨6973254879656258048045053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9297673172875010730726737 6973254879656258048045053)
                    ·
                      refine ⟨2614970579871096768016895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973254879656258048045053 2614970579871096768016895)
                      ·
                        rfl

theorem cell23_5092637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5092637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092637 prefixEnd_5092637 := by exact prefixLift 5092637
  have htrace : WordTrace (prefixWord ++ tailWord_5092637) baseStart_5092637 baseEnd_5092637 := by
    simpa [prefixWord, tailWord_5092637, baseEnd_5092637] using wordTrace_append hprefix tailTrace_5092637
  have hstable : (prefixWord ++ tailWord_5092637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092637).length < 2 ^ (prefixWord ++ tailWord_5092637).sum := by decide
  have hdescent : baseEnd_5092637 < baseStart_5092637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092685 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5092685 : Nat := 118140960795 + 5092685 * 2 ^ 59
def prefixEnd_5092685 : Nat := 4983230072969 + 3 ^ 40 * 5092685 * 2
def baseEnd_5092685 : Nat := 2614995226942512580216675

theorem tailTrace_5092685 : CollatzResearch.WordTrace tailWord_5092685 prefixEnd_5092685 2614995226942512580216675 := by
  unfold tailWord_5092685
  simp only [CollatzResearch.WordTrace]
  refine ⟨185745481555079481197871509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123830321036719654131914339 185745481555079481197871509)
  ·
    refine ⟨8706819447894350681150227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 185745481555079481197871509 8706819447894350681150227)
    ·
      refine ⟨13060229171841526021725341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8706819447894350681150227 13060229171841526021725341)
      ·
        refine ⟨4897585939440572258147003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13060229171841526021725341 4897585939440572258147003)
        ·
          refine ⟨7346378909160858387220505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897585939440572258147003 7346378909160858387220505)
          ·
            refine ⟨5509784181870643790415379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7346378909160858387220505 5509784181870643790415379)
            ·
              refine ⟨8264676272805965685623069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509784181870643790415379 8264676272805965685623069)
              ·
                refine ⟨3099253602302237132108651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8264676272805965685623069 3099253602302237132108651)
                ·
                  refine ⟨4648880403453355698162977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099253602302237132108651 4648880403453355698162977)
                  ·
                    refine ⟨3486660302590016773622233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648880403453355698162977 3486660302590016773622233)
                    ·
                      refine ⟨2614995226942512580216675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486660302590016773622233 2614995226942512580216675)
                      ·
                        rfl

theorem cell23_5092685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5092685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092685 prefixEnd_5092685 := by exact prefixLift 5092685
  have htrace : WordTrace (prefixWord ++ tailWord_5092685) baseStart_5092685 baseEnd_5092685 := by
    simpa [prefixWord, tailWord_5092685, baseEnd_5092685] using wordTrace_append hprefix tailTrace_5092685
  have hstable : (prefixWord ++ tailWord_5092685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092685).length < 2 ^ (prefixWord ++ tailWord_5092685).sum := by decide
  have hdescent : baseEnd_5092685 < baseStart_5092685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092690 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_5092690 : Nat := 118140960795 + 5092690 * 2 ^ 59
def prefixEnd_5092690 : Nat := 4983230072969 + 3 ^ 40 * 5092690 * 2
def baseEnd_5092690 : Nat := 2614997794345785060654151

theorem tailTrace_5092690 : CollatzResearch.WordTrace tailWord_5092690 prefixEnd_5092690 2614997794345785060654151 := by
  unfold tailWord_5092690
  simp only [CollatzResearch.WordTrace]
  refine ⟨46436415980015341762950881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123830442613374244701202349 46436415980015341762950881)
  ·
    refine ⟨34827311985011506322213161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46436415980015341762950881 34827311985011506322213161)
    ·
      refine ⟨26120483988758629741659871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34827311985011506322213161 26120483988758629741659871)
      ·
        refine ⟨39180725983137944612489807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26120483988758629741659871 39180725983137944612489807)
        ·
          refine ⟨58771088974706916918734711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39180725983137944612489807 58771088974706916918734711)
          ·
            refine ⟨88156633462060375378102067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58771088974706916918734711 88156633462060375378102067)
            ·
              refine ⟨132234950193090563067153101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88156633462060375378102067 132234950193090563067153101)
              ·
                refine ⟨49588106322408961150182413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132234950193090563067153101 49588106322408961150182413)
                ·
                  refine ⟨18595539870903360431318405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49588106322408961150182413 18595539870903360431318405)
                  ·
                    refine ⟨3486663725794380080872201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18595539870903360431318405 3486663725794380080872201)
                    ·
                      refine ⟨2614997794345785060654151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486663725794380080872201 2614997794345785060654151)
                      ·
                        rfl

theorem cell23_5092690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_5092690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092690 prefixEnd_5092690 := by exact prefixLift 5092690
  have htrace : WordTrace (prefixWord ++ tailWord_5092690) baseStart_5092690 baseEnd_5092690 := by
    simpa [prefixWord, tailWord_5092690, baseEnd_5092690] using wordTrace_append hprefix tailTrace_5092690
  have hstable : (prefixWord ++ tailWord_5092690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092690).length < 2 ^ (prefixWord ++ tailWord_5092690).sum := by decide
  have hdescent : baseEnd_5092690 < baseStart_5092690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092693 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5092693 : Nat := 118140960795 + 5092693 * 2 ^ 59
def prefixEnd_5092693 : Nat := 4983230072969 + 3 ^ 40 * 5092693 * 2
def baseEnd_5092693 : Nat := 2614999334787748548916637

theorem tailTrace_5092693 : CollatzResearch.WordTrace tailWord_5092693 prefixEnd_5092693 2614999334787748548916637 := by
  unfold tailWord_5092693
  simp only [CollatzResearch.WordTrace]
  refine ⟨185745773339050498564162733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123830515559366999042775155 185745773339050498564162733)
  ·
    refine ⟨69654665002143936961561025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185745773339050498564162733 69654665002143936961561025)
    ·
      refine ⟨52240998751607952721170769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69654665002143936961561025 52240998751607952721170769)
      ·
        refine ⟨39180749063705964540878077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52240998751607952721170769 39180749063705964540878077)
        ·
          refine ⟨14692780898889736702829279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39180749063705964540878077 14692780898889736702829279)
          ·
            refine ⟨22039171348334605054243919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14692780898889736702829279 22039171348334605054243919)
            ·
              refine ⟨33058757022501907581365879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22039171348334605054243919 33058757022501907581365879)
              ·
                refine ⟨49588135533752861372048819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33058757022501907581365879 49588135533752861372048819)
                ·
                  refine ⟨74382203300629292058073229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49588135533752861372048819 74382203300629292058073229)
                  ·
                    refine ⟨27893326237735984521777461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74382203300629292058073229 27893326237735984521777461)
                    ·
                      refine ⟨2614999334787748548916637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27893326237735984521777461 2614999334787748548916637)
                      ·
                        rfl

theorem cell23_5092693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5092693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092693 prefixEnd_5092693 := by exact prefixLift 5092693
  have htrace : WordTrace (prefixWord ++ tailWord_5092693) baseStart_5092693 baseEnd_5092693 := by
    simpa [prefixWord, tailWord_5092693, baseEnd_5092693] using wordTrace_append hprefix tailTrace_5092693
  have hstable : (prefixWord ++ tailWord_5092693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092693).length < 2 ^ (prefixWord ++ tailWord_5092693).sum := by decide
  have hdescent : baseEnd_5092693 < baseStart_5092693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092707 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 4, 2, 2]
def baseStart_5092707 : Nat := 118140960795 + 5092707 * 2 ^ 59
def prefixEnd_5092707 : Nat := 4983230072969 + 3 ^ 40 * 5092707 * 2
def baseEnd_5092707 : Nat := 2615006523516911494141573

theorem tailTrace_5092707 : CollatzResearch.WordTrace tailWord_5092707 prefixEnd_5092707 2615006523516911494141573 := by
  unfold tailWord_5092707
  simp only [CollatzResearch.WordTrace]
  refine ⟨185746283960999778955172375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123830855973999852636781583 185746283960999778955172375)
  ·
    refine ⟨278619425941499668432758563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185746283960999778955172375 278619425941499668432758563)
    ·
      refine ⟨417929138912249502649137845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278619425941499668432758563 417929138912249502649137845)
      ·
        refine ⟨39180856773023390873356673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 417929138912249502649137845 39180856773023390873356673)
        ·
          refine ⟨29385642579767543155017505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39180856773023390873356673 29385642579767543155017505)
          ·
            refine ⟨22039231934825657366263129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29385642579767543155017505 22039231934825657366263129)
            ·
              refine ⟨16529423951119243024697347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22039231934825657366263129 16529423951119243024697347)
              ·
                refine ⟨24794135926678864537046021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16529423951119243024697347 24794135926678864537046021)
                ·
                  refine ⟨4648900486252287100696129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24794135926678864537046021 4648900486252287100696129)
                  ·
                    refine ⟨3486675364689215325522097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648900486252287100696129 3486675364689215325522097)
                    ·
                      refine ⟨2615006523516911494141573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486675364689215325522097 2615006523516911494141573)
                      ·
                        rfl

theorem cell23_5092707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_5092707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092707 prefixEnd_5092707 := by exact prefixLift 5092707
  have htrace : WordTrace (prefixWord ++ tailWord_5092707) baseStart_5092707 baseEnd_5092707 := by
    simpa [prefixWord, tailWord_5092707, baseEnd_5092707] using wordTrace_append hprefix tailTrace_5092707
  have hstable : (prefixWord ++ tailWord_5092707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092707).length < 2 ^ (prefixWord ++ tailWord_5092707).sum := by decide
  have hdescent : baseEnd_5092707 < baseStart_5092707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092718 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5092718 : Nat := 118140960795 + 5092718 * 2 ^ 59
def prefixEnd_5092718 : Nat := 4983230072969 + 3 ^ 40 * 5092718 * 2
def baseEnd_5092718 : Nat := 2615012171804110951104023

theorem tailTrace_5092718 : CollatzResearch.WordTrace tailWord_5092718 prefixEnd_5092718 2615012171804110951104023 := by
  unfold tailWord_5092718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23218335645494990979227851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123831123442639951889215205 23218335645494990979227851)
  ·
    refine ⟨34827503468242486468841777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23218335645494990979227851 34827503468242486468841777)
    ·
      refine ⟨26120627601181864851631333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34827503468242486468841777 26120627601181864851631333)
      ·
        refine ⟨4897617675221599659680875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26120627601181864851631333 4897617675221599659680875)
        ·
          refine ⟨7346426512832399489521313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897617675221599659680875 7346426512832399489521313)
          ·
            refine ⟨5509819884624299617140985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7346426512832399489521313 5509819884624299617140985)
            ·
              refine ⟨4132364913468224712855739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5509819884624299617140985 4132364913468224712855739)
              ·
                refine ⟨6198547370202337069283609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132364913468224712855739 6198547370202337069283609)
                ·
                  refine ⟨4648910527651752801962707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6198547370202337069283609 4648910527651752801962707)
                  ·
                    refine ⟨6973365791477629202944061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648910527651752801962707 6973365791477629202944061)
                    ·
                      refine ⟨2615012171804110951104023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973365791477629202944061 2615012171804110951104023)
                      ·
                        rfl

theorem cell23_5092718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5092718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092718 prefixEnd_5092718 := by exact prefixLift 5092718
  have htrace : WordTrace (prefixWord ++ tailWord_5092718) baseStart_5092718 baseEnd_5092718 := by
    simpa [prefixWord, tailWord_5092718, baseEnd_5092718] using wordTrace_append hprefix tailTrace_5092718
  have hstable : (prefixWord ++ tailWord_5092718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092718).length < 2 ^ (prefixWord ++ tailWord_5092718).sum := by decide
  have hdescent : baseEnd_5092718 < baseStart_5092718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092764 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 5]
def baseStart_5092764 : Nat := 118140960795 + 5092764 * 2 ^ 59
def prefixEnd_5092764 : Nat := 4983230072969 + 3 ^ 40 * 5092764 * 2
def baseEnd_5092764 : Nat := 290559532434913085680979

theorem tailTrace_5092764 : CollatzResearch.WordTrace tailWord_5092764 prefixEnd_5092764 290559532434913085680979 := by
  unfold tailWord_5092764
  simp only [CollatzResearch.WordTrace]
  refine ⟨92874181460896638844998673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123832241947862185126664897 92874181460896638844998673)
  ·
    refine ⟨69655636095672479133749005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92874181460896638844998673 69655636095672479133749005)
    ·
      refine ⟨26120863535877179675155877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69655636095672479133749005 26120863535877179675155877)
      ·
        refine ⟨4897661912976971189091727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26120863535877179675155877 4897661912976971189091727)
        ·
          refine ⟨7346492869465456783637591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897661912976971189091727 7346492869465456783637591)
          ·
            refine ⟨11019739304198185175456387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346492869465456783637591 11019739304198185175456387)
            ·
              refine ⟨16529608956297277763184581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019739304198185175456387 16529608956297277763184581)
              ·
                refine ⟨3099301679305739580597109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16529608956297277763184581 3099301679305739580597109)
                ·
                  refine ⟨290559532434913085680979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3099301679305739580597109 290559532434913085680979)
                  ·
                    rfl

theorem cell23_5092764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_5092764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092764 prefixEnd_5092764 := by exact prefixLift 5092764
  have htrace : WordTrace (prefixWord ++ tailWord_5092764) baseStart_5092764 baseEnd_5092764 := by
    simpa [prefixWord, tailWord_5092764, baseEnd_5092764] using wordTrace_append hprefix tailTrace_5092764
  have hstable : (prefixWord ++ tailWord_5092764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092764).length < 2 ^ (prefixWord ++ tailWord_5092764).sum := by decide
  have hdescent : baseEnd_5092764 < baseStart_5092764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092770 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5092770 : Nat := 118140960795 + 5092770 * 2 ^ 59
def prefixEnd_5092770 : Nat := 4983230072969 + 3 ^ 40 * 5092770 * 2
def baseEnd_5092770 : Nat := 2615038872798144747653783

theorem tailTrace_5092770 : CollatzResearch.WordTrace tailWord_5092770 prefixEnd_5092770 2615038872798144747653783 := by
  unfold tailWord_5092770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46437145439942885178678941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123832387839847693809810509 46437145439942885178678941)
  ·
    refine ⟨17413929539978581942004603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46437145439942885178678941 17413929539978581942004603)
    ·
      refine ⟨26120894309967872913006905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17413929539978581942004603 26120894309967872913006905)
      ·
        refine ⟨19590670732475904684755179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26120894309967872913006905 19590670732475904684755179)
        ·
          refine ⟨29386006098713857027132769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19590670732475904684755179 29386006098713857027132769)
          ·
            refine ⟨22039504574035392770349577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29386006098713857027132769 22039504574035392770349577)
            ·
              refine ⟨16529628430526544577762183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22039504574035392770349577 16529628430526544577762183)
              ·
                refine ⟨24794442645789816866643275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16529628430526544577762183 24794442645789816866643275)
                ·
                  refine ⟨37191663968684725299964913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24794442645789816866643275 37191663968684725299964913)
                  ·
                    refine ⟨27893747976513543974973685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37191663968684725299964913 27893747976513543974973685)
                    ·
                      refine ⟨2615038872798144747653783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27893747976513543974973685 2615038872798144747653783)
                      ·
                        rfl

theorem cell23_5092770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5092770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092770 prefixEnd_5092770 := by exact prefixLift 5092770
  have htrace : WordTrace (prefixWord ++ tailWord_5092770) baseStart_5092770 baseEnd_5092770 := by
    simpa [prefixWord, tailWord_5092770, baseEnd_5092770] using wordTrace_append hprefix tailTrace_5092770
  have hstable : (prefixWord ++ tailWord_5092770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092770).length < 2 ^ (prefixWord ++ tailWord_5092770).sum := by decide
  have hdescent : baseEnd_5092770 < baseStart_5092770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092780 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_5092780 : Nat := 118140960795 + 5092780 * 2 ^ 59
def prefixEnd_5092780 : Nat := 4983230072969 + 3 ^ 40 * 5092780 * 2
def baseEnd_5092780 : Nat := 2615044007604689708528737

theorem tailTrace_5092780 : CollatzResearch.WordTrace tailWord_5092780 prefixEnd_5092780 2615044007604689708528737 := by
  unfold tailWord_5092780
  simp only [CollatzResearch.WordTrace]
  refine ⟨92874473244867656211289897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123832630993156874948386529 92874473244867656211289897)
  ·
    refine ⟨69655854933650742158467423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92874473244867656211289897 69655854933650742158467423)
    ·
      refine ⟨104483782400476113237701135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69655854933650742158467423 104483782400476113237701135)
      ·
        refine ⟨156725673600714169856551703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104483782400476113237701135 156725673600714169856551703)
        ·
          refine ⟨235088510401071254784827555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156725673600714169856551703 235088510401071254784827555)
          ·
            refine ⟨352632765601606882177241333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235088510401071254784827555 352632765601606882177241333)
            ·
              refine ⟨33059321775150645204116375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352632765601606882177241333 33059321775150645204116375)
              ·
                refine ⟨49588982662725967806174563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33059321775150645204116375 49588982662725967806174563)
                ·
                  refine ⟨74383473994088951709261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49588982662725967806174563 74383473994088951709261845)
                  ·
                    refine ⟨3486725343472919611371649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74383473994088951709261845 3486725343472919611371649)
                    ·
                      refine ⟨2615044007604689708528737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486725343472919611371649 2615044007604689708528737)
                      ·
                        rfl

theorem cell23_5092780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_5092780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092780 prefixEnd_5092780 := by exact prefixLift 5092780
  have htrace : WordTrace (prefixWord ++ tailWord_5092780) baseStart_5092780 baseEnd_5092780 := by
    simpa [prefixWord, tailWord_5092780, baseEnd_5092780] using wordTrace_append hprefix tailTrace_5092780
  have hstable : (prefixWord ++ tailWord_5092780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092780).length < 2 ^ (prefixWord ++ tailWord_5092780).sum := by decide
  have hdescent : baseEnd_5092780 < baseStart_5092780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092847 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 3]
def baseStart_5092847 : Nat := 118140960795 + 5092847 * 2 ^ 59
def prefixEnd_5092847 : Nat := 4983230072969 + 3 ^ 40 * 5092847 * 2
def baseEnd_5092847 : Nat := 2615078410808540946390929

theorem tailTrace_5092847 : CollatzResearch.WordTrace tailWord_5092847 prefixEnd_5092847 2615078410808540946390929 := by
  unfold tailWord_5092847
  simp only [CollatzResearch.WordTrace]
  refine ⟨185751390180492582865268795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123834260120328388576845863 185751390180492582865268795)
  ·
    refine ⟨278627085270738874297903193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185751390180492582865268795 278627085270738874297903193)
    ·
      refine ⟨208970313953054155723427395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278627085270738874297903193 208970313953054155723427395)
      ·
        refine ⟨313455470929581233585141093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208970313953054155723427395 313455470929581233585141093)
        ·
          refine ⟨58772900799296481297213955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313455470929581233585141093 58772900799296481297213955)
          ·
            refine ⟨88159351198944721945820933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58772900799296481297213955 88159351198944721945820933)
            ·
              refine ⟨16529878349802135364841425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88159351198944721945820933 16529878349802135364841425)
              ·
                refine ⟨12397408762351601523631069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16529878349802135364841425 12397408762351601523631069)
                ·
                  refine ⟨4649028285881850571361651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12397408762351601523631069 4649028285881850571361651)
                  ·
                    refine ⟨6973542428822775857042477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4649028285881850571361651 6973542428822775857042477)
                    ·
                      refine ⟨2615078410808540946390929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973542428822775857042477 2615078410808540946390929)
                      ·
                        rfl

theorem cell23_5092847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_5092847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092847 prefixEnd_5092847 := by exact prefixLift 5092847
  have htrace : WordTrace (prefixWord ++ tailWord_5092847) baseStart_5092847 baseEnd_5092847 := by
    simpa [prefixWord, tailWord_5092847, baseEnd_5092847] using wordTrace_append hprefix tailTrace_5092847
  have hstable : (prefixWord ++ tailWord_5092847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092847).length < 2 ^ (prefixWord ++ tailWord_5092847).sum := by decide
  have hdescent : baseEnd_5092847 < baseStart_5092847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092857 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 2, 3, 2]
def baseStart_5092857 : Nat := 118140960795 + 5092857 * 2 ^ 59
def prefixEnd_5092857 : Nat := 4983230072969 + 3 ^ 40 * 5092857 * 2
def baseEnd_5092857 : Nat := 2615083545615085907265883

theorem tailTrace_5092857 : CollatzResearch.WordTrace tailWord_5092857 prefixEnd_5092857 2615083545615085907265883 := by
  unfold tailWord_5092857
  simp only [CollatzResearch.WordTrace]
  refine ⟨185751754910456354573132825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123834503273637569715421883 185751754910456354573132825)
  ·
    refine ⟨139313816182842265929849619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185751754910456354573132825 139313816182842265929849619)
    ·
      refine ⟨208970724274263398894774429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139313816182842265929849619 208970724274263398894774429)
      ·
        refine ⟨78364021602848774585540411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208970724274263398894774429 78364021602848774585540411)
        ·
          refine ⟨117546032404273161878310617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78364021602848774585540411 117546032404273161878310617)
          ·
            refine ⟨88159524303204871408732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117546032404273161878310617 88159524303204871408732963)
            ·
              refine ⟨132239286454807307113099445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88159524303204871408732963 132239286454807307113099445)
              ·
                refine ⟨12397433105138185041853073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132239286454807307113099445 12397433105138185041853073)
                ·
                  refine ⟨9298074828853638781389805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12397433105138185041853073 9298074828853638781389805)
                  ·
                    refine ⟨3486778060820114543021177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9298074828853638781389805 3486778060820114543021177)
                    ·
                      refine ⟨2615083545615085907265883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486778060820114543021177 2615083545615085907265883)
                      ·
                        rfl

theorem cell23_5092857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_5092857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092857 prefixEnd_5092857 := by exact prefixLift 5092857
  have htrace : WordTrace (prefixWord ++ tailWord_5092857) baseStart_5092857 baseEnd_5092857 := by
    simpa [prefixWord, tailWord_5092857, baseEnd_5092857] using wordTrace_append hprefix tailTrace_5092857
  have hstable : (prefixWord ++ tailWord_5092857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092857).length < 2 ^ (prefixWord ++ tailWord_5092857).sum := by decide
  have hdescent : baseEnd_5092857 < baseStart_5092857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092874 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_5092874 : Nat := 118140960795 + 5092874 * 2 ^ 59
def prefixEnd_5092874 : Nat := 4983230072969 + 3 ^ 40 * 5092874 * 2
def baseEnd_5092874 : Nat := 2615092274786212340753305

theorem tailTrace_5092874 : CollatzResearch.WordTrace tailWord_5092874 prefixEnd_5092874 2615092274786212340753305 := by
  unfold tailWord_5092874
  simp only [CollatzResearch.WordTrace]
  refine ⟨46438093737848691619125419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123834916634263177651001117 46438093737848691619125419)
  ·
    refine ⟨69657140606773037428688129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46438093737848691619125419 69657140606773037428688129)
    ·
      refine ⟨52242855455079778071516097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69657140606773037428688129 52242855455079778071516097)
      ·
        refine ⟨39182141591309833553637073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52242855455079778071516097 39182141591309833553637073)
        ·
          refine ⟨29386606193482375165227805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39182141591309833553637073 29386606193482375165227805)
          ·
            refine ⟨11019977322555890686960427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29386606193482375165227805 11019977322555890686960427)
            ·
              refine ⟨16529965983833836030440641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019977322555890686960427 16529965983833836030440641)
              ·
                refine ⟨12397474487875377022830481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16529965983833836030440641 12397474487875377022830481)
                ·
                  refine ⟨9298105865906532767122861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12397474487875377022830481 9298105865906532767122861)
                  ·
                    refine ⟨3486789699714949787671073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9298105865906532767122861 3486789699714949787671073)
                    ·
                      refine ⟨2615092274786212340753305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486789699714949787671073 2615092274786212340753305)
                      ·
                        rfl

theorem cell23_5092874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_5092874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092874 prefixEnd_5092874 := by exact prefixLift 5092874
  have htrace : WordTrace (prefixWord ++ tailWord_5092874) baseStart_5092874 baseEnd_5092874 := by
    simpa [prefixWord, tailWord_5092874, baseEnd_5092874] using wordTrace_append hprefix tailTrace_5092874
  have hstable : (prefixWord ++ tailWord_5092874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092874).length < 2 ^ (prefixWord ++ tailWord_5092874).sum := by decide
  have hdescent : baseEnd_5092874 < baseStart_5092874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092881 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 1, 1, 3]
def baseStart_5092881 : Nat := 118140960795 + 5092881 * 2 ^ 59
def prefixEnd_5092881 : Nat := 4983230072969 + 3 ^ 40 * 5092881 * 2
def baseEnd_5092881 : Nat := 2615095869150793813365773

theorem tailTrace_5092881 : CollatzResearch.WordTrace tailWord_5092881 prefixEnd_5092881 2615095869150793813365773 := by
  unfold tailWord_5092881
  simp only [CollatzResearch.WordTrace]
  refine ⟨185752630262369406672006497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123835086841579604448004331 185752630262369406672006497)
  ·
    refine ⟨139314472696777055004004873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185752630262369406672006497 139314472696777055004004873)
    ·
      refine ⟨104485854522582791253003655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139314472696777055004004873 104485854522582791253003655)
      ·
        refine ⟨156728781783874186879505483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104485854522582791253003655 156728781783874186879505483)
        ·
          refine ⟨235093172675811280319258225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156728781783874186879505483 235093172675811280319258225)
          ·
            refine ⟨176319879506858460239443669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235093172675811280319258225 176319879506858460239443669)
            ·
              refine ⟨4132497175941995161861961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176319879506858460239443669 4132497175941995161861961)
              ·
                refine ⟨3099372881956496371396471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132497175941995161861961 3099372881956496371396471)
                ·
                  refine ⟨4649059322934744557094707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099372881956496371396471 4649059322934744557094707)
                  ·
                    refine ⟨6973588984402116835642061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4649059322934744557094707 6973588984402116835642061)
                    ·
                      refine ⟨2615095869150793813365773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973588984402116835642061 2615095869150793813365773)
                      ·
                        rfl

theorem cell23_5092881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_5092881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092881 prefixEnd_5092881 := by exact prefixLift 5092881
  have htrace : WordTrace (prefixWord ++ tailWord_5092881) baseStart_5092881 baseEnd_5092881 := by
    simpa [prefixWord, tailWord_5092881, baseEnd_5092881] using wordTrace_append hprefix tailTrace_5092881
  have hstable : (prefixWord ++ tailWord_5092881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092881).length < 2 ^ (prefixWord ++ tailWord_5092881).sum := by decide
  have hdescent : baseEnd_5092881 < baseStart_5092881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092890 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_5092890 : Nat := 118140960795 + 5092890 * 2 ^ 59
def prefixEnd_5092890 : Nat := 4983230072969 + 3 ^ 40 * 5092890 * 2
def baseEnd_5092890 : Nat := 2615100490476684278153231

theorem tailTrace_5092890 : CollatzResearch.WordTrace tailWord_5092890 prefixEnd_5092890 2615100490476684278153231 := by
  unfold tailWord_5092890
  simp only [CollatzResearch.WordTrace]
  refine ⟨46438239629834200302271031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123835305679557867472722749 46438239629834200302271031)
  ·
    refine ⟨69657359444751300453406547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46438239629834200302271031 69657359444751300453406547)
    ·
      refine ⟨104486039167126950680109821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69657359444751300453406547 104486039167126950680109821)
      ·
        refine ⟨39182264687672606505041183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104486039167126950680109821 39182264687672606505041183)
        ·
          refine ⟨58773397031508909757561775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39182264687672606505041183 58773397031508909757561775)
          ·
            refine ⟨88160095547263364636342663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58773397031508909757561775 88160095547263364636342663)
            ·
              refine ⟨132240143320895046954513995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88160095547263364636342663 132240143320895046954513995)
              ·
                refine ⟨198360214981342570431770993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132240143320895046954513995 198360214981342570431770993)
                ·
                  refine ⟨148770161236006927823828245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198360214981342570431770993 148770161236006927823828245)
                  ·
                    refine ⟨6973601307937824741741949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148770161236006927823828245 6973601307937824741741949)
                    ·
                      refine ⟨2615100490476684278153231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973601307937824741741949 2615100490476684278153231)
                      ·
                        rfl

theorem cell23_5092890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_5092890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092890 prefixEnd_5092890 := by exact prefixLift 5092890
  have htrace : WordTrace (prefixWord ++ tailWord_5092890) baseStart_5092890 baseEnd_5092890 := by
    simpa [prefixWord, tailWord_5092890, baseEnd_5092890] using wordTrace_append hprefix tailTrace_5092890
  have hstable : (prefixWord ++ tailWord_5092890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092890).length < 2 ^ (prefixWord ++ tailWord_5092890).sum := by decide
  have hdescent : baseEnd_5092890 < baseStart_5092890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092904 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5092904 : Nat := 118140960795 + 5092904 * 2 ^ 59
def prefixEnd_5092904 : Nat := 4983230072969 + 3 ^ 40 * 5092904 * 2
def baseEnd_5092904 : Nat := 2615107679205847223378167

theorem tailTrace_5092904 : CollatzResearch.WordTrace tailWord_5092904 prefixEnd_5092904 2615107679205847223378167 := by
  unfold tailWord_5092904
  simp only [CollatzResearch.WordTrace]
  refine ⟨92876734570643040800046883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123835646094190721066729177 92876734570643040800046883)
  ·
    refine ⟨139315101855964561200070325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92876734570643040800046883 139315101855964561200070325)
    ·
      refine ⟨13060790798996677612506593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139315101855964561200070325 13060790798996677612506593)
      ·
        refine ⟨9795593099247508209379945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13060790798996677612506593 9795593099247508209379945)
        ·
          refine ⟨7346694824435631157034959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9795593099247508209379945 7346694824435631157034959)
          ·
            refine ⟨11020042236653446735552439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346694824435631157034959 11020042236653446735552439)
            ·
              refine ⟨16530063354980170103328659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020042236653446735552439 16530063354980170103328659)
              ·
                refine ⟨24795095032470255154992989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16530063354980170103328659 24795095032470255154992989)
                ·
                  refine ⟨9298160637176345683122371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24795095032470255154992989 9298160637176345683122371)
                  ·
                    refine ⟨13947240955764518524683557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9298160637176345683122371 13947240955764518524683557)
                    ·
                      refine ⟨2615107679205847223378167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13947240955764518524683557 2615107679205847223378167)
                      ·
                        rfl

theorem cell23_5092904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5092904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092904 prefixEnd_5092904 := by exact prefixLift 5092904
  have htrace : WordTrace (prefixWord ++ tailWord_5092904) baseStart_5092904 baseEnd_5092904 := by
    simpa [prefixWord, tailWord_5092904, baseEnd_5092904] using wordTrace_append hprefix tailTrace_5092904
  have hstable : (prefixWord ++ tailWord_5092904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092904).length < 2 ^ (prefixWord ++ tailWord_5092904).sum := by decide
  have hdescent : baseEnd_5092904 < baseStart_5092904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092917 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5092917 : Nat := 118140960795 + 5092917 * 2 ^ 59
def prefixEnd_5092917 : Nat := 4983230072969 + 3 ^ 40 * 5092917 * 2
def baseEnd_5092917 : Nat := 2615114354454355672515607

theorem tailTrace_5092917 : CollatzResearch.WordTrace tailWord_5092917 prefixEnd_5092917 2615114354454355672515607 := by
  unfold tailWord_5092917
  simp only [CollatzResearch.WordTrace]
  refine ⟨185753943290238984820317005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123835962193492656546878003 185753943290238984820317005)
  ·
    refine ⟨69657728733839619307618877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185753943290238984820317005 69657728733839619307618877)
    ·
      refine ⟨26121648275189857240357079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69657728733839619307618877 26121648275189857240357079)
      ·
        refine ⟨39182472412784785860535619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26121648275189857240357079 39182472412784785860535619)
        ·
          refine ⟨58773708619177178790803429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39182472412784785860535619 58773708619177178790803429)
          ·
            refine ⟨11020070366095721023275643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58773708619177178790803429 11020070366095721023275643)
            ·
              refine ⟨16530105549143581534913465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020070366095721023275643 16530105549143581534913465)
              ·
                refine ⟨12397579161857686151185099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16530105549143581534913465 12397579161857686151185099)
                ·
                  refine ⟨18596368742786529226777649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12397579161857686151185099 18596368742786529226777649)
                  ·
                    refine ⟨13947276557089896920083237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18596368742786529226777649 13947276557089896920083237)
                    ·
                      refine ⟨2615114354454355672515607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13947276557089896920083237 2615114354454355672515607)
                      ·
                        rfl

theorem cell23_5092917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5092917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092917 prefixEnd_5092917 := by exact prefixLift 5092917
  have htrace : WordTrace (prefixWord ++ tailWord_5092917) baseStart_5092917 baseEnd_5092917 := by
    simpa [prefixWord, tailWord_5092917, baseEnd_5092917] using wordTrace_append hprefix tailTrace_5092917
  have hstable : (prefixWord ++ tailWord_5092917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092917).length < 2 ^ (prefixWord ++ tailWord_5092917).sum := by decide
  have hdescent : baseEnd_5092917 < baseStart_5092917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092924 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_5092924 : Nat := 118140960795 + 5092924 * 2 ^ 59
def prefixEnd_5092924 : Nat := 4983230072969 + 3 ^ 40 * 5092924 * 2
def baseEnd_5092924 : Nat := 2615117948818937145128075

theorem tailTrace_5092924 : CollatzResearch.WordTrace tailWord_5092924 prefixEnd_5092924 2615117948818937145128075 := by
  unfold tailWord_5092924
  simp only [CollatzResearch.WordTrace]
  refine ⟨92877099300606812507910913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123836132400809083343881217 92877099300606812507910913)
  ·
    refine ⟨69657824475455109380933185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92877099300606812507910913 69657824475455109380933185)
    ·
      refine ⟨52243368356591332035699889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69657824475455109380933185 52243368356591332035699889)
      ·
        refine ⟨39182526267443499026774917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52243368356591332035699889 39182526267443499026774917)
        ·
          refine ⟨7346723675145656067520297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39182526267443499026774917 7346723675145656067520297)
          ·
            refine ⟨5510042756359242050640223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7346723675145656067520297 5510042756359242050640223)
            ·
              refine ⟨8265064134538863075960335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5510042756359242050640223 8265064134538863075960335)
              ·
                refine ⟨12397596201808294613940503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265064134538863075960335 12397596201808294613940503)
                ·
                  refine ⟨18596394302712441920910755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12397596201808294613940503 18596394302712441920910755)
                  ·
                    refine ⟨27894591454068662881366133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18596394302712441920910755 27894591454068662881366133)
                    ·
                      refine ⟨2615117948818937145128075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27894591454068662881366133 2615117948818937145128075)
                      ·
                        rfl

theorem cell23_5092924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_5092924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092924 prefixEnd_5092924 := by exact prefixLift 5092924
  have htrace : WordTrace (prefixWord ++ tailWord_5092924) baseStart_5092924 baseEnd_5092924 := by
    simpa [prefixWord, tailWord_5092924, baseEnd_5092924] using wordTrace_append hprefix tailTrace_5092924
  have hstable : (prefixWord ++ tailWord_5092924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092924).length < 2 ^ (prefixWord ++ tailWord_5092924).sum := by decide
  have hdescent : baseEnd_5092924 < baseStart_5092924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092937 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 3]
def baseStart_5092937 : Nat := 118140960795 + 5092937 * 2 ^ 59
def prefixEnd_5092937 : Nat := 4983230072969 + 3 ^ 40 * 5092937 * 2
def baseEnd_5092937 : Nat := 2615124624067445594265515

theorem tailTrace_5092937 : CollatzResearch.WordTrace tailWord_5092937 prefixEnd_5092937 2615124624067445594265515 := by
  unfold tailWord_5092937
  simp only [CollatzResearch.WordTrace]
  refine ⟨185754672750166528236045065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123836448500111018824030043 185754672750166528236045065)
  ·
    refine ⟨139316004562624896177033799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185754672750166528236045065 139316004562624896177033799)
    ·
      refine ⟨208974006843937344265550699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139316004562624896177033799 208974006843937344265550699)
      ·
        refine ⟨313461010265906016398326049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208974006843937344265550699 313461010265906016398326049)
        ·
          refine ⟨235095757699429512298744537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313461010265906016398326049 235095757699429512298744537)
          ·
            refine ⟨176321818274572134224058403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235095757699429512298744537 176321818274572134224058403)
            ·
              refine ⟨264482727411858201336087605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176321818274572134224058403 264482727411858201336087605)
              ·
                refine ⟨24795255694861706375258213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264482727411858201336087605 24795255694861706375258213)
                ·
                  refine ⟨4649110442786569945360915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24795255694861706375258213 4649110442786569945360915)
                  ·
                    refine ⟨6973665664179854918041373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4649110442786569945360915 6973665664179854918041373)
                    ·
                      refine ⟨2615124624067445594265515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973665664179854918041373 2615124624067445594265515)
                      ·
                        rfl

theorem cell23_5092937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_5092937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092937 prefixEnd_5092937 := by exact prefixLift 5092937
  have htrace : WordTrace (prefixWord ++ tailWord_5092937) baseStart_5092937 baseEnd_5092937 := by
    simpa [prefixWord, tailWord_5092937, baseEnd_5092937] using wordTrace_append hprefix tailTrace_5092937
  have hstable : (prefixWord ++ tailWord_5092937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092937).length < 2 ^ (prefixWord ++ tailWord_5092937).sum := by decide
  have hdescent : baseEnd_5092937 < baseStart_5092937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092940 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_5092940 : Nat := 118140960795 + 5092940 * 2 ^ 59
def prefixEnd_5092940 : Nat := 4983230072969 + 3 ^ 40 * 5092940 * 2
def baseEnd_5092940 : Nat := 871708721503136360842667

theorem tailTrace_5092940 : CollatzResearch.WordTrace tailWord_5092940 prefixEnd_5092940 871708721503136360842667 := by
  unfold tailWord_5092940
  simp only [CollatzResearch.WordTrace]
  refine ⟨92877391084577829874202137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123836521446103773165602849 92877391084577829874202137)
  ·
    refine ⟨69658043313433372405651603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92877391084577829874202137 69658043313433372405651603)
    ·
      refine ⟨104487064970150058608477405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69658043313433372405651603 104487064970150058608477405)
      ·
        refine ⟨39182649363806271978179027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104487064970150058608477405 39182649363806271978179027)
        ·
          refine ⟨58773974045709407967268541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39182649363806271978179027 58773974045709407967268541)
          ·
            refine ⟨22040240267141027987725703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58773974045709407967268541 22040240267141027987725703)
            ·
              refine ⟨33060360400711541981588555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22040240267141027987725703 33060360400711541981588555)
              ·
                refine ⟨49590540601067312972382833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33060360400711541981588555 49590540601067312972382833)
                ·
                  refine ⟨37192905450800484729287125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49590540601067312972382833 37192905450800484729287125)
                  ·
                    refine ⟨871708721503136360842667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37192905450800484729287125 871708721503136360842667)
                    ·
                      rfl

theorem cell23_5092940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_5092940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092940 prefixEnd_5092940 := by exact prefixLift 5092940
  have htrace : WordTrace (prefixWord ++ tailWord_5092940) baseStart_5092940 baseEnd_5092940 := by
    simpa [prefixWord, tailWord_5092940, baseEnd_5092940] using wordTrace_append hprefix tailTrace_5092940
  have hstable : (prefixWord ++ tailWord_5092940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092940).length < 2 ^ (prefixWord ++ tailWord_5092940).sum := by decide
  have hdescent : baseEnd_5092940 < baseStart_5092940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092960 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_5092960 : Nat := 118140960795 + 5092960 * 2 ^ 59
def prefixEnd_5092960 : Nat := 4983230072969 + 3 ^ 40 * 5092960 * 2
def baseEnd_5092960 : Nat := 2615136434122499004277909

theorem tailTrace_5092960 : CollatzResearch.WordTrace tailWord_5092960 prefixEnd_5092960 2615136434122499004277909 := by
  unfold tailWord_5092960
  simp only [CollatzResearch.WordTrace]
  refine ⟨92877755814541601582066167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123837007752722135442754889 92877755814541601582066167)
  ·
    refine ⟨139316633721812402373099251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92877755814541601582066167 139316633721812402373099251)
    ·
      refine ⟨208974950582718603559648877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139316633721812402373099251 208974950582718603559648877)
      ·
        refine ⟨78365606468519476334868329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208974950582718603559648877 78365606468519476334868329)
        ·
          refine ⟨58774204851389607251151247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78365606468519476334868329 58774204851389607251151247)
          ·
            refine ⟨88161307277084410876726871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58774204851389607251151247 88161307277084410876726871)
            ·
              refine ⟨132241960915626616315090307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88161307277084410876726871 132241960915626616315090307)
              ·
                refine ⟨198362941373439924472635461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132241960915626616315090307 198362941373439924472635461)
                ·
                  refine ⟨37193051507519985838619149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198362941373439924472635461 37193051507519985838619149)
                  ·
                    refine ⟨13947394315319994689482181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37193051507519985838619149 13947394315319994689482181)
                    ·
                      refine ⟨2615136434122499004277909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13947394315319994689482181 2615136434122499004277909)
                      ·
                        rfl

theorem cell23_5092960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_5092960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092960 prefixEnd_5092960 := by exact prefixLift 5092960
  have htrace : WordTrace (prefixWord ++ tailWord_5092960) baseStart_5092960 baseEnd_5092960 := by
    simpa [prefixWord, tailWord_5092960, baseEnd_5092960] using wordTrace_append hprefix tailTrace_5092960
  have hstable : (prefixWord ++ tailWord_5092960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092960).length < 2 ^ (prefixWord ++ tailWord_5092960).sum := by decide
  have hdescent : baseEnd_5092960 < baseStart_5092960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5092964 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_5092964 : Nat := 118140960795 + 5092964 * 2 ^ 59
def prefixEnd_5092964 : Nat := 4983230072969 + 3 ^ 40 * 5092964 * 2
def baseEnd_5092964 : Nat := 2615138488045116988627891

theorem tailTrace_5092964 : CollatzResearch.WordTrace tailWord_5092964 prefixEnd_5092964 2615138488045116988627891 := by
  unfold tailWord_5092964
  simp only [CollatzResearch.WordTrace]
  refine ⟨92877828760534355923638973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123837105014045807898185297 92877828760534355923638973)
  ·
    refine ⟨34829185785200383471364615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92877828760534355923638973 34829185785200383471364615)
    ·
      refine ⟨52243778677800575207046923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34829185785200383471364615 52243778677800575207046923)
      ·
        refine ⟨78365668016700862810570385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52243778677800575207046923 78365668016700862810570385)
        ·
          refine ⟨58774251012525647107927789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78365668016700862810570385 58774251012525647107927789)
          ·
            refine ⟨22040344129697117665472921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58774251012525647107927789 22040344129697117665472921)
            ·
              refine ⟨16530258097272838249104691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22040344129697117665472921 16530258097272838249104691)
              ·
                refine ⟨24795387145909257373657037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16530258097272838249104691 24795387145909257373657037)
                ·
                  refine ⟨9298270179715971515121389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24795387145909257373657037 9298270179715971515121389)
                  ·
                    refine ⟨3486851317393489318170521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9298270179715971515121389 3486851317393489318170521)
                    ·
                      refine ⟨2615138488045116988627891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486851317393489318170521 2615138488045116988627891)
                      ·
                        rfl

theorem cell23_5092964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_5092964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5092964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5092964 prefixEnd_5092964 := by exact prefixLift 5092964
  have htrace : WordTrace (prefixWord ++ tailWord_5092964) baseStart_5092964 baseEnd_5092964 := by
    simpa [prefixWord, tailWord_5092964, baseEnd_5092964] using wordTrace_append hprefix tailTrace_5092964
  have hstable : (prefixWord ++ tailWord_5092964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5092964).length < 2 ^ (prefixWord ++ tailWord_5092964).sum := by decide
  have hdescent : baseEnd_5092964 < baseStart_5092964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5092964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093047 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 4, 5]
def baseStart_5093047 : Nat := 118140960795 + 5093047 * 2 ^ 59
def prefixEnd_5093047 : Nat := 4983230072969 + 3 ^ 40 * 5093047 * 2
def baseEnd_5093047 : Nat := 871727035646480054630003

theorem tailTrace_5093047 : CollatzResearch.WordTrace tailWord_5093047 prefixEnd_5093047 871727035646480054630003 := by
  unfold tailWord_5093047
  simp only [CollatzResearch.WordTrace]
  refine ⟨185758684779768017022549395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123839123186512011348366263 185758684779768017022549395)
  ·
    refine ⟨278638027169652025533824093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185758684779768017022549395 278638027169652025533824093)
    ·
      refine ⟨104489260188619509575184035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278638027169652025533824093 104489260188619509575184035)
      ·
        refine ⟨156733890282929264362776053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104489260188619509575184035 156733890282929264362776053)
        ·
          refine ⟨14693802214024618534010255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156733890282929264362776053 14693802214024618534010255)
          ·
            refine ⟨22040703321036927801015383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14693802214024618534010255 22040703321036927801015383)
            ·
              refine ⟨33061054981555391701523075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22040703321036927801015383 33061054981555391701523075)
              ·
                refine ⟨49591582472333087552284613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33061054981555391701523075 49591582472333087552284613)
                ·
                  refine ⟨9298421713562453916053365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49591582472333087552284613 9298421713562453916053365)
                  ·
                    refine ⟨871727035646480054630003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9298421713562453916053365 871727035646480054630003)
                    ·
                      rfl

theorem cell23_5093047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_5093047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093047 prefixEnd_5093047 := by exact prefixLift 5093047
  have htrace : WordTrace (prefixWord ++ tailWord_5093047) baseStart_5093047 baseEnd_5093047 := by
    simpa [prefixWord, tailWord_5093047, baseEnd_5093047] using wordTrace_append hprefix tailTrace_5093047
  have hstable : (prefixWord ++ tailWord_5093047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093047).length < 2 ^ (prefixWord ++ tailWord_5093047).sum := by decide
  have hdescent : baseEnd_5093047 < baseStart_5093047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093062 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5093062 : Nat := 118140960795 + 5093062 * 2 ^ 59
def prefixEnd_5093062 : Nat := 4983230072969 + 3 ^ 40 * 5093062 * 2
def baseEnd_5093062 : Nat := 2615188809149257605202441

theorem tailTrace_5093062 : CollatzResearch.WordTrace tailWord_5093062 prefixEnd_5093062 2615188809149257605202441 := by
  unfold tailWord_5093062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804975996084802330760795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123839487916475783056230293 5804975996084802330760795)
  ·
    refine ⟨8707463994127203496141193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5804975996084802330760795 8707463994127203496141193)
    ·
      refine ⟨6530597995595402622105895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8707463994127203496141193 6530597995595402622105895)
      ·
        refine ⟨9795896993393103933158843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530597995595402622105895 9795896993393103933158843)
        ·
          refine ⟨14693845490089655899738265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795896993393103933158843 14693845490089655899738265)
          ·
            refine ⟨11020384117567241924803699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14693845490089655899738265 11020384117567241924803699)
            ·
              refine ⟨16530576176350862887205549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020384117567241924803699 16530576176350862887205549)
              ·
                refine ⟨6198966066131573582702081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16530576176350862887205549 6198966066131573582702081)
                ·
                  refine ⟨4649224549598680187026561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6198966066131573582702081 4649224549598680187026561)
                  ·
                    refine ⟨3486918412199010140269921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4649224549598680187026561 3486918412199010140269921)
                    ·
                      refine ⟨2615188809149257605202441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486918412199010140269921 2615188809149257605202441)
                      ·
                        rfl

theorem cell23_5093062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5093062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093062 prefixEnd_5093062 := by exact prefixLift 5093062
  have htrace : WordTrace (prefixWord ++ tailWord_5093062) baseStart_5093062 baseEnd_5093062 := by
    simpa [prefixWord, tailWord_5093062, baseEnd_5093062] using wordTrace_append hprefix tailTrace_5093062
  have hstable : (prefixWord ++ tailWord_5093062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093062).length < 2 ^ (prefixWord ++ tailWord_5093062).sum := by decide
  have hdescent : baseEnd_5093062 < baseStart_5093062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093107 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 6]
def baseStart_5093107 : Nat := 118140960795 + 5093107 * 2 ^ 59
def prefixEnd_5093107 : Nat := 4983230072969 + 3 ^ 40 * 5093107 * 2
def baseEnd_5093107 : Nat := 290579101753189992126637

theorem tailTrace_5093107 : CollatzResearch.WordTrace tailWord_5093107 prefixEnd_5093107 290579101753189992126637 := by
  unfold tailWord_5093107
  simp only [CollatzResearch.WordTrace]
  refine ⟨185760873159550647269733575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123840582106367098179822383 185760873159550647269733575)
  ·
    refine ⟨278641309739325970904600363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185760873159550647269733575 278641309739325970904600363)
    ·
      refine ⟨417961964608988956356900545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278641309739325970904600363 417961964608988956356900545)
      ·
        refine ⟨313471473456741717267675409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417961964608988956356900545 313471473456741717267675409)
        ·
          refine ⟨235103605092556287950756557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313471473456741717267675409 235103605092556287950756557)
          ·
            refine ⟨88163851909708607981533709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235103605092556287950756557 88163851909708607981533709)
            ·
              refine ⟨33061444466140727993075141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88163851909708607981533709 33061444466140727993075141)
              ·
                refine ⟨6199020837401386498701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33061444466140727993075141 6199020837401386498701589)
                ·
                  refine ⟨290579101753189992126637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6199020837401386498701589 290579101753189992126637)
                  ·
                    rfl

theorem cell23_5093107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6].length) (baseStart_5093107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093107 prefixEnd_5093107 := by exact prefixLift 5093107
  have htrace : WordTrace (prefixWord ++ tailWord_5093107) baseStart_5093107 baseEnd_5093107 := by
    simpa [prefixWord, tailWord_5093107, baseEnd_5093107] using wordTrace_append hprefix tailTrace_5093107
  have hstable : (prefixWord ++ tailWord_5093107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093107).length < 2 ^ (prefixWord ++ tailWord_5093107).sum := by decide
  have hdescent : baseEnd_5093107 < baseStart_5093107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093118 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_5093118 : Nat := 118140960795 + 5093118 * 2 ^ 59
def prefixEnd_5093118 : Nat := 4983230072969 + 3 ^ 40 * 5093118 * 2
def baseEnd_5093118 : Nat := 2615217564065909386102183

theorem tailTrace_5093118 : CollatzResearch.WordTrace tailWord_5093118 prefixEnd_5093118 2615217564065909386102183 := by
  unfold tailWord_5093118
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220159295313849518548001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123840849575007197432256005 23220159295313849518548001)
  ·
    refine ⟨17415119471485387138911001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23220159295313849518548001 17415119471485387138911001)
    ·
      refine ⟨13061339603614040354183251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17415119471485387138911001 13061339603614040354183251)
      ·
        refine ⟨19592009405421060531274877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13061339603614040354183251 19592009405421060531274877)
        ·
          refine ⟨7347003527032897699228079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19592009405421060531274877 7347003527032897699228079)
          ·
            refine ⟨11020505290549346548842119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347003527032897699228079 11020505290549346548842119)
            ·
              refine ⟨16530757935824019823263179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020505290549346548842119 16530757935824019823263179)
              ·
                refine ⟨24796136903736029734894769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16530757935824019823263179 24796136903736029734894769)
                ·
                  refine ⟨18597102677802022301171077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24796136903736029734894769 18597102677802022301171077)
                  ·
                    refine ⟨3486956752087879181469577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18597102677802022301171077 3486956752087879181469577)
                    ·
                      refine ⟨2615217564065909386102183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3486956752087879181469577 2615217564065909386102183)
                      ·
                        rfl

theorem cell23_5093118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_5093118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093118 prefixEnd_5093118 := by exact prefixLift 5093118
  have htrace : WordTrace (prefixWord ++ tailWord_5093118) baseStart_5093118 baseEnd_5093118 := by
    simpa [prefixWord, tailWord_5093118, baseEnd_5093118] using wordTrace_append hprefix tailTrace_5093118
  have hstable : (prefixWord ++ tailWord_5093118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093118).length < 2 ^ (prefixWord ++ tailWord_5093118).sum := by decide
  have hdescent : baseEnd_5093118 < baseStart_5093118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093124 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 6]
def baseStart_5093124 : Nat := 118140960795 + 5093124 * 2 ^ 59
def prefixEnd_5093124 : Nat := 4983230072969 + 3 ^ 40 * 5093124 * 2
def baseEnd_5093124 : Nat := 290580071661092929180795

theorem tailTrace_5093124 : CollatzResearch.WordTrace tailWord_5093124 prefixEnd_5093124 290580071661092929180795 := by
  unfold tailWord_5093124
  simp only [CollatzResearch.WordTrace]
  refine ⟨92880746600244529586551213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123840995466992706115401617 92880746600244529586551213)
  ·
    refine ⟨34830279975091698594956705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92880746600244529586551213 34830279975091698594956705)
    ·
      refine ⟨26122709981318773946217529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34830279975091698594956705 26122709981318773946217529)
      ·
        refine ⟨19592032485989080459663147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26122709981318773946217529 19592032485989080459663147)
        ·
          refine ⟨29388048728983620689494721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19592032485989080459663147 29388048728983620689494721)
          ·
            refine ⟨22041036546737715517121041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29388048728983620689494721 22041036546737715517121041)
            ·
              refine ⟨16530777410053286637840781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22041036546737715517121041 16530777410053286637840781)
              ·
                refine ⟨6199041528769982489190293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16530777410053286637840781 6199041528769982489190293)
                ·
                  refine ⟨290580071661092929180795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6199041528769982489190293 290580071661092929180795)
                  ·
                    rfl

theorem cell23_5093124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_5093124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093124 prefixEnd_5093124 := by exact prefixLift 5093124
  have htrace : WordTrace (prefixWord ++ tailWord_5093124) baseStart_5093124 baseEnd_5093124 := by
    simpa [prefixWord, tailWord_5093124, baseEnd_5093124] using wordTrace_append hprefix tailTrace_5093124
  have hstable : (prefixWord ++ tailWord_5093124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093124).length < 2 ^ (prefixWord ++ tailWord_5093124).sum := by decide
  have hdescent : baseEnd_5093124 < baseStart_5093124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093138 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5093138 : Nat := 118140960795 + 5093138 * 2 ^ 59
def prefixEnd_5093138 : Nat := 4983230072969 + 3 ^ 40 * 5093138 * 2
def baseEnd_5093138 : Nat := 2615227833678999307852091

theorem tailTrace_5093138 : CollatzResearch.WordTrace tailWord_5093138 prefixEnd_5093138 2615227833678999307852091 := by
  unfold tailWord_5093138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46440500955609584891028017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123841335881625559709408045 46440500955609584891028017)
  ·
    refine ⟨34830375716707188668271013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46440500955609584891028017 34830375716707188668271013)
    ·
      refine ⟨6530695446882597875300815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34830375716707188668271013 6530695446882597875300815)
      ·
        refine ⟨9796043170323896812951223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530695446882597875300815 9796043170323896812951223)
        ·
          refine ⟨14694064755485845219426835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9796043170323896812951223 14694064755485845219426835)
          ·
            refine ⟨22041097133228767829140253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14694064755485845219426835 22041097133228767829140253)
            ·
              refine ⟨8265411424960787935927595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22041097133228767829140253 8265411424960787935927595)
              ·
                refine ⟨12398117137441181903891393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265411424960787935927595 12398117137441181903891393)
                ·
                  refine ⟨9298587853080886427918545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12398117137441181903891393 9298587853080886427918545)
                  ·
                    refine ⟨6973940889810664820938909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9298587853080886427918545 6973940889810664820938909)
                    ·
                      refine ⟨2615227833678999307852091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6973940889810664820938909 2615227833678999307852091)
                      ·
                        rfl

theorem cell23_5093138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5093138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093138 prefixEnd_5093138 := by exact prefixLift 5093138
  have htrace : WordTrace (prefixWord ++ tailWord_5093138) baseStart_5093138 baseEnd_5093138 := by
    simpa [prefixWord, tailWord_5093138, baseEnd_5093138] using wordTrace_append hprefix tailTrace_5093138
  have hstable : (prefixWord ++ tailWord_5093138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093138).length < 2 ^ (prefixWord ++ tailWord_5093138).sum := by decide
  have hdescent : baseEnd_5093138 < baseStart_5093138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093227 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 7]
def baseStart_5093227 : Nat := 118140960795 + 5093227 * 2 ^ 59
def prefixEnd_5093227 : Nat := 4983230072969 + 3 ^ 40 * 5093227 * 2
def baseEnd_5093227 : Nat := 871757844485749819879727

theorem tailTrace_5093227 : CollatzResearch.WordTrace tailWord_5093227 prefixEnd_5093227 871757844485749819879727 := by
  unfold tailWord_5093227
  simp only [CollatzResearch.WordTrace]
  refine ⟨185765249919115907764101935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123843499946077271842734623 185765249919115907764101935)
  ·
    refine ⟨278647874878673861646152903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185765249919115907764101935 278647874878673861646152903)
    ·
      refine ⟨417971812318010792469229355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278647874878673861646152903 417971812318010792469229355)
      ·
        refine ⟨626957718477016188703844033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417971812318010792469229355 626957718477016188703844033)
        ·
          refine ⟨470218288857762141527883025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626957718477016188703844033 470218288857762141527883025)
          ·
            refine ⟨352663716643321606145912269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470218288857762141527883025 352663716643321606145912269)
            ·
              refine ⟨132248893741245602304717101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352663716643321606145912269 132248893741245602304717101)
              ·
                refine ⟨49593335152967100864268913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132248893741245602304717101 49593335152967100864268913)
                ·
                  refine ⟨37195001364725325648201685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49593335152967100864268913 37195001364725325648201685)
                  ·
                    refine ⟨871757844485749819879727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37195001364725325648201685 871757844485749819879727)
                    ·
                      rfl

theorem cell23_5093227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_5093227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093227 prefixEnd_5093227 := by exact prefixLift 5093227
  have htrace : WordTrace (prefixWord ++ tailWord_5093227) baseStart_5093227 baseEnd_5093227 := by
    simpa [prefixWord, tailWord_5093227, baseEnd_5093227] using wordTrace_append hprefix tailTrace_5093227
  have hstable : (prefixWord ++ tailWord_5093227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093227).length < 2 ^ (prefixWord ++ tailWord_5093227).sum := by decide
  have hdescent : baseEnd_5093227 < baseStart_5093227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093247 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_5093247 : Nat := 118140960795 + 5093247 * 2 ^ 59
def prefixEnd_5093247 : Nat := 4983230072969 + 3 ^ 40 * 5093247 * 2
def baseEnd_5093247 : Nat := 2615283803070339381389089

theorem tailTrace_5093247 : CollatzResearch.WordTrace tailWord_5093247 prefixEnd_5093247 2615283803070339381389089 := by
  unfold tailWord_5093247
  simp only [CollatzResearch.WordTrace]
  refine ⟨185765979379043451179829995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123843986252695634119886663 185765979379043451179829995)
  ·
    refine ⟨278648969068565176769744993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185765979379043451179829995 278648969068565176769744993)
    ·
      refine ⟨208986726801423882577308745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278648969068565176769744993 208986726801423882577308745)
      ·
        refine ⟨156740045101067911932981559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208986726801423882577308745 156740045101067911932981559)
        ·
          refine ⟨235110067651601867899472339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156740045101067911932981559 235110067651601867899472339)
          ·
            refine ⟨352665101477402801849208509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235110067651601867899472339 352665101477402801849208509)
            ·
              refine ⟨132249413054026050693453191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352665101477402801849208509 132249413054026050693453191)
              ·
                refine ⟨198374119581039076040179787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132249413054026050693453191 198374119581039076040179787)
                ·
                  refine ⟨297561179371558614060269681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198374119581039076040179787 297561179371558614060269681)
                  ·
                    refine ⟨223170884528668960545202261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 297561179371558614060269681 223170884528668960545202261)
                    ·
                      refine ⟨2615283803070339381389089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 223170884528668960545202261 2615283803070339381389089)
                      ·
                        rfl

theorem cell23_5093247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_5093247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093247 prefixEnd_5093247 := by exact prefixLift 5093247
  have htrace : WordTrace (prefixWord ++ tailWord_5093247) baseStart_5093247 baseEnd_5093247 := by
    simpa [prefixWord, tailWord_5093247, baseEnd_5093247] using wordTrace_append hprefix tailTrace_5093247
  have hstable : (prefixWord ++ tailWord_5093247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093247).length < 2 ^ (prefixWord ++ tailWord_5093247).sum := by decide
  have hdescent : baseEnd_5093247 < baseStart_5093247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093258 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5093258 : Nat := 118140960795 + 5093258 * 2 ^ 59
def prefixEnd_5093258 : Nat := 4983230072969 + 3 ^ 40 * 5093258 * 2
def baseEnd_5093258 : Nat := 2615289451357538838351539

theorem tailTrace_5093258 : CollatzResearch.WordTrace tailWord_5093258 prefixEnd_5093258 2615289451357538838351539 := by
  unfold tailWord_5093258
  simp only [CollatzResearch.WordTrace]
  refine ⟨46441595145500900014620107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123844253721335733372320285 46441595145500900014620107)
  ·
    refine ⟨69662392718251350021930161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46441595145500900014620107 69662392718251350021930161)
    ·
      refine ⟨52246794538688512516447621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69662392718251350021930161 52246794538688512516447621)
      ·
        refine ⟨9796273976004096096833929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52246794538688512516447621 9796273976004096096833929)
        ·
          refine ⟨7347205482003072072625447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9796273976004096096833929 7347205482003072072625447)
          ·
            refine ⟨11020808223004608108938171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347205482003072072625447 11020808223004608108938171)
            ·
              refine ⟨16531212334506912163407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020808223004608108938171 16531212334506912163407257)
              ·
                refine ⟨12398409250880184122555443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16531212334506912163407257 12398409250880184122555443)
                ·
                  refine ⟨18597613876320276183833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12398409250880184122555443 18597613876320276183833165)
                  ·
                    refine ⟨6974105203620103568937437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18597613876320276183833165 6974105203620103568937437)
                    ·
                      refine ⟨2615289451357538838351539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6974105203620103568937437 2615289451357538838351539)
                      ·
                        rfl

theorem cell23_5093258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5093258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093258 prefixEnd_5093258 := by exact prefixLift 5093258
  have htrace : WordTrace (prefixWord ++ tailWord_5093258) baseStart_5093258 baseEnd_5093258 := by
    simpa [prefixWord, tailWord_5093258, baseEnd_5093258] using wordTrace_append hprefix tailTrace_5093258
  have hstable : (prefixWord ++ tailWord_5093258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093258).length < 2 ^ (prefixWord ++ tailWord_5093258).sum := by decide
  have hdescent : baseEnd_5093258 < baseStart_5093258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093262 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5093262 : Nat := 118140960795 + 5093262 * 2 ^ 59
def prefixEnd_5093262 : Nat := 4983230072969 + 3 ^ 40 * 5093262 * 2
def baseEnd_5093262 : Nat := 2615291505280156822701521

theorem tailTrace_5093262 : CollatzResearch.WordTrace tailWord_5093262 prefixEnd_5093262 2615291505280156822701521 := by
  unfold tailWord_5093262
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220815809248638592703255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123844350982659405827750693 23220815809248638592703255)
  ·
    refine ⟨34831223713872957889054883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23220815809248638592703255 34831223713872957889054883)
    ·
      refine ⟨52246835570809436833582325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34831223713872957889054883 52246835570809436833582325)
      ·
        refine ⟨4898140834763384703148343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52246835570809436833582325 4898140834763384703148343)
        ·
          refine ⟨7347211252145077054722515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898140834763384703148343 7347211252145077054722515)
          ·
            refine ⟨11020816878217615582083773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347211252145077054722515 11020816878217615582083773)
            ·
              refine ⟨4132806329331605843281415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11020816878217615582083773 4132806329331605843281415)
              ·
                refine ⟨6199209493997408764922123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132806329331605843281415 6199209493997408764922123)
                ·
                  refine ⟨9298814240996113147383185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6199209493997408764922123 9298814240996113147383185)
                  ·
                    refine ⟨6974110680747084860537389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9298814240996113147383185 6974110680747084860537389)
                    ·
                      refine ⟨2615291505280156822701521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6974110680747084860537389 2615291505280156822701521)
                      ·
                        rfl

theorem cell23_5093262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5093262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093262 prefixEnd_5093262 := by exact prefixLift 5093262
  have htrace : WordTrace (prefixWord ++ tailWord_5093262) baseStart_5093262 baseEnd_5093262 := by
    simpa [prefixWord, tailWord_5093262, baseEnd_5093262] using wordTrace_append hprefix tailTrace_5093262
  have hstable : (prefixWord ++ tailWord_5093262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093262).length < 2 ^ (prefixWord ++ tailWord_5093262).sum := by decide
  have hdescent : baseEnd_5093262 < baseStart_5093262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093304 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 7]
def baseStart_5093304 : Nat := 118140960795 + 5093304 * 2 ^ 59
def prefixEnd_5093304 : Nat := 4983230072969 + 3 ^ 40 * 5093304 * 2
def baseEnd_5093304 : Nat := 290590341274182850930703

theorem tailTrace_5093304 : CollatzResearch.WordTrace tailWord_5093304 prefixEnd_5093304 290590341274182850930703 := by
  unfold tailWord_5093304
  simp only [CollatzResearch.WordTrace]
  refine ⟨92884029169918474957327483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123845372226557966609769977 92884029169918474957327483)
  ·
    refine ⟨139326043754877712435991225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92884029169918474957327483 139326043754877712435991225)
    ·
      refine ⟨104494532816158284326993419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139326043754877712435991225 104494532816158284326993419)
      ·
        refine ⟨156741799224237426490490129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104494532816158284326993419 156741799224237426490490129)
        ·
          refine ⟨117556349418178069867867597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156741799224237426490490129 117556349418178069867867597)
          ·
            refine ⟨44083631031816776200450349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117556349418178069867867597 44083631031816776200450349)
            ·
              refine ⟨16531361636931291075168881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44083631031816776200450349 16531361636931291075168881)
              ·
                refine ⟨12398521227698468306376661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16531361636931291075168881 12398521227698468306376661)
                ·
                  refine ⟨290590341274182850930703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12398521227698468306376661 290590341274182850930703)
                  ·
                    rfl

theorem cell23_5093304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_5093304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093304 prefixEnd_5093304 := by exact prefixLift 5093304
  have htrace : WordTrace (prefixWord ++ tailWord_5093304) baseStart_5093304 baseEnd_5093304 := by
    simpa [prefixWord, tailWord_5093304, baseEnd_5093304] using wordTrace_append hprefix tailTrace_5093304
  have hstable : (prefixWord ++ tailWord_5093304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093304).length < 2 ^ (prefixWord ++ tailWord_5093304).sum := by decide
  have hdescent : baseEnd_5093304 < baseStart_5093304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093344 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_5093344 : Nat := 118140960795 + 5093344 * 2 ^ 59
def prefixEnd_5093344 : Nat := 4983230072969 + 3 ^ 40 * 5093344 * 2
def baseEnd_5093344 : Nat := 2615333610693825501876143

theorem tailTrace_5093344 : CollatzResearch.WordTrace tailWord_5093344 prefixEnd_5093344 2615333610693825501876143 := by
  unfold tailWord_5093344
  simp only [CollatzResearch.WordTrace]
  refine ⟨92884758629846018373055543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123846344839794691164074057 92884758629846018373055543)
  ·
    refine ⟨139327137944769027559583315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92884758629846018373055543 139327137944769027559583315)
    ·
      refine ⟨208990706917153541339374973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139327137944769027559583315 208990706917153541339374973)
      ·
        refine ⟨78371515093932578002265615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208990706917153541339374973 78371515093932578002265615)
        ·
          refine ⟨117557272640898867003398423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78371515093932578002265615 117557272640898867003398423)
          ·
            refine ⟨176335908961348300505097635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117557272640898867003398423 176335908961348300505097635)
            ·
              refine ⟨264503863442022450757646453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176335908961348300505097635 264503863442022450757646453)
              ·
                refine ⟨24797237197689604758529355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264503863442022450757646453 24797237197689604758529355)
                ·
                  refine ⟨37195855796534407137794033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24797237197689604758529355 37195855796534407137794033)
                  ·
                    refine ⟨27896891847400805353345525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37195855796534407137794033 27896891847400805353345525)
                    ·
                      refine ⟨2615333610693825501876143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27896891847400805353345525 2615333610693825501876143)
                      ·
                        rfl

theorem cell23_5093344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_5093344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093344 prefixEnd_5093344 := by exact prefixLift 5093344
  have htrace : WordTrace (prefixWord ++ tailWord_5093344) baseStart_5093344 baseEnd_5093344 := by
    simpa [prefixWord, tailWord_5093344, baseEnd_5093344] using wordTrace_append hprefix tailTrace_5093344
  have hstable : (prefixWord ++ tailWord_5093344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093344).length < 2 ^ (prefixWord ++ tailWord_5093344).sum := by decide
  have hdescent : baseEnd_5093344 < baseStart_5093344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093371 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 6, 2]
def baseStart_5093371 : Nat := 118140960795 + 5093371 * 2 ^ 59
def prefixEnd_5093371 : Nat := 4983230072969 + 3 ^ 40 * 5093371 * 2
def baseEnd_5093371 : Nat := 2615347474671496896238519

theorem tailTrace_5093371 : CollatzResearch.WordTrace tailWord_5093371 prefixEnd_5093371 2615347474671496896238519 := by
  unfold tailWord_5093371
  simp only [CollatzResearch.WordTrace]
  refine ⟨185770502030594220357343967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123847001353729480238229311 185770502030594220357343967)
  ·
    refine ⟨278655753045891330536015951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185770502030594220357343967 278655753045891330536015951)
    ·
      refine ⟨417983629568836995804023927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278655753045891330536015951 417983629568836995804023927)
      ·
        refine ⟨626975444353255493706035891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417983629568836995804023927 626975444353255493706035891)
        ·
          refine ⟨940463166529883240559053837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626975444353255493706035891 940463166529883240559053837)
          ·
            refine ⟨352673687448706215209645189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 940463166529883240559053837 352673687448706215209645189)
            ·
              refine ⟨66126316396632415351808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 352673687448706215209645189 66126316396632415351808473)
              ·
                refine ⟨49594737297474311513856355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66126316396632415351808473 49594737297474311513856355)
                ·
                  refine ⟨74392105946211467270784533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49594737297474311513856355 74392105946211467270784533)
                  ·
                    refine ⟨3487129966228662528318025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74392105946211467270784533 3487129966228662528318025)
                    ·
                      refine ⟨2615347474671496896238519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487129966228662528318025 2615347474671496896238519)
                      ·
                        rfl

theorem cell23_5093371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6, 2].length) (baseStart_5093371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093371 prefixEnd_5093371 := by exact prefixLift 5093371
  have htrace : WordTrace (prefixWord ++ tailWord_5093371) baseStart_5093371 baseEnd_5093371 := by
    simpa [prefixWord, tailWord_5093371, baseEnd_5093371] using wordTrace_append hprefix tailTrace_5093371
  have hstable : (prefixWord ++ tailWord_5093371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093371).length < 2 ^ (prefixWord ++ tailWord_5093371).sum := by decide
  have hdescent : baseEnd_5093371 < baseStart_5093371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093389 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5093389 : Nat := 118140960795 + 5093389 * 2 ^ 59
def prefixEnd_5093389 : Nat := 4983230072969 + 3 ^ 40 * 5093389 * 2
def baseEnd_5093389 : Nat := 290595190813697536201493

theorem tailTrace_5093389 : CollatzResearch.WordTrace tailWord_5093389 prefixEnd_5093389 290595190813697536201493 := by
  unfold tailWord_5093389
  simp only [CollatzResearch.WordTrace]
  refine ⟨185771158544529009431499221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123847439029686006287666147 185771158544529009431499221)
  ·
    refine ⟨4354011528387398658550763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 185771158544529009431499221 4354011528387398658550763)
    ·
      refine ⟨6531017292581097987826145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4354011528387398658550763 6531017292581097987826145)
      ·
        refine ⟨4898262969435823490869609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6531017292581097987826145 4898262969435823490869609)
        ·
          refine ⟨3673697227076867618152207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4898262969435823490869609 3673697227076867618152207)
          ·
            refine ⟨5510545840615301427228311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673697227076867618152207 5510545840615301427228311)
            ·
              refine ⟨8265818760922952140842467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5510545840615301427228311 8265818760922952140842467)
              ·
                refine ⟨12398728141384428211263701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265818760922952140842467 12398728141384428211263701)
                ·
                  refine ⟨290595190813697536201493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12398728141384428211263701 290595190813697536201493)
                  ·
                    rfl

theorem cell23_5093389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5093389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093389 prefixEnd_5093389 := by exact prefixLift 5093389
  have htrace : WordTrace (prefixWord ++ tailWord_5093389) baseStart_5093389 baseEnd_5093389 := by
    simpa [prefixWord, tailWord_5093389, baseEnd_5093389] using wordTrace_append hprefix tailTrace_5093389
  have hstable : (prefixWord ++ tailWord_5093389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093389).length < 2 ^ (prefixWord ++ tailWord_5093389).sum := by decide
  have hdescent : baseEnd_5093389 < baseStart_5093389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093411 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 6]
def baseStart_5093411 : Nat := 118140960795 + 5093411 * 2 ^ 59
def prefixEnd_5093411 : Nat := 4983230072969 + 3 ^ 40 * 5093411 * 2
def baseEnd_5093411 : Nat := 290596445988630748859815

theorem tailTrace_5093411 : CollatzResearch.WordTrace tailWord_5093411 prefixEnd_5093411 290596445988630748859815 := by
  unfold tailWord_5093411
  simp only [CollatzResearch.WordTrace]
  refine ⟨185771960950449307188800087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123847973966966204792533391 185771960950449307188800087)
  ·
    refine ⟨278657941425673960783200131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185771960950449307188800087 278657941425673960783200131)
    ·
      refine ⟨417986912138510941174800197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278657941425673960783200131 417986912138510941174800197)
      ·
        refine ⟨78372546025970801470275037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 417986912138510941174800197 78372546025970801470275037)
        ·
          refine ⟨29389704759739050551353139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78372546025970801470275037 29389704759739050551353139)
          ·
            refine ⟨44084557139608575827029709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29389704759739050551353139 44084557139608575827029709)
            ·
              refine ⟨16531708927353215935136141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44084557139608575827029709 16531708927353215935136141)
              ·
                refine ⟨6199390847757455975676053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16531708927353215935136141 6199390847757455975676053)
                ·
                  refine ⟨290596445988630748859815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6199390847757455975676053 290596445988630748859815)
                  ·
                    rfl

theorem cell23_5093411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 6].length) (baseStart_5093411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093411 prefixEnd_5093411 := by exact prefixLift 5093411
  have htrace : WordTrace (prefixWord ++ tailWord_5093411) baseStart_5093411 baseEnd_5093411 := by
    simpa [prefixWord, tailWord_5093411, baseEnd_5093411] using wordTrace_append hprefix tailTrace_5093411
  have hstable : (prefixWord ++ tailWord_5093411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093411).length < 2 ^ (prefixWord ++ tailWord_5093411).sum := by decide
  have hdescent : baseEnd_5093411 < baseStart_5093411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093448 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_5093448 : Nat := 118140960795 + 5093448 * 2 ^ 59
def prefixEnd_5093448 : Nat := 4983230072969 + 3 ^ 40 * 5093448 * 2
def baseEnd_5093448 : Nat := 2615387012681893094975665

theorem tailTrace_5093448 : CollatzResearch.WordTrace tailWord_5093448 prefixEnd_5093448 2615387012681893094975665 := by
  unfold tailWord_5093448
  simp only [CollatzResearch.WordTrace]
  refine ⟨92886655225657631253948499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123848873634210175005264665 92886655225657631253948499)
  ·
    refine ⟨139329982838486446880922749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92886655225657631253948499 139329982838486446880922749)
    ·
      refine ⟨52248743564432417580346031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139329982838486446880922749 52248743564432417580346031)
      ·
        refine ⟨78373115346648626370519047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52248743564432417580346031 78373115346648626370519047)
        ·
          refine ⟨117559673019972939555778571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78373115346648626370519047 117559673019972939555778571)
          ·
            refine ⟨176339509529959409333667857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117559673019972939555778571 176339509529959409333667857)
            ·
              refine ⟨132254632147469557000250893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176339509529959409333667857 132254632147469557000250893)
              ·
                refine ⟨49595487055301083875094085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132254632147469557000250893 49595487055301083875094085)
                ·
                  refine ⟨9299153822868953226580141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49595487055301083875094085 9299153822868953226580141)
                  ·
                    refine ⟨3487182683575857459967553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9299153822868953226580141 3487182683575857459967553)
                    ·
                      refine ⟨2615387012681893094975665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487182683575857459967553 2615387012681893094975665)
                      ·
                        rfl

theorem cell23_5093448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_5093448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093448 prefixEnd_5093448 := by exact prefixLift 5093448
  have htrace : WordTrace (prefixWord ++ tailWord_5093448) baseStart_5093448 baseEnd_5093448 := by
    simpa [prefixWord, tailWord_5093448, baseEnd_5093448] using wordTrace_append hprefix tailTrace_5093448
  have hstable : (prefixWord ++ tailWord_5093448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093448).length < 2 ^ (prefixWord ++ tailWord_5093448).sum := by decide
  have hdescent : baseEnd_5093448 < baseStart_5093448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093455 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 1, 1, 3]
def baseStart_5093455 : Nat := 118140960795 + 5093455 * 2 ^ 59
def prefixEnd_5093455 : Nat := 4983230072969 + 3 ^ 40 * 5093455 * 2
def baseEnd_5093455 : Nat := 2615390607046474567588133

theorem tailTrace_5093455 : CollatzResearch.WordTrace tailWord_5093455 prefixEnd_5093455 2615390607046474567588133 := by
  unfold tailWord_5093455
  simp only [CollatzResearch.WordTrace]
  refine ⟨185773565762289902703401819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123849043841526601802267879 185773565762289902703401819)
  ·
    refine ⟨278660348643434854055102729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185773565762289902703401819 278660348643434854055102729)
    ·
      refine ⟨208995261482576140541327047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278660348643434854055102729 208995261482576140541327047)
      ·
        refine ⟨313492892223864210811990571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208995261482576140541327047 313492892223864210811990571)
        ·
          refine ⟨470239338335796316217985857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313492892223864210811990571 470239338335796316217985857)
          ·
            refine ⟨352679503751847237163489393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470239338335796316217985857 352679503751847237163489393)
            ·
              refine ⟨264509627813885427872617045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352679503751847237163489393 264509627813885427872617045)
              ·
                refine ⟨3099722200943969857882231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 264509627813885427872617045 3099722200943969857882231)
                ·
                  refine ⟨4649583301415954786823347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099722200943969857882231 4649583301415954786823347)
                  ·
                    refine ⟨6974374952123932180235021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4649583301415954786823347 6974374952123932180235021)
                    ·
                      refine ⟨2615390607046474567588133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6974374952123932180235021 2615390607046474567588133)
                      ·
                        rfl

theorem cell23_5093455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 1, 3].length) (baseStart_5093455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093455 prefixEnd_5093455 := by exact prefixLift 5093455
  have htrace : WordTrace (prefixWord ++ tailWord_5093455) baseStart_5093455 baseEnd_5093455 := by
    simpa [prefixWord, tailWord_5093455, baseEnd_5093455] using wordTrace_append hprefix tailTrace_5093455
  have hstable : (prefixWord ++ tailWord_5093455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093455).length < 2 ^ (prefixWord ++ tailWord_5093455).sum := by decide
  have hdescent : baseEnd_5093455 < baseStart_5093455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093495 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_5093495 : Nat := 118140960795 + 5093495 * 2 ^ 59
def prefixEnd_5093495 : Nat := 4983230072969 + 3 ^ 40 * 5093495 * 2
def baseEnd_5093495 : Nat := 2615411146272654411087949

theorem tailTrace_5093495 : CollatzResearch.WordTrace tailWord_5093495 prefixEnd_5093495 2615411146272654411087949 := by
  unfold tailWord_5093495
  simp only [CollatzResearch.WordTrace]
  refine ⟨185775024682144989534857939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123850016454763326356571959 185775024682144989534857939)
  ·
    refine ⟨278662537023217484302286909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185775024682144989534857939 278662537023217484302286909)
    ·
      refine ⟨104498451383706556613357591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278662537023217484302286909 104498451383706556613357591)
      ·
        refine ⟨156747677075559834920036387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104498451383706556613357591 156747677075559834920036387)
        ·
          refine ⟨235121515613339752380054581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156747677075559834920036387 235121515613339752380054581)
          ·
            refine ⟨22042642088750601785630117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235121515613339752380054581 22042642088750601785630117)
            ·
              refine ⟨4132995391640737834805647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22042642088750601785630117 4132995391640737834805647)
              ·
                refine ⟨6199493087461106752208471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132995391640737834805647 6199493087461106752208471)
                ·
                  refine ⟨9299239631191660128312707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6199493087461106752208471 9299239631191660128312707)
                  ·
                    refine ⟨13948859446787490192469061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9299239631191660128312707 13948859446787490192469061)
                    ·
                      refine ⟨2615411146272654411087949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13948859446787490192469061 2615411146272654411087949)
                      ·
                        rfl

theorem cell23_5093495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_5093495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093495 prefixEnd_5093495 := by exact prefixLift 5093495
  have htrace : WordTrace (prefixWord ++ tailWord_5093495) baseStart_5093495 baseEnd_5093495 := by
    simpa [prefixWord, tailWord_5093495, baseEnd_5093495] using wordTrace_append hprefix tailTrace_5093495
  have hstable : (prefixWord ++ tailWord_5093495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093495).length < 2 ^ (prefixWord ++ tailWord_5093495).sum := by decide
  have hdescent : baseEnd_5093495 < baseStart_5093495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093501 : List Nat := [1, 4, 1, 1, 3, 3, 10]
def baseStart_5093501 : Nat := 118140960795 + 5093501 * 2 ^ 59
def prefixEnd_5093501 : Nat := 4983230072969 + 3 ^ 40 * 5093501 * 2
def baseEnd_5093501 : Nat := 32289064532797301081641

theorem tailTrace_5093501 : CollatzResearch.WordTrace tailWord_5093501 prefixEnd_5093501 32289064532797301081641 := by
  unfold tailWord_5093501
  simp only [CollatzResearch.WordTrace]
  refine ⟨185775243520123252559576357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123850162346748835039717571 185775243520123252559576357)
  ·
    refine ⟨34832858160023109854920567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185775243520123252559576357 34832858160023109854920567)
    ·
      refine ⟨52249287240034664782380851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34832858160023109854920567 52249287240034664782380851)
      ·
        refine ⟨78373930860051997173571277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52249287240034664782380851 78373930860051997173571277)
        ·
          refine ⟨29390224072519498940089229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78373930860051997173571277 29390224072519498940089229)
          ·
            refine ⟨11021334027194812102533461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29390224072519498940089229 11021334027194812102533461)
            ·
              refine ⟨32289064532797301081641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11021334027194812102533461 32289064532797301081641)
              ·
                rfl

theorem cell23_5093501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 10].length) (baseStart_5093501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093501 prefixEnd_5093501 := by exact prefixLift 5093501
  have htrace : WordTrace (prefixWord ++ tailWord_5093501) baseStart_5093501 baseEnd_5093501 := by
    simpa [prefixWord, tailWord_5093501, baseEnd_5093501] using wordTrace_append hprefix tailTrace_5093501
  have hstable : (prefixWord ++ tailWord_5093501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093501).length < 2 ^ (prefixWord ++ tailWord_5093501).sum := by decide
  have hdescent : baseEnd_5093501 < baseStart_5093501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093505 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_5093505 : Nat := 118140960795 + 5093505 * 2 ^ 59
def prefixEnd_5093505 : Nat := 4983230072969 + 3 ^ 40 * 5093505 * 2
def baseEnd_5093505 : Nat := 871805427026399790654301

theorem tailTrace_5093505 : CollatzResearch.WordTrace tailWord_5093505 prefixEnd_5093505 871805427026399790654301 := by
  unfold tailWord_5093505
  simp only [CollatzResearch.WordTrace]
  refine ⟨185775389412108761242721969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123850259608072507495147979 185775389412108761242721969)
  ·
    refine ⟨139331542059081570932041477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185775389412108761242721969 139331542059081570932041477)
    ·
      refine ⟨26124664136077794549757777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139331542059081570932041477 26124664136077794549757777)
      ·
        refine ⟨19593498102058345912318333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26124664136077794549757777 19593498102058345912318333)
        ·
          refine ⟨7347561788271879717119375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19593498102058345912318333 7347561788271879717119375)
          ·
            refine ⟨11021342682407819575679063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347561788271879717119375 11021342682407819575679063)
            ·
              refine ⟨16532014023611729363518595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11021342682407819575679063 16532014023611729363518595)
              ·
                refine ⟨24798021035417594045277893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16532014023611729363518595 24798021035417594045277893)
                ·
                  refine ⟨4649628944140798883489605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24798021035417594045277893 4649628944140798883489605)
                  ·
                    refine ⟨871805427026399790654301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649628944140798883489605 871805427026399790654301)
                    ·
                      rfl

theorem cell23_5093505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_5093505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093505 prefixEnd_5093505 := by exact prefixLift 5093505
  have htrace : WordTrace (prefixWord ++ tailWord_5093505) baseStart_5093505 baseEnd_5093505 := by
    simpa [prefixWord, tailWord_5093505, baseEnd_5093505] using wordTrace_append hprefix tailTrace_5093505
  have hstable : (prefixWord ++ tailWord_5093505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093505).length < 2 ^ (prefixWord ++ tailWord_5093505).sum := by decide
  have hdescent : baseEnd_5093505 < baseStart_5093505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093512 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5093512 : Nat := 118140960795 + 5093512 * 2 ^ 59
def prefixEnd_5093512 : Nat := 4983230072969 + 3 ^ 40 * 5093512 * 2
def baseEnd_5093512 : Nat := 2615419875443780844575371

theorem tailTrace_5093512 : CollatzResearch.WordTrace tailWord_5093512 prefixEnd_5093512 2615419875443780844575371 := by
  unfold tailWord_5093512
  simp only [CollatzResearch.WordTrace]
  refine ⟨92887822361541700719113395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123850429815388934292151193 92887822361541700719113395)
  ·
    refine ⟨139331733542312551078670093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92887822361541700719113395 139331733542312551078670093)
    ·
      refine ⟨52249400078367206654501285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139331733542312551078670093 52249400078367206654501285)
      ·
        refine ⟨9796762514693851247718991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52249400078367206654501285 9796762514693851247718991)
        ·
          refine ⟨14695143772040776871578487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9796762514693851247718991 14695143772040776871578487)
          ·
            refine ⟨22042715658061165307367731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14695143772040776871578487 22042715658061165307367731)
            ·
              refine ⟨33064073487091747961051597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22042715658061165307367731 33064073487091747961051597)
              ·
                refine ⟨12399027557659405485394349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33064073487091747961051597 12399027557659405485394349)
                ·
                  refine ⟨4649635334122277057022881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12399027557659405485394349 4649635334122277057022881)
                  ·
                    refine ⟨3487226500591707792767161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4649635334122277057022881 3487226500591707792767161)
                    ·
                      refine ⟨2615419875443780844575371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487226500591707792767161 2615419875443780844575371)
                      ·
                        rfl

theorem cell23_5093512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5093512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093512 prefixEnd_5093512 := by exact prefixLift 5093512
  have htrace : WordTrace (prefixWord ++ tailWord_5093512) baseStart_5093512 baseEnd_5093512 := by
    simpa [prefixWord, tailWord_5093512, baseEnd_5093512] using wordTrace_append hprefix tailTrace_5093512
  have hstable : (prefixWord ++ tailWord_5093512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093512).length < 2 ^ (prefixWord ++ tailWord_5093512).sum := by decide
  have hdescent : baseEnd_5093512 < baseStart_5093512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093522 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_5093522 : Nat := 118140960795 + 5093522 * 2 ^ 59
def prefixEnd_5093522 : Nat := 4983230072969 + 3 ^ 40 * 5093522 * 2
def baseEnd_5093522 : Nat := 871808336750108601816775

theorem tailTrace_5093522 : CollatzResearch.WordTrace tailWord_5093522 prefixEnd_5093522 871808336750108601816775 := by
  unfold tailWord_5093522
  simp only [CollatzResearch.WordTrace]
  refine ⟨46444002363261793286522705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123850672968698115430727213 46444002363261793286522705)
  ·
    refine ⟨34833001772446344964892029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46444002363261793286522705 34833001772446344964892029)
    ·
      refine ⟨13062375664667379361834511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34833001772446344964892029 13062375664667379361834511)
      ·
        refine ⟨19593563497001069042751767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13062375664667379361834511 19593563497001069042751767)
        ·
          refine ⟨29390345245501603564127651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19593563497001069042751767 29390345245501603564127651)
          ·
            refine ⟨44085517868252405346191477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29390345245501603564127651 44085517868252405346191477)
            ·
              refine ⟨4133017300148663001205451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44085517868252405346191477 4133017300148663001205451)
              ·
                refine ⟨6199525950222994501808177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133017300148663001205451 6199525950222994501808177)
                ·
                  refine ⟨4649644462667245876356133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6199525950222994501808177 4649644462667245876356133)
                  ·
                    refine ⟨871808336750108601816775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649644462667245876356133 871808336750108601816775)
                    ·
                      rfl

theorem cell23_5093522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_5093522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093522 prefixEnd_5093522 := by exact prefixLift 5093522
  have htrace : WordTrace (prefixWord ++ tailWord_5093522) baseStart_5093522 baseEnd_5093522 := by
    simpa [prefixWord, tailWord_5093522, baseEnd_5093522] using wordTrace_append hprefix tailTrace_5093522
  have hstable : (prefixWord ++ tailWord_5093522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093522).length < 2 ^ (prefixWord ++ tailWord_5093522).sum := by decide
  have hdescent : baseEnd_5093522 < baseStart_5093522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093535 : List Nat := [1, 1, 2, 6, 1, 3, 2, 7]
def baseStart_5093535 : Nat := 118140960795 + 5093535 * 2 ^ 59
def prefixEnd_5093535 : Nat := 4983230072969 + 3 ^ 40 * 5093535 * 2
def baseEnd_5093535 : Nat := 96867840203660527947695

theorem tailTrace_5093535 : CollatzResearch.WordTrace tailWord_5093535 prefixEnd_5093535 96867840203660527947695 := by
  unfold tailWord_5093535
  simp only [CollatzResearch.WordTrace]
  refine ⟨185776483602000076366314059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123850989068000050910876039 185776483602000076366314059)
  ·
    refine ⟨278664725403000114549471089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185776483602000076366314059 278664725403000114549471089)
    ·
      refine ⟨208998544052250085912103317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278664725403000114549471089 208998544052250085912103317)
      ·
        refine ⟨9796806752449222777129843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208998544052250085912103317 9796806752449222777129843)
        ·
          refine ⟨14695210128673834165694765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9796806752449222777129843 14695210128673834165694765)
          ·
            refine ⟨5510703798252687812135537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14695210128673834165694765 5510703798252687812135537)
            ·
              refine ⟨4133027848689515859101653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510703798252687812135537 4133027848689515859101653)
              ·
                refine ⟨96867840203660527947695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4133027848689515859101653 96867840203660527947695)
                ·
                  rfl

theorem cell23_5093535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 7].length) (baseStart_5093535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093535 prefixEnd_5093535 := by exact prefixLift 5093535
  have htrace : WordTrace (prefixWord ++ tailWord_5093535) baseStart_5093535 baseEnd_5093535 := by
    simpa [prefixWord, tailWord_5093535, baseEnd_5093535] using wordTrace_append hprefix tailTrace_5093535
  have hstable : (prefixWord ++ tailWord_5093535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093535).length < 2 ^ (prefixWord ++ tailWord_5093535).sum := by decide
  have hdescent : baseEnd_5093535 < baseStart_5093535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093541 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_5093541 : Nat := 118140960795 + 5093541 * 2 ^ 59
def prefixEnd_5093541 : Nat := 4983230072969 + 3 ^ 40 * 5093541 * 2
def baseEnd_5093541 : Nat := 2615434766382761231112737

theorem tailTrace_5093541 : CollatzResearch.WordTrace tailWord_5093541 prefixEnd_5093541 2615434766382761231112737 := by
  unfold tailWord_5093541
  simp only [CollatzResearch.WordTrace]
  refine ⟨185776702439978339391032477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123851134959985559594021651 185776702439978339391032477)
  ·
    refine ⟨69666263414991877271637179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185776702439978339391032477 69666263414991877271637179)
    ·
      refine ⟨104499395122487815907455769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69666263414991877271637179 104499395122487815907455769)
      ·
        refine ⟨78374546341865861930591827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104499395122487815907455769 78374546341865861930591827)
        ·
          refine ⟨117561819512798792895887741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78374546341865861930591827 117561819512798792895887741)
          ·
            refine ⟨44085682317299547335957903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117561819512798792895887741 44085682317299547335957903)
            ·
              refine ⟨66128523475949321003936855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44085682317299547335957903 66128523475949321003936855)
              ·
                refine ⟨99192785213923981505905283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66128523475949321003936855 99192785213923981505905283)
                ·
                  refine ⟨148789177820885972258857925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99192785213923981505905283 148789177820885972258857925)
                  ·
                    refine ⟨27897970841416119798535861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148789177820885972258857925 27897970841416119798535861)
                    ·
                      refine ⟨2615434766382761231112737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27897970841416119798535861 2615434766382761231112737)
                      ·
                        rfl

theorem cell23_5093541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_5093541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093541 prefixEnd_5093541 := by exact prefixLift 5093541
  have htrace : WordTrace (prefixWord ++ tailWord_5093541) baseStart_5093541 baseEnd_5093541 := by
    simpa [prefixWord, tailWord_5093541, baseEnd_5093541] using wordTrace_append hprefix tailTrace_5093541
  have hstable : (prefixWord ++ tailWord_5093541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093541).length < 2 ^ (prefixWord ++ tailWord_5093541).sum := by decide
  have hdescent : baseEnd_5093541 < baseStart_5093541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093551 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_5093551 : Nat := 118140960795 + 5093551 * 2 ^ 59
def prefixEnd_5093551 : Nat := 4983230072969 + 3 ^ 40 * 5093551 * 2
def baseEnd_5093551 : Nat := 2615439901189306191987691

theorem tailTrace_5093551 : CollatzResearch.WordTrace tailWord_5093551 prefixEnd_5093551 2615439901189306191987691 := by
  unfold tailWord_5093551
  simp only [CollatzResearch.WordTrace]
  refine ⟨185777067169942111098896507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123851378113294740732597671 185777067169942111098896507)
  ·
    refine ⟨278665600754913166648344761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185777067169942111098896507 278665600754913166648344761)
    ·
      refine ⟨208999200566184874986258571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278665600754913166648344761 208999200566184874986258571)
      ·
        refine ⟨313498800849277312479387857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208999200566184874986258571 313498800849277312479387857)
        ·
          refine ⟨235124100636957984359540893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313498800849277312479387857 235124100636957984359540893)
          ·
            refine ⟨88171537738859244134827835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235124100636957984359540893 88171537738859244134827835)
            ·
              refine ⟨132257306608288866202241753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88171537738859244134827835 132257306608288866202241753)
              ·
                refine ⟨99192979956216649651681315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132257306608288866202241753 99192979956216649651681315)
                ·
                  refine ⟨148789469934324974477521973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99192979956216649651681315 148789469934324974477521973)
                  ·
                    refine ⟨13949012806342966357267685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148789469934324974477521973 13949012806342966357267685)
                    ·
                      refine ⟨2615439901189306191987691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13949012806342966357267685 2615439901189306191987691)
                      ·
                        rfl

theorem cell23_5093551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_5093551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093551 prefixEnd_5093551 := by exact prefixLift 5093551
  have htrace : WordTrace (prefixWord ++ tailWord_5093551) baseStart_5093551 baseEnd_5093551 := by
    simpa [prefixWord, tailWord_5093551, baseEnd_5093551] using wordTrace_append hprefix tailTrace_5093551
  have hstable : (prefixWord ++ tailWord_5093551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093551).length < 2 ^ (prefixWord ++ tailWord_5093551).sum := by decide
  have hdescent : baseEnd_5093551 < baseStart_5093551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093591 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 9]
def baseStart_5093591 : Nat := 118140960795 + 5093591 * 2 ^ 59
def prefixEnd_5093591 : Nat := 4983230072969 + 3 ^ 40 * 5093591 * 2
def baseEnd_5093591 : Nat := 290606715601720670609723

theorem tailTrace_5093591 : CollatzResearch.WordTrace tailWord_5093591 prefixEnd_5093591 290606715601720670609723 := by
  unfold tailWord_5093591
  simp only [CollatzResearch.WordTrace]
  refine ⟨185778526089797197930352627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123852350726531465286901751 185778526089797197930352627)
  ·
    refine ⟨278667789134695796895528941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185778526089797197930352627 278667789134695796895528941)
    ·
      refine ⟨104500420925510923835823353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278667789134695796895528941 104500420925510923835823353)
      ·
        refine ⟨78375315694133192876867515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104500420925510923835823353 78375315694133192876867515)
        ·
          refine ⟨117562973541199789315301273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78375315694133192876867515 117562973541199789315301273)
          ·
            refine ⟨88172230155899841986475955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117562973541199789315301273 88172230155899841986475955)
            ·
              refine ⟨132258345233849762979713933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88172230155899841986475955 132258345233849762979713933)
              ·
                refine ⟨49596879462693661117392725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132258345233849762979713933 49596879462693661117392725)
                ·
                  refine ⟨290606715601720670609723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49596879462693661117392725 290606715601720670609723)
                  ·
                    rfl

theorem cell23_5093591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 9].length) (baseStart_5093591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093591 prefixEnd_5093591 := by exact prefixLift 5093591
  have htrace : WordTrace (prefixWord ++ tailWord_5093591) baseStart_5093591 baseEnd_5093591 := by
    simpa [prefixWord, tailWord_5093591, baseEnd_5093591] using wordTrace_append hprefix tailTrace_5093591
  have hstable : (prefixWord ++ tailWord_5093591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093591).length < 2 ^ (prefixWord ++ tailWord_5093591).sum := by decide
  have hdescent : baseEnd_5093591 < baseStart_5093591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093655 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 2, 5]
def baseStart_5093655 : Nat := 118140960795 + 5093655 * 2 ^ 59
def prefixEnd_5093655 : Nat := 4983230072969 + 3 ^ 40 * 5093655 * 2
def baseEnd_5093655 : Nat := 871831101059124595029071

theorem tailTrace_5093655 : CollatzResearch.WordTrace tailWord_5093655 prefixEnd_5093655 871831101059124595029071 := by
  unfold tailWord_5093655
  simp only [CollatzResearch.WordTrace]
  refine ⟨185780860361565336860682419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123853906907710224573788279 185780860361565336860682419)
  ·
    refine ⟨278671290542348005291023629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185780860361565336860682419 278671290542348005291023629)
    ·
      refine ⟨104501733953380501984133861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278671290542348005291023629 104501733953380501984133861)
      ·
        refine ⟨19594075116258844122025099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104501733953380501984133861 19594075116258844122025099)
        ·
          refine ⟨29391112674388266183037649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19594075116258844122025099 29391112674388266183037649)
          ·
            refine ⟨22043334505791199637278237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29391112674388266183037649 22043334505791199637278237)
            ·
              refine ⟨8266250439671699863979339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22043334505791199637278237 8266250439671699863979339)
              ·
                refine ⟨12399375659507549795969009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266250439671699863979339 12399375659507549795969009)
                ·
                  refine ⟨9299531744630662346976757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12399375659507549795969009 9299531744630662346976757)
                  ·
                    refine ⟨871831101059124595029071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9299531744630662346976757 871831101059124595029071)
                    ·
                      rfl

theorem cell23_5093655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_5093655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093655 prefixEnd_5093655 := by exact prefixLift 5093655
  have htrace : WordTrace (prefixWord ++ tailWord_5093655) baseStart_5093655 baseEnd_5093655 := by
    simpa [prefixWord, tailWord_5093655, baseEnd_5093655] using wordTrace_append hprefix tailTrace_5093655
  have hstable : (prefixWord ++ tailWord_5093655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093655).length < 2 ^ (prefixWord ++ tailWord_5093655).sum := by decide
  have hdescent : baseEnd_5093655 < baseStart_5093655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093736 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 1, 4]
def baseStart_5093736 : Nat := 118140960795 + 5093736 * 2 ^ 59
def prefixEnd_5093736 : Nat := 4983230072969 + 3 ^ 40 * 5093736 * 2
def baseEnd_5093736 : Nat := 871844965036795989391447

theorem tailTrace_5093736 : CollatzResearch.WordTrace tailWord_5093736 prefixEnd_5093736 871844965036795989391447 := by
  unfold tailWord_5093736
  simp only [CollatzResearch.WordTrace]
  refine ⟨92891907337135943847190531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123855876449514591796254041 92891907337135943847190531)
  ·
    refine ⟨139337861005703915770785797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92891907337135943847190531 139337861005703915770785797)
    ·
      refine ⟨26125848938569484207022337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139337861005703915770785797 26125848938569484207022337)
      ·
        refine ⟨19594386703927113155266753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26125848938569484207022337 19594386703927113155266753)
        ·
          refine ⟨14695790027945334866450065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19594386703927113155266753 14695790027945334866450065)
          ·
            refine ⟨11021842520959001149837549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14695790027945334866450065 11021842520959001149837549)
            ·
              refine ⟨4133190945359625431189081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11021842520959001149837549 4133190945359625431189081)
              ·
                refine ⟨3099893209019719073391811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133190945359625431189081 3099893209019719073391811)
                ·
                  refine ⟨4649839813529578610087717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099893209019719073391811 4649839813529578610087717)
                  ·
                    refine ⟨871844965036795989391447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649839813529578610087717 871844965036795989391447)
                    ·
                      rfl

theorem cell23_5093736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_5093736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093736 prefixEnd_5093736 := by exact prefixLift 5093736
  have htrace : WordTrace (prefixWord ++ tailWord_5093736) baseStart_5093736 baseEnd_5093736 := by
    simpa [prefixWord, tailWord_5093736, baseEnd_5093736] using wordTrace_append hprefix tailTrace_5093736
  have hstable : (prefixWord ++ tailWord_5093736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093736).length < 2 ^ (prefixWord ++ tailWord_5093736).sum := by decide
  have hdescent : baseEnd_5093736 < baseStart_5093736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093749 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 6]
def baseStart_5093749 : Nat := 118140960795 + 5093749 * 2 ^ 59
def prefixEnd_5093749 : Nat := 4983230072969 + 3 ^ 40 * 5093749 * 2
def baseEnd_5093749 : Nat := 290615730039877379701309

theorem tailTrace_5093749 : CollatzResearch.WordTrace tailWord_5093749 prefixEnd_5093749 290615730039877379701309 := by
  unfold tailWord_5093749
  simp only [CollatzResearch.WordTrace]
  refine ⟨185784288823224790914604301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123856192548816527276402867 185784288823224790914604301)
  ·
    refine ⟨69669108308709296592976613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185784288823224790914604301 69669108308709296592976613)
    ·
      refine ⟨13062957807882993111183115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69669108308709296592976613 13062957807882993111183115)
      ·
        refine ⟨19594436711824489666774673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13062957807882993111183115 19594436711824489666774673)
        ·
          refine ⟨14695827533868367250081005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19594436711824489666774673 14695827533868367250081005)
          ·
            refine ⟨5510935325200637718780377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14695827533868367250081005 5510935325200637718780377)
            ·
              refine ⟨4133201493900478289085283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510935325200637718780377 4133201493900478289085283)
              ·
                refine ⟨6199802240850717433627925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133201493900478289085283 6199802240850717433627925)
                ·
                  refine ⟨290615730039877379701309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6199802240850717433627925 290615730039877379701309)
                  ·
                    rfl

theorem cell23_5093749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_5093749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093749 prefixEnd_5093749 := by exact prefixLift 5093749
  have htrace : WordTrace (prefixWord ++ tailWord_5093749) baseStart_5093749 baseEnd_5093749 := by
    simpa [prefixWord, tailWord_5093749, baseEnd_5093749] using wordTrace_append hprefix tailTrace_5093749
  have hstable : (prefixWord ++ tailWord_5093749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093749).length < 2 ^ (prefixWord ++ tailWord_5093749).sum := by decide
  have hdescent : baseEnd_5093749 < baseStart_5093749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093769 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 2, 3, 2]
def baseStart_5093769 : Nat := 118140960795 + 5093769 * 2 ^ 59
def prefixEnd_5093769 : Nat := 4983230072969 + 3 ^ 40 * 5093769 * 2
def baseEnd_5093769 : Nat := 2615551839971986339061689

theorem tailTrace_5093769 : CollatzResearch.WordTrace tailWord_5093769 prefixEnd_5093769 2615551839971986339061689 := by
  unfold tailWord_5093769
  simp only [CollatzResearch.WordTrace]
  refine ⟨185785018283152334330332361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123856678855434889553554907 185785018283152334330332361)
  ·
    refine ⟨139338763712364250747749271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185785018283152334330332361 139338763712364250747749271)
    ·
      refine ⟨209008145568546376121623907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139338763712364250747749271 209008145568546376121623907)
      ·
        refine ⟨313512218352819564182435861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209008145568546376121623907 313512218352819564182435861)
        ·
          refine ⟨14695885235288417071051681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 313512218352819564182435861 14695885235288417071051681)
          ·
            refine ⟨11021913926466312803288761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14695885235288417071051681 11021913926466312803288761)
            ·
              refine ⟨8266435444849734602466571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11021913926466312803288761 8266435444849734602466571)
              ·
                refine ⟨12399653167274601903699857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266435444849734602466571 12399653167274601903699857)
                ·
                  refine ⟨9299739875455951427774893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12399653167274601903699857 9299739875455951427774893)
                  ·
                    refine ⟨3487402453295981785415585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9299739875455951427774893 3487402453295981785415585)
                    ·
                      refine ⟨2615551839971986339061689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487402453295981785415585 2615551839971986339061689)
                      ·
                        rfl

theorem cell23_5093769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3, 2].length) (baseStart_5093769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093769 prefixEnd_5093769 := by exact prefixLift 5093769
  have htrace : WordTrace (prefixWord ++ tailWord_5093769) baseStart_5093769 baseEnd_5093769 := by
    simpa [prefixWord, tailWord_5093769, baseEnd_5093769] using wordTrace_append hprefix tailTrace_5093769
  have hstable : (prefixWord ++ tailWord_5093769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093769).length < 2 ^ (prefixWord ++ tailWord_5093769).sum := by decide
  have hdescent : baseEnd_5093769 < baseStart_5093769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093788 : List Nat := [2, 2, 3, 16]
def baseStart_5093788 : Nat := 118140960795 + 5093788 * 2 ^ 59
def prefixEnd_5093788 : Nat := 4983230072969 + 3 ^ 40 * 5093788 * 2
def baseEnd_5093788 : Nat := 1195958663056434277423

theorem tailTrace_5093788 : CollatzResearch.WordTrace tailWord_5093788 prefixEnd_5093788 1195958663056434277423 := by
  unfold tailWord_5093788
  simp only [CollatzResearch.WordTrace]
  refine ⟨92892855635041750287637009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123857140846722333716849345 92892855635041750287637009)
  ·
    refine ⟨69669641726281312715727757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92892855635041750287637009 69669641726281312715727757)
    ·
      refine ⟨26126115647355492268397909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69669641726281312715727757 26126115647355492268397909)
      ·
        refine ⟨1195958663056434277423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 26126115647355492268397909 1195958663056434277423)
        ·
          rfl

theorem cell23_5093788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 16].length) (baseStart_5093788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093788 prefixEnd_5093788 := by exact prefixLift 5093788
  have htrace : WordTrace (prefixWord ++ tailWord_5093788) baseStart_5093788 baseEnd_5093788 := by
    simpa [prefixWord, tailWord_5093788, baseEnd_5093788] using wordTrace_append hprefix tailTrace_5093788
  have hstable : (prefixWord ++ tailWord_5093788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093788).length < 2 ^ (prefixWord ++ tailWord_5093788).sum := by decide
  have hdescent : baseEnd_5093788 < baseStart_5093788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093792 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_5093792 : Nat := 118140960795 + 5093792 * 2 ^ 59
def prefixEnd_5093792 : Nat := 4983230072969 + 3 ^ 40 * 5093792 * 2
def baseEnd_5093792 : Nat := 871854550009013249691361

theorem tailTrace_5093792 : CollatzResearch.WordTrace tailWord_5093792 prefixEnd_5093792 871854550009013249691361 := by
  unfold tailWord_5093792
  simp only [CollatzResearch.WordTrace]
  refine ⟨92892928581034504629209815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123857238108046006172279753 92892928581034504629209815)
  ·
    refine ⟨139339392871551756943814723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92892928581034504629209815 139339392871551756943814723)
    ·
      refine ⟨209009089307327635415722085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139339392871551756943814723 209009089307327635415722085)
      ·
        refine ⟨39189204245123931640447891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209009089307327635415722085 39189204245123931640447891)
        ·
          refine ⟨58783806367685897460671837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39189204245123931640447891 58783806367685897460671837)
          ·
            refine ⟨22043927387882211547751939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58783806367685897460671837 22043927387882211547751939)
            ·
              refine ⟨33065891081823317321627909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22043927387882211547751939 33065891081823317321627909)
              ·
                refine ⟨6199854577841871997805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33065891081823317321627909 6199854577841871997805233)
                ·
                  refine ⟨4649890933381403998353925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6199854577841871997805233 4649890933381403998353925)
                  ·
                    refine ⟨871854550009013249691361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649890933381403998353925 871854550009013249691361)
                    ·
                      rfl

theorem cell23_5093792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_5093792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093792 prefixEnd_5093792 := by exact prefixLift 5093792
  have htrace : WordTrace (prefixWord ++ tailWord_5093792) baseStart_5093792 baseEnd_5093792 := by
    simpa [prefixWord, tailWord_5093792, baseEnd_5093792] using wordTrace_append hprefix tailTrace_5093792
  have hstable : (prefixWord ++ tailWord_5093792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093792).length < 2 ^ (prefixWord ++ tailWord_5093792).sum := by decide
  have hdescent : baseEnd_5093792 < baseStart_5093792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093793 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5093793 : Nat := 118140960795 + 5093793 * 2 ^ 59
def prefixEnd_5093793 : Nat := 4983230072969 + 3 ^ 40 * 5093793 * 2
def baseEnd_5093793 : Nat := 2615564163507694245161579

theorem tailTrace_5093793 : CollatzResearch.WordTrace tailWord_5093793 prefixEnd_5093793 2615564163507694245161579 := by
  unfold tailWord_5093793
  simp only [CollatzResearch.WordTrace]
  refine ⟨185785893635065386429206033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123857262423376924286137355 185785893635065386429206033)
  ·
    refine ⟨139339420226299039821904525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185785893635065386429206033 139339420226299039821904525)
    ·
      refine ⟨52252282584862139933214197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139339420226299039821904525 52252282584862139933214197)
      ·
        refine ⟨4898651492330825618738831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52252282584862139933214197 4898651492330825618738831)
        ·
          refine ⟨7347977238496238428108247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898651492330825618738831 7347977238496238428108247)
          ·
            refine ⟨11021965857744357642162371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347977238496238428108247 11021965857744357642162371)
            ·
              refine ⟨16532948786616536463243557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11021965857744357642162371 16532948786616536463243557)
              ·
                refine ⟨3099927897490600586858167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16532948786616536463243557 3099927897490600586858167)
                ·
                  refine ⟨4649891846235900880287251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099927897490600586858167 4649891846235900880287251)
                  ·
                    refine ⟨6974837769353851320430877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4649891846235900880287251 6974837769353851320430877)
                    ·
                      refine ⟨2615564163507694245161579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6974837769353851320430877 2615564163507694245161579)
                      ·
                        rfl

theorem cell23_5093793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5093793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093793 prefixEnd_5093793 := by exact prefixLift 5093793
  have htrace : WordTrace (prefixWord ++ tailWord_5093793) baseStart_5093793 baseEnd_5093793 := by
    simpa [prefixWord, tailWord_5093793, baseEnd_5093793] using wordTrace_append hprefix tailTrace_5093793
  have hstable : (prefixWord ++ tailWord_5093793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093793).length < 2 ^ (prefixWord ++ tailWord_5093793).sum := by decide
  have hdescent : baseEnd_5093793 < baseStart_5093793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093832 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_5093832 : Nat := 118140960795 + 5093832 * 2 ^ 59
def prefixEnd_5093832 : Nat := 4983230072969 + 3 ^ 40 * 5093832 * 2
def baseEnd_5093832 : Nat := 2615584189253219592573899

theorem tailTrace_5093832 : CollatzResearch.WordTrace tailWord_5093832 prefixEnd_5093832 2615584189253219592573899 := by
  unfold tailWord_5093832
  simp only [CollatzResearch.WordTrace]
  refine ⟨92893658040962048044937875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123858210721282730726583833 92893658040962048044937875)
  ·
    refine ⟨139340487061443072067406813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92893658040962048044937875 139340487061443072067406813)
    ·
      refine ⟨52252682648041152025277555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139340487061443072067406813 52252682648041152025277555)
      ·
        refine ⟨78379023972061728037916333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52252682648041152025277555 78379023972061728037916333)
        ·
          refine ⟨29392133989523148014218625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78379023972061728037916333 29392133989523148014218625)
          ·
            refine ⟨22044100492142361010663969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29392133989523148014218625 22044100492142361010663969)
            ·
              refine ⟨16533075369106770757997977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22044100492142361010663969 16533075369106770757997977)
              ·
                refine ⟨12399806526830078068498483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16533075369106770757997977 12399806526830078068498483)
                ·
                  refine ⟨18599709790245117102747725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12399806526830078068498483 18599709790245117102747725)
                  ·
                    refine ⟨6974891171341918913530397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18599709790245117102747725 6974891171341918913530397)
                    ·
                      refine ⟨2615584189253219592573899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6974891171341918913530397 2615584189253219592573899)
                      ·
                        rfl

theorem cell23_5093832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_5093832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093832 prefixEnd_5093832 := by exact prefixLift 5093832
  have htrace : WordTrace (prefixWord ++ tailWord_5093832) baseStart_5093832 baseEnd_5093832 := by
    simpa [prefixWord, tailWord_5093832, baseEnd_5093832] using wordTrace_append hprefix tailTrace_5093832
  have hstable : (prefixWord ++ tailWord_5093832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093832).length < 2 ^ (prefixWord ++ tailWord_5093832).sum := by decide
  have hdescent : baseEnd_5093832 < baseStart_5093832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093875 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_5093875 : Nat := 118140960795 + 5093875 * 2 ^ 59
def prefixEnd_5093875 : Nat := 4983230072969 + 3 ^ 40 * 5093875 * 2
def baseEnd_5093875 : Nat := 2615606268921362924336201

theorem tailTrace_5093875 : CollatzResearch.WordTrace tailWord_5093875 prefixEnd_5093875 2615606268921362924336201 := by
  unfold tailWord_5093875
  simp only [CollatzResearch.WordTrace]
  refine ⟨185788884420768314433691079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123859256280512209622460719 185788884420768314433691079)
  ·
    refine ⟨278683326631152471650536619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185788884420768314433691079 278683326631152471650536619)
    ·
      refine ⟨418024989946728707475804929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278683326631152471650536619 418024989946728707475804929)
      ·
        refine ⟨313518742460046530606853697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418024989946728707475804929 313518742460046530606853697)
        ·
          refine ⟨235139056845034897955140273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313518742460046530606853697 235139056845034897955140273)
          ·
            refine ⟨176354292633776173466355205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235139056845034897955140273 176354292633776173466355205)
            ·
              refine ⟨33066429868833032524941601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176354292633776173466355205 33066429868833032524941601)
              ·
                refine ⟨24799822401624774393706201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33066429868833032524941601 24799822401624774393706201)
                ·
                  refine ⟨18599866801218580795279651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24799822401624774393706201 18599866801218580795279651)
                  ·
                    refine ⟨27899800201827871192919477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18599866801218580795279651 27899800201827871192919477)
                    ·
                      refine ⟨2615606268921362924336201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27899800201827871192919477 2615606268921362924336201)
                      ·
                        rfl

theorem cell23_5093875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_5093875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093875 prefixEnd_5093875 := by exact prefixLift 5093875
  have htrace : WordTrace (prefixWord ++ tailWord_5093875) baseStart_5093875 baseEnd_5093875 := by
    simpa [prefixWord, tailWord_5093875, baseEnd_5093875] using wordTrace_append hprefix tailTrace_5093875
  have hstable : (prefixWord ++ tailWord_5093875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093875).length < 2 ^ (prefixWord ++ tailWord_5093875).sum := by decide
  have hdescent : baseEnd_5093875 < baseStart_5093875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093892 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5093892 : Nat := 118140960795 + 5093892 * 2 ^ 59
def prefixEnd_5093892 : Nat := 4983230072969 + 3 ^ 40 * 5093892 * 2
def baseEnd_5093892 : Nat := 2615614998092489357823623

theorem tailTrace_5093892 : CollatzResearch.WordTrace tailWord_5093892 prefixEnd_5093892 2615614998092489357823623 := by
  unfold tailWord_5093892
  simp only [CollatzResearch.WordTrace]
  refine ⟨92894752230853363168529965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123859669641137817558039953 92894752230853363168529965)
  ·
    refine ⟨34835532086570011188198737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92894752230853363168529965 34835532086570011188198737)
    ·
      refine ⟨26126649064927508391149053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34835532086570011188198737 26126649064927508391149053)
      ·
        refine ⟨9797493399347815646680895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26126649064927508391149053 9797493399347815646680895)
        ·
          refine ⟨14696240099021723470021343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797493399347815646680895 14696240099021723470021343)
          ·
            refine ⟨22044360148532585205032015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14696240099021723470021343 22044360148532585205032015)
            ·
              refine ⟨33066540222798877807548023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22044360148532585205032015 33066540222798877807548023)
              ·
                refine ⟨49599810334198316711322035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33066540222798877807548023 49599810334198316711322035)
                ·
                  refine ⟨74399715501297475066983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49599810334198316711322035 74399715501297475066983053)
                  ·
                    refine ⟨27899893312986553150118645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74399715501297475066983053 27899893312986553150118645)
                    ·
                      refine ⟨2615614998092489357823623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27899893312986553150118645 2615614998092489357823623)
                      ·
                        rfl

theorem cell23_5093892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5093892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093892 prefixEnd_5093892 := by exact prefixLift 5093892
  have htrace : WordTrace (prefixWord ++ tailWord_5093892) baseStart_5093892 baseEnd_5093892 := by
    simpa [prefixWord, tailWord_5093892, baseEnd_5093892] using wordTrace_append hprefix tailTrace_5093892
  have hstable : (prefixWord ++ tailWord_5093892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093892).length < 2 ^ (prefixWord ++ tailWord_5093892).sum := by decide
  have hdescent : baseEnd_5093892 < baseStart_5093892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093912 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 7]
def baseStart_5093912 : Nat := 118140960795 + 5093912 * 2 ^ 59
def prefixEnd_5093912 : Nat := 4983230072969 + 3 ^ 40 * 5093912 * 2
def baseEnd_5093912 : Nat := 290625029745064364397059

theorem tailTrace_5093912 : CollatzResearch.WordTrace tailWord_5093912 prefixEnd_5093912 290625029745064364397059 := by
  unfold tailWord_5093912
  simp only [CollatzResearch.WordTrace]
  refine ⟨92895116960817134876393995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123860155947756179835191993 92895116960817134876393995)
  ·
    refine ⟨139342675441225702314590993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92895116960817134876393995 139342675441225702314590993)
    ·
      refine ⟨104507006580919276735943245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139342675441225702314590993 104507006580919276735943245)
      ·
        refine ⟨39190127467844728775978717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104507006580919276735943245 39190127467844728775978717)
        ·
          refine ⟨14696297800441773290992019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39190127467844728775978717 14696297800441773290992019)
          ·
            refine ⟨22044446700662659936488029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14696297800441773290992019 22044446700662659936488029)
            ·
              refine ⟨8266667512748497476183011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22044446700662659936488029 8266667512748497476183011)
              ·
                refine ⟨12400001269122746214274517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266667512748497476183011 12400001269122746214274517)
                ·
                  refine ⟨290625029745064364397059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12400001269122746214274517 290625029745064364397059)
                  ·
                    rfl

theorem cell23_5093912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_5093912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093912 prefixEnd_5093912 := by exact prefixLift 5093912
  have htrace : WordTrace (prefixWord ++ tailWord_5093912) baseStart_5093912 baseEnd_5093912 := by
    simpa [prefixWord, tailWord_5093912, baseEnd_5093912] using wordTrace_append hprefix tailTrace_5093912
  have hstable : (prefixWord ++ tailWord_5093912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093912).length < 2 ^ (prefixWord ++ tailWord_5093912).sum := by decide
  have hdescent : baseEnd_5093912 < baseStart_5093912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093922 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_5093922 : Nat := 118140960795 + 5093922 * 2 ^ 59
def prefixEnd_5093922 : Nat := 4983230072969 + 3 ^ 40 * 5093922 * 2
def baseEnd_5093922 : Nat := 2615630402512124240448485

theorem tailTrace_5093922 : CollatzResearch.WordTrace tailWord_5093922 prefixEnd_5093922 2615630402512124240448485 := by
  unfold tailWord_5093922
  simp only [CollatzResearch.WordTrace]
  refine ⟨46447649662899510365163005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123860399101065360973768013 46447649662899510365163005)
  ·
    refine ⟨17417868623587316386936127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46447649662899510365163005 17417868623587316386936127)
    ·
      refine ⟨26126802935380974580404191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17417868623587316386936127 26126802935380974580404191)
      ·
        refine ⟨39190204403071461870606287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26126802935380974580404191 39190204403071461870606287)
        ·
          refine ⟨58785306604607192805909431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39190204403071461870606287 58785306604607192805909431)
          ·
            refine ⟨88177959906910789208864147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58785306604607192805909431 88177959906910789208864147)
            ·
              refine ⟨132266939860366183813296221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88177959906910789208864147 132266939860366183813296221)
              ·
                refine ⟨49600102447637318929986083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132266939860366183813296221 49600102447637318929986083)
                ·
                  refine ⟨74400153671455978394979125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49600102447637318929986083 74400153671455978394979125)
                  ·
                    refine ⟨6975014406698997974529293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74400153671455978394979125 6975014406698997974529293)
                    ·
                      refine ⟨2615630402512124240448485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975014406698997974529293 2615630402512124240448485)
                      ·
                        rfl

theorem cell23_5093922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_5093922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093922 prefixEnd_5093922 := by exact prefixLift 5093922
  have htrace : WordTrace (prefixWord ++ tailWord_5093922) baseStart_5093922 baseEnd_5093922 := by
    simpa [prefixWord, tailWord_5093922, baseEnd_5093922] using wordTrace_append hprefix tailTrace_5093922
  have hstable : (prefixWord ++ tailWord_5093922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093922).length < 2 ^ (prefixWord ++ tailWord_5093922).sum := by decide
  have hdescent : baseEnd_5093922 < baseStart_5093922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093923 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 2, 2, 2]
def baseStart_5093923 : Nat := 118140960795 + 5093923 * 2 ^ 59
def prefixEnd_5093923 : Nat := 4983230072969 + 3 ^ 40 * 5093923 * 2
def baseEnd_5093923 : Nat := 2615630915992778736535981

theorem tailTrace_5093923 : CollatzResearch.WordTrace tailWord_5093923 prefixEnd_5093923 2615630915992778736535981 := by
  unfold tailWord_5093923
  simp only [CollatzResearch.WordTrace]
  refine ⟨185790635124594418631438423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123860423416396279087625615 185790635124594418631438423)
  ·
    refine ⟨278685952686891627947157635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185790635124594418631438423 278685952686891627947157635)
    ·
      refine ⟨418028929030337441920736453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278685952686891627947157635 418028929030337441920736453)
      ·
        refine ⟨78380424193188270360138085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418028929030337441920736453 78380424193188270360138085)
        ·
          refine ⟨14696329536222800692525891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78380424193188270360138085 14696329536222800692525891)
          ·
            refine ⟨22044494304334201038788837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14696329536222800692525891 22044494304334201038788837)
            ·
              refine ⟨4133342682062662694772907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22044494304334201038788837 4133342682062662694772907)
              ·
                refine ⟨6200014023093994042159361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133342682062662694772907 6200014023093994042159361)
                ·
                  refine ⟨4650010517320495531619521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6200014023093994042159361 4650010517320495531619521)
                  ·
                    refine ⟨3487507887990371648714641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650010517320495531619521 3487507887990371648714641)
                    ·
                      refine ⟨2615630915992778736535981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487507887990371648714641 2615630915992778736535981)
                      ·
                        rfl

theorem cell23_5093923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_5093923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093923 prefixEnd_5093923 := by exact prefixLift 5093923
  have htrace : WordTrace (prefixWord ++ tailWord_5093923) baseStart_5093923 baseEnd_5093923 := by
    simpa [prefixWord, tailWord_5093923, baseEnd_5093923] using wordTrace_append hprefix tailTrace_5093923
  have hstable : (prefixWord ++ tailWord_5093923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093923).length < 2 ^ (prefixWord ++ tailWord_5093923).sum := by decide
  have hdescent : baseEnd_5093923 < baseStart_5093923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093925 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_5093925 : Nat := 118140960795 + 5093925 * 2 ^ 59
def prefixEnd_5093925 : Nat := 4983230072969 + 3 ^ 40 * 5093925 * 2
def baseEnd_5093925 : Nat := 871877314318029242903657

theorem tailTrace_5093925 : CollatzResearch.WordTrace tailWord_5093925 prefixEnd_5093925 871877314318029242903657 := by
  unfold tailWord_5093925
  simp only [CollatzResearch.WordTrace]
  refine ⟨185790708070587172973011229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123860472047058115315340819 185790708070587172973011229)
  ·
    refine ⟨69671515526470189864879211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185790708070587172973011229 69671515526470189864879211)
    ·
      refine ⟨104507273289705284797318817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69671515526470189864879211 104507273289705284797318817)
      ·
        refine ⟨78380454967278963597989113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104507273289705284797318817 78380454967278963597989113)
        ·
          refine ⟨58785341225459222698491835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78380454967278963597989113 58785341225459222698491835)
          ·
            refine ⟨88178011838188834047737753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58785341225459222698491835 88178011838188834047737753)
            ·
              refine ⟨66133508878641625535803315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88178011838188834047737753 66133508878641625535803315)
              ·
                refine ⟨99200263317962438303704973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66133508878641625535803315 99200263317962438303704973)
                ·
                  refine ⟨37200098744235914363889365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99200263317962438303704973 37200098744235914363889365)
                  ·
                    refine ⟨871877314318029242903657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37200098744235914363889365 871877314318029242903657)
                    ·
                      rfl

theorem cell23_5093925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_5093925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093925 prefixEnd_5093925 := by exact prefixLift 5093925
  have htrace : WordTrace (prefixWord ++ tailWord_5093925) baseStart_5093925 baseEnd_5093925 := by
    simpa [prefixWord, tailWord_5093925, baseEnd_5093925] using wordTrace_append hprefix tailTrace_5093925
  have hstable : (prefixWord ++ tailWord_5093925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093925).length < 2 ^ (prefixWord ++ tailWord_5093925).sum := by decide
  have hdescent : baseEnd_5093925 < baseStart_5093925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093927 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5093927 : Nat := 118140960795 + 5093927 * 2 ^ 59
def prefixEnd_5093927 : Nat := 4983230072969 + 3 ^ 40 * 5093927 * 2
def baseEnd_5093927 : Nat := 2615632969915396720885963

theorem tailTrace_5093927 : CollatzResearch.WordTrace tailWord_5093927 prefixEnd_5093927 2615632969915396720885963 := by
  unfold tailWord_5093927
  simp only [CollatzResearch.WordTrace]
  refine ⟨185790781016579927314584035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123860520677719951543056023 185790781016579927314584035)
  ·
    refine ⟨278686171524869890971876053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185790781016579927314584035 278686171524869890971876053)
    ·
      refine ⟨6531707145114138069653345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 278686171524869890971876053 6531707145114138069653345)
      ·
        refine ⟨4898780358835603552240009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6531707145114138069653345 4898780358835603552240009)
        ·
          refine ⟨3674085269126702664180007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4898780358835603552240009 3674085269126702664180007)
          ·
            refine ⟨5511127903690053996270011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674085269126702664180007 5511127903690053996270011)
            ·
              refine ⟨8266691855535080994405017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511127903690053996270011 8266691855535080994405017)
              ·
                refine ⟨6200018891651310745803763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266691855535080994405017 6200018891651310745803763)
                ·
                  refine ⟨9300028337476966118705645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200018891651310745803763 9300028337476966118705645)
                  ·
                    refine ⟨3487510626553862294514617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9300028337476966118705645 3487510626553862294514617)
                    ·
                      refine ⟨2615632969915396720885963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487510626553862294514617 2615632969915396720885963)
                      ·
                        rfl

theorem cell23_5093927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5093927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093927 prefixEnd_5093927 := by exact prefixLift 5093927
  have htrace : WordTrace (prefixWord ++ tailWord_5093927) baseStart_5093927 baseEnd_5093927 := by
    simpa [prefixWord, tailWord_5093927, baseEnd_5093927] using wordTrace_append hprefix tailTrace_5093927
  have hstable : (prefixWord ++ tailWord_5093927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093927).length < 2 ^ (prefixWord ++ tailWord_5093927).sum := by decide
  have hdescent : baseEnd_5093927 < baseStart_5093927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093999 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_5093999 : Nat := 118140960795 + 5093999 * 2 ^ 59
def prefixEnd_5093999 : Nat := 4983230072969 + 3 ^ 40 * 5093999 * 2
def baseEnd_5093999 : Nat := 2615669940522520439185631

theorem tailTrace_5093999 : CollatzResearch.WordTrace tailWord_5093999 prefixEnd_5093999 2615669940522520439185631 := by
  unfold tailWord_5093999
  simp only [CollatzResearch.WordTrace]
  refine ⟨185793407072319083611205051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123862271381546055740803367 185793407072319083611205051)
  ·
    refine ⟨278690110608478625416807577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185793407072319083611205051 278690110608478625416807577)
    ·
      refine ⟨209017582956358969062605683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278690110608478625416807577 209017582956358969062605683)
      ·
        refine ⟨313526374434538453593908525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209017582956358969062605683 313526374434538453593908525)
        ·
          refine ⟨117572390412951920097715697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313526374434538453593908525 117572390412951920097715697)
          ·
            refine ⟨88179292809713940073286773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117572390412951920097715697 88179292809713940073286773)
            ·
              refine ⟨8266808700910681881870635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88179292809713940073286773 8266808700910681881870635)
              ·
                refine ⟨12400213051366022822805953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266808700910681881870635 12400213051366022822805953)
                ·
                  refine ⟨9300159788524517117104465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12400213051366022822805953 9300159788524517117104465)
                  ·
                    refine ⟨6975119841393387837828349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9300159788524517117104465 6975119841393387837828349)
                    ·
                      refine ⟨2615669940522520439185631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975119841393387837828349 2615669940522520439185631)
                      ·
                        rfl

theorem cell23_5093999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_5093999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5093999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5093999 prefixEnd_5093999 := by exact prefixLift 5093999
  have htrace : WordTrace (prefixWord ++ tailWord_5093999) baseStart_5093999 baseEnd_5093999 := by
    simpa [prefixWord, tailWord_5093999, baseEnd_5093999] using wordTrace_append hprefix tailTrace_5093999
  have hstable : (prefixWord ++ tailWord_5093999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093999).length < 2 ^ (prefixWord ++ tailWord_5093999).sum := by decide
  have hdescent : baseEnd_5093999 < baseStart_5093999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094039 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_5094039 : Nat := 118140960795 + 5094039 * 2 ^ 59
def prefixEnd_5094039 : Nat := 4983230072969 + 3 ^ 40 * 5094039 * 2
def baseEnd_5094039 : Nat := 2615690479748700282685447

theorem tailTrace_5094039 : CollatzResearch.WordTrace tailWord_5094039 prefixEnd_5094039 2615690479748700282685447 := by
  unfold tailWord_5094039
  simp only [CollatzResearch.WordTrace]
  refine ⟨185794865992174170442661171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123863243994782780295107447 185794865992174170442661171)
  ·
    refine ⟨278692298988261255663991757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185794865992174170442661171 278692298988261255663991757)
    ·
      refine ⟨104509612120597970873996909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278692298988261255663991757 104509612120597970873996909)
      ·
        refine ⟨39191104545224239077748841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104509612120597970873996909 39191104545224239077748841)
        ·
          refine ⟨29393328408918179308311631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39191104545224239077748841 29393328408918179308311631)
          ·
            refine ⟨44089992613377268962467447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29393328408918179308311631 44089992613377268962467447)
            ·
              refine ⟨66134988920065903443701171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44089992613377268962467447 66134988920065903443701171)
              ·
                refine ⟨99202483380098855165551757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66134988920065903443701171 99202483380098855165551757)
                ·
                  refine ⟨37200931267537070687081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99202483380098855165551757 37200931267537070687081909)
                  ·
                    refine ⟨3487587306331600376913929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37200931267537070687081909 3487587306331600376913929)
                    ·
                      refine ⟨2615690479748700282685447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487587306331600376913929 2615690479748700282685447)
                      ·
                        rfl

theorem cell23_5094039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_5094039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094039 prefixEnd_5094039 := by exact prefixLift 5094039
  have htrace : WordTrace (prefixWord ++ tailWord_5094039) baseStart_5094039 baseEnd_5094039 := by
    simpa [prefixWord, tailWord_5094039, baseEnd_5094039] using wordTrace_append hprefix tailTrace_5094039
  have hstable : (prefixWord ++ tailWord_5094039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094039).length < 2 ^ (prefixWord ++ tailWord_5094039).sum := by decide
  have hdescent : baseEnd_5094039 < baseStart_5094039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094063 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 1, 1, 3]
def baseStart_5094063 : Nat := 118140960795 + 5094063 * 2 ^ 59
def prefixEnd_5094063 : Nat := 4983230072969 + 3 ^ 40 * 5094063 * 2
def baseEnd_5094063 : Nat := 2615702803284408188785337

theorem tailTrace_5094063 : CollatzResearch.WordTrace tailWord_5094063 prefixEnd_5094063 2615702803284408188785337 := by
  unfold tailWord_5094063
  simp only [CollatzResearch.WordTrace]
  refine ⟨185795741344087222541534843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123863827562724815027689895 185795741344087222541534843)
  ·
    refine ⟨278693612016130833812302265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185795741344087222541534843 278693612016130833812302265)
    ·
      refine ⟨209020209012098125359226699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278693612016130833812302265 209020209012098125359226699)
      ·
        refine ⟨313530313518147188038840049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209020209012098125359226699 313530313518147188038840049)
        ·
          refine ⟨235147735138610391029130037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313530313518147188038840049 235147735138610391029130037)
          ·
            refine ⟨22045100169244724158980941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235147735138610391029130037 22045100169244724158980941)
            ·
              refine ⟨8266912563466771559617853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22045100169244724158980941 8266912563466771559617853)
              ·
                refine ⟨3100092211300039334856695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8266912563466771559617853 3100092211300039334856695)
                ·
                  refine ⟨4650138316950059002285043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100092211300039334856695 4650138316950059002285043)
                  ·
                    refine ⟨6975207475425088503427565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650138316950059002285043 6975207475425088503427565)
                    ·
                      refine ⟨2615702803284408188785337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975207475425088503427565 2615702803284408188785337)
                      ·
                        rfl

theorem cell23_5094063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 1, 3].length) (baseStart_5094063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094063 prefixEnd_5094063 := by exact prefixLift 5094063
  have htrace : WordTrace (prefixWord ++ tailWord_5094063) baseStart_5094063 baseEnd_5094063 := by
    simpa [prefixWord, tailWord_5094063, baseEnd_5094063] using wordTrace_append hprefix tailTrace_5094063
  have hstable : (prefixWord ++ tailWord_5094063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094063).length < 2 ^ (prefixWord ++ tailWord_5094063).sum := by decide
  have hdescent : baseEnd_5094063 < baseStart_5094063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094079 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 4, 4]
def baseStart_5094079 : Nat := 118140960795 + 5094079 * 2 ^ 59
def prefixEnd_5094079 : Nat := 4983230072969 + 3 ^ 40 * 5094079 * 2
def baseEnd_5094079 : Nat := 871903672991626708728421

theorem tailTrace_5094079 : CollatzResearch.WordTrace tailWord_5094079 prefixEnd_5094079 871903672991626708728421 := by
  unfold tailWord_5094079
  simp only [CollatzResearch.WordTrace]
  refine ⟨185796324912029257274117291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123864216608019504849411527 185796324912029257274117291)
  ·
    refine ⟨278694487368043885911175937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185796324912029257274117291 278694487368043885911175937)
    ·
      refine ⟨209020865526032914433381953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278694487368043885911175937 209020865526032914433381953)
      ·
        refine ⟨156765649144524685825036465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209020865526032914433381953 156765649144524685825036465)
        ·
          refine ⟨117574236858393514368777349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156765649144524685825036465 117574236858393514368777349)
          ·
            refine ⟨22045169410948783944145753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117574236858393514368777349 22045169410948783944145753)
            ·
              refine ⟨16533877058211587958109315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22045169410948783944145753 16533877058211587958109315)
              ·
                refine ⟨24800815587317381937163973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16533877058211587958109315 24800815587317381937163973)
                ·
                  refine ⟨4650152922622009113218245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24800815587317381937163973 4650152922622009113218245)
                  ·
                    refine ⟨871903672991626708728421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650152922622009113218245 871903672991626708728421)
                    ·
                      rfl

theorem cell23_5094079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_5094079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094079 prefixEnd_5094079 := by exact prefixLift 5094079
  have htrace : WordTrace (prefixWord ++ tailWord_5094079) baseStart_5094079 baseEnd_5094079 := by
    simpa [prefixWord, tailWord_5094079, baseEnd_5094079] using wordTrace_append hprefix tailTrace_5094079
  have hstable : (prefixWord ++ tailWord_5094079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094079).length < 2 ^ (prefixWord ++ tailWord_5094079).sum := by decide
  have hdescent : baseEnd_5094079 < baseStart_5094079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094080 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 1, 1, 3]
def baseStart_5094080 : Nat := 118140960795 + 5094080 * 2 ^ 59
def prefixEnd_5094080 : Nat := 4983230072969 + 3 ^ 40 * 5094080 * 2
def baseEnd_5094080 : Nat := 2615711532455534622272759

theorem tailTrace_5094080 : CollatzResearch.WordTrace tailWord_5094080 prefixEnd_5094080 2615711532455534622272759 := by
  unfold tailWord_5094080
  simp only [CollatzResearch.WordTrace]
  refine ⟨92898180692512817222451847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123864240923350422963269129 92898180692512817222451847)
  ·
    refine ⟨139347271038769225833677771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92898180692512817222451847 139347271038769225833677771)
    ·
      refine ⟨209020906558153838750516657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139347271038769225833677771 209020906558153838750516657)
      ·
        refine ⟨156765679918615379062887493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209020906558153838750516657 156765679918615379062887493)
        ·
          refine ⟨29393564984740383574291405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156765679918615379062887493 29393564984740383574291405)
          ·
            refine ⟨11022586869277643840359277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29393564984740383574291405 11022586869277643840359277)
            ·
              refine ⟨4133470075979116440134729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11022586869277643840359277 4133470075979116440134729)
              ·
                refine ⟨3100102556984337330101047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133470075979116440134729 3100102556984337330101047)
                ·
                  refine ⟨4650153835476505995151571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100102556984337330101047 4650153835476505995151571)
                  ·
                    refine ⟨6975230753214758992727357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650153835476505995151571 6975230753214758992727357)
                    ·
                      refine ⟨2615711532455534622272759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975230753214758992727357 2615711532455534622272759)
                      ·
                        rfl

theorem cell23_5094080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_5094080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094080 prefixEnd_5094080 := by exact prefixLift 5094080
  have htrace : WordTrace (prefixWord ++ tailWord_5094080) baseStart_5094080 baseEnd_5094080 := by
    simpa [prefixWord, tailWord_5094080, baseEnd_5094080] using wordTrace_append hprefix tailTrace_5094080
  have hstable : (prefixWord ++ tailWord_5094080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094080).length < 2 ^ (prefixWord ++ tailWord_5094080).sum := by decide
  have hdescent : baseEnd_5094080 < baseStart_5094080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094100 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_5094100 : Nat := 118140960795 + 5094100 * 2 ^ 59
def prefixEnd_5094100 : Nat := 4983230072969 + 3 ^ 40 * 5094100 * 2
def baseEnd_5094100 : Nat := 871907267356208181340889

theorem tailTrace_5094100 : CollatzResearch.WordTrace tailWord_5094100 prefixEnd_5094100 871907267356208181340889 := by
  unfold tailWord_5094100
  simp only [CollatzResearch.WordTrace]
  refine ⟨92898545422476588930315877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123864727229968785240421169 92898545422476588930315877)
  ·
    refine ⟨17418477266714360424434227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92898545422476588930315877 17418477266714360424434227)
    ·
      refine ⟨26127715900071540636651341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17418477266714360424434227 26127715900071540636651341)
      ·
        refine ⟨9797893462526827738744253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26127715900071540636651341 9797893462526827738744253)
        ·
          refine ⟨3674210048447560402029095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9797893462526827738744253 3674210048447560402029095)
          ·
            refine ⟨5511315072671340603043643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674210048447560402029095 5511315072671340603043643)
            ·
              refine ⟨8266972609007010904565465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511315072671340603043643 8266972609007010904565465)
              ·
                refine ⟨6200229456755258178424099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266972609007010904565465 6200229456755258178424099)
                ·
                  refine ⟨9300344185132887267636149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200229456755258178424099 9300344185132887267636149)
                  ·
                    refine ⟨871907267356208181340889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9300344185132887267636149 871907267356208181340889)
                    ·
                      rfl

theorem cell23_5094100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_5094100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094100 prefixEnd_5094100 := by exact prefixLift 5094100
  have htrace : WordTrace (prefixWord ++ tailWord_5094100) baseStart_5094100 baseEnd_5094100 := by
    simpa [prefixWord, tailWord_5094100, baseEnd_5094100] using wordTrace_append hprefix tailTrace_5094100
  have hstable : (prefixWord ++ tailWord_5094100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094100).length < 2 ^ (prefixWord ++ tailWord_5094100).sum := by decide
  have hdescent : baseEnd_5094100 < baseStart_5094100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094180 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_5094180 : Nat := 118140960795 + 5094180 * 2 ^ 59
def prefixEnd_5094180 : Nat := 4983230072969 + 3 ^ 40 * 5094180 * 2
def baseEnd_5094180 : Nat := 2615762880520984231022299

theorem tailTrace_5094180 : CollatzResearch.WordTrace tailWord_5094180 prefixEnd_5094180 2615762880520984231022299 := by
  unfold tailWord_5094180
  simp only [CollatzResearch.WordTrace]
  refine ⟨92900004342331675761771997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123866672456442234349029329 92900004342331675761771997)
  ·
    refine ⟨34837501628374378410664499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92900004342331675761771997 34837501628374378410664499)
    ·
      refine ⟨52256252442561567615996749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34837501628374378410664499 52256252442561567615996749)
      ·
        refine ⟨19596094665960587855998781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52256252442561567615996749 19596094665960587855998781)
        ·
          refine ⟨7348535499735220445999543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19596094665960587855998781 7348535499735220445999543)
          ·
            refine ⟨11022803249602830668999315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7348535499735220445999543 11022803249602830668999315)
            ·
              refine ⟨16534204874404246003498973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11022803249602830668999315 16534204874404246003498973)
              ·
                refine ⟨6200326827901592251312115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16534204874404246003498973 6200326827901592251312115)
                ·
                  refine ⟨9300490241852388376968173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200326827901592251312115 9300490241852388376968173)
                  ·
                    refine ⟨3487683840694645641363065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9300490241852388376968173 3487683840694645641363065)
                    ·
                      refine ⟨2615762880520984231022299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487683840694645641363065 2615762880520984231022299)
                      ·
                        rfl

theorem cell23_5094180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_5094180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094180 prefixEnd_5094180 := by exact prefixLift 5094180
  have htrace : WordTrace (prefixWord ++ tailWord_5094180) baseStart_5094180 baseEnd_5094180 := by
    simpa [prefixWord, tailWord_5094180, baseEnd_5094180] using wordTrace_append hprefix tailTrace_5094180
  have hstable : (prefixWord ++ tailWord_5094180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094180).length < 2 ^ (prefixWord ++ tailWord_5094180).sum := by decide
  have hdescent : baseEnd_5094180 < baseStart_5094180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094193 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_5094193 : Nat := 118140960795 + 5094193 * 2 ^ 59
def prefixEnd_5094193 : Nat := 4983230072969 + 3 ^ 40 * 5094193 * 2
def baseEnd_5094193 : Nat := 2615769555769492680159739

theorem tailTrace_5094193 : CollatzResearch.WordTrace tailWord_5094193 prefixEnd_5094193 2615769555769492680159739 := by
  unfold tailWord_5094193
  simp only [CollatzResearch.WordTrace]
  refine ⟨185800482833616254743767233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123866988555744169829178155 185800482833616254743767233)
  ·
    refine ⟨139350362125212191057825425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185800482833616254743767233 139350362125212191057825425)
    ·
      refine ⟨104512771593909143293369069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139350362125212191057825425 104512771593909143293369069)
      ·
        refine ⟨39192289347715928735013401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104512771593909143293369069 39192289347715928735013401)
        ·
          refine ⟨29394217010786946551260051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39192289347715928735013401 29394217010786946551260051)
          ·
            refine ⟨44091325516180419826890077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29394217010786946551260051 44091325516180419826890077)
            ·
              refine ⟨16534247068567657435083779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44091325516180419826890077 16534247068567657435083779)
              ·
                refine ⟨24801370602851486152625669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16534247068567657435083779 24801370602851486152625669)
                ·
                  refine ⟨4650256988034653653617313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24801370602851486152625669 4650256988034653653617313)
                  ·
                    refine ⟨3487692741025990240212985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650256988034653653617313 3487692741025990240212985)
                    ·
                      refine ⟨2615769555769492680159739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487692741025990240212985 2615769555769492680159739)
                      ·
                        rfl

theorem cell23_5094193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_5094193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094193 prefixEnd_5094193 := by exact prefixLift 5094193
  have htrace : WordTrace (prefixWord ++ tailWord_5094193) baseStart_5094193 baseEnd_5094193 := by
    simpa [prefixWord, tailWord_5094193, baseEnd_5094193] using wordTrace_append hprefix tailTrace_5094193
  have hstable : (prefixWord ++ tailWord_5094193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094193).length < 2 ^ (prefixWord ++ tailWord_5094193).sum := by decide
  have hdescent : baseEnd_5094193 < baseStart_5094193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094199 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 7]
def baseStart_5094199 : Nat := 118140960795 + 5094199 * 2 ^ 59
def prefixEnd_5094199 : Nat := 4983230072969 + 3 ^ 40 * 5094199 * 2
def baseEnd_5094199 : Nat := 290641404072602184076079

theorem tailTrace_5094199 : CollatzResearch.WordTrace tailWord_5094199 prefixEnd_5094199 290641404072602184076079 := by
  unfold tailWord_5094199
  simp only [CollatzResearch.WordTrace]
  refine ⟨185800701671594517768485651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123867134447729678512323767 185800701671594517768485651)
  ·
    refine ⟨278701052507391776652728477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185800701671594517768485651 278701052507391776652728477)
    ·
      refine ⟨104512894690271916244773179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278701052507391776652728477 104512894690271916244773179)
      ·
        refine ⟨156769342035407874367159769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104512894690271916244773179 156769342035407874367159769)
        ·
          refine ⟨117577006526555905775369827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156769342035407874367159769 117577006526555905775369827)
          ·
            refine ⟨176365509789833858663054741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117577006526555905775369827 176365509789833858663054741)
            ·
              refine ⟨8267133271398462124830691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 176365509789833858663054741 8267133271398462124830691)
              ·
                refine ⟨12400699907097693187246037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8267133271398462124830691 12400699907097693187246037)
                ·
                  refine ⟨290641404072602184076079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12400699907097693187246037 290641404072602184076079)
                  ·
                    rfl

theorem cell23_5094199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 7].length) (baseStart_5094199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094199 prefixEnd_5094199 := by exact prefixLift 5094199
  have htrace : WordTrace (prefixWord ++ tailWord_5094199) baseStart_5094199 baseEnd_5094199 := by
    simpa [prefixWord, tailWord_5094199, baseEnd_5094199] using wordTrace_append hprefix tailTrace_5094199
  have hstable : (prefixWord ++ tailWord_5094199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094199).length < 2 ^ (prefixWord ++ tailWord_5094199).sum := by decide
  have hdescent : baseEnd_5094199 < baseStart_5094199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094214 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5094214 : Nat := 118140960795 + 5094214 * 2 ^ 59
def prefixEnd_5094214 : Nat := 4983230072969 + 3 ^ 40 * 5094214 * 2
def baseEnd_5094214 : Nat := 2615780338863237097997143

theorem tailTrace_5094214 : CollatzResearch.WordTrace tailWord_5094214 prefixEnd_5094214 2615780338863237097997143 := by
  unfold tailWord_5094214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806289023954380479071303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123867499177693450220187797 5806289023954380479071303)
  ·
    refine ⟨8709433535931570718606955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5806289023954380479071303 8709433535931570718606955)
    ·
      refine ⟨13064150303897356077910433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8709433535931570718606955 13064150303897356077910433)
      ·
        refine ⟨9798112727923017058432825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13064150303897356077910433 9798112727923017058432825)
        ·
          refine ⟨7348584545942262793824619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9798112727923017058432825 7348584545942262793824619)
          ·
            refine ⟨11022876818913394190736929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7348584545942262793824619 11022876818913394190736929)
            ·
              refine ⟨8267157614185045643052697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11022876818913394190736929 8267157614185045643052697)
              ·
                refine ⟨6200368210638784232289523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8267157614185045643052697 6200368210638784232289523)
                ·
                  refine ⟨9300552315958176348434285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200368210638784232289523 9300552315958176348434285)
                  ·
                    refine ⟨3487707118484316130662857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9300552315958176348434285 3487707118484316130662857)
                    ·
                      refine ⟨2615780338863237097997143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487707118484316130662857 2615780338863237097997143)
                      ·
                        rfl

theorem cell23_5094214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5094214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094214 prefixEnd_5094214 := by exact prefixLift 5094214
  have htrace : WordTrace (prefixWord ++ tailWord_5094214) baseStart_5094214 baseEnd_5094214 := by
    simpa [prefixWord, tailWord_5094214, baseEnd_5094214] using wordTrace_append hprefix tailTrace_5094214
  have hstable : (prefixWord ++ tailWord_5094214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094214).length < 2 ^ (prefixWord ++ tailWord_5094214).sum := by decide
  have hdescent : baseEnd_5094214 < baseStart_5094214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094229 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_5094229 : Nat := 118140960795 + 5094229 * 2 ^ 59
def prefixEnd_5094229 : Nat := 4983230072969 + 3 ^ 40 * 5094229 * 2
def baseEnd_5094229 : Nat := 871929347024351513103191

theorem tailTrace_5094229 : CollatzResearch.WordTrace tailWord_5094229 prefixEnd_5094229 871929347024351513103191 := by
  unfold tailWord_5094229
  simp only [CollatzResearch.WordTrace]
  refine ⟨185801795861485832892077741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123867863907657221928051827 185801795861485832892077741)
  ·
    refine ⟨69675673448057187334529153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185801795861485832892077741 69675673448057187334529153)
    ·
      refine ⟨52256755086042890500896865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69675673448057187334529153 52256755086042890500896865)
      ·
        refine ⟨39192566314532167875672649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52256755086042890500896865 39192566314532167875672649)
        ·
          refine ⟨29394424735899125906754487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39192566314532167875672649 29394424735899125906754487)
          ·
            refine ⟨44091637103848688860131731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29394424735899125906754487 44091637103848688860131731)
            ·
              refine ⟨66137455655773033290197597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44091637103848688860131731 66137455655773033290197597)
              ·
                refine ⟨24801545870914887483824099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66137455655773033290197597 24801545870914887483824099)
                ·
                  refine ⟨37202318806372331225736149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24801545870914887483824099 37202318806372331225736149)
                  ·
                    refine ⟨871929347024351513103191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37202318806372331225736149 871929347024351513103191)
                    ·
                      rfl

theorem cell23_5094229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_5094229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094229 prefixEnd_5094229 := by exact prefixLift 5094229
  have htrace : WordTrace (prefixWord ++ tailWord_5094229) baseStart_5094229 baseEnd_5094229 := by
    simpa [prefixWord, tailWord_5094229, baseEnd_5094229] using wordTrace_append hprefix tailTrace_5094229
  have hstable : (prefixWord ++ tailWord_5094229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094229).length < 2 ^ (prefixWord ++ tailWord_5094229).sum := by decide
  have hdescent : baseEnd_5094229 < baseStart_5094229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094233 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 5]
def baseStart_5094233 : Nat := 118140960795 + 5094233 * 2 ^ 59
def prefixEnd_5094233 : Nat := 4983230072969 + 3 ^ 40 * 5094233 * 2
def baseEnd_5094233 : Nat := 290643343888408058184395

theorem tailTrace_5094233 : CollatzResearch.WordTrace tailWord_5094233 prefixEnd_5094233 290643343888408058184395 := by
  unfold tailWord_5094233
  simp only [CollatzResearch.WordTrace]
  refine ⟨185801941753471341575223353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123867961168980894383482235 185801941753471341575223353)
  ·
    refine ⟨139351456315103506181417515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185801941753471341575223353 139351456315103506181417515)
    ·
      refine ⟨209027184472655259272126273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139351456315103506181417515 209027184472655259272126273)
      ·
        refine ⟨156770388354491444454094705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209027184472655259272126273 156770388354491444454094705)
        ·
          refine ⟨117577791265868583340571029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156770388354491444454094705 117577791265868583340571029)
          ·
            refine ⟨5511458965587589844089267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117577791265868583340571029 5511458965587589844089267)
            ·
              refine ⟨8267188448381384766133901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511458965587589844089267 8267188448381384766133901)
              ·
                refine ⟨3100195668143019287300213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8267188448381384766133901 3100195668143019287300213)
                ·
                  refine ⟨290643343888408058184395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3100195668143019287300213 290643343888408058184395)
                  ·
                    rfl

theorem cell23_5094233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 5].length) (baseStart_5094233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094233 prefixEnd_5094233 := by exact prefixLift 5094233
  have htrace : WordTrace (prefixWord ++ tailWord_5094233) baseStart_5094233 baseEnd_5094233 := by
    simpa [prefixWord, tailWord_5094233, baseEnd_5094233] using wordTrace_append hprefix tailTrace_5094233
  have hstable : (prefixWord ++ tailWord_5094233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094233).length < 2 ^ (prefixWord ++ tailWord_5094233).sum := by decide
  have hdescent : baseEnd_5094233 < baseStart_5094233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094239 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5094239 : Nat := 118140960795 + 5094239 * 2 ^ 59
def prefixEnd_5094239 : Nat := 4983230072969 + 3 ^ 40 * 5094239 * 2
def baseEnd_5094239 : Nat := 2615793175879599500184527

theorem tailTrace_5094239 : CollatzResearch.WordTrace tailWord_5094239 prefixEnd_5094239 2615793175879599500184527 := by
  unfold tailWord_5094239
  simp only [CollatzResearch.WordTrace]
  refine ⟨185802160591449604599941771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123868107060966403066627847 185802160591449604599941771)
  ·
    refine ⟨278703240887174406899912657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185802160591449604599941771 278703240887174406899912657)
    ·
      refine ⟨209027430665380805174934493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278703240887174406899912657 209027430665380805174934493)
      ·
        refine ⟨78385286499517801940600435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209027430665380805174934493 78385286499517801940600435)
        ·
          refine ⟨117577929749276702910900653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78385286499517801940600435 117577929749276702910900653)
          ·
            refine ⟨44091723655978763591587745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117577929749276702910900653 44091723655978763591587745)
            ·
              refine ⟨33068792741984072693690809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44091723655978763591587745 33068792741984072693690809)
              ·
                refine ⟨24801594556488054520268107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33068792741984072693690809 24801594556488054520268107)
                ·
                  refine ⟨37202391834732081780402161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24801594556488054520268107 37202391834732081780402161)
                  ·
                    refine ⟨27901793876049061335301621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37202391834732081780402161 27901793876049061335301621)
                    ·
                      refine ⟨2615793175879599500184527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27901793876049061335301621 2615793175879599500184527)
                      ·
                        rfl

theorem cell23_5094239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5094239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094239 prefixEnd_5094239 := by exact prefixLift 5094239
  have htrace : WordTrace (prefixWord ++ tailWord_5094239) baseStart_5094239 baseEnd_5094239 := by
    simpa [prefixWord, tailWord_5094239, baseEnd_5094239] using wordTrace_append hprefix tailTrace_5094239
  have hstable : (prefixWord ++ tailWord_5094239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094239).length < 2 ^ (prefixWord ++ tailWord_5094239).sum := by decide
  have hdescent : baseEnd_5094239 < baseStart_5094239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094266 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_5094266 : Nat := 118140960795 + 5094266 * 2 ^ 59
def prefixEnd_5094266 : Nat := 4983230072969 + 3 ^ 40 * 5094266 * 2
def baseEnd_5094266 : Nat := 2615807039857270894546903

theorem tailTrace_5094266 : CollatzResearch.WordTrace tailWord_5094266 prefixEnd_5094266 2615807039857270894546903 := by
  unfold tailWord_5094266
  simp only [CollatzResearch.WordTrace]
  refine ⟨46450786340587947052793663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123868763574901192140783101 46450786340587947052793663)
  ·
    refine ⟨69676179510881920579190495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46450786340587947052793663 69676179510881920579190495)
    ·
      refine ⟨104514269266322880868785743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69676179510881920579190495 104514269266322880868785743)
      ·
        refine ⟨156771403899484321303178615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104514269266322880868785743 156771403899484321303178615)
        ·
          refine ⟨235157105849226481954767923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156771403899484321303178615 235157105849226481954767923)
          ·
            refine ⟨352735658773839722932151885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235157105849226481954767923 352735658773839722932151885)
            ·
              refine ⟨132275872040189896099556957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352735658773839722932151885 132275872040189896099556957)
              ·
                refine ⟨49603452015071211037333859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132275872040189896099556957 49603452015071211037333859)
                ·
                  refine ⟨74405178022606816556000789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49603452015071211037333859 74405178022606816556000789)
                  ·
                    refine ⟨3487742719809694526062537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74405178022606816556000789 3487742719809694526062537)
                    ·
                      refine ⟨2615807039857270894546903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487742719809694526062537 2615807039857270894546903)
                      ·
                        rfl

theorem cell23_5094266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_5094266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094266 prefixEnd_5094266 := by exact prefixLift 5094266
  have htrace : WordTrace (prefixWord ++ tailWord_5094266) baseStart_5094266 baseEnd_5094266 := by
    simpa [prefixWord, tailWord_5094266, baseEnd_5094266] using wordTrace_append hprefix tailTrace_5094266
  have hstable : (prefixWord ++ tailWord_5094266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094266).length < 2 ^ (prefixWord ++ tailWord_5094266).sum := by decide
  have hdescent : baseEnd_5094266 < baseStart_5094266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094276 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_5094276 : Nat := 118140960795 + 5094276 * 2 ^ 59
def prefixEnd_5094276 : Nat := 4983230072969 + 3 ^ 40 * 5094276 * 2
def baseEnd_5094276 : Nat := 871937391554605285140619

theorem tailTrace_5094276 : CollatzResearch.WordTrace tailWord_5094276 prefixEnd_5094276 871937391554605285140619 := by
  unfold tailWord_5094276
  simp only [CollatzResearch.WordTrace]
  refine ⟨92901755046157779959519341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123869006728210373279359121 92901755046157779959519341)
  ·
    refine ⟨34838158142309167484819753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92901755046157779959519341 34838158142309167484819753)
    ·
      refine ⟨26128618606731875613614815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34838158142309167484819753 26128618606731875613614815)
      ·
        refine ⟨39192927910097813420422223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26128618606731875613614815 39192927910097813420422223)
        ·
          refine ⟨58789391865146720130633335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39192927910097813420422223 58789391865146720130633335)
          ·
            refine ⟨88184087797720080195950003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58789391865146720130633335 88184087797720080195950003)
            ·
              refine ⟨132276131696580120293925005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88184087797720080195950003 132276131696580120293925005)
              ·
                refine ⟨49603549386217545110221877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132276131696580120293925005 49603549386217545110221877)
                ·
                  refine ⟨4650332754957894854083301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49603549386217545110221877 4650332754957894854083301)
                  ·
                    refine ⟨871937391554605285140619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650332754957894854083301 871937391554605285140619)
                    ·
                      rfl

theorem cell23_5094276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_5094276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094276 prefixEnd_5094276 := by exact prefixLift 5094276
  have htrace : WordTrace (prefixWord ++ tailWord_5094276) baseStart_5094276 baseEnd_5094276 := by
    simpa [prefixWord, tailWord_5094276, baseEnd_5094276] using wordTrace_append hprefix tailTrace_5094276
  have hstable : (prefixWord ++ tailWord_5094276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094276).length < 2 ^ (prefixWord ++ tailWord_5094276).sum := by decide
  have hdescent : baseEnd_5094276 < baseStart_5094276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094303 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5094303 : Nat := 118140960795 + 5094303 * 2 ^ 59
def prefixEnd_5094303 : Nat := 4983230072969 + 3 ^ 40 * 5094303 * 2
def baseEnd_5094303 : Nat := 2615826038641487249784233

theorem tailTrace_5094303 : CollatzResearch.WordTrace tailWord_5094303 prefixEnd_5094303 2615826038641487249784233 := by
  unfold tailWord_5094303
  simp only [CollatzResearch.WordTrace]
  refine ⟨185804494863217743530271563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123869663242145162353514375 185804494863217743530271563)
  ·
    refine ⟨278706742294826615295407345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185804494863217743530271563 278706742294826615295407345)
    ·
      refine ⟨209030056721119961471555509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278706742294826615295407345 209030056721119961471555509)
      ·
        refine ⟨19596567817604996387958329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209030056721119961471555509 19596567817604996387958329)
        ·
          refine ⟨14697425863203747290968747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19596567817604996387958329 14697425863203747290968747)
          ·
            refine ⟨22046138794805620936453121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14697425863203747290968747 22046138794805620936453121)
            ·
              refine ⟨16534604096104215702339841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22046138794805620936453121 16534604096104215702339841)
              ·
                refine ⟨12400953072078161776754881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16534604096104215702339841 12400953072078161776754881)
                ·
                  refine ⟨9300714804058621332566161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12400953072078161776754881 9300714804058621332566161)
                  ·
                    refine ⟨6975536103043965999424621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9300714804058621332566161 6975536103043965999424621)
                    ·
                      refine ⟨2615826038641487249784233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975536103043965999424621 2615826038641487249784233)
                      ·
                        rfl

theorem cell23_5094303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5094303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094303 prefixEnd_5094303 := by exact prefixLift 5094303
  have htrace : WordTrace (prefixWord ++ tailWord_5094303) baseStart_5094303 baseEnd_5094303 := by
    simpa [prefixWord, tailWord_5094303, baseEnd_5094303] using wordTrace_append hprefix tailTrace_5094303
  have hstable : (prefixWord ++ tailWord_5094303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094303).length < 2 ^ (prefixWord ++ tailWord_5094303).sum := by decide
  have hdescent : baseEnd_5094303 < baseStart_5094303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094317 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5094317 : Nat := 118140960795 + 5094317 * 2 ^ 59
def prefixEnd_5094317 : Nat := 4983230072969 + 3 ^ 40 * 5094317 * 2
def baseEnd_5094317 : Nat := 2615833227370650195009169

theorem tailTrace_5094317 : CollatzResearch.WordTrace tailWord_5094317 prefixEnd_5094317 2615833227370650195009169 := by
  unfold tailWord_5094317
  simp only [CollatzResearch.WordTrace]
  refine ⟨185805005485167023921281205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123870003656778015947520803 185805005485167023921281205)
  ·
    refine ⟨17419219264234408492620113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185805005485167023921281205 17419219264234408492620113)
    ·
      refine ⟨13064414448175806369465085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17419219264234408492620113 13064414448175806369465085)
      ·
        refine ⟨4899155418065927388549407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13064414448175806369465085 4899155418065927388549407)
        ·
          refine ⟨7348733127098891082824111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899155418065927388549407 7348733127098891082824111)
          ·
            refine ⟨11023099690648336624236167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7348733127098891082824111 11023099690648336624236167)
            ·
              refine ⟨16534649535972504936354251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11023099690648336624236167 16534649535972504936354251)
              ·
                refine ⟨24801974303958757404531377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16534649535972504936354251 24801974303958757404531377)
                ·
                  refine ⟨18601480727969068053398533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24801974303958757404531377 18601480727969068053398533)
                  ·
                    refine ⟨3487777636494200260012225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18601480727969068053398533 3487777636494200260012225)
                    ·
                      refine ⟨2615833227370650195009169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487777636494200260012225 2615833227370650195009169)
                      ·
                        rfl

theorem cell23_5094317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5094317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094317 prefixEnd_5094317 := by exact prefixLift 5094317
  have htrace : WordTrace (prefixWord ++ tailWord_5094317) baseStart_5094317 baseEnd_5094317 := by
    simpa [prefixWord, tailWord_5094317, baseEnd_5094317] using wordTrace_append hprefix tailTrace_5094317
  have hstable : (prefixWord ++ tailWord_5094317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094317).length < 2 ^ (prefixWord ++ tailWord_5094317).sum := by decide
  have hdescent : baseEnd_5094317 < baseStart_5094317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094336 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_5094336 : Nat := 118140960795 + 5094336 * 2 ^ 59
def prefixEnd_5094336 : Nat := 4983230072969 + 3 ^ 40 * 5094336 * 2
def baseEnd_5094336 : Nat := 871947661167695206890527

theorem tailTrace_5094336 : CollatzResearch.WordTrace tailWord_5094336 prefixEnd_5094336 871947661167695206890527 := by
  unfold tailWord_5094336
  simp only [CollatzResearch.WordTrace]
  refine ⟨92902849236049095083111431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123870465648065460110815241 92902849236049095083111431)
  ·
    refine ⟨139354273854073642624667147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92902849236049095083111431 139354273854073642624667147)
    ·
      refine ⟨209031410781110463937000721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139354273854073642624667147 209031410781110463937000721)
      ·
        refine ⟨156773558085832847952750541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209031410781110463937000721 156773558085832847952750541)
        ·
          refine ⟨58790084282187317982281453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156773558085832847952750541 58790084282187317982281453)
          ·
            refine ⟨22046281605820244243355545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58790084282187317982281453 22046281605820244243355545)
            ·
              refine ⟨16534711204365183182516659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22046281605820244243355545 16534711204365183182516659)
              ·
                refine ⟨24802066806547774773774989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16534711204365183182516659 24802066806547774773774989)
                ·
                  refine ⟨9300775052455415540165621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24802066806547774773774989 9300775052455415540165621)
                  ·
                    refine ⟨871947661167695206890527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9300775052455415540165621 871947661167695206890527)
                    ·
                      rfl

theorem cell23_5094336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_5094336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094336 prefixEnd_5094336 := by exact prefixLift 5094336
  have htrace : WordTrace (prefixWord ++ tailWord_5094336) baseStart_5094336 baseEnd_5094336 := by
    simpa [prefixWord, tailWord_5094336, baseEnd_5094336] using wordTrace_append hprefix tailTrace_5094336
  have hstable : (prefixWord ++ tailWord_5094336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094336).length < 2 ^ (prefixWord ++ tailWord_5094336).sum := by decide
  have hdescent : baseEnd_5094336 < baseStart_5094336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094376 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5094376 : Nat := 118140960795 + 5094376 * 2 ^ 59
def prefixEnd_5094376 : Nat := 4983230072969 + 3 ^ 40 * 5094376 * 2
def baseEnd_5094376 : Nat := 2615863522729265464171397

theorem tailTrace_5094376 : CollatzResearch.WordTrace tailWord_5094376 prefixEnd_5094376 2615863522729265464171397 := by
  unfold tailWord_5094376
  simp only [CollatzResearch.WordTrace]
  refine ⟨92903578695976638498839491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123871438261302184665119321 92903578695976638498839491)
  ·
    refine ⟨139355368043964957748259237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92903578695976638498839491 139355368043964957748259237)
    ·
      refine ⟨26129131508243429577798607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139355368043964957748259237 26129131508243429577798607)
      ·
        refine ⟨39193697262365144366697911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26129131508243429577798607 39193697262365144366697911)
        ·
          refine ⟨58790545893547716550046867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39193697262365144366697911 58790545893547716550046867)
          ·
            refine ⟨88185818840321574825070301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58790545893547716550046867 88185818840321574825070301)
            ·
              refine ⟨33069682065120590559401363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88185818840321574825070301 33069682065120590559401363)
              ·
                refine ⟨49604523097680885839102045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33069682065120590559401363 49604523097680885839102045)
                ·
                  refine ⟨18601696161630332189663267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49604523097680885839102045 18601696161630332189663267)
                  ·
                    refine ⟨27902544242445498284494901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18601696161630332189663267 27902544242445498284494901)
                    ·
                      refine ⟨2615863522729265464171397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27902544242445498284494901 2615863522729265464171397)
                      ·
                        rfl

theorem cell23_5094376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5094376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094376 prefixEnd_5094376 := by exact prefixLift 5094376
  have htrace : WordTrace (prefixWord ++ tailWord_5094376) baseStart_5094376 baseEnd_5094376 := by
    simpa [prefixWord, tailWord_5094376, baseEnd_5094376] using wordTrace_append hprefix tailTrace_5094376
  have hstable : (prefixWord ++ tailWord_5094376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094376).length < 2 ^ (prefixWord ++ tailWord_5094376).sum := by decide
  have hdescent : baseEnd_5094376 < baseStart_5094376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094383 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 1, 6]
def baseStart_5094383 : Nat := 118140960795 + 5094383 * 2 ^ 59
def prefixEnd_5094383 : Nat := 4983230072969 + 3 ^ 40 * 5094383 * 2
def baseEnd_5094383 : Nat := 871955705697948978927955

theorem tailTrace_5094383 : CollatzResearch.WordTrace tailWord_5094383 prefixEnd_5094383 871955705697948978927955 := by
  unfold tailWord_5094383
  simp only [CollatzResearch.WordTrace]
  refine ⟨185807412702927917193183803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123871608468618611462122535 185807412702927917193183803)
  ·
    refine ⟨278711119054391875789775705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185807412702927917193183803 278711119054391875789775705)
    ·
      refine ⟨209033339290793906842331779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278711119054391875789775705 209033339290793906842331779)
      ·
        refine ⟨313550008936190860263497669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209033339290793906842331779 313550008936190860263497669)
        ·
          refine ⟨58790626675535786299405813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313550008936190860263497669 58790626675535786299405813)
          ·
            refine ⟨5511621250831479965569295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58790626675535786299405813 5511621250831479965569295)
            ·
              refine ⟨8267431876247219948353943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511621250831479965569295 8267431876247219948353943)
              ·
                refine ⟨12401147814370829922530915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8267431876247219948353943 12401147814370829922530915)
                ·
                  refine ⟨18601721721556244883796373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12401147814370829922530915 18601721721556244883796373)
                  ·
                    refine ⟨871955705697948978927955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18601721721556244883796373 871955705697948978927955)
                    ·
                      rfl

theorem cell23_5094383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_5094383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094383 prefixEnd_5094383 := by exact prefixLift 5094383
  have htrace : WordTrace (prefixWord ++ tailWord_5094383) baseStart_5094383 baseEnd_5094383 := by
    simpa [prefixWord, tailWord_5094383, baseEnd_5094383] using wordTrace_append hprefix tailTrace_5094383
  have hstable : (prefixWord ++ tailWord_5094383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094383).length < 2 ^ (prefixWord ++ tailWord_5094383).sum := by decide
  have hdescent : baseEnd_5094383 < baseStart_5094383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094390 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5094390 : Nat := 118140960795 + 5094390 * 2 ^ 59
def prefixEnd_5094390 : Nat := 4983230072969 + 3 ^ 40 * 5094390 * 2
def baseEnd_5094390 : Nat := 2615870711458428409396333

theorem tailTrace_5094390 : CollatzResearch.WordTrace tailWord_5094390 prefixEnd_5094390 2615870711458428409396333 := by
  unfold tailWord_5094390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11612979250868909836793039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123871778675935038259125749 11612979250868909836793039)
  ·
    refine ⟨17419468876303364755189559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11612979250868909836793039 17419468876303364755189559)
    ·
      refine ⟨26129203314455047132784339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17419468876303364755189559 26129203314455047132784339)
      ·
        refine ⟨39193804971682570699176509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26129203314455047132784339 39193804971682570699176509)
        ·
          refine ⟨14697676864380964012191191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39193804971682570699176509 14697676864380964012191191)
          ·
            refine ⟨22046515296571446018286787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14697676864380964012191191 22046515296571446018286787)
            ·
              refine ⟨33069772944857169027430181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22046515296571446018286787 33069772944857169027430181)
              ·
                refine ⟨6200582427160719192643159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33069772944857169027430181 6200582427160719192643159)
                ·
                  refine ⟨9300873640741078788964739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200582427160719192643159 9300873640741078788964739)
                  ·
                    refine ⟨13951310461111618183447109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9300873640741078788964739 13951310461111618183447109)
                    ·
                      refine ⟨2615870711458428409396333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13951310461111618183447109 2615870711458428409396333)
                      ·
                        rfl

theorem cell23_5094390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5094390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094390 prefixEnd_5094390 := by exact prefixLift 5094390
  have htrace : WordTrace (prefixWord ++ tailWord_5094390) baseStart_5094390 baseEnd_5094390 := by
    simpa [prefixWord, tailWord_5094390, baseEnd_5094390] using wordTrace_append hprefix tailTrace_5094390
  have hstable : (prefixWord ++ tailWord_5094390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094390).length < 2 ^ (prefixWord ++ tailWord_5094390).sum := by decide
  have hdescent : baseEnd_5094390 < baseStart_5094390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094396 : List Nat := [2, 2, 2, 1, 2, 4, 1, 9]
def baseStart_5094396 : Nat := 118140960795 + 5094396 * 2 ^ 59
def prefixEnd_5094396 : Nat := 4983230072969 + 3 ^ 40 * 5094396 * 2
def baseEnd_5094396 : Nat := 96884214531198347626715

theorem tailTrace_5094396 : CollatzResearch.WordTrace tailWord_5094396 prefixEnd_5094396 96884214531198347626715 := by
  unfold tailWord_5094396
  simp only [CollatzResearch.WordTrace]
  refine ⟨92903943425940410206703521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123871924567920546942271361 92903943425940410206703521)
  ·
    refine ⟨69677957569455307655027641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92903943425940410206703521 69677957569455307655027641)
    ·
      refine ⟨52258468177091480741270731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69677957569455307655027641 52258468177091480741270731)
      ·
        refine ⟨78387702265637221111906097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52258468177091480741270731 78387702265637221111906097)
        ·
          refine ⟨58790776699227915833929573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78387702265637221111906097 58790776699227915833929573)
          ·
            refine ⟨11023270631105234218861795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58790776699227915833929573 11023270631105234218861795)
            ·
              refine ⟨16534905946657851328292693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11023270631105234218861795 16534905946657851328292693)
              ·
                refine ⟨96884214531198347626715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16534905946657851328292693 96884214531198347626715)
                ·
                  rfl

theorem cell23_5094396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 9].length) (baseStart_5094396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094396 prefixEnd_5094396 := by exact prefixLift 5094396
  have htrace : WordTrace (prefixWord ++ tailWord_5094396) baseStart_5094396 baseEnd_5094396 := by
    simpa [prefixWord, tailWord_5094396, baseEnd_5094396] using wordTrace_append hprefix tailTrace_5094396
  have hstable : (prefixWord ++ tailWord_5094396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094396).length < 2 ^ (prefixWord ++ tailWord_5094396).sum := by decide
  have hdescent : baseEnd_5094396 < baseStart_5094396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094410 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_5094410 : Nat := 118140960795 + 5094410 * 2 ^ 59
def prefixEnd_5094410 : Nat := 4983230072969 + 3 ^ 40 * 5094410 * 2
def baseEnd_5094410 : Nat := 2615880981071518331146241

theorem tailTrace_5094410 : CollatzResearch.WordTrace tailWord_5094410 prefixEnd_5094410 2615880981071518331146241 := by
  unfold tailWord_5094410
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452099368457525201104171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123872264982553400536277789 46452099368457525201104171)
  ·
    refine ⟨69678149052686287801656257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46452099368457525201104171 69678149052686287801656257)
    ·
      refine ⟨52258611789514715851242193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69678149052686287801656257 52258611789514715851242193)
      ·
        refine ⟨39193958842136036888431645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52258611789514715851242193 39193958842136036888431645)
        ·
          refine ⟨14697734565801013833161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39193958842136036888431645 14697734565801013833161867)
          ·
            refine ⟨22046601848701520749742801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14697734565801013833161867 22046601848701520749742801)
            ·
              refine ⟨16534951386526140562307101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22046601848701520749742801 16534951386526140562307101)
              ·
                refine ⟨6200606769947302710865163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16534951386526140562307101 6200606769947302710865163)
                ·
                  refine ⟨9300910154920954066297745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200606769947302710865163 9300910154920954066297745)
                  ·
                    refine ⟨6975682616190715549723309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9300910154920954066297745 6975682616190715549723309)
                    ·
                      refine ⟨2615880981071518331146241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975682616190715549723309 2615880981071518331146241)
                      ·
                        rfl

theorem cell23_5094410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_5094410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094410 prefixEnd_5094410 := by exact prefixLift 5094410
  have htrace : WordTrace (prefixWord ++ tailWord_5094410) baseStart_5094410 baseEnd_5094410 := by
    simpa [prefixWord, tailWord_5094410, baseEnd_5094410] using wordTrace_append hprefix tailTrace_5094410
  have hstable : (prefixWord ++ tailWord_5094410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094410).length < 2 ^ (prefixWord ++ tailWord_5094410).sum := by decide
  have hdescent : baseEnd_5094410 < baseStart_5094410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094418 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5094418 : Nat := 118140960795 + 5094418 * 2 ^ 59
def prefixEnd_5094418 : Nat := 4983230072969 + 3 ^ 40 * 5094418 * 2
def baseEnd_5094418 : Nat := 2615885088916754299846205

theorem tailTrace_5094418 : CollatzResearch.WordTrace tailWord_5094418 prefixEnd_5094418 2615885088916754299846205 := by
  unfold tailWord_5094418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452172314450279542676977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123872459505200745447138605 46452172314450279542676977)
  ·
    refine ⟨34839129235837709657007733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46452172314450279542676977 34839129235837709657007733)
    ·
      refine ⟨3266168365859785280344475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34839129235837709657007733 3266168365859785280344475)
      ·
        refine ⟨4899252548789677920516713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266168365859785280344475 4899252548789677920516713)
        ·
          refine ⟨3674439411592258440387535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899252548789677920516713 3674439411592258440387535)
          ·
            refine ⟨5511659117388387660581303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674439411592258440387535 5511659117388387660581303)
            ·
              refine ⟨8267488676082581490871955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511659117388387660581303 8267488676082581490871955)
              ·
                refine ⟨12401233014123872236307933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8267488676082581490871955 12401233014123872236307933)
                ·
                  refine ⟨4650462380296452088615475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12401233014123872236307933 4650462380296452088615475)
                  ·
                    refine ⟨6975693570444678132923213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650462380296452088615475 6975693570444678132923213)
                    ·
                      refine ⟨2615885088916754299846205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975693570444678132923213 2615885088916754299846205)
                      ·
                        rfl

theorem cell23_5094418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5094418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094418 prefixEnd_5094418 := by exact prefixLift 5094418
  have htrace : WordTrace (prefixWord ++ tailWord_5094418) baseStart_5094418 baseEnd_5094418 := by
    simpa [prefixWord, tailWord_5094418, baseEnd_5094418] using wordTrace_append hprefix tailTrace_5094418
  have hstable : (prefixWord ++ tailWord_5094418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094418).length < 2 ^ (prefixWord ++ tailWord_5094418).sum := by decide
  have hdescent : baseEnd_5094418 < baseStart_5094418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094426 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_5094426 : Nat := 118140960795 + 5094426 * 2 ^ 59
def prefixEnd_5094426 : Nat := 4983230072969 + 3 ^ 40 * 5094426 * 2
def baseEnd_5094426 : Nat := 871963065587330089515389

theorem tailTrace_5094426 : CollatzResearch.WordTrace tailWord_5094426 prefixEnd_5094426 871963065587330089515389 := by
  unfold tailWord_5094426
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452245260443033884249783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123872654027848090357999421 46452245260443033884249783)
  ·
    refine ⟨69678367890664550826374675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46452245260443033884249783 69678367890664550826374675)
    ·
      refine ⟨104517551835996826239562013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69678367890664550826374675 104517551835996826239562013)
      ·
        refine ⟨39194081938498809839835755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104517551835996826239562013 39194081938498809839835755)
        ·
          refine ⟨58791122907748214759753633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39194081938498809839835755 58791122907748214759753633)
          ·
            refine ⟨44093342180811161069815225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58791122907748214759753633 44093342180811161069815225)
            ·
              refine ⟨33070006635608370802361419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44093342180811161069815225 33070006635608370802361419)
              ·
                refine ⟨49605009953412556203542129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33070006635608370802361419 49605009953412556203542129)
                ·
                  refine ⟨37203757465059417152656597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49605009953412556203542129 37203757465059417152656597)
                  ·
                    refine ⟨871963065587330089515389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37203757465059417152656597 871963065587330089515389)
                    ·
                      rfl

theorem cell23_5094426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_5094426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094426 prefixEnd_5094426 := by exact prefixLift 5094426
  have htrace : WordTrace (prefixWord ++ tailWord_5094426) baseStart_5094426 baseEnd_5094426 := by
    simpa [prefixWord, tailWord_5094426, baseEnd_5094426] using wordTrace_append hprefix tailTrace_5094426
  have hstable : (prefixWord ++ tailWord_5094426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094426).length < 2 ^ (prefixWord ++ tailWord_5094426).sum := by decide
  have hdescent : baseEnd_5094426 < baseStart_5094426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094450 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_5094450 : Nat := 118140960795 + 5094450 * 2 ^ 59
def prefixEnd_5094450 : Nat := 4983230072969 + 3 ^ 40 * 5094450 * 2
def baseEnd_5094450 : Nat := 2615901520297698174646057

theorem tailTrace_5094450 : CollatzResearch.WordTrace tailWord_5094450 prefixEnd_5094450 2615901520297698174646057 := by
  unfold tailWord_5094450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452464098421296908968201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123873237595790125090581869 46452464098421296908968201)
  ·
    refine ⟨34839348073815972681726151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46452464098421296908968201 34839348073815972681726151)
    ·
      refine ⟨52259022110723959022589227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34839348073815972681726151 52259022110723959022589227)
      ·
        refine ⟨78388533166085938533883841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52259022110723959022589227 78388533166085938533883841)
        ·
          refine ⟨58791399874564453900412881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78388533166085938533883841 58791399874564453900412881)
          ·
            refine ⟨44093549905923340425309661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58791399874564453900412881 44093549905923340425309661)
            ·
              refine ⟨16535081214721252659491123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44093549905923340425309661 16535081214721252659491123)
              ·
                refine ⟨24802621822081878989236685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16535081214721252659491123 24802621822081878989236685)
                ·
                  refine ⟨9300983183280704620963757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24802621822081878989236685 9300983183280704620963757)
                  ·
                    refine ⟨3487868693730264232861409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9300983183280704620963757 3487868693730264232861409)
                    ·
                      refine ⟨2615901520297698174646057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487868693730264232861409 2615901520297698174646057)
                      ·
                        rfl

theorem cell23_5094450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_5094450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094450 prefixEnd_5094450 := by exact prefixLift 5094450
  have htrace : WordTrace (prefixWord ++ tailWord_5094450) baseStart_5094450 baseEnd_5094450 := by
    simpa [prefixWord, tailWord_5094450, baseEnd_5094450] using wordTrace_append hprefix tailTrace_5094450
  have hstable : (prefixWord ++ tailWord_5094450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094450).length < 2 ^ (prefixWord ++ tailWord_5094450).sum := by decide
  have hdescent : baseEnd_5094450 < baseStart_5094450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094467 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 1, 3, 2]
def baseStart_5094467 : Nat := 118140960795 + 5094467 * 2 ^ 59
def prefixEnd_5094467 : Nat := 4983230072969 + 3 ^ 40 * 5094467 * 2
def baseEnd_5094467 : Nat := 2615910249468824608133479

theorem tailTrace_5094467 : CollatzResearch.WordTrace tailWord_5094467 prefixEnd_5094467 2615910249468824608133479 := by
  unfold tailWord_5094467
  simp only [CollatzResearch.WordTrace]
  refine ⟨185810476434623599539241655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123873650956415733026161103 185810476434623599539241655)
  ·
    refine ⟨278715714651935399308862483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185810476434623599539241655 278715714651935399308862483)
    ·
      refine ⟨418073571977903098963293725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278715714651935399308862483 418073571977903098963293725)
      ·
        refine ⟨156777589491713662111235147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418073571977903098963293725 156777589491713662111235147)
        ·
          refine ⟨235166384237570493166852721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156777589491713662111235147 235166384237570493166852721)
          ·
            refine ⟨176374788178177869875139541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235166384237570493166852721 176374788178177869875139541)
            ·
              refine ⟨4133784097926043825198583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176374788178177869875139541 4133784097926043825198583)
              ·
                refine ⟨6200676146889065737797875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133784097926043825198583 6200676146889065737797875)
                ·
                  refine ⟨9301014220333598606696813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200676146889065737797875 9301014220333598606696813)
                  ·
                    refine ⟨3487880332625099477511305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9301014220333598606696813 3487880332625099477511305)
                    ·
                      refine ⟨2615910249468824608133479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487880332625099477511305 2615910249468824608133479)
                      ·
                        rfl

theorem cell23_5094467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_5094467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094467 prefixEnd_5094467 := by exact prefixLift 5094467
  have htrace : WordTrace (prefixWord ++ tailWord_5094467) baseStart_5094467 baseEnd_5094467 := by
    simpa [prefixWord, tailWord_5094467, baseEnd_5094467] using wordTrace_append hprefix tailTrace_5094467
  have hstable : (prefixWord ++ tailWord_5094467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094467).length < 2 ^ (prefixWord ++ tailWord_5094467).sum := by decide
  have hdescent : baseEnd_5094467 < baseStart_5094467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094476 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5094476 : Nat := 118140960795 + 5094476 * 2 ^ 59
def prefixEnd_5094476 : Nat := 4983230072969 + 3 ^ 40 * 5094476 * 2
def baseEnd_5094476 : Nat := 2615914870794715072920937

theorem tailTrace_5094476 : CollatzResearch.WordTrace tailWord_5094476 prefixEnd_5094476 2615914870794715072920937 := by
  unfold tailWord_5094476
  simp only [CollatzResearch.WordTrace]
  refine ⟨92905402345795497038159641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123873869794393996050879521 92905402345795497038159641)
  ·
    refine ⟨69679051759346622778619731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92905402345795497038159641 69679051759346622778619731)
    ·
      refine ⟨104518577639019934167929597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69679051759346622778619731 104518577639019934167929597)
      ·
        refine ⟨39194466614632475312973599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104518577639019934167929597 39194466614632475312973599)
        ·
          refine ⟨58791699921948712969460399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39194466614632475312973599 58791699921948712969460399)
          ·
            refine ⟨88187549882923069454190599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58791699921948712969460399 88187549882923069454190599)
            ·
              refine ⟨132281324824384604181285899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88187549882923069454190599 132281324824384604181285899)
              ·
                refine ⟨198421987236576906271928849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132281324824384604181285899 198421987236576906271928849)
                ·
                  refine ⟨148816490427432679703946637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198421987236576906271928849 148816490427432679703946637)
                  ·
                    refine ⟨55806183910287254888979989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148816490427432679703946637 55806183910287254888979989)
                    ·
                      refine ⟨2615914870794715072920937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55806183910287254888979989 2615914870794715072920937)
                      ·
                        rfl

theorem cell23_5094476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5094476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094476 prefixEnd_5094476 := by exact prefixLift 5094476
  have htrace : WordTrace (prefixWord ++ tailWord_5094476) baseStart_5094476 baseEnd_5094476 := by
    simpa [prefixWord, tailWord_5094476, baseEnd_5094476] using wordTrace_append hprefix tailTrace_5094476
  have hstable : (prefixWord ++ tailWord_5094476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094476).length < 2 ^ (prefixWord ++ tailWord_5094476).sum := by decide
  have hdescent : baseEnd_5094476 < baseStart_5094476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094480 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2]
def baseStart_5094480 : Nat := 118140960795 + 5094480 * 2 ^ 59
def prefixEnd_5094480 : Nat := 4983230072969 + 3 ^ 40 * 5094480 * 2
def baseEnd_5094480 : Nat := 2615916924717333057270919

theorem tailTrace_5094480 : CollatzResearch.WordTrace tailWord_5094480 prefixEnd_5094480 2615916924717333057270919 := by
  unfold tailWord_5094480
  simp only [CollatzResearch.WordTrace]
  refine ⟨92905475291788251379732447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123873967055717668506309929 92905475291788251379732447)
  ·
    refine ⟨139358212937682377069598671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92905475291788251379732447 139358212937682377069598671)
    ·
      refine ⟨209037319406523565604398007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139358212937682377069598671 209037319406523565604398007)
      ·
        refine ⟨313555979109785348406597011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209037319406523565604398007 313555979109785348406597011)
        ·
          refine ⟨470333968664678022609895517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313555979109785348406597011 470333968664678022609895517)
          ·
            refine ⟨176375238249254258478710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470333968664678022609895517 176375238249254258478710819)
            ·
              refine ⟨264562857373881387718066229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176375238249254258478710819 264562857373881387718066229)
              ·
                refine ⟨24802767878801380098568709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264562857373881387718066229 24802767878801380098568709)
                ·
                  refine ⟨4650518977275258768481633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24802767878801380098568709 4650518977275258768481633)
                  ·
                    refine ⟨3487889232956444076361225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650518977275258768481633 3487889232956444076361225)
                    ·
                      refine ⟨2615916924717333057270919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487889232956444076361225 2615916924717333057270919)
                      ·
                        rfl

theorem cell23_5094480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2].length) (baseStart_5094480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094480 prefixEnd_5094480 := by exact prefixLift 5094480
  have htrace : WordTrace (prefixWord ++ tailWord_5094480) baseStart_5094480 baseEnd_5094480 := by
    simpa [prefixWord, tailWord_5094480, baseEnd_5094480] using wordTrace_append hprefix tailTrace_5094480
  have hstable : (prefixWord ++ tailWord_5094480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094480).length < 2 ^ (prefixWord ++ tailWord_5094480).sum := by decide
  have hdescent : baseEnd_5094480 < baseStart_5094480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094497 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_5094497 : Nat := 118140960795 + 5094497 * 2 ^ 59
def prefixEnd_5094497 : Nat := 4983230072969 + 3 ^ 40 * 5094497 * 2
def baseEnd_5094497 : Nat := 2615925653888459490758341

theorem tailTrace_5094497 : CollatzResearch.WordTrace tailWord_5094497 prefixEnd_5094497 2615925653888459490758341 := by
  unfold tailWord_5094497
  simp only [CollatzResearch.WordTrace]
  refine ⟨185811570624514914662833745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123874380416343276441889163 185811570624514914662833745)
  ·
    refine ⟨139358677968386185997125309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185811570624514914662833745 139358677968386185997125309)
    ·
      refine ⟨52259504238144819748921991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139358677968386185997125309 52259504238144819748921991)
      ·
        refine ⟨78389256357217229623382987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52259504238144819748921991 78389256357217229623382987)
        ·
          refine ⟨117583884535825844435074481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78389256357217229623382987 117583884535825844435074481)
          ·
            refine ⟨88187913401869383326305861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117583884535825844435074481 88187913401869383326305861)
            ·
              refine ⟨16535233762850509373682349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88187913401869383326305861 16535233762850509373682349)
              ·
                refine ⟨6200712661068941015130881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16535233762850509373682349 6200712661068941015130881)
                ·
                  refine ⟨4650534495801705761348161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6200712661068941015130881 4650534495801705761348161)
                  ·
                    refine ⟨3487900871851279321011121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650534495801705761348161 3487900871851279321011121)
                    ·
                      refine ⟨2615925653888459490758341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3487900871851279321011121 2615925653888459490758341)
                      ·
                        rfl

theorem cell23_5094497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_5094497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094497 prefixEnd_5094497 := by exact prefixLift 5094497
  have htrace : WordTrace (prefixWord ++ tailWord_5094497) baseStart_5094497 baseEnd_5094497 := by
    simpa [prefixWord, tailWord_5094497, baseEnd_5094497] using wordTrace_append hprefix tailTrace_5094497
  have hstable : (prefixWord ++ tailWord_5094497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094497).length < 2 ^ (prefixWord ++ tailWord_5094497).sum := by decide
  have hdescent : baseEnd_5094497 < baseStart_5094497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094503 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 7]
def baseStart_5094503 : Nat := 118140960795 + 5094503 * 2 ^ 59
def prefixEnd_5094503 : Nat := 4983230072969 + 3 ^ 40 * 5094503 * 2
def baseEnd_5094503 : Nat := 290658748308042940809257

theorem tailTrace_5094503 : CollatzResearch.WordTrace tailWord_5094503 prefixEnd_5094503 290658748308042940809257 := by
  unfold tailWord_5094503
  simp only [CollatzResearch.WordTrace]
  refine ⟨185811789462493177687552163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123874526308328785125034775 185811789462493177687552163)
  ·
    refine ⟨278717684193739766531328245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185811789462493177687552163 278717684193739766531328245)
    ·
      refine ⟨26129782893163103112312023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278717684193739766531328245 26129782893163103112312023)
      ·
        refine ⟨39194674339744654668468035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26129782893163103112312023 39194674339744654668468035)
        ·
          refine ⟨58792011509616982002702053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39194674339744654668468035 58792011509616982002702053)
          ·
            refine ⟨11023502158053184125506635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58792011509616982002702053 11023502158053184125506635)
            ·
              refine ⟨16535253237079776188259953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11023502158053184125506635 16535253237079776188259953)
              ·
                refine ⟨12401439927809832141194965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16535253237079776188259953 12401439927809832141194965)
                ·
                  refine ⟨290658748308042940809257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12401439927809832141194965 290658748308042940809257)
                  ·
                    rfl

theorem cell23_5094503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 7].length) (baseStart_5094503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094503 prefixEnd_5094503 := by exact prefixLift 5094503
  have htrace : WordTrace (prefixWord ++ tailWord_5094503) baseStart_5094503 baseEnd_5094503 := by
    simpa [prefixWord, tailWord_5094503, baseEnd_5094503] using wordTrace_append hprefix tailTrace_5094503
  have hstable : (prefixWord ++ tailWord_5094503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094503).length < 2 ^ (prefixWord ++ tailWord_5094503).sum := by decide
  have hdescent : baseEnd_5094503 < baseStart_5094503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094594 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5094594 : Nat := 118140960795 + 5094594 * 2 ^ 59
def prefixEnd_5094594 : Nat := 4983230072969 + 3 ^ 40 * 5094594 * 2
def baseEnd_5094594 : Nat := 2615975461511945611245395

theorem tailTrace_5094594 : CollatzResearch.WordTrace tailWord_5094594 prefixEnd_5094594 2615975461511945611245395 := by
  unfold tailWord_5094594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46453777126290875057278709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123876739003442333486076557 46453777126290875057278709)
  ·
    refine ⟨4355041605589769536619879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46453777126290875057278709 4355041605589769536619879)
    ·
      refine ⟨6532562408384654304929819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4355041605589769536619879 6532562408384654304929819)
      ·
        refine ⟨9798843612576981457394729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532562408384654304929819 9798843612576981457394729)
        ·
          refine ⟨7349132709432736093046047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9798843612576981457394729 7349132709432736093046047)
          ·
            refine ⟨11023699064149104139569071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7349132709432736093046047 11023699064149104139569071)
            ·
              refine ⟨16535548596223656209353607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11023699064149104139569071 16535548596223656209353607)
              ·
                refine ⟨24803322894335484314030411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16535548596223656209353607 24803322894335484314030411)
                ·
                  refine ⟨37204984341503226471045617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24803322894335484314030411 37204984341503226471045617)
                  ·
                    refine ⟨27903738256127419853284213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37204984341503226471045617 27903738256127419853284213)
                    ·
                      refine ⟨2615975461511945611245395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27903738256127419853284213 2615975461511945611245395)
                      ·
                        rfl

theorem cell23_5094594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5094594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094594 prefixEnd_5094594 := by exact prefixLift 5094594
  have htrace : WordTrace (prefixWord ++ tailWord_5094594) baseStart_5094594 baseEnd_5094594 := by
    simpa [prefixWord, tailWord_5094594, baseEnd_5094594] using wordTrace_append hprefix tailTrace_5094594
  have hstable : (prefixWord ++ tailWord_5094594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094594).length < 2 ^ (prefixWord ++ tailWord_5094594).sum := by decide
  have hdescent : baseEnd_5094594 < baseStart_5094594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094603 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3]
def baseStart_5094603 : Nat := 118140960795 + 5094603 * 2 ^ 59
def prefixEnd_5094603 : Nat := 4983230072969 + 3 ^ 40 * 5094603 * 2
def baseEnd_5094603 : Nat := 2615980082837836076032853

theorem tailTrace_5094603 : CollatzResearch.WordTrace tailWord_5094603 prefixEnd_5094603 2615980082837836076032853 := by
  unfold tailWord_5094603
  simp only [CollatzResearch.WordTrace]
  refine ⟨185815436762130894766192463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123876957841420596510794975 185815436762130894766192463)
  ·
    refine ⟨278723155143196342149288695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185815436762130894766192463 278723155143196342149288695)
    ·
      refine ⟨418084732714794513223933043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278723155143196342149288695 418084732714794513223933043)
      ·
        refine ⟨627127099072191769835899565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418084732714794513223933043 627127099072191769835899565)
        ·
          refine ⟨235172662152071913688462337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627127099072191769835899565 235172662152071913688462337)
          ·
            refine ⟨176379496614053935266346753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235172662152071913688462337 176379496614053935266346753)
            ·
              refine ⟨132284622460540451449760065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176379496614053935266346753 132284622460540451449760065)
              ·
                refine ⟨99213466845405338587320049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132284622460540451449760065 99213466845405338587320049)
                ·
                  refine ⟨74410100134054003940490037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99213466845405338587320049 74410100134054003940490037)
                  ·
                    refine ⟨6975946887567562869420941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74410100134054003940490037 6975946887567562869420941)
                    ·
                      refine ⟨2615980082837836076032853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6975946887567562869420941 2615980082837836076032853)
                      ·
                        rfl

theorem cell23_5094603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3].length) (baseStart_5094603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094603 prefixEnd_5094603 := by exact prefixLift 5094603
  have htrace : WordTrace (prefixWord ++ tailWord_5094603) baseStart_5094603 baseEnd_5094603 := by
    simpa [prefixWord, tailWord_5094603, baseEnd_5094603] using wordTrace_append hprefix tailTrace_5094603
  have hstable : (prefixWord ++ tailWord_5094603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094603).length < 2 ^ (prefixWord ++ tailWord_5094603).sum := by decide
  have hdescent : baseEnd_5094603 < baseStart_5094603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094610 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_5094610 : Nat := 118140960795 + 5094610 * 2 ^ 59
def prefixEnd_5094610 : Nat := 4983230072969 + 3 ^ 40 * 5094610 * 2
def baseEnd_5094610 : Nat := 290664853022490838738369

theorem tailTrace_5094610 : CollatzResearch.WordTrace tailWord_5094610 prefixEnd_5094610 290664853022490838738369 := by
  unfold tailWord_5094610
  simp only [CollatzResearch.WordTrace]
  refine ⟨46453923018276383740424321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123877128048737023307798189 46453923018276383740424321)
  ·
    refine ⟨34840442263707287805318241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46453923018276383740424321 34840442263707287805318241)
    ·
      refine ⟨26130331697780465853988681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34840442263707287805318241 26130331697780465853988681)
      ·
        refine ⟨19597748773335349390491511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26130331697780465853988681 19597748773335349390491511)
        ·
          refine ⟨29396623160003024085737267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19597748773335349390491511 29396623160003024085737267)
          ·
            refine ⟨44094934740004536128605901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29396623160003024085737267 44094934740004536128605901)
            ·
              refine ⟨16535600527501701048227213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44094934740004536128605901 16535600527501701048227213)
              ·
                refine ⟨6200850197813137893085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16535600527501701048227213 6200850197813137893085205)
                ·
                  refine ⟨290664853022490838738369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6200850197813137893085205 290664853022490838738369)
                  ·
                    rfl

theorem cell23_5094610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_5094610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094610 prefixEnd_5094610 := by exact prefixLift 5094610
  have htrace : WordTrace (prefixWord ++ tailWord_5094610) baseStart_5094610 baseEnd_5094610 := by
    simpa [prefixWord, tailWord_5094610, baseEnd_5094610] using wordTrace_append hprefix tailTrace_5094610
  have hstable : (prefixWord ++ tailWord_5094610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094610).length < 2 ^ (prefixWord ++ tailWord_5094610).sum := by decide
  have hdescent : baseEnd_5094610 < baseStart_5094610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094670 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_5094670 : Nat := 118140960795 + 5094670 * 2 ^ 59
def prefixEnd_5094670 : Nat := 4983230072969 + 3 ^ 40 * 5094670 * 2
def baseEnd_5094670 : Nat := 872004828680562437965015

theorem tailTrace_5094670 : CollatzResearch.WordTrace tailWord_5094670 prefixEnd_5094670 872004828680562437965015 := by
  unfold tailWord_5094670
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227235056611020651110183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123878586968592110139254309 23227235056611020651110183)
  ·
    refine ⟨34840852584916530976665275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23227235056611020651110183 34840852584916530976665275)
    ·
      refine ⟨52261278877374796464997913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34840852584916530976665275 52261278877374796464997913)
      ·
        refine ⟨39195959158031097348748435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52261278877374796464997913 39195959158031097348748435)
        ·
          refine ⟨58793938737046646023122653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39195959158031097348748435 58793938737046646023122653)
          ·
            refine ⟨22047727026392492258670995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58793938737046646023122653 22047727026392492258670995)
            ·
              refine ⟨33071590539588738388006493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22047727026392492258670995 33071590539588738388006493)
              ·
                refine ⟨12401846452345776895502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33071590539588738388006493 12401846452345776895502435)
                ·
                  refine ⟨18602769678518665343253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12401846452345776895502435 18602769678518665343253653)
                  ·
                    refine ⟨872004828680562437965015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18602769678518665343253653 872004828680562437965015)
                    ·
                      rfl

theorem cell23_5094670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_5094670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094670 prefixEnd_5094670 := by exact prefixLift 5094670
  have htrace : WordTrace (prefixWord ++ tailWord_5094670) baseStart_5094670 baseEnd_5094670 := by
    simpa [prefixWord, tailWord_5094670, baseEnd_5094670] using wordTrace_append hprefix tailTrace_5094670
  have hstable : (prefixWord ++ tailWord_5094670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094670).length < 2 ^ (prefixWord ++ tailWord_5094670).sum := by decide
  have hdescent : baseEnd_5094670 < baseStart_5094670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094703 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_5094703 : Nat := 118140960795 + 5094703 * 2 ^ 59
def prefixEnd_5094703 : Nat := 4983230072969 + 3 ^ 40 * 5094703 * 2
def baseEnd_5094703 : Nat := 2616031430903285684782393

theorem tailTrace_5094703 : CollatzResearch.WordTrace tailWord_5094703 prefixEnd_5094703 2616031430903285684782393 := by
  unfold tailWord_5094703
  simp only [CollatzResearch.WordTrace]
  refine ⟨185819084061768611844832763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123879389374512407896555175 185819084061768611844832763)
  ·
    refine ⟨278728626092652917767249145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185819084061768611844832763 278728626092652917767249145)
    ·
      refine ⟨209046469569489688325436859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278728626092652917767249145 209046469569489688325436859)
      ·
        refine ⟨313569704354234532488155289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209046469569489688325436859 313569704354234532488155289)
        ·
          refine ⟨235177278265675899366116467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313569704354234532488155289 235177278265675899366116467)
          ·
            refine ⟨352765917398513849049174701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235177278265675899366116467 352765917398513849049174701)
            ·
              refine ⟨132287219024442693393440513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352765917398513849049174701 132287219024442693393440513)
              ·
                refine ⟨99215414268332020045080385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132287219024442693393440513 99215414268332020045080385)
                ·
                  refine ⟨74411560701249015033810289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99215414268332020045080385 74411560701249015033810289)
                  ·
                    refine ⟨55808670525936761275357717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74411560701249015033810289 55808670525936761275357717)
                    ·
                      refine ⟨2616031430903285684782393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55808670525936761275357717 2616031430903285684782393)
                      ·
                        rfl

theorem cell23_5094703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_5094703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094703 prefixEnd_5094703 := by exact prefixLift 5094703
  have htrace : WordTrace (prefixWord ++ tailWord_5094703) baseStart_5094703 baseEnd_5094703 := by
    simpa [prefixWord, tailWord_5094703, baseEnd_5094703] using wordTrace_append hprefix tailTrace_5094703
  have hstable : (prefixWord ++ tailWord_5094703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094703).length < 2 ^ (prefixWord ++ tailWord_5094703).sum := by decide
  have hdescent : baseEnd_5094703 < baseStart_5094703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094721 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5094721 : Nat := 118140960795 + 5094721 * 2 ^ 59
def prefixEnd_5094721 : Nat := 4983230072969 + 3 ^ 40 * 5094721 * 2
def baseEnd_5094721 : Nat := 872013557851688871452437

theorem tailTrace_5094721 : CollatzResearch.WordTrace tailWord_5094721 prefixEnd_5094721 872013557851688871452437 := by
  unfold tailWord_5094721
  simp only [CollatzResearch.WordTrace]
  refine ⟨185819740575703400918988017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123879827050468933945992011 185819740575703400918988017)
  ·
    refine ⟨139364805431777550689241013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185819740575703400918988017 139364805431777550689241013)
    ·
      refine ⟨13065450509229145377116345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139364805431777550689241013 13065450509229145377116345)
      ·
        refine ⟨9799087881921859032837259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13065450509229145377116345 9799087881921859032837259)
        ·
          refine ⟨14698631822882788549255889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9799087881921859032837259 14698631822882788549255889)
          ·
            refine ⟨11023973867162091411941917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14698631822882788549255889 11023973867162091411941917)
            ·
              refine ⟨4133990200185784279478219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11023973867162091411941917 4133990200185784279478219)
              ·
                refine ⟨6200985300278676419217329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133990200185784279478219 6200985300278676419217329)
                ·
                  refine ⟨4650738975209007314412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6200985300278676419217329 4650738975209007314412997)
                  ·
                    refine ⟨872013557851688871452437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650738975209007314412997 872013557851688871452437)
                    ·
                      rfl

theorem cell23_5094721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5094721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094721 prefixEnd_5094721 := by exact prefixLift 5094721
  have htrace : WordTrace (prefixWord ++ tailWord_5094721) baseStart_5094721 baseEnd_5094721 := by
    simpa [prefixWord, tailWord_5094721, baseEnd_5094721] using wordTrace_append hprefix tailTrace_5094721
  have hstable : (prefixWord ++ tailWord_5094721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094721).length < 2 ^ (prefixWord ++ tailWord_5094721).sum := by decide
  have hdescent : baseEnd_5094721 < baseStart_5094721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094724 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5094724 : Nat := 118140960795 + 5094724 * 2 ^ 59
def prefixEnd_5094724 : Nat := 4983230072969 + 3 ^ 40 * 5094724 * 2
def baseEnd_5094724 : Nat := 2616042213997030102619797

theorem tailTrace_5094724 : CollatzResearch.WordTrace tailWord_5094724 prefixEnd_5094724 2616042213997030102619797 := by
  unfold tailWord_5094724
  simp only [CollatzResearch.WordTrace]
  refine ⟨92909924997346266215673613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123879899996461688287564817 92909924997346266215673613)
  ·
    refine ⟨34841221874004849830877605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92909924997346266215673613 34841221874004849830877605)
    ·
      refine ⟨6532729101375909343289551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34841221874004849830877605 6532729101375909343289551)
      ·
        refine ⟨9799093652063864014934327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532729101375909343289551 9799093652063864014934327)
        ·
          refine ⟨14698640478095796022401491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9799093652063864014934327 14698640478095796022401491)
          ·
            refine ⟨22047960717143694033602237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14698640478095796022401491 22047960717143694033602237)
            ·
              refine ⟨8267985268928885262600839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22047960717143694033602237 8267985268928885262600839)
              ·
                refine ⟨12401977903393327893901259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8267985268928885262600839 12401977903393327893901259)
                ·
                  refine ⟨18602966855089991840851889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12401977903393327893901259 18602966855089991840851889)
                  ·
                    refine ⟨13952225141317493880638917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18602966855089991840851889 13952225141317493880638917)
                    ·
                      refine ⟨2616042213997030102619797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13952225141317493880638917 2616042213997030102619797)
                      ·
                        rfl

theorem cell23_5094724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5094724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094724 prefixEnd_5094724 := by exact prefixLift 5094724
  have htrace : WordTrace (prefixWord ++ tailWord_5094724) baseStart_5094724 baseEnd_5094724 := by
    simpa [prefixWord, tailWord_5094724, baseEnd_5094724] using wordTrace_append hprefix tailTrace_5094724
  have hstable : (prefixWord ++ tailWord_5094724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094724).length < 2 ^ (prefixWord ++ tailWord_5094724).sum := by decide
  have hdescent : baseEnd_5094724 < baseStart_5094724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094727 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_5094727 : Nat := 118140960795 + 5094727 * 2 ^ 59
def prefixEnd_5094727 : Nat := 4983230072969 + 3 ^ 40 * 5094727 * 2
def baseEnd_5094727 : Nat := 2616043754438993590882283

theorem tailTrace_5094727 : CollatzResearch.WordTrace tailWord_5094727 prefixEnd_5094727 2616043754438993590882283 := by
  unfold tailWord_5094727
  simp only [CollatzResearch.WordTrace]
  refine ⟨185819959413681663943706435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123879972942454442629137623 185819959413681663943706435)
  ·
    refine ⟨278729939120522495915559653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185819959413681663943706435 278729939120522495915559653)
    ·
      refine ⟨52261863585097967984167435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278729939120522495915559653 52261863585097967984167435)
      ·
        refine ⟨78392795377646951976251153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52261863585097967984167435 78392795377646951976251153)
        ·
          refine ⟨58794596533235213982188365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78392795377646951976251153 58794596533235213982188365)
          ·
            refine ⟨22047973699963205243320637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58794596533235213982188365 22047973699963205243320637)
            ·
              refine ⟨8267990137486201966245239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22047973699963205243320637 8267990137486201966245239)
              ·
                refine ⟨12401985206229302949367859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8267990137486201966245239 12401985206229302949367859)
                ·
                  refine ⟨18602977809343954424051789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12401985206229302949367859 18602977809343954424051789)
                  ·
                    refine ⟨6976116678503982909019421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18602977809343954424051789 6976116678503982909019421)
                    ·
                      refine ⟨2616043754438993590882283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6976116678503982909019421 2616043754438993590882283)
                      ·
                        rfl

theorem cell23_5094727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_5094727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094727 prefixEnd_5094727 := by exact prefixLift 5094727
  have htrace : WordTrace (prefixWord ++ tailWord_5094727) baseStart_5094727 baseEnd_5094727 := by
    simpa [prefixWord, tailWord_5094727, baseEnd_5094727] using wordTrace_append hprefix tailTrace_5094727
  have hstable : (prefixWord ++ tailWord_5094727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094727).length < 2 ^ (prefixWord ++ tailWord_5094727).sum := by decide
  have hdescent : baseEnd_5094727 < baseStart_5094727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094740 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5094740 : Nat := 118140960795 + 5094740 * 2 ^ 59
def prefixEnd_5094740 : Nat := 4983230072969 + 3 ^ 40 * 5094740 * 2
def baseEnd_5094740 : Nat := 2616050429687502040019723

theorem tailTrace_5094740 : CollatzResearch.WordTrace tailWord_5094740 prefixEnd_5094740 2616050429687502040019723 := by
  unfold tailWord_5094740
  simp only [CollatzResearch.WordTrace]
  refine ⟨92910216781317283581964837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123880289041756378109286449 92910216781317283581964837)
  ·
    refine ⟨17420665646496990671618407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92910216781317283581964837 17420665646496990671618407)
    ·
      refine ⟨26130998469745486007427611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17420665646496990671618407 26130998469745486007427611)
      ·
        refine ⟨39196497704618229011141417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26130998469745486007427611 39196497704618229011141417)
        ·
          refine ⟨29397373278463671758356063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39196497704618229011141417 29397373278463671758356063)
          ·
            refine ⟨44096059917695507637534095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29397373278463671758356063 44096059917695507637534095)
            ·
              refine ⟨66144089876543261456301143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44096059917695507637534095 66144089876543261456301143)
              ·
                refine ⟨99216134814814892184451715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66144089876543261456301143 99216134814814892184451715)
                ·
                  refine ⟨148824202222222338276677573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99216134814814892184451715 148824202222222338276677573)
                  ·
                    refine ⟨27904537916666688426877045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148824202222222338276677573 27904537916666688426877045)
                    ·
                      refine ⟨2616050429687502040019723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27904537916666688426877045 2616050429687502040019723)
                      ·
                        rfl

theorem cell23_5094740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5094740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094740 prefixEnd_5094740 := by exact prefixLift 5094740
  have htrace : WordTrace (prefixWord ++ tailWord_5094740) baseStart_5094740 baseEnd_5094740 := by
    simpa [prefixWord, tailWord_5094740, baseEnd_5094740] using wordTrace_append hprefix tailTrace_5094740
  have hstable : (prefixWord ++ tailWord_5094740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094740).length < 2 ^ (prefixWord ++ tailWord_5094740).sum := by decide
  have hdescent : baseEnd_5094740 < baseStart_5094740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094770 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5094770 : Nat := 118140960795 + 5094770 * 2 ^ 59
def prefixEnd_5094770 : Nat := 4983230072969 + 3 ^ 40 * 5094770 * 2
def baseEnd_5094770 : Nat := 2616065834107136922644585

theorem tailTrace_5094770 : CollatzResearch.WordTrace tailWord_5094770 prefixEnd_5094770 2616065834107136922644585 := by
  unfold tailWord_5094770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46455381938131470571880441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123881018501683921525014509 46455381938131470571880441)
  ·
    refine ⟨34841536453598602928910331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46455381938131470571880441 34841536453598602928910331)
    ·
      refine ⟨52262304680397904393365497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34841536453598602928910331 52262304680397904393365497)
      ·
        refine ⟨39196728510298428295024123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52262304680397904393365497 39196728510298428295024123)
        ·
          refine ⟨58795092765447642442536185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39196728510298428295024123 58795092765447642442536185)
          ·
            refine ⟨44096319574085731831902139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58795092765447642442536185 44096319574085731831902139)
            ·
              refine ⟨66144479361128597747853209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44096319574085731831902139 66144479361128597747853209)
              ·
                refine ⟨49608359520846448310889907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66144479361128597747853209 49608359520846448310889907)
                ·
                  refine ⟨74412539281269672466334861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49608359520846448310889907 74412539281269672466334861)
                  ·
                    refine ⟨27904702230476127174875573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74412539281269672466334861 27904702230476127174875573)
                    ·
                      refine ⟨2616065834107136922644585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27904702230476127174875573 2616065834107136922644585)
                      ·
                        rfl

theorem cell23_5094770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5094770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094770 prefixEnd_5094770 := by exact prefixLift 5094770
  have htrace : WordTrace (prefixWord ++ tailWord_5094770) baseStart_5094770 baseEnd_5094770 := by
    simpa [prefixWord, tailWord_5094770, baseEnd_5094770] using wordTrace_append hprefix tailTrace_5094770
  have hstable : (prefixWord ++ tailWord_5094770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094770).length < 2 ^ (prefixWord ++ tailWord_5094770).sum := by decide
  have hdescent : baseEnd_5094770 < baseStart_5094770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094780 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_5094780 : Nat := 118140960795 + 5094780 * 2 ^ 59
def prefixEnd_5094780 : Nat := 4983230072969 + 3 ^ 40 * 5094780 * 2
def baseEnd_5094780 : Nat := 2616070968913681883519539

theorem tailTrace_5094780 : CollatzResearch.WordTrace tailWord_5094780 prefixEnd_5094780 2616070968913681883519539 := by
  unfold tailWord_5094780
  simp only [CollatzResearch.WordTrace]
  refine ⟨92910946241244826997692897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123881261654993102663590529 92910946241244826997692897)
  ·
    refine ⟨69683209680933620248269673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92910946241244826997692897 69683209680933620248269673)
    ·
      refine ⟨52262407260700215186202255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69683209680933620248269673 52262407260700215186202255)
      ·
        refine ⟨78393610891050322779303383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52262407260700215186202255 78393610891050322779303383)
        ·
          refine ⟨117590416336575484168955075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78393610891050322779303383 117590416336575484168955075)
          ·
            refine ⟨176385624504863226253432613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117590416336575484168955075 176385624504863226253432613)
            ·
              refine ⟨33072304594661854922518615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176385624504863226253432613 33072304594661854922518615)
              ·
                refine ⟨49608456891992782383777923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33072304594661854922518615 49608456891992782383777923)
                ·
                  refine ⟨74412685337989173575666885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49608456891992782383777923 74412685337989173575666885)
                  ·
                    refine ⟨13952378500872970045437541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74412685337989173575666885 13952378500872970045437541)
                    ·
                      refine ⟨2616070968913681883519539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13952378500872970045437541 2616070968913681883519539)
                      ·
                        rfl

theorem cell23_5094780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_5094780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094780 prefixEnd_5094780 := by exact prefixLift 5094780
  have htrace : WordTrace (prefixWord ++ tailWord_5094780) baseStart_5094780 baseEnd_5094780 := by
    simpa [prefixWord, tailWord_5094780, baseEnd_5094780] using wordTrace_append hprefix tailTrace_5094780
  have hstable : (prefixWord ++ tailWord_5094780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094780).length < 2 ^ (prefixWord ++ tailWord_5094780).sum := by decide
  have hdescent : baseEnd_5094780 < baseStart_5094780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094807 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 5]
def baseStart_5094807 : Nat := 118140960795 + 5094807 * 2 ^ 59
def prefixEnd_5094807 : Nat := 4983230072969 + 3 ^ 40 * 5094807 * 2
def baseEnd_5094807 : Nat := 290676092543483697542435

theorem tailTrace_5094807 : CollatzResearch.WordTrace tailWord_5094807 prefixEnd_5094807 290676092543483697542435 := by
  unfold tailWord_5094807
  simp only [CollatzResearch.WordTrace]
  refine ⟨185822877253391837606618675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123881918168927891737745783 185822877253391837606618675)
  ·
    refine ⟨278734315880087756409928013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185822877253391837606618675 278734315880087756409928013)
    ·
      refine ⟨104525368455032908653723005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278734315880087756409928013 104525368455032908653723005)
      ·
        refine ⟨39197013170637340745146127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104525368455032908653723005 39197013170637340745146127)
        ·
          refine ⟨58795519755956011117719191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39197013170637340745146127 58795519755956011117719191)
          ·
            refine ⟨88193279633934016676578787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58795519755956011117719191 88193279633934016676578787)
            ·
              refine ⟨132289919450901025014868181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88193279633934016676578787 132289919450901025014868181)
              ·
                refine ⟨3100544987130492773785973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132289919450901025014868181 3100544987130492773785973)
                ·
                  refine ⟨290676092543483697542435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3100544987130492773785973 290676092543483697542435)
                  ·
                    rfl

theorem cell23_5094807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 5].length) (baseStart_5094807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094807 prefixEnd_5094807 := by exact prefixLift 5094807
  have htrace : WordTrace (prefixWord ++ tailWord_5094807) baseStart_5094807 baseEnd_5094807 := by
    simpa [prefixWord, tailWord_5094807, baseEnd_5094807] using wordTrace_append hprefix tailTrace_5094807
  have hstable : (prefixWord ++ tailWord_5094807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094807).length < 2 ^ (prefixWord ++ tailWord_5094807).sum := by decide
  have hdescent : baseEnd_5094807 < baseStart_5094807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094818 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_5094818 : Nat := 118140960795 + 5094818 * 2 ^ 59
def prefixEnd_5094818 : Nat := 4983230072969 + 3 ^ 40 * 5094818 * 2
def baseEnd_5094818 : Nat := 2616090481178552734844365

theorem tailTrace_5094818 : CollatzResearch.WordTrace tailWord_5094818 prefixEnd_5094818 2616090481178552734844365 := by
  unfold tailWord_5094818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46455819614087996621317277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123882185637567990990179405 46455819614087996621317277)
  ·
    refine ⟨17420932355282998732993979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46455819614087996621317277 17420932355282998732993979)
    ·
      refine ⟨26131398532924498099490969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17420932355282998732993979 26131398532924498099490969)
      ·
        refine ⟨19598548899693373574618227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26131398532924498099490969 19598548899693373574618227)
        ·
          refine ⟨29397823349540060361927341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19598548899693373574618227 29397823349540060361927341)
          ·
            refine ⟨11024183756077522635722753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29397823349540060361927341 11024183756077522635722753)
            ·
              refine ⟨8268137817058141976792065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11024183756077522635722753 8268137817058141976792065)
              ·
                refine ⟨6201103362793606482594049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8268137817058141976792065 6201103362793606482594049)
                ·
                  refine ⟨4650827522095204861945537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6201103362793606482594049 4650827522095204861945537)
                  ·
                    refine ⟨3488120641571403646459153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650827522095204861945537 3488120641571403646459153)
                    ·
                      refine ⟨2616090481178552734844365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488120641571403646459153 2616090481178552734844365)
                      ·
                        rfl

theorem cell23_5094818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_5094818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094818 prefixEnd_5094818 := by exact prefixLift 5094818
  have htrace : WordTrace (prefixWord ++ tailWord_5094818) baseStart_5094818 baseEnd_5094818 := by
    simpa [prefixWord, tailWord_5094818, baseEnd_5094818] using wordTrace_append hprefix tailTrace_5094818
  have hstable : (prefixWord ++ tailWord_5094818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094818).length < 2 ^ (prefixWord ++ tailWord_5094818).sum := by decide
  have hdescent : baseEnd_5094818 < baseStart_5094818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094820 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_5094820 : Nat := 118140960795 + 5094820 * 2 ^ 59
def prefixEnd_5094820 : Nat := 4983230072969 + 3 ^ 40 * 5094820 * 2
def baseEnd_5094820 : Nat := 872030502713287242339785

theorem tailTrace_5094820 : CollatzResearch.WordTrace tailWord_5094820 prefixEnd_5094820 872030502713287242339785 := by
  unfold tailWord_5094820
  simp only [CollatzResearch.WordTrace]
  refine ⟨92911675701172370413420957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123882234268229827217894609 92911675701172370413420957)
  ·
    refine ⟨34841878387939638905032859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92911675701172370413420957 34841878387939638905032859)
    ·
      refine ⟨52262817581909458357549289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34841878387939638905032859 52262817581909458357549289)
      ·
        refine ⟨39197113186432093768161967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52262817581909458357549289 39197113186432093768161967)
        ·
          refine ⟨58795669779648140652242951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39197113186432093768161967 58795669779648140652242951)
          ·
            refine ⟨88193504669472210978364427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58795669779648140652242951 88193504669472210978364427)
            ·
              refine ⟨132290257004208316467546641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88193504669472210978364427 132290257004208316467546641)
              ·
                refine ⟨99217692753156237350659981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132290257004208316467546641 99217692753156237350659981)
                ·
                  refine ⟨37206634782433589006497493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99217692753156237350659981 37206634782433589006497493)
                  ·
                    refine ⟨872030502713287242339785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37206634782433589006497493 872030502713287242339785)
                    ·
                      rfl

theorem cell23_5094820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_5094820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094820 prefixEnd_5094820 := by exact prefixLift 5094820
  have htrace : WordTrace (prefixWord ++ tailWord_5094820) baseStart_5094820 baseEnd_5094820 := by
    simpa [prefixWord, tailWord_5094820, baseEnd_5094820] using wordTrace_append hprefix tailTrace_5094820
  have hstable : (prefixWord ++ tailWord_5094820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094820).length < 2 ^ (prefixWord ++ tailWord_5094820).sum := by decide
  have hdescent : baseEnd_5094820 < baseStart_5094820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094857 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 6, 2]
def baseStart_5094857 : Nat := 118140960795 + 5094857 * 2 ^ 59
def prefixEnd_5094857 : Nat := 4983230072969 + 3 ^ 40 * 5094857 * 2
def baseEnd_5094857 : Nat := 2616110506924078082256685

theorem tailTrace_5094857 : CollatzResearch.WordTrace tailWord_5094857 prefixEnd_5094857 2616110506924078082256685 := by
  unfold tailWord_5094857
  simp only [CollatzResearch.WordTrace]
  refine ⟨185824700903210696145938825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123883133935473797430625883 185824700903210696145938825)
  ·
    refine ⟨139368525677408022109454119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185824700903210696145938825 139368525677408022109454119)
    ·
      refine ⟨209052788516112033164181179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139368525677408022109454119 209052788516112033164181179)
      ·
        refine ⟨313579182774168049746271769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209052788516112033164181179 313579182774168049746271769)
        ·
          refine ⟨235184387080626037309703827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313579182774168049746271769 235184387080626037309703827)
          ·
            refine ⟨352776580620939055964555741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235184387080626037309703827 352776580620939055964555741)
            ·
              refine ⟨132291217732852145986708403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352776580620939055964555741 132291217732852145986708403)
              ·
                refine ⟨198436826599278218980062605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132291217732852145986708403 198436826599278218980062605)
                ·
                  refine ⟨74413809974729332117523477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198436826599278218980062605 74413809974729332117523477)
                  ·
                    refine ⟨3488147342565437443008913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74413809974729332117523477 3488147342565437443008913)
                    ·
                      refine ⟨2616110506924078082256685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488147342565437443008913 2616110506924078082256685)
                      ·
                        rfl

theorem cell23_5094857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6, 2].length) (baseStart_5094857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094857 prefixEnd_5094857 := by exact prefixLift 5094857
  have htrace : WordTrace (prefixWord ++ tailWord_5094857) baseStart_5094857 baseEnd_5094857 := by
    simpa [prefixWord, tailWord_5094857, baseEnd_5094857] using wordTrace_append hprefix tailTrace_5094857
  have hstable : (prefixWord ++ tailWord_5094857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094857).length < 2 ^ (prefixWord ++ tailWord_5094857).sum := by decide
  have hdescent : baseEnd_5094857 < baseStart_5094857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094874 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_5094874 : Nat := 118140960795 + 5094874 * 2 ^ 59
def prefixEnd_5094874 : Nat := 4983230072969 + 3 ^ 40 * 5094874 * 2
def baseEnd_5094874 : Nat := 2616119236095204515744107

theorem tailTrace_5094874 : CollatzResearch.WordTrace tailWord_5094874 prefixEnd_5094874 2616119236095204515744107 := by
  unfold tailWord_5094874
  simp only [CollatzResearch.WordTrace]
  refine ⟨46456330236037277012326919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123883547296099405366205117 46456330236037277012326919)
  ·
    refine ⟨69684495354055915518490379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46456330236037277012326919 69684495354055915518490379)
    ·
      refine ⟨104526743031083873277735569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69684495354055915518490379 104526743031083873277735569)
      ·
        refine ⟨78395057273312904958301677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104526743031083873277735569 78395057273312904958301677)
        ·
          refine ⟨29398146477492339359363129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78395057273312904958301677 29398146477492339359363129)
          ·
            refine ⟨22048609858119254519522347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29398146477492339359363129 22048609858119254519522347)
            ·
              refine ⟨33072914787178881779283521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22048609858119254519522347 33072914787178881779283521)
              ·
                refine ⟨24804686090384161334462641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33072914787178881779283521 24804686090384161334462641)
                ·
                  refine ⟨18603514567788121000846981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24804686090384161334462641 18603514567788121000846981)
                  ·
                    refine ⟨3488158981460272687658809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18603514567788121000846981 3488158981460272687658809)
                    ·
                      refine ⟨2616119236095204515744107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488158981460272687658809 2616119236095204515744107)
                      ·
                        rfl

theorem cell23_5094874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_5094874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094874 prefixEnd_5094874 := by exact prefixLift 5094874
  have htrace : WordTrace (prefixWord ++ tailWord_5094874) baseStart_5094874 baseEnd_5094874 := by
    simpa [prefixWord, tailWord_5094874, baseEnd_5094874] using wordTrace_append hprefix tailTrace_5094874
  have hstable : (prefixWord ++ tailWord_5094874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094874).length < 2 ^ (prefixWord ++ tailWord_5094874).sum := by decide
  have hdescent : baseEnd_5094874 < baseStart_5094874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094901 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5094901 : Nat := 118140960795 + 5094901 * 2 ^ 59
def prefixEnd_5094901 : Nat := 4983230072969 + 3 ^ 40 * 5094901 * 2
def baseEnd_5094901 : Nat := 872044366690958636702161

theorem tailTrace_5094901 : CollatzResearch.WordTrace tailWord_5094901 prefixEnd_5094901 872044366690958636702161 := by
  unfold tailWord_5094901
  simp only [CollatzResearch.WordTrace]
  refine ⟨185826305715051291660540557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123884203810034194440360371 185826305715051291660540557)
  ·
    refine ⟨69684864643144234372702709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185826305715051291660540557 69684864643144234372702709)
    ·
      refine ⟨6532956060294771972440879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69684864643144234372702709 6532956060294771972440879)
      ·
        refine ⟨9799434090442157958661319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532956060294771972440879 9799434090442157958661319)
        ·
          refine ⟨14699151135663236937991979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9799434090442157958661319 14699151135663236937991979)
          ·
            refine ⟨22048726703494855406987969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14699151135663236937991979 22048726703494855406987969)
            ·
              refine ⟨16536545027621141555240977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22048726703494855406987969 16536545027621141555240977)
              ·
                refine ⟨12402408770715856166430733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16536545027621141555240977 12402408770715856166430733)
                ·
                  refine ⟨4650903289018446062411525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12402408770715856166430733 4650903289018446062411525)
                  ·
                    refine ⟨872044366690958636702161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650903289018446062411525 872044366690958636702161)
                    ·
                      rfl

theorem cell23_5094901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5094901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094901 prefixEnd_5094901 := by exact prefixLift 5094901
  have htrace : WordTrace (prefixWord ++ tailWord_5094901) baseStart_5094901 baseEnd_5094901 := by
    simpa [prefixWord, tailWord_5094901, baseEnd_5094901] using wordTrace_append hprefix tailTrace_5094901
  have hstable : (prefixWord ++ tailWord_5094901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094901).length < 2 ^ (prefixWord ++ tailWord_5094901).sum := by decide
  have hdescent : baseEnd_5094901 < baseStart_5094901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094914 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_5094914 : Nat := 118140960795 + 5094914 * 2 ^ 59
def prefixEnd_5094914 : Nat := 4983230072969 + 3 ^ 40 * 5094914 * 2
def baseEnd_5094914 : Nat := 290682197257931595471547

theorem tailTrace_5094914 : CollatzResearch.WordTrace tailWord_5094914 prefixEnd_5094914 290682197257931595471547 := by
  unfold tailWord_5094914
  simp only [CollatzResearch.WordTrace]
  refine ⟨46456694966001048720190949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123884519909336129920509197 46456694966001048720190949)
  ·
    refine ⟨8710630306125196635035803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46456694966001048720190949 8710630306125196635035803)
    ·
      refine ⟨13065945459187794952553705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8710630306125196635035803 13065945459187794952553705)
      ·
        refine ⟨9799459094390846214415279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13065945459187794952553705 9799459094390846214415279)
        ·
          refine ⟨14699188641586269321622919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9799459094390846214415279 14699188641586269321622919)
          ·
            refine ⟨22048782962379403982434379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14699188641586269321622919 22048782962379403982434379)
            ·
              refine ⟨33073174443569105973651569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22048782962379403982434379 33073174443569105973651569)
              ·
                refine ⟨24804880832676829480238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33073174443569105973651569 24804880832676829480238677)
                ·
                  refine ⟨290682197257931595471547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24804880832676829480238677 290682197257931595471547)
                  ·
                    rfl

theorem cell23_5094914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_5094914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094914 prefixEnd_5094914 := by exact prefixLift 5094914
  have htrace : WordTrace (prefixWord ++ tailWord_5094914) baseStart_5094914 baseEnd_5094914 := by
    simpa [prefixWord, tailWord_5094914, baseEnd_5094914] using wordTrace_append hprefix tailTrace_5094914
  have hstable : (prefixWord ++ tailWord_5094914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094914).length < 2 ^ (prefixWord ++ tailWord_5094914).sum := by decide
  have hdescent : baseEnd_5094914 < baseStart_5094914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5094981 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_5094981 : Nat := 118140960795 + 5094981 * 2 ^ 59
def prefixEnd_5094981 : Nat := 4983230072969 + 3 ^ 40 * 5094981 * 2
def baseEnd_5094981 : Nat := 2616174178525235597106115

theorem tailTrace_5094981 : CollatzResearch.WordTrace tailWord_5094981 prefixEnd_5094981 2616174178525235597106115 := by
  unfold tailWord_5094981
  simp only [CollatzResearch.WordTrace]
  refine ⟨185829223554761465323452797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123886149036507643548968531 185829223554761465323452797)
  ·
    refine ⟨69685958833035549496294799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185829223554761465323452797 69685958833035549496294799)
    ·
      refine ⟨104528938249553324244442199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69685958833035549496294799 104528938249553324244442199)
      ·
        refine ⟨156793407374329986366663299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104528938249553324244442199 156793407374329986366663299)
        ·
          refine ⟨235190111061494979549994949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156793407374329986366663299 235190111061494979549994949)
          ·
            refine ⟨44098145824030308665624053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235190111061494979549994949 44098145824030308665624053)
            ·
              refine ⟨4134201171002841437402255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44098145824030308665624053 4134201171002841437402255)
              ·
                refine ⟨6201301756504262156103383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134201171002841437402255 6201301756504262156103383)
                ·
                  refine ⟨9301952634756393234155075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6201301756504262156103383 9301952634756393234155075)
                  ·
                    refine ⟨13952928952134589851232613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9301952634756393234155075 13952928952134589851232613)
                    ·
                      refine ⟨2616174178525235597106115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13952928952134589851232613 2616174178525235597106115)
                      ·
                        rfl

theorem cell23_5094981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_5094981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5094981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5094981 prefixEnd_5094981 := by exact prefixLift 5094981
  have htrace : WordTrace (prefixWord ++ tailWord_5094981) baseStart_5094981 baseEnd_5094981 := by
    simpa [prefixWord, tailWord_5094981, baseEnd_5094981] using wordTrace_append hprefix tailTrace_5094981
  have hstable : (prefixWord ++ tailWord_5094981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5094981).length < 2 ^ (prefixWord ++ tailWord_5094981).sum := by decide
  have hdescent : baseEnd_5094981 < baseStart_5094981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5094981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095004 : List Nat := [2, 2, 4, 1, 2, 1, 3, 8]
def baseStart_5095004 : Nat := 118140960795 + 5095004 * 2 ^ 59
def prefixEnd_5095004 : Nat := 4983230072969 + 3 ^ 40 * 5095004 * 2
def baseEnd_5095004 : Nat := 96895777354825518782167

theorem tailTrace_5095004 : CollatzResearch.WordTrace tailWord_5095004 prefixEnd_5095004 96895777354825518782167 := by
  unfold tailWord_5095004
  simp only [CollatzResearch.WordTrace]
  refine ⟨92915031216839070125770033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123886708289118760167693377 92915031216839070125770033)
  ·
    refine ⟨69686273412629302594327525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92915031216839070125770033 69686273412629302594327525)
    ·
      refine ⟨13066176264867994236436411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69686273412629302594327525 13066176264867994236436411)
      ·
        refine ⟨19599264397301991354654617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13066176264867994236436411 19599264397301991354654617)
        ·
          refine ⟨14699448297976493515990963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19599264397301991354654617 14699448297976493515990963)
          ·
            refine ⟨22049172446964740273986445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14699448297976493515990963 22049172446964740273986445)
            ·
              refine ⟨8268439667611777602744917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22049172446964740273986445 8268439667611777602744917)
              ·
                refine ⟨96895777354825518782167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8268439667611777602744917 96895777354825518782167)
                ·
                  rfl

theorem cell23_5095004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 8].length) (baseStart_5095004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095004 prefixEnd_5095004 := by exact prefixLift 5095004
  have htrace : WordTrace (prefixWord ++ tailWord_5095004) baseStart_5095004 baseEnd_5095004 := by
    simpa [prefixWord, tailWord_5095004, baseEnd_5095004] using wordTrace_append hprefix tailTrace_5095004
  have hstable : (prefixWord ++ tailWord_5095004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095004).length < 2 ^ (prefixWord ++ tailWord_5095004).sum := by decide
  have hdescent : baseEnd_5095004 < baseStart_5095004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095021 : List Nat := [1, 5, 1, 1, 4, 1, 3, 7]
def baseStart_5095021 : Nat := 118140960795 + 5095021 * 2 ^ 59
def prefixEnd_5095021 : Nat := 4983230072969 + 3 ^ 40 * 5095021 * 2
def baseEnd_5095021 : Nat := 96896100657459831133553

theorem tailTrace_5095021 : CollatzResearch.WordTrace tailWord_5095021 prefixEnd_5095021 96896100657459831133553 := by
  unfold tailWord_5095021
  simp only [CollatzResearch.WordTrace]
  refine ⟨185830682474616552154908917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123887121649744368103272611 185830682474616552154908917)
  ·
    refine ⟨17421626481995301764522711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185830682474616552154908917 17421626481995301764522711)
    ·
      refine ⟨26132439722992952646784067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17421626481995301764522711 26132439722992952646784067)
      ·
        refine ⟨39198659584489428970176101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26132439722992952646784067 39198659584489428970176101)
        ·
          refine ⟨7349748672091767931908019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39198659584489428970176101 7349748672091767931908019)
          ·
            refine ⟨11024623008137651897862029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7349748672091767931908019 11024623008137651897862029)
            ·
              refine ⟨4134233628051619461698261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11024623008137651897862029 4134233628051619461698261)
              ·
                refine ⟨96896100657459831133553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4134233628051619461698261 96896100657459831133553)
                ·
                  rfl

theorem cell23_5095021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 7].length) (baseStart_5095021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095021 prefixEnd_5095021 := by exact prefixLift 5095021
  have htrace : WordTrace (prefixWord ++ tailWord_5095021) baseStart_5095021 baseEnd_5095021 := by
    simpa [prefixWord, tailWord_5095021, baseEnd_5095021] using wordTrace_append hprefix tailTrace_5095021
  have hstable : (prefixWord ++ tailWord_5095021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095021).length < 2 ^ (prefixWord ++ tailWord_5095021).sum := by decide
  have hdescent : baseEnd_5095021 < baseStart_5095021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095057 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_5095057 : Nat := 118140960795 + 5095057 * 2 ^ 59
def prefixEnd_5095057 : Nat := 4983230072969 + 3 ^ 40 * 5095057 * 2
def baseEnd_5095057 : Nat := 2616213203054977299755765

theorem tailTrace_5095057 : CollatzResearch.WordTrace tailWord_5095057 prefixEnd_5095057 2616213203054977299755765 := by
  unfold tailWord_5095057
  simp only [CollatzResearch.WordTrace]
  refine ⟨185831995502486130303219425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123887997001657420202146283 185831995502486130303219425)
  ·
    refine ⟨139373996626864597727414569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185831995502486130303219425 139373996626864597727414569)
    ·
      refine ⟨104530497470148448295560927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139373996626864597727414569 104530497470148448295560927)
      ·
        refine ⟨156795746205222672443341391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104530497470148448295560927 156795746205222672443341391)
        ·
          refine ⟨235193619307834008665012087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156795746205222672443341391 235193619307834008665012087)
          ·
            refine ⟨352790428961751012997518131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235193619307834008665012087 352790428961751012997518131)
            ·
              refine ⟨529185643442626519496277197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352790428961751012997518131 529185643442626519496277197)
              ·
                refine ⟨198444616290984944811103949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529185643442626519496277197 198444616290984944811103949)
                ·
                  refine ⟨74416731109119354304163981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198444616290984944811103949 74416731109119354304163981)
                  ·
                    refine ⟨27906274165919757864061493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74416731109119354304163981 27906274165919757864061493)
                    ·
                      refine ⟨2616213203054977299755765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27906274165919757864061493 2616213203054977299755765)
                      ·
                        rfl

theorem cell23_5095057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_5095057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095057 prefixEnd_5095057 := by exact prefixLift 5095057
  have htrace : WordTrace (prefixWord ++ tailWord_5095057) baseStart_5095057 baseEnd_5095057 := by
    simpa [prefixWord, tailWord_5095057, baseEnd_5095057] using wordTrace_append hprefix tailTrace_5095057
  have hstable : (prefixWord ++ tailWord_5095057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095057).length < 2 ^ (prefixWord ++ tailWord_5095057).sum := by decide
  have hdescent : baseEnd_5095057 < baseStart_5095057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095064 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_5095064 : Nat := 118140960795 + 5095064 * 2 ^ 59
def prefixEnd_5095064 : Nat := 4983230072969 + 3 ^ 40 * 5095064 * 2
def baseEnd_5095064 : Nat := 872072265806519590789411

theorem tailTrace_5095064 : CollatzResearch.WordTrace tailWord_5095064 prefixEnd_5095064 872072265806519590789411 := by
  unfold tailWord_5095064
  simp only [CollatzResearch.WordTrace]
  refine ⟨92916125406730385249362123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123888167208973846999149497 92916125406730385249362123)
  ·
    refine ⟨139374188110095577874043185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92916125406730385249362123 139374188110095577874043185)
    ·
      refine ⟨104530641082571683405532389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139374188110095577874043185 104530641082571683405532389)
      ·
        refine ⟨19599495202982190638537323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104530641082571683405532389 19599495202982190638537323)
        ·
          refine ⟨29399242804473285957805985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19599495202982190638537323 29399242804473285957805985)
          ·
            refine ⟨22049432103354964468354489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29399242804473285957805985 22049432103354964468354489)
            ·
              refine ⟨16537074077516223351265867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22049432103354964468354489 16537074077516223351265867)
              ·
                refine ⟨24805611116274335026898801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16537074077516223351265867 24805611116274335026898801)
                ·
                  refine ⟨18604208337205751270174101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24805611116274335026898801 18604208337205751270174101)
                  ·
                    refine ⟨872072265806519590789411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18604208337205751270174101 872072265806519590789411)
                    ·
                      rfl

theorem cell23_5095064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_5095064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095064 prefixEnd_5095064 := by exact prefixLift 5095064
  have htrace : WordTrace (prefixWord ++ tailWord_5095064) baseStart_5095064 baseEnd_5095064 := by
    simpa [prefixWord, tailWord_5095064, baseEnd_5095064] using wordTrace_append hprefix tailTrace_5095064
  have hstable : (prefixWord ++ tailWord_5095064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095064).length < 2 ^ (prefixWord ++ tailWord_5095064).sum := by decide
  have hdescent : baseEnd_5095064 < baseStart_5095064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 11]
def baseStart_5095107 : Nat := 118140960795 + 5095107 * 2 ^ 59
def prefixEnd_5095107 : Nat := 4983230072969 + 3 ^ 40 * 5095107 * 2
def baseEnd_5095107 : Nat := 872079625695900701376845

theorem tailTrace_5095107 : CollatzResearch.WordTrace tailWord_5095107 prefixEnd_5095107 872079625695900701376845 := by
  unfold tailWord_5095107
  simp only [CollatzResearch.WordTrace]
  refine ⟨185833819152304988842539575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123889212768203325895026383 185833819152304988842539575)
  ·
    refine ⟨278750728728457483263809363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185833819152304988842539575 278750728728457483263809363)
    ·
      refine ⟨418126093092686224895714045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278750728728457483263809363 418126093092686224895714045)
      ·
        refine ⟨156797284909757334335892767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418126093092686224895714045 156797284909757334335892767)
        ·
          refine ⟨235195927364636001503839151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156797284909757334335892767 235195927364636001503839151)
          ·
            refine ⟨352793891046954002255758727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235195927364636001503839151 352793891046954002255758727)
            ·
              refine ⟨529190836570431003383638091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352793891046954002255758727 529190836570431003383638091)
              ·
                refine ⟨793786254855646505075457137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529190836570431003383638091 793786254855646505075457137)
                ·
                  refine ⟨595339691141734878806592853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 793786254855646505075457137 595339691141734878806592853)
                  ·
                    refine ⟨872079625695900701376845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 595339691141734878806592853 872079625695900701376845)
                    ·
                      rfl

theorem cell23_5095107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_5095107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095107 prefixEnd_5095107 := by exact prefixLift 5095107
  have htrace : WordTrace (prefixWord ++ tailWord_5095107) baseStart_5095107 baseEnd_5095107 := by
    simpa [prefixWord, tailWord_5095107, baseEnd_5095107] using wordTrace_append hprefix tailTrace_5095107
  have hstable : (prefixWord ++ tailWord_5095107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095107).length < 2 ^ (prefixWord ++ tailWord_5095107).sum := by decide
  have hdescent : baseEnd_5095107 < baseStart_5095107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095122 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5095122 : Nat := 118140960795 + 5095122 * 2 ^ 59
def prefixEnd_5095122 : Nat := 4983230072969 + 3 ^ 40 * 5095122 * 2
def baseEnd_5095122 : Nat := 2616246579297519545442967

theorem tailTrace_5095122 : CollatzResearch.WordTrace tailWord_5095122 prefixEnd_5095122 2616246579297519545442967 := by
  unfold tailWord_5095122
  simp only [CollatzResearch.WordTrace]
  refine ⟨46458591561812661601083905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123889577498167097602890413 46458591561812661601083905)
  ·
    refine ⟨34843943671359496200812929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46458591561812661601083905 34843943671359496200812929)
    ·
      refine ⟨26132957753519622150609697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34843943671359496200812929 26132957753519622150609697)
      ·
        refine ⟨19599718315139716612957273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26132957753519622150609697 19599718315139716612957273)
        ·
          refine ⟨14699788736354787459717955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19599718315139716612957273 14699788736354787459717955)
          ·
            refine ⟨22049683104532181189576933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14699788736354787459717955 22049683104532181189576933)
            ·
              refine ⟨4134315582099783973045675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22049683104532181189576933 4134315582099783973045675)
              ·
                refine ⟨6201473373149675959568513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134315582099783973045675 6201473373149675959568513)
                ·
                  refine ⟨4651105029862256969676385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6201473373149675959568513 4651105029862256969676385)
                  ·
                    refine ⟨3488328772396692727257289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4651105029862256969676385 3488328772396692727257289)
                    ·
                      refine ⟨2616246579297519545442967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488328772396692727257289 2616246579297519545442967)
                      ·
                        rfl

theorem cell23_5095122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5095122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095122 prefixEnd_5095122 := by exact prefixLift 5095122
  have htrace : WordTrace (prefixWord ++ tailWord_5095122) baseStart_5095122 baseEnd_5095122 := by
    simpa [prefixWord, tailWord_5095122, baseEnd_5095122] using wordTrace_append hprefix tailTrace_5095122
  have hstable : (prefixWord ++ tailWord_5095122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095122).length < 2 ^ (prefixWord ++ tailWord_5095122).sum := by decide
  have hdescent : baseEnd_5095122 < baseStart_5095122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095126 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5095126 : Nat := 118140960795 + 5095126 * 2 ^ 59
def prefixEnd_5095126 : Nat := 4983230072969 + 3 ^ 40 * 5095126 * 2
def baseEnd_5095126 : Nat := 2616248633220137529792949

theorem tailTrace_5095126 : CollatzResearch.WordTrace tailWord_5095126 prefixEnd_5095126 2616248633220137529792949 := by
  unfold tailWord_5095126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614657008702259692967577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123889674759490770058320821 11614657008702259692967577)
  ·
    refine ⟨8710992756526694769725683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11614657008702259692967577 8710992756526694769725683)
    ·
      refine ⟨13066489134790042154588525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8710992756526694769725683 13066489134790042154588525)
      ·
        refine ⟨4899933425546265807970697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13066489134790042154588525 4899933425546265807970697)
        ·
          refine ⟨3674950069159699355978023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899933425546265807970697 3674950069159699355978023)
          ·
            refine ⟨5512425103739549033967035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674950069159699355978023 5512425103739549033967035)
            ·
              refine ⟨8268637655609323550950553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512425103739549033967035 8268637655609323550950553)
              ·
                refine ⟨6201478241706992663212915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8268637655609323550950553 6201478241706992663212915)
                ·
                  refine ⟨9302217362560488994819373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6201478241706992663212915 9302217362560488994819373)
                  ·
                    refine ⟨3488331510960183373057265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9302217362560488994819373 3488331510960183373057265)
                    ·
                      refine ⟨2616248633220137529792949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488331510960183373057265 2616248633220137529792949)
                      ·
                        rfl

theorem cell23_5095126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5095126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095126 prefixEnd_5095126 := by exact prefixLift 5095126
  have htrace : WordTrace (prefixWord ++ tailWord_5095126) baseStart_5095126 baseEnd_5095126 := by
    simpa [prefixWord, tailWord_5095126, baseEnd_5095126] using wordTrace_append hprefix tailTrace_5095126
  have hstable : (prefixWord ++ tailWord_5095126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095126).length < 2 ^ (prefixWord ++ tailWord_5095126).sum := by decide
  have hdescent : baseEnd_5095126 < baseStart_5095126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095141 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_5095141 : Nat := 118140960795 + 5095141 * 2 ^ 59
def prefixEnd_5095141 : Nat := 4983230072969 + 3 ^ 40 * 5095141 * 2
def baseEnd_5095141 : Nat := 872085445143318323701793

theorem tailTrace_5095141 : CollatzResearch.WordTrace tailWord_5095141 prefixEnd_5095141 872085445143318323701793 := by
  unfold tailWord_5095141
  simp only [CollatzResearch.WordTrace]
  refine ⟨185835059234181812649277277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123890039489454541766184851 185835059234181812649277277)
  ·
    refine ⟨69688147212818179743478979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185835059234181812649277277 69688147212818179743478979)
    ·
      refine ⟨104532220819227269615218469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69688147212818179743478979 104532220819227269615218469)
      ·
        refine ⟨19599791403605113052853463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104532220819227269615218469 19599791403605113052853463)
        ·
          refine ⟨29399687105407669579280195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19599791403605113052853463 29399687105407669579280195)
          ·
            refine ⟨44099530658111504368920293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29399687105407669579280195 44099530658111504368920293)
            ·
              refine ⟨8268661998395907069172555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44099530658111504368920293 8268661998395907069172555)
              ·
                refine ⟨12402992997593860603758833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8268661998395907069172555 12402992997593860603758833)
                ·
                  refine ⟨9302244748195395452819125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12402992997593860603758833 9302244748195395452819125)
                  ·
                    refine ⟨872085445143318323701793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9302244748195395452819125 872085445143318323701793)
                    ·
                      rfl

theorem cell23_5095141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_5095141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095141 prefixEnd_5095141 := by exact prefixLift 5095141
  have htrace : WordTrace (prefixWord ++ tailWord_5095141) baseStart_5095141 baseEnd_5095141 := by
    simpa [prefixWord, tailWord_5095141, baseEnd_5095141] using wordTrace_append hprefix tailTrace_5095141
  have hstable : (prefixWord ++ tailWord_5095141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095141).length < 2 ^ (prefixWord ++ tailWord_5095141).sum := by decide
  have hdescent : baseEnd_5095141 < baseStart_5095141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095164 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_5095164 : Nat := 118140960795 + 5095164 * 2 ^ 59
def prefixEnd_5095164 : Nat := 4983230072969 + 3 ^ 40 * 5095164 * 2
def baseEnd_5095164 : Nat := 2616268145485008381117773

theorem tailTrace_5095164 : CollatzResearch.WordTrace tailWord_5095164 prefixEnd_5095164 2616268145485008381117773 := by
  unfold tailWord_5095164
  simp only [CollatzResearch.WordTrace]
  refine ⟨92917949056549243788682273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123890598742065658384909697 92917949056549243788682273)
  ·
    refine ⟨69688461792411932841511705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92917949056549243788682273 69688461792411932841511705)
    ·
      refine ⟨52266346344308949631133779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69688461792411932841511705 52266346344308949631133779)
      ·
        refine ⟨78399519516463424446700669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52266346344308949631133779 78399519516463424446700669)
        ·
          refine ⟨29399819818673784167512751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78399519516463424446700669 29399819818673784167512751)
          ·
            refine ⟨44099729728010676251269127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29399819818673784167512751 44099729728010676251269127)
            ·
              refine ⟨66149594592016014376903691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44099729728010676251269127 66149594592016014376903691)
              ·
                refine ⟨99224391888024021565355537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66149594592016014376903691 99224391888024021565355537)
                ·
                  refine ⟨74418293916018016174016653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99224391888024021565355537 74418293916018016174016653)
                  ·
                    refine ⟨27906860218506756065256245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74418293916018016174016653 27906860218506756065256245)
                    ·
                      refine ⟨2616268145485008381117773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27906860218506756065256245 2616268145485008381117773)
                      ·
                        rfl

theorem cell23_5095164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_5095164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095164 prefixEnd_5095164 := by exact prefixLift 5095164
  have htrace : WordTrace (prefixWord ++ tailWord_5095164) baseStart_5095164 baseEnd_5095164 := by
    simpa [prefixWord, tailWord_5095164, baseEnd_5095164] using wordTrace_append hprefix tailTrace_5095164
  have hstable : (prefixWord ++ tailWord_5095164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095164).length < 2 ^ (prefixWord ++ tailWord_5095164).sum := by decide
  have hdescent : baseEnd_5095164 < baseStart_5095164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095178 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_5095178 : Nat := 118140960795 + 5095178 * 2 ^ 59
def prefixEnd_5095178 : Nat := 4983230072969 + 3 ^ 40 * 5095178 * 2
def baseEnd_5095178 : Nat := 2616275334214171326342709

theorem tailTrace_5095178 : CollatzResearch.WordTrace tailWord_5095178 prefixEnd_5095178 2616275334214171326342709 := by
  unfold tailWord_5095178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459102183761941992093547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123890939156698511978916125 46459102183761941992093547)
  ·
    refine ⟨69688653275642912988140321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46459102183761941992093547 69688653275642912988140321)
    ·
      refine ⟨52266489956732184741105241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69688653275642912988140321 52266489956732184741105241)
      ·
        refine ⟨39199867467549138555828931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52266489956732184741105241 39199867467549138555828931)
        ·
          refine ⟨58799801201323707833743397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39199867467549138555828931 58799801201323707833743397)
          ·
            refine ⟨11024962725248195218826887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58799801201323707833743397 11024962725248195218826887)
            ·
              refine ⟨16537444087872292828240331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11024962725248195218826887 16537444087872292828240331)
              ·
                refine ⟨24806166131808439242360497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16537444087872292828240331 24806166131808439242360497)
                ·
                  refine ⟨18604624598856329431770373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24806166131808439242360497 18604624598856329431770373)
                  ·
                    refine ⟨3488367112285561768456945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18604624598856329431770373 3488367112285561768456945)
                    ·
                      refine ⟨2616275334214171326342709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488367112285561768456945 2616275334214171326342709)
                      ·
                        rfl

theorem cell23_5095178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_5095178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095178 prefixEnd_5095178 := by exact prefixLift 5095178
  have htrace : WordTrace (prefixWord ++ tailWord_5095178) baseStart_5095178 baseEnd_5095178 := by
    simpa [prefixWord, tailWord_5095178, baseEnd_5095178] using wordTrace_append hprefix tailTrace_5095178
  have hstable : (prefixWord ++ tailWord_5095178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095178).length < 2 ^ (prefixWord ++ tailWord_5095178).sum := by decide
  have hdescent : baseEnd_5095178 < baseStart_5095178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095205 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_5095205 : Nat := 118140960795 + 5095205 * 2 ^ 59
def prefixEnd_5095205 : Nat := 4983230072969 + 3 ^ 40 * 5095205 * 2
def baseEnd_5095205 : Nat := 872096399397280906901695

theorem tailTrace_5095205 : CollatzResearch.WordTrace tailWord_5095205 prefixEnd_5095205 872096399397280906901695 := by
  unfold tailWord_5095205
  simp only [CollatzResearch.WordTrace]
  refine ⟨185837393505949951579607069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123891595670633301053071379 185837393505949951579607069)
  ·
    refine ⟨69689022564731231842352651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185837393505949951579607069 69689022564731231842352651)
    ·
      refine ⟨104533533847096847763528977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69689022564731231842352651 104533533847096847763528977)
      ·
        refine ⟨78400150385322635822646733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104533533847096847763528977 78400150385322635822646733)
        ·
          refine ⟨29400056394495988433492525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78400150385322635822646733 29400056394495988433492525)
          ·
            refine ⟨11025021147935995662559697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29400056394495988433492525 11025021147935995662559697)
            ·
              refine ⟨8268765860951996746919773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11025021147935995662559697 8268765860951996746919773)
              ·
                refine ⟨3100787197856998780094915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8268765860951996746919773 3100787197856998780094915)
                ·
                  refine ⟨4651180796785498170142373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100787197856998780094915 4651180796785498170142373)
                  ·
                    refine ⟨872096399397280906901695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4651180796785498170142373 872096399397280906901695)
                    ·
                      rfl

theorem cell23_5095205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_5095205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095205 prefixEnd_5095205 := by exact prefixLift 5095205
  have htrace : WordTrace (prefixWord ++ tailWord_5095205) baseStart_5095205 baseEnd_5095205 := by
    simpa [prefixWord, tailWord_5095205, baseEnd_5095205] using wordTrace_append hprefix tailTrace_5095205
  have hstable : (prefixWord ++ tailWord_5095205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095205).length < 2 ^ (prefixWord ++ tailWord_5095205).sum := by decide
  have hdescent : baseEnd_5095205 < baseStart_5095205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
